// forall-lsp: Language Server Protocol server
//
// Implements LSP 3.17 over JSON-RPC via stdin/stdout.
//
// Capabilities:
//   Phase 1: textDocument/didOpen, didChange, didSave ->
//              re-run checker -> emit textDocument/publishDiagnostics
//   Phase 2: textDocument/hover ->
//              look up identifier in module-level LspEnv, return proposition
//   Phase 3: textDocument/definition ->
//              look up identifier intro location, return LSP Location
//   Phase 4: textDocument/completion ->
//              context-aware completions: step keywords, tactic keywords, hyp names
//
// No external JSON library required -- we do minimal hand-rolled JSON
// parsing and generation for the small subset needed.
//
// -- Hover protocol (LSP2) ----------------------------------------------------
// Request:  textDocument/hover  { textDocument: {uri}, position: {line, character} }
// Response: { result: { contents: { kind: "markdown", value: "**name** : prop" } } }
//           or { result: null } if not found.
//
// -- Definition protocol (LSP3) -----------------------------------------------
// Request:  textDocument/definition  { textDocument: {uri}, position: {line, character} }
// Response: { result: { uri, range: { start: {line,char}, end: {line,char} } } }
//           or { result: null } if not found.
//
// -- Completion protocol (LSP4) -----------------------------------------------
// Request:  textDocument/completion  { textDocument: {uri}, position: {line, character} }
// Response: { result: { isIncomplete: false, items: [ {label, kind}, ... ] } }
//   CompletionItemKind: 6 = Variable (hyp names), 14 = Keyword (step/tactic keywords)
// -----------------------------------------------------------------------------

#include <forall/checker/checker.hpp>
#include <forall/diagnostics/diagnostic.hpp>
#include <forall/lexer/lexer.hpp>
#include <forall/lexer/token.hpp>

#include <cstdlib>
#include <iostream>
#include <optional>
#include <sstream>
#include <string>
#include <unordered_map>

// -- Minimal JSON-RPC helpers -------------------------------------------------

// Read a single JSON-RPC message from stdin.
// Format: "Content-Length: N\r\n\r\n<N bytes of JSON>"
static std::optional<std::string> read_message() {
    std::string header;
    std::size_t content_length = 0;
    while (std::getline(std::cin, header)) {
        if (header == "\r" || header.empty()) break;
        const std::string prefix = "Content-Length: ";
        if (header.substr(0, prefix.size()) == prefix)
            content_length = std::stoul(header.substr(prefix.size()));
    }
    if (content_length == 0 || !std::cin.good()) return std::nullopt;
    std::string body(content_length, '\0');
    std::cin.read(body.data(), static_cast<std::streamsize>(content_length));
    if (!std::cin.good()) return std::nullopt;
    return body;
}

// Write a JSON-RPC message to stdout.
static void write_message(const std::string& json) {
    std::cout << "Content-Length: " << json.size() << "\r\n\r\n" << json;
    std::cout.flush();
}

// Minimal JSON string escape.
static std::string json_escape(const std::string& s) {
    std::string out;
    for (char c : s) {
        switch (c) {
            case '"':  out += "\\\""; break;
            case '\\': out += "\\\\"; break;
            case '\n': out += "\\n";  break;
            case '\r': out += "\\r";  break;
            case '\t': out += "\\t";  break;
            default:   out += c;      break;
        }
    }
    return out;
}

// Extract a string value for a JSON key (very minimal -- single-level only).
// Returns empty string if not found.
static std::string json_str(const std::string& json, const std::string& key) {
    const std::string needle = "\"" + key + "\":\"";
    auto pos = json.find(needle);
    if (pos == std::string::npos) return {};
    pos += needle.size();
    auto end = pos;
    while (end < json.size() && json[end] != '"') {
        if (json[end] == '\\') ++end; // skip escaped char
        ++end;
    }
    return json.substr(pos, end - pos);
}

// Extract a numeric id from JSON.  Returns -1 if absent or not numeric.
static int json_id(const std::string& json) {
    const std::string needle = "\"id\":";
    auto pos = json.find(needle);
    if (pos == std::string::npos) return -1;
    pos += needle.size();
    while (pos < json.size() && (json[pos] == ' ')) ++pos;
    if (pos < json.size() && json[pos] == '"') return -1; // string id -- unsupported
    try { return std::stoi(json.substr(pos)); } catch (...) { return -1; }
}

// Extract the "method" field.
static std::string json_method(const std::string& json) {
    return json_str(json, "method");
}

// Extract nested text from textDocument content.
// Handles: { "textDocument": { "text": "..." } }
// and:     { "contentChanges": [ { "text": "..." } ] }
static std::string extract_text(const std::string& json) {
    auto pos = json.find("\"text\":\"");
    if (pos == std::string::npos) return {};
    pos += 8;
    std::string result;
    while (pos < json.size() && json[pos] != '"') {
        if (json[pos] == '\\' && pos + 1 < json.size()) {
            ++pos;
            switch (json[pos]) {
                case '"':  result += '"';  break;
                case '\\': result += '\\'; break;
                case 'n':  result += '\n'; break;
                case 'r':  result += '\r'; break;
                case 't':  result += '\t'; break;
                default:   result += json[pos]; break;
            }
        } else {
            result += json[pos];
        }
        ++pos;
    }
    return result;
}

// Extract the URI from the message.
static std::string extract_uri(const std::string& json) {
    return json_str(json, "uri");
}

// Convert a file:// URI to a filesystem path.
static std::string uri_to_path(const std::string& uri) {
    const std::string prefix = "file://";
    if (uri.substr(0, prefix.size()) != prefix) return uri;
    std::string path = uri.substr(prefix.size());
    // URL-decode %XX sequences.
    std::string decoded;
    for (std::size_t i = 0; i < path.size(); ++i) {
        if (path[i] == '%' && i + 2 < path.size()) {
            char hex[3] = {path[i+1], path[i+2], 0};
            decoded += static_cast<char>(std::strtol(hex, nullptr, 16));
            i += 2;
        } else if (path[i] == '/') {
#ifdef _WIN32
            decoded += '\\';
#else
            decoded += '/';
#endif
        } else {
            decoded += path[i];
        }
    }
    // On Windows, strip leading slash from /C:/... paths.
#ifdef _WIN32
    if (!decoded.empty() && decoded[0] == '\\' && decoded.size() > 2 && decoded[2] == ':')
        decoded = decoded.substr(1);
#endif
    return decoded;
}

// Convert a filesystem path back to a file:// URI (needed for go-to-definition
// when the intro location is in a different file from the one being edited).
static std::string path_to_uri(const std::string& path) {
    std::string uri = "file://";
#ifdef _WIN32
    // Windows: backslash -> forward slash; prepend / for drive letter
    uri += '/';
    for (char c : path)
        uri += (c == '\\') ? '/' : c;
#else
    uri += path;
#endif
    return uri;
}

// -- Diagnostic -> LSP JSON ---------------------------------------------------

static std::string severity_to_lsp(forall::diag::Severity sev) {
    switch (sev) {
        case forall::diag::Severity::Error:   return "1";
        case forall::diag::Severity::Warning: return "2";
        case forall::diag::Severity::Note:    return "3";
    }
    return "1";
}

// Build LSP publishDiagnostics JSON for a URI and diagnostic list.
static std::string make_publish_diagnostics(const std::string& uri,
                                             const std::vector<forall::diag::Diagnostic>& diags)
{
    std::ostringstream out;
    out << R"({"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":")"
        << json_escape(uri) << R"(","diagnostics":[)";
    bool first = true;
    for (const auto& d : diags) {
        if (!first) out << ",";
        first = false;
        // LSP lines/cols are 0-based; our SourceLocation is 1-based.
        uint32_t line    = d.loc.line > 0 ? d.loc.line - 1 : 0;
        uint32_t col     = d.loc.col  > 0 ? d.loc.col  - 1 : 0;
        // Use end_col when available (exclusive, 1-based -> 0-based = end_col - 1).
        uint32_t end_col = (d.end_col > d.loc.col) ? (d.end_col - 1) : (col + 1);
        out << R"({"range":{"start":{"line":)" << line
            << R"(,"character":)" << col
            << R"(},"end":{"line":)" << line
            << R"(,"character":)" << end_col
            << R"(}},"severity":)" << severity_to_lsp(d.severity)
            << R"(,"message":")" << json_escape(d.message) << R"("})";
    }
    out << R"(]}})";
    return out.str();
}

// -- Position extraction helpers ----------------------------------------------

// Extract a numeric value for a JSON key (integer).  Returns -1 if absent.
static int json_int(const std::string& json, const std::string& key) {
    const std::string needle = "\"" + key + "\":";
    auto pos = json.find(needle);
    if (pos == std::string::npos) return -1;
    pos += needle.size();
    while (pos < json.size() && json[pos] == ' ') ++pos;
    if (pos >= json.size() || json[pos] == '"') return -1;
    try { return std::stoi(json.substr(pos)); } catch (...) { return -1; }
}

// Extract cursor position from a textDocument request.
// LSP positions are 0-based; we convert to 1-based for our SourceLocation.
// Returns {line1based, col1based} or {0, 0} on failure.
static std::pair<uint32_t, uint32_t> extract_position(const std::string& json) {
    auto pos_start = json.find("\"position\":");
    if (pos_start == std::string::npos) return {0, 0};
    const std::string sub = json.substr(pos_start);
    int line = json_int(sub, "line");
    int character = json_int(sub, "character");
    if (line < 0 || character < 0) return {0, 0};
    return {static_cast<uint32_t>(line + 1), static_cast<uint32_t>(character + 1)};
}

// -- Identifier hit-testing ---------------------------------------------------
//
// Tokenizes the source and finds the identifier token whose location spans the
// given 1-based (line, col) position.  Returns the token lexeme, or empty
// string if no identifier is at that position.

static std::string find_name_at(const std::string& source,
                                 const std::string& filename,
                                 uint32_t line1, uint32_t col1)
{
    forall::diag::DiagnosticEngine dummy_diag;
    forall::lexer::Lexer lex{source, filename, dummy_diag};
    const auto tokens = lex.tokenize();

    for (const auto& tok : tokens) {
        if (tok.loc.line != line1) continue;
        // Token spans [start_col, start_col + len).  loc.col is 1-based.
        uint32_t start_col = tok.loc.col;
        uint32_t end_col   = start_col + static_cast<uint32_t>(tok.lexeme.size());
        if (col1 >= start_col && col1 < end_col) {
            if (tok.kind == forall::lexer::TokenKind::Identifier)
                return tok.lexeme;
        }
    }
    return {};
}

// -- Completion context detection ---------------------------------------------
//
// Determines what kind of completion to offer based on the text up to the
// cursor on the current line:
//   AfterBy      -- line (trimmed) starts with "by " or "from " -> tactic + hyp names
//   StartOfLine  -- only whitespace before cursor -> proof step keywords
//   General      -- anything else -> module-level names

enum class CompletionContext { AfterBy, StartOfLine, General };

static CompletionContext detect_completion_context(const std::string& source,
                                                   uint32_t line1,
                                                   uint32_t col1)
{
    std::vector<std::string> lines;
    std::istringstream iss(source);
    std::string ln;
    while (std::getline(iss, ln)) lines.push_back(ln);

    if (line1 < 1 || line1 > static_cast<uint32_t>(lines.size()))
        return CompletionContext::General;

    const std::string& current = lines[line1 - 1];
    uint32_t char_idx = col1 > 0 ? col1 - 1 : 0;
    const std::string prefix = current.substr(0, std::min(static_cast<std::size_t>(char_idx),
                                                          current.size()));

    std::string trimmed = prefix;
    trimmed.erase(0, trimmed.find_first_not_of(" \t"));

    if (trimmed.size() >= 3 &&
        (trimmed.substr(0, 3) == "by " ||
         (trimmed.size() >= 5 && trimmed.substr(0, 5) == "from ")))
        return CompletionContext::AfterBy;

    if (trimmed.empty())
        return CompletionContext::StartOfLine;

    return CompletionContext::General;
}

// -- Document state -----------------------------------------------------------

struct DocState {
    std::string              source;
    forall::checker::LspEnv  lsp_env;  // populated after each validation
};

// -- LSP server main loop -----------------------------------------------------

// Validate source, publish diagnostics, and return the LspEnv for hover/definition.
static forall::checker::LspEnv validate_and_publish(const std::string& uri,
                                                     const std::string& source)
{
    forall::diag::DiagnosticEngine diag;
    forall::checker::Checker checker{diag};
    const std::string path = uri_to_path(uri);
    auto lsp_env = checker.check_content_lsp(source, path);
    write_message(make_publish_diagnostics(uri, diag.diagnostics()));
    return lsp_env;
}

int main() {
    // Disable sync for faster I/O.
    std::ios::sync_with_stdio(false);

    // In-memory document store: URI -> DocState.
    std::unordered_map<std::string, DocState> documents;

    while (true) {
        auto msg = read_message();
        if (!msg) break;

        const std::string& json = *msg;
        const std::string method = json_method(json);
        const int id = json_id(json);

        if (method == "initialize") {
            // Respond with server capabilities.
            std::ostringstream resp;
            resp << R"({"jsonrpc":"2.0","id":)" << id
                 << R"(,"result":{"capabilities":{)"
                 << R"("textDocumentSync":1,)"
                 << R"("hoverProvider":true,)"
                 << R"("definitionProvider":true,)"
                 << R"("completionProvider":{"triggerCharacters":[" "]})"
                 << R"(},"serverInfo":{"name":"forall-lsp","version":"0.2.0"}}})";
            write_message(resp.str());

        } else if (method == "initialized") {
            // No response needed for notification.

        } else if (method == "shutdown") {
            std::ostringstream resp;
            resp << R"({"jsonrpc":"2.0","id":)" << id << R"(,"result":null})";
            write_message(resp.str());

        } else if (method == "exit") {
            break;

        } else if (method == "textDocument/didOpen") {
            const std::string uri  = extract_uri(json);
            const std::string text = extract_text(json);
            if (!uri.empty()) {
                auto& doc = documents[uri];
                doc.source  = text;
                doc.lsp_env = validate_and_publish(uri, text);
            }

        } else if (method == "textDocument/didChange") {
            const std::string uri  = extract_uri(json);
            const std::string text = extract_text(json);
            if (!uri.empty() && !text.empty()) {
                auto& doc = documents[uri];
                doc.source  = text;
                doc.lsp_env = validate_and_publish(uri, text);
            }

        } else if (method == "textDocument/didSave") {
            const std::string uri = extract_uri(json);
            auto it = documents.find(uri);
            if (it != documents.end()) {
                it->second.lsp_env = validate_and_publish(uri, it->second.source);
            }

        } else if (method == "textDocument/hover") {
            // LSP2: hover -> show proposition for the identifier under cursor.
            const std::string uri = extract_uri(json);
            auto [line1, col1] = extract_position(json);

            std::ostringstream resp;
            resp << R"({"jsonrpc":"2.0","id":)" << id;

            auto it = documents.find(uri);
            if (it != documents.end() && line1 > 0 && col1 > 0) {
                const std::string name = find_name_at(it->second.source,
                                                       uri_to_path(uri),
                                                       line1, col1);
                auto eit = it->second.lsp_env.find(name);
                if (!name.empty() && eit != it->second.lsp_env.end()) {
                    resp << R"(,"result":{"contents":{"kind":"markdown","value":"**)"
                         << json_escape(name) << "** : "
                         << json_escape(eit->second.prop_text)
                         << R"("}})";
                } else {
                    resp << R"(,"result":null)";
                }
            } else {
                resp << R"(,"result":null)";
            }
            resp << "}";
            write_message(resp.str());

        } else if (method == "textDocument/definition") {
            // LSP3: go-to-definition -> return the intro location for the identifier.
            const std::string uri = extract_uri(json);
            auto [line1, col1] = extract_position(json);

            std::ostringstream resp;
            resp << R"({"jsonrpc":"2.0","id":)" << id;

            auto it = documents.find(uri);
            if (it != documents.end() && line1 > 0 && col1 > 0) {
                const std::string name = find_name_at(it->second.source,
                                                       uri_to_path(uri),
                                                       line1, col1);
                auto eit = it->second.lsp_env.find(name);
                if (!name.empty() && eit != it->second.lsp_env.end()) {
                    const auto& loc = eit->second.intro_loc;
                    if (loc.line > 0) {
                        // Convert 1-based SourceLocation to 0-based LSP range.
                        uint32_t def_line = loc.line - 1;
                        uint32_t def_col  = loc.col  > 0 ? loc.col - 1 : 0;
                        const std::string def_uri = loc.file.empty() ? uri
                                                  : path_to_uri(loc.file);
                        resp << R"(,"result":{"uri":")" << json_escape(def_uri)
                             << R"(","range":{"start":{"line":)" << def_line
                             << R"(,"character":)" << def_col
                             << R"(},"end":{"line":)" << def_line
                             << R"(,"character":)" << (def_col + static_cast<uint32_t>(name.size()))
                             << R"(}}})";
                    } else {
                        resp << R"(,"result":null)";
                    }
                } else {
                    resp << R"(,"result":null)";
                }
            } else {
                resp << R"(,"result":null)";
            }
            resp << "}";
            write_message(resp.str());

        } else if (method == "textDocument/completion") {
            // LSP4: context-aware completions.
            const std::string uri = extract_uri(json);
            auto [line1, col1] = extract_position(json);

            std::ostringstream resp;
            resp << R"({"jsonrpc":"2.0","id":)" << id
                 << R"(,"result":{"isIncomplete":false,"items":[)";

            auto it = documents.find(uri);
            bool first_item = true;

            auto emit_item = [&](const std::string& label, int kind) {
                if (!first_item) resp << ",";
                first_item = false;
                resp << R"({"label":")" << json_escape(label)
                     << R"(","kind":)" << kind << "}";
            };

            if (it != documents.end()) {
                const CompletionContext ctx =
                    detect_completion_context(it->second.source, line1, col1);

                if (ctx == CompletionContext::AfterBy) {
                    // Tactic keywords (kind 14 = Keyword)
                    for (const char* kw : {"linarith", "ring", "norm_num", "decide",
                                           "omega", "simp", "field_simp", "positivity",
                                           "gcongr", "contrapositive"}) {
                        emit_item(kw, 14);
                    }
                    // All in-scope hypothesis names (kind 6 = Variable)
                    for (const auto& [name, entry] : it->second.lsp_env)
                        emit_item(name, 6);

                } else if (ctx == CompletionContext::StartOfLine) {
                    // Proof step keywords (kind 14 = Keyword)
                    for (const char* kw : {"have", "suppose", "assume", "take",
                                           "cases", "obtain", "induction", "calc",
                                           "then", "therefore", "thus",
                                           "contradiction", "split", "push neg"}) {
                        emit_item(kw, 14);
                    }

                } else {
                    // General: all module-level names (kind 6 = Variable)
                    for (const auto& [name, entry] : it->second.lsp_env)
                        emit_item(name, 6);
                }
            }

            resp << "]}}";
            write_message(resp.str());

        } else if (id >= 0) {
            // Unknown request -- respond with null result.
            std::ostringstream resp;
            resp << R"({"jsonrpc":"2.0","id":)" << id << R"(,"result":null})";
            write_message(resp.str());
        }
        // Unknown notifications are silently ignored.
    }
    return EXIT_SUCCESS;
}
