#include <forall/formatter/formatter.hpp>
#include <forall/pretty/to_string.hpp>

#include <sstream>

namespace forall::formatter {

namespace {

using pretty::to_string;

// ── Justification helper ──────────────────────────────────────────────────────

static std::string format_justification(const std::vector<std::string>& refs,
                                        const std::optional<ast::ExprPtr>& witness = {})
{
    if (refs.size() == 1 && refs[0] == "__decide__")  return " by decide";
    if (refs.size() == 1 && refs[0] == "__norm_num__") return " by norm_num";
    if (refs.size() == 1 && refs[0] == "__ring__")     return " by ring";
    if (refs.size() == 1 && refs[0] == "__linarith__") return " by linarith";
    if (refs.size() == 1 && refs[0] == "__simp__")     return " by simp";
    if (refs.size() == 1 && refs[0] == "__contra__")  return " by contra";
    if (refs.empty()) return "";
    std::string r = " by " + refs[0];
    for (std::size_t i = 1; i < refs.size(); ++i)
        r += " and " + refs[i];
    if (witness)
        r += " at " + to_string(**witness);
    return r;
}

// ── Step formatting ───────────────────────────────────────────────────────────

// Forward declaration for recursive step printing.
static std::string format_step(const ast::Step& step, const std::string& indent);
static std::string format_steps(const std::vector<std::unique_ptr<ast::Step>>& steps,
                                const std::string& indent);

static std::string format_steps(const std::vector<ast::Step>& steps,
                                const std::string& indent);

static std::string format_step(const ast::Step& step, const std::string& indent) {
    return std::visit([&](const auto& s) -> std::string {
        using T = std::decay_t<decltype(s)>;

        if constexpr (std::is_same_v<T, ast::LetStep>) {
            std::string r = indent + "let " + s.var;
            if (s.definition) r += " = " + to_string(**s.definition);
            else if (s.type)  r += " be a " + to_string(*s.type);
            return r;
        }

        if constexpr (std::is_same_v<T, ast::TakeStep>) {
            std::string r = indent + "take " + s.var;
            if (s.type) r += " : " + to_string(*s.type);
            return r;
        }

        if constexpr (std::is_same_v<T, ast::SupposeStep>) {
            std::string r = indent + "suppose";
            if (s.name) r += " " + *s.name + " : ";
            else        r += " ";
            r += to_string(s.prop);
            return r;
        }

        if constexpr (std::is_same_v<T, ast::HaveStep>) {
            return indent + "have " + s.name + " : "
                   + to_string(s.prop)
                   + format_justification(s.justification, s.witness);
        }

        if constexpr (std::is_same_v<T, ast::ThenStep>) {
            return indent + "then " + to_string(s.prop)
                   + format_justification(s.justification, s.witness);
        }

        if constexpr (std::is_same_v<T, ast::ContradictionStep>) {
            // contradiction uses ":" not "by"
            if (s.justification.empty()) return indent + "contradiction";
            std::string r = indent + "contradiction : " + s.justification[0];
            for (std::size_t i = 1; i < s.justification.size(); ++i)
                r += " and " + s.justification[i];
            return r;
        }

        if constexpr (std::is_same_v<T, ast::CasesStep>) {
            std::string r = indent + "cases " + s.name + " : " + s.disjunct_ref + "\n";
            const std::string arm_indent = indent + "  ";
            for (const auto& arm : s.arms) {
                r += indent + "  case " + arm.name + " : " + to_string(arm.prop) + " =>\n";
                r += format_steps(arm.steps, arm_indent + "  ");
                if (!r.empty() && r.back() != '\n') r += "\n";
                // Emit "done" only if the arm was followed by more steps.
                // Since we can't detect that from AST alone, always emit "done"
                // for arms to allow follow-up steps after cases.
                r += arm_indent + "  done\n";
            }
            return r;
        }

        if constexpr (std::is_same_v<T, ast::ObtainStep>) {
            std::string r = indent + "obtain " + s.name + " from " + s.exists_ref + "\n";
            r += indent + "  case " + s.var;
            if (s.type) r += " : " + to_string(*s.type);
            r += " , " + s.hyp_name + " : " + to_string(s.hyp_prop) + " =>\n";
            r += format_steps(s.steps, indent + "    ");
            if (!r.empty() && r.back() != '\n') r += "\n";
            r += indent + "  done";
            return r;
        }

        if constexpr (std::is_same_v<T, ast::InductionStep>) {
            std::string r = indent + "induction " + s.name + " on " + s.var
                            + " : " + to_string(s.body) + "\n";
            r += indent + "  base:\n";
            r += format_steps(s.base_steps, indent + "    ");
            r += indent + "  inductive:\n";
            r += format_steps(s.inductive_steps, indent + "    ");
            return r;
        }

        if constexpr (std::is_same_v<T, ast::ShowStep>) {
            return indent + "show " + to_string(s.prop);
        }

        if constexpr (std::is_same_v<T, ast::ExactStep>) {
            return indent + "exact " + s.hyp_ref;
        }

        if constexpr (std::is_same_v<T, ast::RewriteStep>) {
            return indent + "rewrite " + (s.reverse ? "\xe2\x86\x90 " : "") + s.hyp_ref;
        }

        if constexpr (std::is_same_v<T, ast::ApplyStep>) {
            return indent + "apply " + s.hyp_ref;
        }

        return indent + "-- (unknown step)";
    }, step.node);
}

static std::string format_steps(const std::vector<std::unique_ptr<ast::Step>>& steps,
                                const std::string& indent)
{
    std::string r;
    for (const auto& uptr : steps) {
        r += format_step(*uptr, indent) + "\n";
    }
    return r;
}

static std::string format_steps(const std::vector<ast::Step>& steps,
                                const std::string& indent)
{
    std::string r;
    for (const auto& step : steps) {
        r += format_step(step, indent) + "\n";
    }
    return r;
}

// ── Declaration formatting ────────────────────────────────────────────────────

static std::string format_params(const std::vector<ast::Param>& params) {
    std::string r;
    for (const auto& p : params)
        r += " (" + p.name + " : " + to_string(p.type) + ")";
    return r;
}

} // namespace

// Convert all Unicode math symbols to their ASCII/keyword equivalents.
// Applied when FormatterOptions::ascii_output is true.
static std::string to_ascii(std::string s) {
    struct Replacement { const char* from; const char* to; };
    static constexpr Replacement reps[] = {
        // Multi-byte replacements first (longer sequences must come before sub-sequences)
        {"\xe2\x88\x80", "for all"},     // ∀
        {"\xe2\x88\x83", "there exists"},// ∃
        {"\xe2\x86\x92", "->"},          // →
        {"\xe2\x86\x94", "iff"},         // ↔
        {"\xe2\x88\xa7", "and"},         // ∧
        {"\xe2\x88\xa8", "or"},          // ∨
        {"\xe2\x88\xa4", "true"},        // ⊤
        {"\xe2\x88\xa5", "false"},       // ⊥
        {"\xe2\x88\x88", "in"},          // ∈
        {"\xe2\x88\x89", "not in"},      // ∉
        {"\xe2\x8a\x86", "subseteq"},    // ⊆
        {"\xe2\x8a\x82", "subset"},      // ⊂
        {"\xe2\x8a\x87", "supseteq"},    // ⊇
        {"\xe2\x88\xaa", "union"},       // ∪
        {"\xe2\x88\xa9", "inter"},       // ∩
        {"\xe2\x88\x96", "setminus"},    // ∖
        {"\xe2\x88\x98", "compose"},     // ∘
        {"\xe2\x89\xa4", "<="},          // ≤
        {"\xe2\x89\xa5", ">="},          // ≥
        {"\xe2\x89\xa0", "/="},          // ≠
        {"\xe2\x88\x11", "prod"},        // ∏
        {"\xe2\x88\x91", "sum"},         // ∑
        {"\xe2\x96\xa1", "end"},         // □
        {"\xc2\xac", "not "},            // ¬ (with trailing space)
        {"\xce\xbb", "fun"},             // λ
    };
    for (const auto& r : reps) {
        std::string result;
        result.reserve(s.size());
        const std::size_t from_len = std::string_view{r.from}.size();
        std::size_t i = 0;
        while (i < s.size()) {
            if (s.compare(i, from_len, r.from) == 0) {
                result += r.to;
                i += from_len;
            } else {
                result += s[i++];
            }
        }
        s = std::move(result);
    }
    return s;
}

std::string format_decl(const ast::Decl& decl, const FormatterOptions& opts) {
    switch (decl.kind) {
    case ast::DeclKind::Axiom:
        return "axiom " + decl.name + " : " + to_string(decl.statement);

    case ast::DeclKind::Definition:
        if (!decl.struct_type.empty()) {
            // Structure instantiation form
            std::string r = "definition " + decl.name + " : " + decl.struct_type + " :=\n";
            for (const auto& [fname, fexpr] : decl.struct_bindings)
                r += "  " + fname + " := " + to_string(*fexpr) + "\n";
            if (!r.empty() && r.back() == '\n') r.pop_back();
            return r;
        }
        return "definition " + decl.name
               + format_params(decl.params)
               + " : " + to_string(decl.statement);

    case ast::DeclKind::Lemma:
    case ast::DeclKind::Theorem: {
        const char* kw = (decl.kind == ast::DeclKind::Lemma) ? "lemma" : "theorem";
        std::string r = std::string{kw} + " " + decl.name
                        + format_params(decl.params)
                        + " : " + to_string(decl.statement) + "\n";
        r += "proof\n";
        if (decl.proof)
            r += format_steps(decl.proof->steps, "  ");
        r += "end";
        return r;
    }

    case ast::DeclKind::Import:
        return "import \"" + decl.name + "\"";

    case ast::DeclKind::Instance:
        return "instance " + decl.name + " : " + decl.instance_class;

    case ast::DeclKind::Structure: {
        std::string r = "structure " + decl.name + " :=\n";
        for (const auto& field : decl.fields) {
            if (const auto* ft = std::get_if<ast::FieldTerm>(&field))
                r += "  " + ft->name + " : " + to_string(ft->type) + "\n";
            else if (const auto* fa = std::get_if<ast::FieldAxiom>(&field))
                r += "  axiom " + fa->name + " : " + to_string(fa->prop) + "\n";
        }
        // Remove trailing newline so format_module's own "\n" separator works correctly.
        if (!r.empty() && r.back() == '\n') r.pop_back();
        return r;
    }
    }
    return {};
}

std::string format_module(const ast::Module& mod, const FormatterOptions& opts) {
    std::string r;
    for (std::size_t i = 0; i < mod.decls.size(); ++i) {
        if (i > 0) r += "\n";
        r += format_decl(*mod.decls[i], opts) + "\n";
    }
    if (opts.ascii_output)
        r = to_ascii(std::move(r));
    return r;
}

} // namespace forall::formatter
