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
            if (s.type) r += " be a " + to_string(*s.type);
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

std::string format_decl(const ast::Decl& decl) {
    switch (decl.kind) {
    case ast::DeclKind::Axiom:
        return "axiom " + decl.name + " : " + to_string(decl.statement);

    case ast::DeclKind::Definition:
        return "definition " + decl.name
               + format_params(decl.params)
               + " : " + to_string(decl.statement);

    case ast::DeclKind::Lemma:
    case ast::DeclKind::Theorem: {
        const char* kw = (decl.kind == ast::DeclKind::Lemma) ? "lemma" : "theorem";
        std::string r = std::string{kw} + " " + decl.name + " : "
                        + to_string(decl.statement) + "\n";
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
    }
    return {};
}

std::string format_module(const ast::Module& mod) {
    std::string r;
    for (std::size_t i = 0; i < mod.decls.size(); ++i) {
        if (i > 0) r += "\n";
        r += format_decl(*mod.decls[i]) + "\n";
    }
    return r;
}

} // namespace forall::formatter
