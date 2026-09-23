import Gamen.Formula

/-!
# Gamen.Notation

Textbook notation for basic modal formulas, for notebooks and exercises:

    ml[ □(p → q) → (□p → □q) ]
    ml[ ◇(consent ∧ ¬thrombolytic) ]
    ml[ active_bleeding → □¬thrombolytic ]

Identifiers become atoms (`p` ↦ `Formula.atom "p"`); `{t}` splices in any
Lean term of type `Formula`, so named formulas can be reused:
`ml[ {g1} ∧ {g2} ]`.

Precedence follows B&D: ¬, □, ◇ bind tightest; then ∧, ∨, →, ↔; → and ↔
associate to the right. The symbols live in their own syntax category, so
they don't clash with Lean's `¬`, `∧`, `∨`, `→` on propositions.
-/
namespace Gamen

declare_syntax_cat modal

syntax ident : modal
syntax "⊥" : modal
syntax "⊤" : modal
syntax "(" modal ")" : modal
syntax "{" term "}" : modal
syntax:max "¬" modal:40 : modal
syntax:max "□" modal:40 : modal
syntax:max "◇" modal:40 : modal
syntax:35 modal:36 " ∧ " modal:35 : modal
syntax:30 modal:31 " ∨ " modal:30 : modal
syntax:25 modal:26 " → " modal:25 : modal
syntax:20 modal:21 " ↔ " modal:20 : modal

/-- `ml[ … ]` — a modal formula in textbook notation. -/
syntax:max "ml[" modal "]" : term

macro_rules
  | `(ml[ $x:ident ]) => `(Formula.atom $(Lean.quote x.getId.toString))
  | `(ml[ ⊥ ]) => `(Formula.bot)
  | `(ml[ ⊤ ]) => `(Formula.top)
  | `(ml[ ( $p ) ]) => `(ml[ $p ])
  | `(ml[ { $t } ]) => `(($t : Formula))
  | `(ml[ ¬ $p ]) => `(Formula.not ml[ $p ])
  | `(ml[ □ $p ]) => `(Formula.box ml[ $p ])
  | `(ml[ ◇ $p ]) => `(Formula.diamond ml[ $p ])
  | `(ml[ $p ∧ $q ]) => `(Formula.and ml[ $p ] ml[ $q ])
  | `(ml[ $p ∨ $q ]) => `(Formula.or ml[ $p ] ml[ $q ])
  | `(ml[ $p → $q ]) => `(Formula.implies ml[ $p ] ml[ $q ])
  | `(ml[ $p ↔ $q ]) => `(Formula.iff ml[ $p ] ml[ $q ])

-- The notation round-trips through the printer used everywhere else.
#guard toString ml[ □(p → q) → (□p → □q) ] == "(□(p → q) → (□p → □q))"
#guard toString ml[ ¬□¬p ∧ ◇q ∨ r ] == "((¬□¬p ∧ ◇q) ∨ r)"
#guard ml[ p → q → r ] == ml[ p → (q → r) ]
#guard ml[ {Formula.atom "x"} ∧ ⊤ ] == .and (.atom "x") (.not .bot)

end Gamen
