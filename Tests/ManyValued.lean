import Gamen.ManyValued
import Gamen.Semantics
import Plausible
import Lean.Data.Json
import Lean.Util.CollectAxioms

/-!
# Tests for `Gamen.ManyValued` (Lean-only)

Plan: `plans/three-valued-logic-2026-09-29.md`, "Verification". Four
kinds of check:

- the **axiom audit** (`#assert_kernel_only`), which fails the build if a
  theorem depends on any axiom beyond `propext`, `Quot.sound` and
  `Classical.choice` (so on `sorryAx`, `Lean.ofReduceBool`, or the
  per-theorem axiom `native_decide` adds at 4.34);
- `decide` examples, checked by the kernel when this file compiles;
- unit `cases`, run by `lake test`;
- `specTableCases`: the CQL and FHIRPath truth tables in `data/specs/`
  against `strongKleene`.

The Plausible properties are in `Tests/Main.lean`'s `properties`; the
generator and predicates they use are here.
-/

namespace ManyValuedTests

open Gamen Gamen.ManyValued Lean Plausible

/-! ## Axiom audit -/

open Lean Elab Command in
/-- `#assert_kernel_only n₁ n₂ …` fails unless each constant depends only
on Lean's three standard axioms (`propext`, `Quot.sound`,
`Classical.choice`), i.e. unless it is checked by the kernel alone.

An allowlist, not a blocklist: at toolchain 4.34 `native_decide` no
longer shows up as `Lean.ofReduceBool` in `#print axioms` but as a fresh
axiom `<thm>._native.native_decide.ax_…` (found by planting one), so a
check for `ofReduceBool` alone would pass it. `sorryAx`,
`Lean.ofReduceBool` and `Lean.trustCompiler` are rejected too. -/
elab "#assert_kernel_only " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| collectAxioms n
    let bad := axs.filter fun a =>
      !(a == ``propext || a == ``Quot.sound || a == ``Classical.choice)
    unless bad.isEmpty do
      throwError m!"axiom audit: {n} depends on {bad.toList}"

#assert_kernel_only
  strongKleene_tables_classical strongKleene_agrees_classical eval_core_ok
  eval_allU strongKleene_allU strongKleene_no_tautologies weakKleene_no_tautologies
  lukasiewicz3_agrees_strongKleene lukasiewicz3_impl_differs

/-! ## Kernel-checked examples (`decide`) -/

def p : Formula := .atom "p"
def q : Formula := .atom "q"

/-- Excluded middle fails in K3 (`[thr:skl, prop 1]`) and holds in LP
(`[thr:mul:prop:LP-taut-CL]`). -/
theorem k3_lem : isTautology strongKleene (.or p (.not p)) = .ok false := by decide
theorem lp_lem : isTautology logicOfParadox (.or p (.not p)) = .ok true := by decide
/-- Łukasiewicz stipulated `u → u = t` so that A → A stays a tautology
(`[thr:luk]`, the paragraph before `def:lukasiewicz`). -/
theorem l3_selfImpl : isTautology lukasiewicz3 (.implies p p) = .ok true := by decide
/-- The OLT's worked example after `[thr:luk, prop 1]`. -/
theorem l3_example : isTautology lukasiewicz3 (.implies (.not p) (.implies p q)) = .ok true := by
  decide
/-- LP is paraconsistent: p, ¬p ⊭ q. K3 is not. -/
theorem lp_noExplosion : entails logicOfParadox [p, .not p] q = .ok false := by decide
theorem k3_explosion : entails strongKleene [p, .not p] q = .ok true := by decide

#assert_kernel_only k3_lem lp_lem l3_selfImpl l3_example lp_noExplosion k3_explosion

/-! ## Unit cases -/

def isErr (e : Except String α) : Bool :=
  match e with
  | .ok _ => false
  | .error _ => true

def cases : List (String × Bool) := [
  ("ManyValued: K3 has no tautology p ∨ ¬p [thr:skl, prop 1]",
    isTautology strongKleene (.or p (.not p)) == .ok false),
  ("ManyValued: weak Kleene has no tautology p → p [thr:skl, prop 1]",
    isTautology weakKleene (.implies p p) == .ok false),
  ("ManyValued: modus ponens p, p → q ⊨ q in K3",
    entails strongKleene [p, .implies p q] q == .ok true),
  ("ManyValued: p ⊭ p ∨ q in weak Kleene (q = u makes p ∨ q = u)",
    entails weakKleene [p] (.or p q) == .ok false),
  ("ManyValued: p ⊨ p ∨ q in strong Kleene",
    entails strongKleene [p] (.or p q) == .ok true),
  ("ManyValued: p → p is a Ł3 tautology, not a K3 one",
    isTautology lukasiewicz3 (.implies p p) == .ok true
      && isTautology strongKleene (.implies p p) == .ok false),
  ("ManyValued: ¬p → (p → q) is a Ł3 tautology [thr:luk]",
    isTautology lukasiewicz3 (.implies (.not p) (.implies p q)) == .ok true),
  ("ManyValued: p ∨ ¬p is an LP tautology [thr:mul:prop:LP-taut-CL]",
    isTautology logicOfParadox (.or p (.not p)) == .ok true),
  ("ManyValued: LP designates u: p, ¬p ⊭ q",
    entails logicOfParadox [p, .not p] q == .ok false),
  ("ManyValued: Gödel ¬u = f, so ¬¬p → p fails and p ∨ ¬p fails [thr:god:defn:goedel]",
    isTautology goedel3 (.implies (.not (.not p)) p) == .ok false
      && isTautology goedel3 (.or p (.not p)) == .ok false),
  ("ManyValued: Gödel ⊨ ¬(p ∧ ¬p)",
    isTautology goedel3 (.not (.and p (.not p))) == .ok true),
  ("ManyValued: classical ¬⊥ is a tautology; ⊥ entails anything",
    isTautology classical (.not .bot) == .ok true && entails classical [.bot] q == .ok true),
  ("ManyValued: ⊥ is not in K3's language (error, not a default)",
    isErr (isTautology strongKleene (.not .bot))),
  ("ManyValued: ↔ is not in any OLT three-valued matrix (error)",
    isErr (eval lukasiewicz3 (fun _ => .t) (.iff p q))),
  ("ManyValued: □p is not propositional (error, even with no atoms to enumerate)",
    isErr (isTautology strongKleene (.box p)) && isErr (isTautology classical (.box .bot))),
  ("ManyValued: an error in a premise is reported",
    isErr (entails strongKleene [.diamond p] p)),
  ("ManyValued: 3 atoms give 27 three-valued assignments, 8 classical",
    (assignments strongKleene.values [⟨"p"⟩, ⟨"q"⟩, ⟨"r"⟩]).length == 27
      && (assignments classical.values [⟨"p"⟩, ⟨"q"⟩, ⟨"r"⟩]).length == 8),
  ("ManyValued: atomList dedups in first-occurrence order",
    atomList (.and q (.or p (.not q))) == [⟨"q"⟩, ⟨"p"⟩])
]

/-! ## Spec truth tables (`data/specs/`) -/

/-- The three-valued function a spec operator should equal. `xor` is
not in the OLT's K3 matrix; it is checked against the K3 composite
(A ∨ B) ∧ ¬(A ∧ B). -/
def k3Op : String → Option (Nat × (TV3 → TV3 → TV3))
  | "and" => some (2, conjK3)
  | "or" => some (2, disjK3)
  | "implies" => some (2, implK3)
  | "xor" => some (2, fun a b => conjK3 (disjK3 a b) (negK (conjK3 a b)))
  | "not" => some (1, fun a _ => negK a)
  | _ => none

def tvOfString : String → Option TV3
  | "t" => some .t
  | "u" => some .u
  | "f" => some .f
  | _ => none

/-- Check one operator's table: every row maps through `valueMap` to a
value, the rows cover all `3^arity` inputs exactly once, and each result
equals the K3 function's. -/
def checkOperator (valueMap : String → Option TV3) (op : Json) : Except String Unit := do
  let name ← op.getObjValAs? String "name"
  let arity ← op.getObjValAs? Nat "arity"
  let rows ← op.getObjValAs? (Array (Array String)) "table"
  let some (k, fn) := k3Op name | throw s!"unknown operator {name}"
  unless k == arity do throw s!"{name}: arity {arity}, expected {k}"
  let mut seen : List (List TV3) := []
  for row in rows do
    let vals ← row.toList.mapM fun s =>
      match valueMap s with
      | some v => pure v
      | none => throw s!"{name}: cell {s.quote} has no value in valueMap"
    let (args, res) ← match arity, vals with
      | 1, [a, r] => pure ([a], fn a .t == r)
      | 2, [a, b, r] => pure ([a, b], fn a b == r)
      | _, _ => throw s!"{name}: row {row} has the wrong length"
    if seen.contains args then throw s!"{name}: duplicate row {row}"
    seen := args :: seen
    unless res do throw s!"{name}: row {row} disagrees with strong Kleene"
  unless seen.length == 3 ^ arity do
    throw s!"{name}: {seen.length} rows, expected {3 ^ arity}"

/-- One case per operator per spec file, plus one that each file has all
five operators. A file that can't be read or parsed fails its cases. -/
def specTableCases : IO (List (String × Bool)) := do
  let files := ["data/specs/cql-2.0.0-logical.json", "data/specs/fhirpath-3.0.0-boolean.json"]
  let mut out := []
  for path in files do
    let text ← try IO.FS.readFile path catch e => pure s!"<unreadable: {e}>"
    match Json.parse text with
    | .error e => out := out ++ [(s!"spec tables: {path} parses ({e})", false)]
    | .ok j =>
      let vm : Except String (List (String × String)) := do
        let obj ← j.getObjVal? "valueMap"
        let .obj kvs := obj | throw "valueMap is not an object"
        kvs.toList.mapM fun (key, v) => do pure (key, ← v.getStr?)
      let ops := (j.getObjValAs? (Array Json) "operators").toOption.getD #[]
      match vm with
      | .error e => out := out ++ [(s!"spec tables: {path} valueMap ({e})", false)]
      | .ok vm =>
        let valueMap := fun s => (vm.lookup s).bind tvOfString
        let names := ops.toList.filterMap fun o => (o.getObjValAs? String "name").toOption
        out := out ++ [(s!"spec tables: {path} has and, or, not, xor, implies",
          ["and", "or", "not", "xor", "implies"].all names.contains)]
        for op in ops do
          let name := (op.getObjValAs? String "name").toOption.getD "?"
          match checkOperator valueMap op with
          | .ok () => out := out ++ [(s!"spec tables: {path} {name} = strong Kleene", true)]
          | .error e =>
            IO.println s!"    {e}"
            out := out ++ [(s!"spec tables: {path} {name} = strong Kleene", false)]
  return out

/-! ## Plausible support -/

/-- A formula built from atoms p, q, r with ¬, ∧, ∨, → (`isCore`). -/
structure CoreFormula where
  getFormula : Formula
  deriving Repr

def genCore : Nat → Gen Formula
  | 0 => genAtom
  | n + 1 =>
    let h := (n + 1) / 2
    Gen.frequency genAtom [
      (4, genAtom),
      (3, .not <$> genCore n),
      (3, .and <$> genCore h <*> genCore h),
      (2, .or <$> genCore h <*> genCore h),
      (2, .implies <$> genCore h <*> genCore h)]
where
  genAtom : Gen Formula := do
    let ⟨i, _⟩ ← Gen.choose Nat 0 2 (by omega)
    return .atom (["p", "q", "r"].getD i "p")

instance : Arbitrary CoreFormula := ⟨CoreFormula.mk <$> Gen.sized fun n => genCore (min n 12)⟩
instance : Shrinkable CoreFormula where shrink _ := []

/-- A classical valuation of p, q, r. -/
def boolVal (bp bq br : Bool) (a : Atom) : Bool :=
  if a.name == "p" then bp else if a.name == "q" then bq else if a.name == "r" then br else false

/-- K3 on a {t, f}-valuation equals `Gamen.Semantics.satisfies` in the
one-world Kripke model with the same valuation. -/
def k3MatchesSemantics (f : Formula) (bp bq br : Bool) : Bool :=
  let trueAtoms := [("p", bp), ("q", bq), ("r", br)].filterMap fun (n, b) =>
    if b then some (n, ["w"]) else none
  match mkFrame ["w"] [] with
  | .error _ => false
  | .ok fr =>
    match satisfies (mkModel fr trueAtoms) "w" f,
          eval strongKleene (fun a => .ofBool (boolVal bp bq br a)) f with
    | .ok b, .ok x => x == .ofBool b
    | _, _ => false

/-- `eval` succeeds for every matrix on a core formula. -/
def evalNeverErrorsCore (f : Formula) : Bool :=
  let v3 : Atom → TV3 := fun a => if a.name == "p" then .u else if a.name == "q" then .t else .f
  let vb : Atom → Bool := fun a => a.name == "q"
  !isErr (eval classical vb f)
    && [strongKleene, weakKleene, lukasiewicz3, goedel3, logicOfParadox].all
      fun m => !isErr (eval m v3 f)

/-- `eval` succeeds for the matrices with ⊥ on formulas that use ⊥. -/
def evalNeverErrorsWithBot (f : Formula) : Bool :=
  !isErr (eval classical (fun a => a.name == "q") f)
    && !isErr (eval goedel3 (fun a => if a.name == "p" then .u else .t) f)

/-- LP's tautologies are the classical ones `[thr:mul:prop:LP-taut-CL]`. -/
def lpTautologiesClassical (f : Formula) : Bool :=
  match isTautology logicOfParadox f, isTautology classical f with
  | .ok a, .ok b => a == b
  | _, _ => false

/-- Enumeration-based classical tautology agrees with
`Gamen.Semantics.isTautology`. -/
def classicalTautologyMatchesSemantics (f : Formula) : Bool :=
  match isTautology classical f, Gamen.isTautology f with
  | .ok a, .ok b => a == b
  | _, _ => false

end ManyValuedTests
