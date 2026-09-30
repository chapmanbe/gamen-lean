# DCLEG: final thesis vs. v5.0 draft vs. `Gamen.Dcleg` (2026-09-30)

A report, not a change: no code or tests were touched. It compares the
DCLEG v5.0 draft that `Gamen.Dcleg` was ported against with Chapter 3 of
Jeremiah Chapman's final thesis, then checks the implementation against
every difference.

## Sources

| | File | SHA-256 (checked 2026-09-30) |
|---|---|---|
| Final thesis (June 4th 2026), Ch. 3 | `notes/dcleg-thesis-final.pdf` (untracked) | `e4828132…fe86c88`, matches `notes/dcleg-edition.md` |
| v5.0 draft (April 2026) | `gamen-hs/notes/DCLEGv5.tex` | `73fa60ab…9cff480`, matches `notes/dcleg-edition.md` |
| Implementation | `Gamen/Dcleg.lean` at `057cd21` | |
| Tests | `Tests/Main.lean` (`dclegCases`, `dclegPaperCorrespondenceCases`, `dclegRegressionCases`, Dcleg properties at 3669–3695), `Tests/PropertyHelpers.lean` 1205–1265 | |

Final-thesis text was extracted with `pdftotext -layout`. Page numbers
below are the **printed** ones. Chapter 3 runs from p. 15 to p. 25:
§3.1.1 pp. 15–16, §3.1.2 p. 16, §3.2.1 pp. 16–18, §3.2.2 pp. 18–20,
§3.2.3 pp. 20–22, §3.2.4 pp. 22–23, §3.2.5 p. 23, §3.2.6 pp. 24–25.
The v5.0 sections map as §1.x → §3.1.x and §2.1–§2.6 → §3.2.1–§3.2.6.
v5.0's §2.7 ("Some Validities", Table 1) and §2.7.1 ("Notes on Comparisons
between ELEG and DCLEG") **have no counterpart in the final thesis.**

## Summary

| Status | Count |
|---|---|
| same | 60 |
| reworded | 17 |
| CHANGED IN MEANING | 1 |
| new | 4 |
| removed | 22 |
| **total** | **104** |

* **The semantics are unchanged.** The strategic structure and its seven
  conditions, the game model, Centering and Contemporary Universality, all
  eight doxastic conditions, and every satisfaction clause, the
  counterfactual included, have the same meaning. No condition was added.
  `dclegSatisfies` (`Gamen/Dcleg.lean:373–419`) implements the final
  thesis's §3.2.3 as it implemented v5.0's §2.3.
* **The one meaning change is Counterfactual K′ (§3.2.4, p. 22).** Its
  consequent changes from ψ to B_i ψ. The v5.0 form is not valid: the
  implementation falsifies it in a two-world model that meets every DCLEG
  condition (row 58), and the final form holds there. Neither
  form appears in the code or tests.
* **Table 1 is gone.** Its 17 validities, the prose around it and three of
  the four ELEG comparison notes are removed. Two of the 17 survive
  elsewhere: Ctf. K′_X is in §3.2.6, and Aware is Intentional Awareness
  (§3.2.4). Ten test labels cite "§2.7 Table 1" and have no final-thesis
  counterpart (section 3).
* **One B/□ interaction is dropped** (§3.2.5 lists four, v5.0 listed five).
  The dropped `¬B_i□φ ∨ φ` still holds under the final semantics.
* **Renames:** v5.0's `beg`/`fin` are now `start`/`end` (same definitions);
  `Mv` is `Move`.

## 1. Item-by-item comparison

Symbols: □→ is `\boxright`, □↔ is `\boxiff`, ◇→ is `\Diamondright`.

### Syntax (v5.0 §1 → final §3.1)

| # | Item | v5.0 | Final | Status |
|---|---|---|---|---|
| 1 | Atomic formulas ⊥, p, turn_i, m, k_i | §1.1 | §3.1.1 p. 15 | reworded: k_i's reading adds "“payoff” refers to the (at least ordinal) utility" |
| 2 | Constructors ¬, ∨, □→, B_i, X, Y, □ | §1.1 | §3.1.1 pp. 15–16 | same |
| 3 | Readings of the operators | §1.1 | §3.1.1 p. 16 | reworded: X φ "after this move" → "immediately after this move" |
| 4 | ⊤ := ¬⊥ | §1.2 | §3.1.2 p. 16 | same |
| 5 | φ ∧ ψ := ¬(¬φ ∨ ¬ψ) | §1.2 | §3.1.2 | same |
| 6 | m_i := m ∧ turn_i | §1.2 | §3.1.2 | same |
| 7 | φ □↔ ψ := (φ □→ ψ) ∧ (ψ □→ φ) | §1.2 | §3.1.2 | reworded: definition same; v5.0 said "(φ□↔ψ)□↔(¬φ□↔¬ψ) is not in general valid", final says "φ □↔ ψ is not equivalent to ¬φ □↔ ¬ψ" |
| 8 | φ ◇→ ψ := ¬(φ □→ ¬ψ) | §1.2 | §3.1.2 | same |
| 9 | B^E φ := ⋀_i B_i φ | §1.2 | §3.1.2 | same |
| 10 | B̂_i φ := ¬B_i¬φ | §1.2 | §3.1.2 | same |
| 11 | ◇φ := ¬□¬φ | §1.2 | §3.1.2 | same |
| 12 | `beg` := □¬Y⊤ | §1.2 | §3.1.2: **`start`** := □¬Y⊤ | reworded (renamed; adds the reading "No player has yet made a move") |
| 13 | `fin` := □¬X⊤ | §1.2 | §3.1.2: **`end`** := □¬X⊤ | reworded (renamed) |
| 14 | AX φ := ¬fin ∧ ⋀_m (m □→ X φ) | §1.2 | §3.1.2 (with `end`) | same |

### Strategic structures (v5.0 §2.1 → final §3.2.1)

| # | Item | Final | Status |
|---|---|---|---|
| 15 | T = ⟨V, EndV, Q, PMoves, next⟩ and the component types | pp. 16–17 | same |
| 16–22 | Conditions 1–7 (Q undefined iff end; PMoves empty iff end; next defined iff m ∈ PMoves; no self-loops; next injective; every outcome has a predecessor; unique root) | p. 17 | same (7 items) |
| 23 | "Does this structure describe a FPIE game?" | p. 17 | reworded: "no moves by nature" → "random chance plays no role"; adds "Q … ranges over A (rather than P(A))" |
| 24 | "Does this capture every FPIE game?" | pp. 17–18 | same |

### Game model (v5.0 §2.2 → final §3.2.2)

| # | Item | Final | Status |
|---|---|---|---|
| 25 | M = ⟨T, Γ, H, F, π, {R^w}, {ᚣ^w_i}, {P_i}⟩; \|Γ\| ≥ \|EndV\| | p. 18 | reworded (adds a motivating paragraph) |
| 26 | S⁺ := S ∪ S² ∪ … (footnote 1, "inspired by the Kleene plus") | p. 18 | new (notation for v5.0's undefined (V × Act)⁺) |
| 27 | History conditions 1–3 | pp. 18–19 | same |
| 28 | V_γ; every outcome node reached by some world | p. 19 | same |
| 29 | I, propositions ⊆ I, π, P_i | p. 19 | same |
| 30 | R^w := {(β,γ) \| w ∈ V_γ ∩ V_β} | p. 19 | same |
| 31 | F : Γ × V → P(P(I)) | p. 19 | same |
| 32 | Centering: ∩F(γ,w) = {(γ,w)} | p. 19 | same |
| 33 | Contemporary Universality: w ∈ V_β → (β,w) ∈ ∪F(γ,w) | p. 19 | same (forward reference now to §3.2.3) |
| 34 | ⟦φ⟧; "maximally φ-consistent"; max^φ_{F(γ,w)}(Γ) | p. 19 | reworded (adds ⟦⊤⟧ = I, ⟦⊥⟧ = ∅); definition same |
| 35 | Centering ⇒ max^φ = {(γ,w)} when (γ,w) ∈ ⟦φ⟧ | p. 19 | same |
| 36 | ᚣ^w_i ⊆ Γ² and ᚣ^w_i(γ) | pp. 19–20 | same |
| 37–44 | Presence, Present Seriality, Transitivity, Euclideanness, Self-Awareness, Minimal Revision, Expectational Continuity, Recall (conditions 1–8) | p. 20 | same (8 items; numbering and wording unchanged; no new condition) |

### Satisfaction (v5.0 §2.3 → final §3.2.3)

| # | Item | Final | Status |
|---|---|---|---|
| 46 | Mv(γ,w) | p. 20: **Move**(γ,w) = m "if m is such that (w,m) ∈ H(γ); if w ∉ V_γ … undefined" | reworded (renamed; undefinedness made explicit) |
| 47 | ⊥, p, turn_i clauses | p. 21 | same |
| 48 | m clause | p. 21 | reworded: v5.0 "(m,w) ∈ H(γ)" (pair reversed against H's (node, move) pairs) → "Move(γ,w) = m" |
| 49 | k_i clause | p. 21 | same |
| 50 | ¬, ∨ | p. 21 | same |
| 51 | B_i φ: w ∈ V_γ and φ at every µ with γ ᚣ^w_i µ | p. 21 | same |
| 52 | X φ: φ at next(w, Move(γ,w)) | p. 21 | same |
| 53 | Y φ: φ at w′ with w = next(w′, Move(γ,w′)) | p. 21 | same |
| 54 | □φ: φ at every β with γ R^w β | p. 21 | same |
| 55 | **φ □→ ψ: ψ at w in every β ∈ max^φ_{F(γ,w)}(Γ)** | p. 21 | **same** (clause and its commentary, pp. 21–22, identical) |
| 56 | Why `start`/`end` pick out the root and the outcomes | p. 21 | reworded (renamed) |
| 57 | Worked example for Contemporary Universality: without it, m′ □→ 1_i would hold vacuously though i's payoff would be 0 (footnote 5: "for any and all values k ∈ N") | p. 22 | new (illustration; no formal change) |

### Characteristics of belief (v5.0 §2.4 → final §3.2.4)

| # | Item | Final | Status |
|---|---|---|---|
| 58 | **Counterfactual K′** | p. 22 | **CHANGED IN MEANING** (see below) |
| 59 | Counterfactual D: B_i φ □→ B̂_i φ | p. 22 | same |
| 60 | Counterfactual 4: B_i φ □→ B_i B_i φ | p. 22 | same |
| 61 | Counterfactual 5: B̂_i φ □→ B_i B̂_i φ | p. 22 | same |
| 62 | Invalidity of the □→-translation of K, and of T and B | p. 22 | same |
| 63 | Counterfactual C4: B_i B_i φ □→ B_i φ; hence B_i φ □↔ B_i B_i φ | pp. 22–23 | same |
| 64 | Intentional Awareness: B_i m_i □↔ m_i | p. 23 | same |

**Row 58.** v5.0 §2.4: `(B_i(φ □→ ψ) ∧ B_i φ) □→ ψ`. Final §3.2.4,
p. 22: `(Bi (φ □→ ψ) ∧ Bi φ) □→ Bi ψ`. The text around it ("the
counterfactual translation of a classically equivalent formulation of K")
is the same in both, and fits only the final form. The v5.0 form is
T-like: it lets a belief force the truth of its object. It is not valid,
and the port's own evaluator shows it (scratch file, not committed). Take
one decision node v0 for p1 (moves L → v1, R → v2) and worlds gL
(plays L) and gR (plays R), with `withMovePremises`. p1 believes the move
actually played. p2 believes gR at v0 from both worlds, and at v1 and v2
believes the actual world. Checked by hand, this model meets Presence,
Present Seriality, Transitivity, Euclideanness, Self-Awareness, Minimal
Revision, Expectational Continuity, Recall, Centering and Contemporary
Universality, and `validateDclegModel` returns `[]`. With φ = ⊤ and
ψ = R, at (gL, v0):

| Formula | `dclegSatisfies` |
|---|---|
| v5.0: `(B_p2(⊤ □→ R) ∧ B_p2 ⊤) □→ R` | `ok false` |
| final: `(B_p2(⊤ □→ R) ∧ B_p2 ⊤) □→ B_p2 R` | `ok true` |

So the final thesis corrects what was probably a typo in v5.0, and the
correction makes the claim consistent with the semantics that both
versions share.

### Characteristics of necessity (v5.0 §2.5 → final §3.2.5)

| # | Item | Final | Status |
|---|---|---|---|
| 65 | When φ □→ ψ collapses to a material conditional | p. 23 | reworded (narrowed): v5.0 "many counterfactuals with □ in the antecedent collapse", with a footnote claiming, e.g., that □(p∧q) □→ r collapses and (□p □→ q) □→ r does not; final "if the main connective of φ is □, the counterfactual conditional φ □→ ψ always collapses to a material conditional"; footnote dropped |
| 66 | K, T, 5 for □; hence S5 (D, B, 4, C, C4) | p. 23 | same |
| 67 | `¬B_i□φ ∨ φ` | none | removed (v5.0 listed it first of five, with the prose "If φ is necessarily true, then it must be true now") |
| 68 | ¬B_i□φ ∨ □φ | p. 23 | same |
| 69 | ¬□φ ∨ B_i□φ | p. 23 | same |
| 70 | ¬B_i□φ ∨ □B_iφ | p. 23 | same |
| 71 | ¬B_i□φ ∨ □B_i□φ | p. 23 | same |
| 72 | Motivation for the B/□ interactions | p. 23 | reworded (new opening paragraph: the analysis is "necessary to guarantee that the conditions for perfect information hold") |

Row 67 is a removal from the text, not a change in the logic. The item
still holds: B_i□φ with Present Seriality gives □φ at some accessible
world; □φ is uniform across the worlds reaching w (Presence puts that
world there), so φ holds at γ. It also follows from row 68 and T. The
evaluator agrees: `dclegTrueIn` of `B_p2 □R → R` is `ok true` in the
model above. Row 65 matters for the implementation (section 2).

### Characteristics of the temporal operators (v5.0 §2.6 → final §3.2.6)

| # | Item | Final | Status |
|---|---|---|---|
| 73 | Opening paragraph: X and Y depend on the world, so they don't collapse as □ does, and counterfactual versions of the axioms are needed | p. 24 | new (prose) |
| 74 | Counterfactual K′_Y | p. 24 | same |
| 75 | Counterfactual K′_X | p. 24 | same (listed after K′_Y now) |
| 76 | Conditioned FUNC_Y: Y¬φ □↔ (Y⊤ ∧ ¬Yφ) | p. 24 | same |
| 77 | Conditioned FUNC_X: X¬φ □↔ (X⊤ ∧ ¬Xφ) | p. 24 | same |
| 78 | Why FUNC must be conditioned | p. 24 | reworded (justification replaced): v5.0 "If w ∉ V_γ, then we can have ¬Tφ without Tφ" (a case that satisfaction never evaluates); final "because time is finite in both directions … if w ∈ EndV, … ¬Xφ even though … ⊮ X¬φ" |
| 79 | (m ∧ B_i m ∧ B_i Xφ) □↔ (m ∧ B_i m ∧ X B_i φ) | p. 24 | same |
| 80 | B_i AX φ □→ X B_i φ | p. 24 | same |
| 81 | B_i Y B_i φ □↔ Y B_i φ | p. 25 | reworded (formula same; adds the "perfect recall" rationale) |

### Some Validities and ELEG notes (v5.0 §2.7, §2.7.1 → final: none)

| # | Item (v5.0 §2.7) | Final | Status |
|---|---|---|---|
| 82 | Intro: validities adapted from Lorini & Moisan (2011) Table 1; "all principles of classical propositional logic are preserved" | none | removed |
| 83 | Ctf. K′_X | none in a table (the same formula is §3.2.6 p. 24, row 75) | removed |
| 84 | Ctf. K′_AX: (AX(φ □→ ψ) ∧ AXφ) □→ AXψ | none | removed |
| 85 | Det_X: X⊤ □→ (Xφ ∨ X¬φ) | none | removed |
| 86 | PerfectInfo: □φ □→ B_i φ | none (nearest: ¬□φ ∨ B_i□φ, §3.2.5 p. 23; ¬□φ ∨ B_iφ appears in the prose only) | removed |
| 87 | NxtVert: □X□φ □↔ AX□φ | none | removed |
| 88 | TurnStr: turn_i □→ □turn_i | none | removed |
| 89 | TimeVert: (AXφ ∧ X⊤) □→ Xφ | none | removed |
| 90 | Aware: m_i □↔ B_i m_i | none in a table (Intentional Awareness, §3.2.4 p. 23, row 64) | removed |
| 91 | CompletePref: ⋁_k k_i | none | removed |
| 92 | SinglePref: k_i □→ ¬h_i (k ≠ h) | none | removed |
| 93 | OneAct: fin ∨ ⋁_m m | none | removed |
| 94 | SingleAct: m □→ ¬m′ (m ≠ m′) | none | removed |
| 95 | TurnTaking: fin ∨ ⋁_i turn_i | none | removed |
| 96 | SingleTurn: ¬turn_i ∨ ¬turn_j (i ≠ j) | none | removed |
| 97 | TimePref: fin ∨ (k_i □↔ X k_i) | none | removed |
| 98 | End Act: (X fin ∧ m ∧ k_i) □→ □(m □→ k_i) | none | removed |
| 99 | StrAct: (m ∧ X□φ) □→ □(m □→ Xφ) | none | removed |
| 100 | §2.7.1: AX had to be dropped from the basic syntax and redefined with counterfactuals | §2.5.2 p. 13 ("the AX operator of ELEG loses its original meaning and will be omitted from the basic syntax") | reworded (moved to Ch. 2) |
| 101 | §2.7.1: Perm_{[K_i],AX} translates to B_i AXφ □↔ AX B_i φ, which is invalid | none | removed |
| 102 | §2.7.1 footnote: AXφ can hold where Xφ does not | none | removed |
| 103 | §2.7.1: the new Y operator | §2.5.2 p. 14 | reworded (moved to Ch. 2) |
| 104 | §2.7.1: "there can be no past analogue of AX" | none | removed |

The final Chapter 3 also opens with a new overview paragraph (p. 15). It
is counted as new, which makes the fourth new item. The rows run to 104,
with no row 45, so there are 104 items.

## 2. Does `Gamen/Dcleg.lean` implement v5.0 or the final meaning?

The semantics didn't change, so no item forces a change to the library.
Item by item:

| Item | Where in the code | Which meaning | Code change to align |
|---|---|---|---|
| 58 Counterfactual K′ changed | Not stated or tested anywhere (`grep -n "K′\|K'" Gamen/Dcleg.lean Tests/Main.lean`: no DCLEG hits) | Both are evaluated faithfully by `dclegSatisfies` (`Gamen/Dcleg.lean:417–419`), and the final form is the one that holds | None in the library. Optionally add the section 1 countermodel as a test: final K′ true there, v5.0 K′ false |
| 67 `¬B_i□φ ∨ φ` removed | Not in the code or tests | n/a (still valid) | None |
| 82–99 Table 1 removed | Tests only: `Tests/Main.lean:5522–5525` (PerfectInfo in `dclegCases`), `5748–5770` (TurnStr, PerfectInfo, fin ×2, beg ×2, OneAct, SinglePref, CompletePref), header `5393–5398` | v5.0 (as material `→` at one point, per gamen-hs#53) | Tests only; see section 5. Either relabel as "DCLEG v5.0, Table 1" and follow gamen-hs PR #61, or re-anchor PerfectInfo to §3.2.5's `¬□φ ∨ B_i□φ` and the fin/beg cases to §3.1.2/§3.2.3 |
| 12–13 `beg`/`fin` → `start`/`end` | `Tests/Main.lean:5680–5684` (`dclegFin`, `dclegBeg`), labels at 5712–5714, 5756–5763; the library has no named abbreviation | Same definitions | Optional rename to `dclegEnd`/`dclegStart` and label text |
| 46 `Mv` → `Move` | `Gamen/Dcleg.lean:227` docstring (`moveAt`) | Same | Rename in the docstring only |
| 65 □-antecedent collapse (reworded, narrowed) | `withMovePremises`, `Gamen/Dcleg.lean:444–473` | **Neither version holds everywhere in the implementation's models.** At a single-move vertex that more than one world reaches, `withMovePremises` breaks Centering (review B8; the test at `Tests/Main.lean:5663` shows max^⊤ = [gA, gB]). There, □⊤ □→ ψ needs ψ at both worlds, while □⊤ → ψ needs it only at γ, so the final's "always collapses" fails | Close gamen-hs's TODO(#18), in Lean: add the singleton premise {(γ,w)} to F(γ,w) (`Gamen/Dcleg.lean:457–460`), then update the B8 tests at 5663 and the docstring at 468–472. This is a behavior change, so check `tools/compare/compare.py` scope first |

Pre-existing gaps, unchanged by the final thesis but relevant to it:
`validateDclegModel` (`Gamen/Dcleg.lean:282–324`) checks Presence (as
`nSubsetR`, 305–315) and Present Seriality only where an agent has a
doxastic map at w (316–324). The final thesis, like v5.0, requires Present
Seriality at every w ∈ V. Transitivity, Euclideanness, Self-Awareness,
Minimal Revision, Expectational Continuity, Recall, Centering, Contemporary
Universality, strategic-structure conditions 1–7, history conditions 1–3,
|Γ| ≥ |EndV| and outcome coverage are not checked. §3.2.3's new example
(row 57) says every available move has a maximally m-consistent world. That
depends on the outcome-coverage requirement, which the code doesn't
enforce.

## 3. Citation map

Every DCLEG section, condition or table citation. "v5.0" is where the
citation points now; "final" is where it should point.

### `Gamen/Dcleg.lean`

| Line(s) | Cites | v5.0 | Final |
|---|---|---|---|
| 8–11 | *Doxastic Conditional Logic of Extensive Games* (v5.0), April 2026 | the draft | *Doxastic Conditional Logic, Rationality, and Backward Induction …*, June 4th 2026, Ch. 3 |
| 18 | Syntax §1.1, abbreviations §1.2, strategic structures §2.1 | §1.1, §1.2, §2.1 | §3.1.1 pp. 15–16, §3.1.2 p. 16, §3.2.1 pp. 16–18 |
| 19 | Game models and premise function §2.2, satisfaction §2.3 | §2.2, §2.3 | §3.2.2 pp. 18–20, §3.2.3 pp. 20–22 |
| 69, 71 | Syntax | §1.1 | §3.1.1 pp. 15–16 |
| 100 | Abbreviations | §1.2 | §3.1.2 p. 16 |
| 118, 120 | T and conditions 1–7 | §2.1 | §3.2.1 pp. 16–17 |
| 147, 149 | History and its conditions | §2.2 | §3.2.2 pp. 18–19 |
| 166 | Propositions ⊆ I | §2.2 | §3.2.2 p. 19 |
| 179, 181, 183 | M; R^w | §2.2 | §3.2.2 pp. 18–19 |
| 189 | F; Centering; Contemporary Universality | §2.2 | §3.2.2 p. 19 |
| 227 | Mv(γ,w) | §2.3 | §3.2.3 p. 20 (as **Move**) |
| 247 | R^w | §2.2 | §3.2.2 p. 19 |
| 257 | ᚣ^w_i(γ) (written N^w_i) | §2.2 | §3.2.2 pp. 19–20 |
| 280 | Present Seriality, doxastic condition 2 | §2.2 | §3.2.2 p. 20 |
| 281 | Conditions 1–7 | §2.1 | §3.2.1 p. 17 |
| 326, 337 | max^φ_{F(γ,w)}(Γ) | §2.2 | §3.2.2 p. 19 |
| 369, 371 | Satisfaction | §2.3 | §3.2.3 p. 21 |
| 414 | □'s uniformity | §2.5 | §3.2.5 p. 23 |
| 416 | □→ | §2.2–2.3 | §3.2.2 p. 19, §3.2.3 pp. 21–22 |
| 421, 426 | ⟦φ⟧, max^φ | §2.2 | §3.2.2 p. 19 |
| 463 | Centering, Contemporary Universality | §2.2 | §3.2.2 p. 19 |

### `Tests/Main.lean`

| Line(s) | Cites | v5.0 | Final |
|---|---|---|---|
| 3685 | □ T-axiom (S5) | §2.5 | §3.2.5 p. 23 |
| 3690 | Centering | §2.2 | §3.2.2 p. 19 |
| 5384–5385 | gamen-hs's section title "(DCLEG v5.0)" | quoted name | keep as quoted |
| 5393–5398 | Header: Table 1 is §2.7; □ uniformity §2.5; Presence and Self-Awareness §2.2 conditions 1 and 5; gamen-hs#53 | §2.7, §2.5, §2.2 | Table 1: **none**; §3.2.5 p. 23; §3.2.2 p. 20 (conditions 1 and 5); #53: see section 5 |
| 5477–5506 | Atomic and temporal clauses | §2.3 | §3.2.3 p. 21 |
| 5508 | □ and B_i | §2.3–2.4 | §3.2.3 p. 21, §3.2.4 pp. 22–23 |
| 5509–5520 (except 5513–5514) | □, B_i clauses | §2.3 | §3.2.3 p. 21 |
| 5513–5514 | □ uniformity | §2.5 | §3.2.5 p. 23 |
| 5522–5523 | **PerfectInfo (Table 1, §2.7)**; Presence (§2.2) | §2.7; §2.2 | **none**; Presence §3.2.2 p. 20 |
| 5536–5538 | max-consistency witnesses; Centering | §2.2 | §3.2.2 p. 19 |
| 5540–5549 | □→ clause, vacuity | §2.3, §2.2 | §3.2.3 pp. 21–22, §3.2.2 p. 19 |
| 5551–5571 | Presence, Present Seriality, Transitivity, Euclideanness | §2.2 | §3.2.2 p. 20 (conditions 1–4) |
| 5576–5579 | Self-Awareness | §2.2 | §3.2.2 p. 20 (condition 5) |
| 5581–5585 | Intentional Awareness | §2.4 | §3.2.4 p. 23 |
| 5587–5600 | Centering, CU, F | §2.2 | §3.2.2 p. 19 |
| 5602–5623 | Minimal Revision, Expectational Continuity, Recall | §2.2 | §3.2.2 p. 20 (conditions 6–8) |
| 5680, 5683 | `fin`, `beg` | §1.2 | §3.1.2 p. 16, as `end`, `start` |
| 5688 | Label prefix "Chapman (2026) — DCLEG" | v5.0 | ambiguous once migrated; name the edition |
| 5689–5721, 5725–5741 | Satisfaction clauses | §2.3 | §3.2.3 pp. 21–22 |
| 5712, 5714 | "§2.3, fin/beg" | §2.3, §1.2 | §3.2.3 p. 21, `end`/`start` |
| 5723 | □ uniformity | §2.5 | §3.2.5 p. 23 |
| 5726, 5732 | Centering; vacuous □→ | §2.2 | §3.2.2 p. 19; vacuity §3.2.3 p. 22 |
| 5734–5737 | Self-Awareness | §2.2 | §3.2.2 p. 20 |
| 5743–5744 | Intentional Awareness | §2.4 | §3.2.4 p. 23 |
| 5748–5751 | Comment: Table 1 is §2.7; #53 | §2.7 | **none** |
| 5752, 5754 | **§2.7 Table 1**: TurnStr, PerfectInfo | §2.7 | **none** |
| 5756–5762 | **§2.7 Table 1**: fin ×2, beg ×2 (and §1.2) | §2.7, §1.2 | Table: **none**; definitions §3.1.2 p. 16; behavior §3.2.3 p. 21 |
| 5763–5770 | **§2.7 Table 1**: OneAct, SinglePref, CompletePref | §2.7 | **none** |

`Tests/PropertyHelpers.lean` (1205–1265) cites no DCLEG sections.

**Is the migration mechanical?** Mostly. Apart from Table 1, every
citation moves by a fixed rule (§1.x → §3.1.x, §2.k → §3.2.k for
k = 1…6), and conditions keep their numbers and names. Add the printed page,
and rename `beg`/`fin`/`Mv` → `start`/`end`/`Move`. **The ten Table 1
labels are not mechanical** (`Tests/Main.lean:5523, 5752, 5754, 5756, 5758,
5760, 5762, 5763, 5765, 5768`, plus the comments at 5393–5398,
5513, 5522, 5748–5751 and 5767). They cite a table the final thesis dropped, so each needs a
decision: keep it as an explicit "DCLEG v5.0, Table 1" test, or re-anchor
it (fin/beg → §3.1.2; PerfectInfo → §3.2.5's `¬□φ ∨ B_i□φ`; the others
have no final counterpart).

## 4. Chapters 4–5 against the implementation

Every definition in Chapters 4–5 is an abbreviation over the Chapter 3
language (¬, ∨, □→, B_i, X, Y, □), so `DclegFormula` can express them all.
Nothing needs a new operator or a new satisfaction clause. What the
implementation lacks is machinery to build and check them:

| Thesis item | Uses | What the implementation lacks |
|---|---|---|
| BI_z (§4.1.1 p. 26; Lemma 4.1 p. 27) | `end`, X, ◇, □→ over moves, ⋁ over payoffs h > k | n-ary ⋀/⋁ helpers; no global move set M (only per-vertex `ssMoves`); no payoff set N (derivable from `dmPayoff`); no `depth` function for Lemma 4.1's statement |
| Rat_i, maximin_i, maximin′_i, maximin″_i (§4.2 pp. 29–30) | turn_i, m, B_i, □, □→, ⋁_{h∈N} h_i | same n-ary helpers and N; no helper for m_i |
| R^z (§4.3 p. 31), Theorem 4.2 (p. 31) | B^E, AX, ◇, □→, X | no helpers for B^E (needs the agent set, which the model doesn't declare: agents are implicit in `ssPlayer`/`dmDoxastic`/`dmPayoff` keys) or AX (needs M) |
| high(n), deep(n); bounded S_n, U_n (§5.4.2 p. 38) | start, end, Y, ◇X, X | no recursive helper constructors (definable) |
| PastRat^y_i, FutRat^z_i, CondRat^z_i (§5.4.2 pp. 38–39) | S_y, U_z, B^E, B̂_i, ◇, □→ | as above |
| PF, P^{y,z}_i, H^y_i, V^{y,z}_i (§5.5.1 pp. 39–40); Theorem 5.1 (p. 40); Lemma 5.2 (p. 43) | B_j, B_i, AX, □→, high/deep | as above |
| Every Ch. 4–5 theorem is a *validity* | frame conditions (Theorem 4.2's proof uses perfect information, C4 from D+5, Expectational Continuity) | No validity checker for DCLEG: `dclegTrueIn` checks one model. It is sound for these theorems only on models meeting all of §3.2's conditions, and `validateDclegModel` checks only Presence and part of Present Seriality (section 2). The verification plan's stage 1 (`plans/dcleg-thesis-verification-2026-09-29.md`) is the missing piece |
| Appendix A models (A.1 pp. 48–51, A.2 pp. 52–) | hand-built F with singleton premises, whole-node premises, and premises containing pairs at *other* nodes (e.g. F(γ,w₂) ∋ {(η,w) \| w ∈ V_η}); doxastic relations at outcome nodes left unspecified | Not a missing feature. `dmPremises` accepts any F, but `mkDclegModel` takes no premise argument (use a record update), and `withMovePremises` can't produce these. `maxPhiConsistentWith` (`Gamen/Dcleg.lean:343–356`) intersects with the whole of ⟦φ⟧, including other-node pairs, as the thesis's definition does. Unspecified outcome-node beliefs make B_i vacuous there, and `validateDclegModel` won't flag them unless the agent has a map at that vertex |

## 5. gamen-hs#53 under the final thesis

gamen-hs#53 ("DCLEG Table 1 tests check → where the draft states □→") was
**closed as completed on 2026-09-30** by gamen-hs PR #61. That PR rebuilt
TurnStr, PerfectInfo and SinglePref with `DFConditional` and checked them
with `dclegTrueIn` at every point: all three hold in `dclegM`, and a
control, `turn_p1 □→ ¬turn_p1`, fails. **gamen-lean has not followed:**
`Tests/Main.lean:5752–5755, 5765–5766` still test the material `→` at
(γL, v0), and the header (5396–5398) still describes the old state.

Under the final thesis the issue is **moot as a paper-correspondence
question**, because Table 1 and all three validities are gone (rows 86, 88,
92). What remains:

* The tests now check claims that only v5.0 makes. If they stay, they
  should say "DCLEG v5.0, Table 1". gamen-hs is frozen, so aligning with
  PR #61 is Lean-only work.
* The material/counterfactual gap was real for only one of the three.
  TurnStr's antecedent (turn_i) and PerfectInfo's (□φ) have the same truth
  value at every world reaching w. So wherever Centering holds, φ □→ ψ and
  φ → ψ agree at a point: if φ is true, Centering selects γ; if it is
  false, no world at w satisfies it, so both are true. The final thesis's
  narrowed §3.2.5 claim (row 65) is this observation for □. SinglePref's
  antecedent k_i varies by world, and there the material test really is
  weaker.
* The collapse fails where Centering does: at single-move vertices under
  `withMovePremises` (section 2, row 65). `dclegM` has no such vertex, so
  PR #61's results carry over to it.
* The one final-thesis claim near PerfectInfo is §3.2.5's
  `¬□φ ∨ B_i□φ` (p. 23). It is untested in gamen-lean.
