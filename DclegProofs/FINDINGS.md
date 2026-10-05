# Findings from formalizing the DCLEG thesis

A neutral summary of what the Lean formalization in this directory turned
up about the thesis, for Brian to decide whether and how to raise with
Jeremiah. Page numbers are the printed ones in the final thesis
(2026-06-04). Each item has a classification, a pointer into the thesis
(quote and page), and a pointer into the Lean (file:line, as of this
commit). Everything here was checked against the thesis text, not
recalled; an independent review corrected two earlier misstatements
(recorded in the git history).

Classifications:

* **typo** — a slip in the text with an obvious intended reading.
* **reading-dependent (Q#)** — a finding that holds under one reading of
  the thesis's definitions and goes away under another; Q# is the
  question in the Lean files where the reading is asked about.
* **missing step** — a claim in a proof that is true but needs an
  argument or a lemma the thesis does not give.
* **proof gap** — a step in a proof for which no justification was found;
  says nothing about whether the result is true.
* **redundancy** — a step that is not needed.

## Safe to raise now

These do not depend on how any of the open questions are answered.

1. **Centering's domain** — reading-dependent (Q7), but with only one
   viable reading. *Thesis:* p. 19, F : (Γ × V) → P(P(I)) and
   "∀γ ∈ Γ. ∀w ∈ V. ⋂F(γ,w) = {(γ,w)} (Centering)." *Finding:* at a pair
   (γ,w) with w ∉ V_γ, ⋂F(γ,w) ⊆ I cannot equal {(γ,w)} ∉ I when F(γ,w) ≠ ∅,
   and cannot when F(γ,w) = ∅ either; so as printed Centering holds only if
   every world reaches every node. Restricting it to (γ,w) ∈ I is the
   reading under which models exist. *Lean:* `Semantics.lean:391` (Q7);
   consequence `Basics.lean:310` (`F_nonempty`).

2. **Typos in the proof of Theorem 4.2** — typo. *Thesis:* p. 32, (4.12)
   displays "□¬m ∨ ◇(m ∧ …)" where m′ is meant (cf. (4.13)); p. 33, "Take
   m′ ∈ PMoves(w) \ w" for PMoves(w) \ {m}; p. 33, the sentence before
   (4.18), "Bᵢ(m′ □→ ⋁_{0≤z≤n} R^z)", lacks the X that (4.18) has; p. 33,
   "M, ν, w ⊩ X ⋁ BI" where η is meant. *Lean:* `Theorem4_2.lean:210`
   (item 5), `:217` (item 6).

3. **Theorem 4.2, "regardless of the value of z, R^z = B^E ψ"** — missing
   step. *Thesis:* p. 32. *Finding:* false for z = 0, where R⁰ = end. The
   inference it supports (X ⋁ B^E R^z ⟹ X ⋁ R^z) still holds for that
   disjunct, but via Present Seriality, the node-dependence of `end`, and
   A ≠ ∅ (B^E over an empty A is ⊤), not via C4. *Lean:*
   `Theorem4_2.lean:172` (item 1); tools `Basics.lean` (`sat_end_iff`,
   `dox_reaches`), `Theorem4_2.lean:120` (`belE_belE_imp_belE`).

4. **Theorem 4.2, from (4.20) to "M, μ, w ⊮ Ratᵢ"** — missing step.
   *Thesis:* p. 33. *Finding:* (4.20) fixes the k of (4.11), but Ratᵢ at μ
   is a disjunction over all k′ ∈ N; refuting it needs k′ ≤ k for every
   live k′, which follows from B̂ᵢ(m □→ ⋁_{h≤k} hᵢ) by centering and
   Self-Awareness (all plausible worlds play m). True, not written.
   *Lean:* `Theorem4_2.lean:225` (item 7); `Theorem4_2.lean:142`
   (`sat_rat_of_dox`).

5. **The closing paragraph of each validity proof** — redundancy.
   *Thesis:* p. 33 ("Suppose M, γ, w ⊮ R^{n+1}. If M, γ, w ⊩ □¬R^{n+1} …
   vacuously. Otherwise, by contemporary universality …"), and p. 41
   likewise. *Finding:* every world in max^φ_{F(γ,w)}(Γ) satisfies φ
   (clause 1 of p. 19), so "φ → ψ at every pointed model" already gives
   "φ □→ ψ valid"; conversely, by centering, validity of φ □→ ψ gives
   validity of φ → ψ. The case split and the appeal to contemporary
   universality are not needed. *Lean:* `Basics.lean:300`
   (`valid_cf_of_imp`), `:359` (`valid_cf_iff`).

6. **Lemma 4.1, "every possible path has to be represented in a model"** —
   missing step. *Thesis:* p. 27. *Finding:* the model requires only that
   every *outcome node* be reached in some world (p. 19). Getting a world
   whose history follows a given path from w″ to an outcome o also uses
   condition 5 (no merging) and that histories start at the root, so the
   world reaching o passes through w″ along that path. *Lean:*
   `Lemma4_1.lean:300` (item 2).

7. **Lemma 4.1, organization of the induction** — missing step. *Thesis:*
   pp. 27–29. *Finding:* the *BI path ⇒ Satisfaction* direction is proved
   with a depth-indexed hypothesis and *Satisfaction ⇒ BI path* with a
   depth-free one (p. 29, "Suppose that, for any z = 0, …, n, if
   M, γ, w ⊩ BI_z …", and its base case "Take any w ∈ V"); applying the
   latter at w′ is fine on its own terms. But each direction uses the
   other at the successor: the step from (4.7) to "taking move m_γ and
   subsequently following a backward induction path guarantees at least
   k_BI" needs *BI path ⇒ Satisfaction* at w′ (with depth(w′) ≤ n), and
   (4.3) in the first direction needs *Satisfaction ⇒ BI path* at w′. So
   the two directions need a single joint induction on depth, with the
   auxiliary fact "M, γ, w ⊩ BI_z implies depth(w) = z". *Lean:*
   `Lemma4_1.lean:273` (item 1).

8. **Theorem 4.2, "by perfect information, X ⋁ B^E R^z"** — missing step,
   whose proof is reading-dependent (Q12). *Thesis:* p. 32. *Finding:*
   moving a disjunction out of B^E is justified only because R^z can hold
   only at nodes of depth z, a lemma the thesis does not state. Its proof
   reads the counterfactuals in AX ⋁ R^{z′} and ⋁_m(◇m ∧ (m □→ X R^z)) at
   maximally m-consistent worlds, so it needs those to exist, which is
   item 11 below. Raise the missing lemma now; its proof waits on Q12.
   *Lean:* `Theorem4_2.lean:180` (item 2).

9. **Theorem 5.1 and Lemma 5.2** — proof gap. *Thesis:* p. 41, "We also
   know that M, γ, w ⊩ Bᵢ AX FutRat^zᵢ. This gives us M, μ, w ⊩
   m □→ X Bᵢ FutRat^zᵢ. Therefore … for every m ∈ PMoves(w)"; and the
   opening "If M, γ, w ⊩ ¬◇(m ∧ Ratᵢ), then clearly M, γ, w ⊩ ¬m.
   Otherwise …", after which the first case is not taken up again, though
   (5.5) is asserted for every available m′. *Finding:* (a) the quoted
   inference holds for the move m actually made, by Self-Awareness,
   Expectational Continuity, Transitivity, Euclideanness and Centering,
   none of which the proof cites; for m′ ≠ m no justification was found,
   because a world maximally m′-consistent with μ plays m′, so lies
   outside ⊒ʷᵢ(γ), and its later beliefs are constrained only through its
   own plausible worlds. (b) The case ¬◇(m′ ∧ Ratᵢ) is dropped; the
   closing remark on p. 41 ("Note that this ignores the cases when it is
   impossible for i to play a move m′ and have everyone subsequently
   believe …") anticipates part of this and proposes exempting such
   moves. These are gaps in the proof; no countermodel was constructed
   and the results' truth is not settled by this work. Lemma 5.2 has no
   written proof (p. 43: "similar to the proof presented for …").
   *Lean:* `Theorem5_1.lean:238` (item 1), `:256` (item 2), `:209`
   (`bel_next_of_bel_AX`, the actual-move case); `Lemma5_2.lean:95`
   (`lemma5_2_actual_move`), `:150` (item 2).

## Waits on Jeremiah's answers

These depend on Q12 (does clause 2(b) of "maximally φ-consistent" range
over pairs at every node, or only at the current one; equivalently, may
premises contain pairs at other nodes) or Q13 (is "backward induction
path" the recursive description used on p. 27). Under node-local premises,
items 10 and 11 largely go away and item 8 reduces to writing the lemma
down.

10. **The p. 22 claim about contemporary universality** —
    reading-dependent (Q12). *Thesis:* p. 22, "Contemporary universality
    says that every such β is m′-consistent with a non-empty subset of
    F(γ,w), so there will be at least one world which is maximally
    m′-consistent with F(γ,w)." *Finding:* under the literal p. 19
    definition, a G whose intersection contains an m′-world at w can have
    a strict superset whose intersection contains an m′-pair at another
    node, so no G is maximal and max^{m′}_{F(γ,w)}(Γ) = ∅ while ◇m′ holds.
    `Q12Example.lean` builds a five-node, three-world game model, has
    Lean verify every `GameModel` condition on it, and proves
    `dia_move'`, `no_maxConsistent` and `cf_bot` (m′ □→ ⊥ true at (γ,r)).
    Under node-local premises the claim holds
    (`exists_maxConsistent_of_dia`), given finiteness (Q6). *Lean:*
    `Basics.lean:376` (Q12), `:475`; `Q12Example.lean:290`, `:320`.

11. **Theorem 4.2's use of that claim** — reading-dependent (Q12).
    *Thesis:* p. 32, "Then clearly M, γ, w ⊩ B^E ◇X R^n" from
    B^E ⋁_m (◇m ∧ (m □→ X R^n)). *Finding:* needs, at each plausible world,
    a maximally m-consistent world, i.e. item 10; and the depth lemma of
    item 8 needs the same. Whether the proof of Theorem 4.2 goes through
    as written therefore depends on Q12; nothing here implies the theorem
    fails under the node-local reading, and under the literal reading the
    question is open. *Lean:* `Theorem4_2.lean:197` (item 3).

12. **The (5.6) inference** — reading-dependent (Q12, Q6). *Thesis:*
    p. 41, (5.6) from Bᵢ(m □→ ⋁ hᵢ) and Bᵢ(m □→ X B^E FutRat). *Finding:*
    this is cautious monotonicity, which in premise semantics needs a
    maximal G to exist (finiteness) and, under the literal reading, node-
    local premises; for the actual move it is not needed at all, since the
    antecedent is true at every plausible world and the counterfactual
    collapses. *Lean:* `Theorem5_1.lean:272` (item 3); `Basics.lean`
    (`maxConsistent_of_and_of_local`).

13. **Which "backward induction path"** — reading-dependent (Q13).
    *Thesis:* p. 7 (pruning, "using the maximin principle" for degenerate
    games) versus p. 27 (the recursive description with k_{w′} = min over
    BI-reachable outcomes). *Finding:* the Lean defines the p. 27 version
    (`BIOutcomes`, `BIMove`, `FollowsBI`) and does not relate it to
    pruning; Lemma 4.1 as formalized is about that version. *Lean:*
    `Lemma4_1.lean:320` (item 5).

14. **Choosing k_BI ∈ N** — missing step, minor. *Thesis:* p. 27. The
    minimum of the BI-reachable payoffs must lie in N; it does (Pᵢ maps
    into N), but a formal proof must construct it. Listed here because
    its formalization follows the answer to Q13. *Lean:*
    `Lemma4_1.lean:309` (item 3).
