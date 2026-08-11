import Linglib.Logic.Modal.BSML.Defs
import Linglib.Logic.Modal.Bisimulation

/-!
# Bisimulation invariance for BSML

The carrier-level bisimulation substrate (`WorldBisim`, `StateBisim`, and
the Lemma 3.7 transport lemmas of [aloni-anttila-yang-2024]) lives in
`Logic/Modal/Bisimulation.lean`, shared across the modal team logics. This
file specialises it to BSML: the modal-depth measure on `Formula` and
the invariance result (Theorem 3.8) for BSML's bilateral evaluation, which
the [anttila-2025] expressive-completeness development consumes in
`BSML/ExpressiveCompleteness.lean`.

## Main declarations

* `Formula.modalDepth` — modal depth (page 9): atoms/NE are 0,
  `conj`/`disj` take max, `poss` increments.
* `bisim_invariant_eval` — Theorem 3.8 for BSML: `k`-bisimilar states agree
  on `eval` for all formulas of modal depth `≤ k`, for both polarities.

## Implementation notes

The bisim-invariance proof inducts on the formula, handling both polarities
(`eval M b φ s`) jointly at each step. The negation case flips polarity
without changing depth; the modal case recurses at depth `k` through
`WorldBisim.accessStateBisim` (the singleton form of Lemma 3.7(i)), with
`StateBisim.exists_image_subset` transporting the `poss`-support witness
sub-team; conjunction and disjunction use `StateBisim.splitPreserve`
(Lemma 3.7(ii)) for the split-existential clauses (conj-antiSupport and
disj-support).

## Todo

* Hennessy-Milner direction (Theorem 3.3): `k`-equivalence implies
  `k`-bisimilarity, via Hintikka formulas. Requires a finite atom set
  hypothesis (`[Fintype Atom]`) for the characteristic-formula construction.
  Deferred — Theorem 3.8 alone is enough for the soundness half of the
  expressive-completeness theorem in `BSML/ExpressiveCompleteness.lean`.
-/

namespace BSML

open ModalLogic

variable {W W' : Type*} [DecidableEq W] [Fintype W] [DecidableEq W'] [Fintype W']
variable {Atom : Type*}

/-! ### Modal depth -/

/-- Modal depth of a `Formula` (page 9 of [aloni-anttila-yang-2024]).
    Atoms and `NE` are 0; `neg` preserves depth; `conj` and `disj` take
    the max; `poss` increments. -/
def Formula.modalDepth : Formula Atom → ℕ
  | .atom _ => 0
  | .ne => 0
  | .neg ψ => ψ.modalDepth
  | .conj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .disj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .poss ψ => ψ.modalDepth + 1

/-! ### Theorem 3.8: bisimulation invariance for BSML -/

/-- **Theorem 3.8** of [aloni-anttila-yang-2024] specialised to BSML:
    if `s ⇌_k s'` and `φ : Formula Atom` has modal depth `≤ k`, then
    `eval M b φ s ↔ eval M' b φ s'` for both polarities.

    Proved by structural induction on `φ`, with both polarities handled
    jointly at each step. The `neg` case flips polarity without changing
    depth; the `poss` case recurses at depth `k` through
    `WorldBisim.accessStateBisim`; conjunction and disjunction use
    Lemma 3.7(ii) for the split-existential clauses (conj-antiSupport
    and disj-support). -/
theorem bisim_invariant_eval {M : KripkeModel W Atom} {M' : KripkeModel W' Atom}
    (φ : Formula Atom) {k : ℕ} (hd : φ.modalDepth ≤ k)
    {s : Finset W} {s' : Finset W'} (hbisim : StateBisim k M s M' s')
    (b : Bool) : eval M b φ s ↔ eval M' b φ s' := by
  induction φ generalizing k s s' b with
  | atom p =>
    -- For both polarities: each side of the iff uses the bisim partner's
    -- valuation, related by `WorldBisim.val_eq`.
    cases b <;>
    · constructor
      · intro h w' hw'
        obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
        rw [← hbw.val_eq]; exact h w hw
      · intro h w hw
        obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
        rw [hbw.val_eq]; exact h w' hw'
  | ne =>
    cases b
    · exact hbisim.eq_empty_iff
    · exact hbisim.nonempty_iff
  | neg ψ ih =>
    cases b
    · -- antiSupport (neg ψ) = support ψ
      exact ih hd hbisim true
    · -- support (neg ψ) = antiSupport ψ
      exact ih hd hbisim false
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have hd₁ : ψ₁.modalDepth ≤ k := (le_max_left _ _).trans hd
    have hd₂ : ψ₂.modalDepth ≤ k := (le_max_right _ _).trans hd
    cases b
    · -- antiSupport (conj ψ₁ ψ₂): ∃ t u, splitsAs ∧ antiSupport ψ₁ t ∧ antiSupport ψ₂ u
      constructor
      · rintro ⟨t, u, hsplit, h₁, h₂⟩
        obtain ⟨t', u', hsplit', hbt, hbu⟩ :=
          hbisim.splitPreserve hsplit
            (Team.splitsAs_left_subset hsplit)
            (Team.splitsAs_right_subset hsplit)
        exact ⟨t', u', hsplit', (ih₁ hd₁ hbt false).mp h₁,
               (ih₂ hd₂ hbu false).mp h₂⟩
      · rintro ⟨t', u', hsplit', h₁, h₂⟩
        obtain ⟨t, u, hsplit, hbt, hbu⟩ :=
          StateBisim.splitPreserve hbisim.symm hsplit'
            (Team.splitsAs_left_subset hsplit')
            (Team.splitsAs_right_subset hsplit')
        refine ⟨t, u, hsplit, ?_, ?_⟩
        · exact (ih₁ hd₁ hbt.symm false).mpr h₁
        · exact (ih₂ hd₂ hbu.symm false).mpr h₂
    · -- support (conj ψ₁ ψ₂) = support ψ₁ ∧ support ψ₂
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim true).mp h₁, (ih₂ hd₂ hbisim true).mp h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim true).mpr h₁, (ih₂ hd₂ hbisim true).mpr h₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have hd₁ : ψ₁.modalDepth ≤ k := (le_max_left _ _).trans hd
    have hd₂ : ψ₂.modalDepth ≤ k := (le_max_right _ _).trans hd
    cases b
    · -- antiSupport (disj ψ₁ ψ₂) = antiSupport ψ₁ ∧ antiSupport ψ₂
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim false).mp h₁, (ih₂ hd₂ hbisim false).mp h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ih₁ hd₁ hbisim false).mpr h₁, (ih₂ hd₂ hbisim false).mpr h₂⟩
    · -- support (disj ψ₁ ψ₂): ∃ t u, splitsAs ∧ support ψ₁ t ∧ support ψ₂ u
      constructor
      · rintro ⟨t, u, hsplit, h₁, h₂⟩
        obtain ⟨t', u', hsplit', hbt, hbu⟩ :=
          hbisim.splitPreserve hsplit
            (Team.splitsAs_left_subset hsplit)
            (Team.splitsAs_right_subset hsplit)
        exact ⟨t', u', hsplit', (ih₁ hd₁ hbt true).mp h₁,
               (ih₂ hd₂ hbu true).mp h₂⟩
      · rintro ⟨t', u', hsplit', h₁, h₂⟩
        obtain ⟨t, u, hsplit, hbt, hbu⟩ :=
          StateBisim.splitPreserve hbisim.symm hsplit'
            (Team.splitsAs_left_subset hsplit')
            (Team.splitsAs_right_subset hsplit')
        refine ⟨t, u, hsplit, ?_, ?_⟩
        · exact (ih₁ hd₁ hbt.symm true).mpr h₁
        · exact (ih₂ hd₂ hbu.symm true).mpr h₂
  | poss ψ ih =>
    -- modalDepth (poss ψ) = ψ.modalDepth + 1, so `k` is a successor and the
    -- recursion through `accessStateBisim` happens one depth down.
    cases k with
    | zero => exact absurd hd (Nat.not_succ_le_zero _)
    | succ k =>
      have hdψ : ψ.modalDepth ≤ k := Nat.le_of_succ_le_succ hd
      cases b
      · -- antiSupport (poss ψ): ∀ w ∈ s, antiSupport ψ (M.access w).
        -- For each side, find the bisim-partner world and use IH at the
        -- accessibility-image state bisim.
        constructor
        · intro h w' hw'
          obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
          exact (ih hdψ hbw.accessStateBisim false).mp (h w hw)
        · intro h w hw
          obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
          exact (ih hdψ hbw.accessStateBisim false).mpr (h w' hw')
      · -- support (poss ψ): ∀ w ∈ s, ∃ t ⊆ R[w], t.Nonempty ∧ support ψ t.
        -- The witness sub-team `t` of the access image transports across
        -- models via `exists_image_subset`.
        constructor
        · intro h w' hw'
          obtain ⟨w, hw, hbw⟩ := hbisim.2 w' hw'
          obtain ⟨t, htsub, htne, htsupp⟩ := h w hw
          obtain ⟨t', ht'sub, ht'ne, htbisim⟩ :=
            hbw.accessStateBisim.exists_image_subset htsub
          exact ⟨t', ht'sub, ht'ne htne, (ih hdψ htbisim true).mp htsupp⟩
        · intro h w hw
          obtain ⟨w', hw', hbw⟩ := hbisim.1 w hw
          obtain ⟨t', ht'sub, ht'ne, ht'supp⟩ := h w' hw'
          obtain ⟨t, htsub, htne, htbisim⟩ :=
            hbw.accessStateBisim.symm.exists_image_subset ht'sub
          exact ⟨t, htsub, htne ht'ne, (ih hdψ htbisim.symm true).mpr ht'supp⟩

end BSML
