import Linglib.Core.Logic.Modal.BSML.Defs
import Linglib.Core.Logic.Modal.Bisimulation

/-!
# Bisimulation invariance for BSML

@cite{aloni-anttila-yang-2024} @cite{anttila-2025}

The carrier-level bisimulation substrate (`WorldBisim`, `StateBisim`, and
the Lemma 3.7 transport lemmas) lives in `Core/Logic/Modal/Bisimulation.lean`,
shared across the modal team logics. This file specialises it to BSML: the
modal-depth measure on `BSMLFormula` and the headline invariance result
(Theorem 3.8) for BSML's bilateral evaluation.

## Main declarations

* `BSMLFormula.modalDepth` — modal depth (page 9): atoms/NE are 0,
  `conj`/`disj` take max, `poss` increments.
* `bisim_invariant_eval` — Theorem 3.8 for BSML: `k`-bisimilar states agree
  on `eval` for all formulas of modal depth `≤ k`, for both polarities.

## Implementation notes

The bisim-invariance proof inducts on the formula, handling both polarities
(`eval M b φ s`) jointly at each step. The negation case flips polarity
without changing depth; the modal case uses `StateBisim.accessImage`
(Lemma 3.7(i)) to recurse at depth `k`; conjunction and disjunction use
`StateBisim.splitPreserve` (Lemma 3.7(ii)) for the split-existential clauses
(conj-antiSupport and disj-support).

## Todo

* Hennessy-Milner direction (Theorem 3.3): `k`-equivalence implies
  `k`-bisimilarity, via Hintikka formulas. Requires a finite atom set
  hypothesis (`[Fintype Atom]`) for the characteristic-formula construction.
  Deferred — Theorem 3.8 alone is enough for the expressive-completeness side
  of @cite{aloni-anttila-yang-2024} §3.
* Bisim invariance for `BSMLOr.eval` and `BSMLEmpty.eval`. Same shape with one
  new case each (`gdisj` is structurally like `support_conj` at the team
  level; `empt` reduces to support of the inner formula or `s = ∅`, both
  bisim-preserved).
-/

namespace Core.Logic.Modal.BSML

open Core.Logic.Modal

-- Re-export the carrier-level bisimulation names under the BSML namespace so
-- consumers that historically opened `Core.Logic.Modal.BSML (StateBisim …)`
-- continue to resolve after the lift to `Core.Logic.Modal`.
export Core.Logic.Modal (WorldBisim StateBisim)

variable {W W' : Type*} [DecidableEq W] [Fintype W] [DecidableEq W'] [Fintype W']
variable {Atom : Type*}

/-! ### Modal depth -/

/-- Modal depth of a `BSMLFormula` (page 9 of @cite{aloni-anttila-yang-2024}).
    Atoms and `NE` are 0; `neg` preserves depth; `conj` and `disj` take
    the max; `poss` increments. -/
def BSMLFormula.modalDepth : BSMLFormula Atom → ℕ
  | .atom _ => 0
  | .ne => 0
  | .neg ψ => ψ.modalDepth
  | .conj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .disj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .poss ψ => ψ.modalDepth + 1

/-! ### Theorem 3.8: bisimulation invariance for BSML -/

/-- **Theorem 3.8** of @cite{aloni-anttila-yang-2024} specialised to BSML:
    if `s ⇌_k s'` and `φ : BSMLFormula Atom` has modal depth `≤ k`, then
    `eval M b φ s ↔ eval M' b φ s'` for both polarities.

    Proved by structural induction on `φ`, with both polarities handled
    jointly at each step. The `neg` case flips polarity without changing
    depth; the `poss` case uses Lemma 3.7(i) to recurse at depth `k`;
    conjunction and disjunction use Lemma 3.7(ii) for the split-existential
    clauses (conj-antiSupport and disj-support). -/
theorem bisim_invariant_eval (φ : BSMLFormula Atom) :
    ∀ {k : ℕ}, φ.modalDepth ≤ k →
    ∀ {M : BSMLModel W Atom} {M' : BSMLModel W' Atom}
      {s : Finset W} {s' : Finset W'},
    StateBisim k M s M' s' →
    ∀ b : Bool, eval M b φ s ↔ eval M' b φ s' := by
  induction φ with
  | atom p =>
    intro k _ M M' s s' hbisim b
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
    intro k _ M M' s s' hbisim b
    cases b
    · exact hbisim.eq_empty_iff
    · exact hbisim.nonempty_iff
  | neg ψ ih =>
    intro k hd M M' s s' hbisim b
    cases b
    · -- antiSupport (neg ψ) = support ψ
      exact ih hd hbisim true
    · -- support (neg ψ) = antiSupport ψ
      exact ih hd hbisim false
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    intro k hd M M' s s' hbisim b
    have hd₁ : ψ₁.modalDepth ≤ k :=
      le_trans (le_max_left _ _) hd
    have hd₂ : ψ₂.modalDepth ≤ k :=
      le_trans (le_max_right _ _) hd
    cases b
    · -- antiSupport (conj ψ₁ ψ₂): ∃ t u, splitsAs ∧ antiSupport ψ₁ t ∧ antiSupport ψ₂ u
      constructor
      · rintro ⟨t, u, hsplit, h₁, h₂⟩
        obtain ⟨t', u', hsplit', hbt, hbu⟩ :=
          hbisim.splitPreserve hsplit
            (Core.Logic.Team.splitsAs_left_subset hsplit)
            (Core.Logic.Team.splitsAs_right_subset hsplit)
        exact ⟨t', u', hsplit', (ih₁ hd₁ hbt false).mp h₁,
               (ih₂ hd₂ hbu false).mp h₂⟩
      · rintro ⟨t', u', hsplit', h₁, h₂⟩
        obtain ⟨t, u, hsplit, hbt, hbu⟩ :=
          StateBisim.splitPreserve hbisim.symm hsplit'
            (Core.Logic.Team.splitsAs_left_subset hsplit')
            (Core.Logic.Team.splitsAs_right_subset hsplit')
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
    intro k hd M M' s s' hbisim b
    have hd₁ : ψ₁.modalDepth ≤ k :=
      le_trans (le_max_left _ _) hd
    have hd₂ : ψ₂.modalDepth ≤ k :=
      le_trans (le_max_right _ _) hd
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
            (Core.Logic.Team.splitsAs_left_subset hsplit)
            (Core.Logic.Team.splitsAs_right_subset hsplit)
        exact ⟨t', u', hsplit', (ih₁ hd₁ hbt true).mp h₁,
               (ih₂ hd₂ hbu true).mp h₂⟩
      · rintro ⟨t', u', hsplit', h₁, h₂⟩
        obtain ⟨t, u, hsplit, hbt, hbu⟩ :=
          StateBisim.splitPreserve hbisim.symm hsplit'
            (Core.Logic.Team.splitsAs_left_subset hsplit')
            (Core.Logic.Team.splitsAs_right_subset hsplit')
        refine ⟨t, u, hsplit, ?_, ?_⟩
        · exact (ih₁ hd₁ hbt.symm true).mpr h₁
        · exact (ih₂ hd₂ hbu.symm true).mpr h₂
  | poss ψ ih =>
    intro k hd M M' s s' hbisim b
    -- modalDepth (poss ψ) = ψ.modalDepth + 1, so we need k = succ for accessImage
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := by
      cases k with
      | zero => exact absurd hd (by simp [BSMLFormula.modalDepth])
      | succ k => exact ⟨k, rfl⟩
    have hdψ : ψ.modalDepth ≤ k := by
      have := hd
      simp only [BSMLFormula.modalDepth] at this
      omega
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

end Core.Logic.Modal.BSML
