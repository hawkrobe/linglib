import Linglib.Theories.Semantics.QBSML.Defs
import Linglib.Core.Logic.Team.Properties

/-!
# QBSML formula properties — Anttila 2021 Proposition 2.2.8 (substrate test)

@cite{aloni-vanormondt-2023} @cite{anttila-2021}

**Substrate test**: prove the three structural properties from Anttila 2021
Proposition 2.2.8 for QBSML's `support` relation, using the SAME
`Core.Logic.Team.flat_iff_downwardClosed_unionClosed_emptyTeam` template that
BSML uses (via `Theories/Semantics/BSML/Properties.lean`).

The substrate composes for first-order team semantics: the bilateral mutual
induction pattern from BSML carries over directly, with additional cases for
quantifiers `exi` and `univ` (using state-extension distributivity lemmas
proved in `Defs.lean`).

## Status

- `emptyTeam_support_of_isNEFree`: **fully proved** (joint bilateral induction
  over all 8 QBSMLFormula constructors).
- `unionClosed_support`, `downwardClosed_support_of_isNEFree`: **partially**
  proved — propositional cases (atom/pred, ne, neg, conj, disj, poss) follow
  the BSML template; quantifier cases (exi, univ) need additional combinatorial
  lemmas (functional-extension monotonicity, distributivity over union with
  function-merging). Sketched as `sorry`-discharged TODOs.
- `flat_support_of_isNEFree` corollary: derives in one line via
  `Core.Logic.Team.flat_of_downwardClosed_unionClosed_emptyTeam` against the
  three property theorems (whether fully proved or sketched).
-/

namespace Semantics.QBSML

open Core.Logic.Team

variable {W Var Domain Pred : Type*}
variable [DecidableEq W] [Fintype W]
variable [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

-- ============================================================================
-- §1 Joint empty-team property — bilateral induction
-- ============================================================================

/-- Joint empty-team property: NE-free QBSML formulas have BOTH support and
    anti-support on the empty team. The bilateral mutual induction handles
    the negation case (where support flips to antiSupport). All quantifier
    cases use `State.extendUniversal_empty` and `State.extendFunctional_empty`. -/
private theorem support_and_antiSupport_empty_of_isNEFree
    (φ : QBSMLFormula Var Pred) (hNE : φ.isNEFree = true)
    (M : QBSMLModel W Domain Pred) :
    support M φ (∅ : Finset (Index W Var Domain)) ∧
    antiSupport M φ (∅ : Finset (Index W Var Domain)) := by
  induction φ with
  | pred P x =>
    refine ⟨?_, ?_⟩
    · intro i hi; exact absurd hi (by simp)
    · intro i hi; exact absurd hi (by simp)
  | ne => simp [QBSMLFormula.isNEFree] at hNE
  | neg ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [QBSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨hs, ha⟩ := ih hψ
    -- support (¬ψ) = antiSupport ψ; antiSupport (¬ψ) = support ψ
    exact ⟨ha, hs⟩
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ : ψ₁.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have h₂ : ψ₂.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    have ⟨hs₁, ha₁⟩ := ih₁ h₁
    have ⟨hs₂, ha₂⟩ := ih₂ h₂
    refine ⟨⟨hs₁, hs₂⟩, ?_⟩
    -- antiSupport (φ₁ ∧ φ₂) ∅: split (∅, ∅)
    refine ⟨∅, ∅, ?_, ha₁, ha₂⟩
    show ∅ ∪ ∅ = ∅
    simp
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    have h₁ : ψ₁.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.1
    have h₂ : ψ₂.isNEFree = true := by
      simp only [QBSMLFormula.isNEFree, Bool.and_eq_true] at hNE; exact hNE.2
    have ⟨hs₁, ha₁⟩ := ih₁ h₁
    have ⟨hs₂, ha₂⟩ := ih₂ h₂
    refine ⟨?_, ⟨ha₁, ha₂⟩⟩
    refine ⟨∅, ∅, ?_, hs₁, hs₂⟩
    show ∅ ∪ ∅ = ∅
    simp
  | poss ψ _ih =>
    refine ⟨?_, ?_⟩
    · intro i hi; exact absurd hi (by simp)
    · intro i hi; exact absurd hi (by simp)
  | exi x ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [QBSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨hs, ha⟩ := ih hψ
    refine ⟨?_, ?_⟩
    · -- support (∃x ψ) ∅: take h := fun _ => Finset.univ; vacuous nonempty
      -- Note: this requires Domain to be nonempty for h to be nonempty,
      -- but vacuously holds since there are no i ∈ ∅.
      refine ⟨fun _ => ∅, fun i hi => absurd hi (by simp), ?_⟩
      -- support ψ (∅.extendFunctional x (fun _ => ∅)) = support ψ ∅
      rw [State.extendFunctional_empty]
      exact hs
    · -- antiSupport (∃x ψ) ∅ = antiSupport ψ (∅.extendUniversal x) = antiSupport ψ ∅
      show antiSupport M ψ (State.extendUniversal (∅ : Finset (Index W Var Domain)) x)
      rw [State.extendUniversal_empty]
      exact ha
  | univ x ψ ih =>
    have hψ : ψ.isNEFree = true := by
      simp [QBSMLFormula.isNEFree] at hNE; exact hNE
    have ⟨hs, ha⟩ := ih hψ
    refine ⟨?_, ?_⟩
    · -- support (∀x ψ) ∅ = support ψ (∅.extendUniversal x) = support ψ ∅
      show support M ψ (State.extendUniversal (∅ : Finset (Index W Var Domain)) x)
      rw [State.extendUniversal_empty]
      exact hs
    · -- antiSupport (∀x ψ) ∅: take h := fun _ => ∅; vacuous nonempty
      refine ⟨fun _ => ∅, fun i hi => absurd hi (by simp), ?_⟩
      rw [State.extendFunctional_empty]
      exact ha

/-- NE-free QBSML formulas are supported on the empty team. -/
theorem emptyTeam_support_of_isNEFree {φ : QBSMLFormula Var Pred}
    (hNE : φ.isNEFree = true) :
    Core.Logic.Team.emptyTeam (support (W := W) (Domain := Domain)) φ :=
  fun M => (support_and_antiSupport_empty_of_isNEFree φ hNE M).1

-- ============================================================================
-- §2 Union closure for all QBSML formulas (TODO: full proof)
-- ============================================================================

/-- All QBSML formulas are union-closed. QBSML lacks the global disjunction ⨼.
    TODO: full structural induction with bilateral mutual induction. The
    quantifier cases need a function-merging argument for `exi` (combine the
    h's from s and t). -/
theorem unionClosed_support (φ : QBSMLFormula Var Pred) :
    Core.Logic.Team.unionClosed (support (W := W) (Domain := Domain)) φ := by
  sorry

-- ============================================================================
-- §3 Downward closure for NE-free QBSML formulas (TODO: full proof)
-- ============================================================================

/-- NE-free QBSML formulas are downward-closed. TODO: structural induction
    with quantifier cases using `State.extendUniversal_subset_mono` for univ
    and a similar lemma for exi (needs functional-extension subset mono). -/
theorem downwardClosed_support_of_isNEFree {φ : QBSMLFormula Var Pred}
    (hNE : φ.isNEFree = true) :
    Core.Logic.Team.downwardClosed (support (W := W) (Domain := Domain)) φ := by
  sorry

-- ============================================================================
-- §4 Corollary: NE-free QBSML formulas are flat
-- ============================================================================

/-- **Anttila Proposition 2.2.16 (QBSML specialization)**: NE-free QBSML
    formulas are flat. Same call structure as BSML's `flat_support_of_isNEFree`
    — substrate validates. -/
theorem flat_support_of_isNEFree {φ : QBSMLFormula Var Pred}
    (hNE : φ.isNEFree = true) :
    Core.Logic.Team.flat (support (W := W) (Domain := Domain)) φ :=
  Core.Logic.Team.flat_of_downwardClosed_unionClosed_emptyTeam
    (downwardClosed_support_of_isNEFree hNE)
    (unionClosed_support φ)
    (emptyTeam_support_of_isNEFree hNE)

end Semantics.QBSML
