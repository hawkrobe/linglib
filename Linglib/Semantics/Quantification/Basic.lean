import Linglib.Semantics.Quantification.Defs
import Linglib.Semantics.Quantification.Properties
import Linglib.Core.Logic.Aristotelian.Basic

/-!
# Concrete propositional generalized quantifiers
[barwise-cooper-1981] [keenan-stavi-1986] [peters-westerstahl-2006]

The three propositional GQs `every_sem`, `some_sem`, `no_sem` and the property
proofs that don't need `Fintype`. Counting GQs (`most_sem`, `few_sem`, etc.) and
their proofs live in `Quantification.Counting`.

## Main declarations

* `every_sem`, `some_sem`, `no_sem` — the three propositional GQ denotations.
* `SatisfiesUniversals` — B&C universals: conservativity + monotonicity in scope.
* Conservativity/monotonicity/symmetry/intersectivity/duality/etc. proofs.
-/

namespace Quantification

/-! ### Denotations -/

/-- ⟦every⟧ = λR.λS. ∀x. R(x) → S(x). -/
def every_sem {α : Type*} : GQ α := fun R S => ∀ x : α, R x → S x

/-- ⟦some⟧ = λR.λS. ∃x. R(x) ∧ S(x). -/
def some_sem {α : Type*} : GQ α := fun R S => ∃ x : α, R x ∧ S x

/-- ⟦no⟧ = λR.λS. ∀x. R(x) → ¬S(x). -/
def no_sem {α : Type*} : GQ α := fun R S => ∀ x : α, R x → ¬ S x

/-- B&C semantic universals ([barwise-cooper-1981]): conservativity plus
    monotonicity in scope. Convenience conjunction of three Core predicates. -/
def SatisfiesUniversals {α : Type*} (q : GQ α) : Prop :=
  Conservative q ∧ (ScopeUpwardMono q ∨ ScopeDownwardMono q)

variable {α : Type*}

/-- Denotation brackets for the logical determiners (Heim & Kratzer `⟦·⟧`), with `α`
    pinned to the section variable — so a bare statement reads `Conservative ⟦every⟧`
    instead of the noisy `Conservative (every_sem (α := α))`. -/
local notation:max "⟦every⟧" => (every_sem : GQ α)
local notation:max "⟦some⟧" => (some_sem : GQ α)
local notation:max "⟦no⟧" => (no_sem : GQ α)

/-! ### Bijection invariance -/

/-- `∀ x, P x` is invariant under bijective substitution. -/
theorem forall_bij_inv (f : α → α) (hBij : Function.Bijective f)
    (P : α → Prop) :
    (∀ x, P x) ↔ (∀ x, P (f x)) := by
  refine ⟨fun h x => h (f x), fun h x => ?_⟩
  obtain ⟨y, rfl⟩ := hBij.surjective x; exact h y

/-- `∃ x, P x` is invariant under bijective substitution. -/
theorem exists_bij_inv (f : α → α) (hBij : Function.Bijective f)
    (P : α → Prop) :
    (∃ x, P x) ↔ (∃ x, P (f x)) := by
  refine ⟨fun ⟨x, hx⟩ => ?_, fun ⟨y, hy⟩ => ⟨f y, hy⟩⟩
  obtain ⟨y, rfl⟩ := hBij.surjective x; exact ⟨y, hx⟩

/-! ### Conservativity -/

theorem every_conservative : Conservative ⟦every⟧ := by
  intro R S; simp only [every_sem]
  exact ⟨fun h x hR => ⟨hR, h x hR⟩, fun h x hR => (h x hR).2⟩

theorem some_conservative : Conservative ⟦some⟧ := by
  intro R S; simp only [some_sem]
  exact ⟨fun ⟨x, hR, hS⟩ => ⟨x, hR, hR, hS⟩, fun ⟨x, hR, _, hS⟩ => ⟨x, hR, hS⟩⟩

theorem no_conservative : Conservative ⟦no⟧ := by
  intro R S; simp only [no_sem]
  exact ⟨fun h x hR ⟨_, hS⟩ => h x hR hS, fun h x hR hS => h x hR ⟨hR, hS⟩⟩

/-! ### Scope monotonicity -/

theorem every_scope_up : ScopeUpwardMono ⟦every⟧ := by
  intro R S S' hSS' h x hR; exact hSS' x (h x hR)

theorem some_scope_up : ScopeUpwardMono ⟦some⟧ := by
  intro R S S' hSS' ⟨x, hR, hS⟩; exact ⟨x, hR, hSS' x hS⟩

theorem no_scope_down : ScopeDownwardMono ⟦no⟧ := by
  intro R S S' hSS' h x hR hS; exact h x hR (hSS' x hS)

/-! ### Symmetry (P&W Ch.6) -/

theorem some_symmetric : QSymmetric ⟦some⟧ := by
  intro R S; simp only [some_sem]
  exact ⟨fun ⟨x, hR, hS⟩ => ⟨x, hS, hR⟩, fun ⟨x, hS, hR⟩ => ⟨x, hR, hS⟩⟩

theorem no_symmetric : QSymmetric ⟦no⟧ := by
  intro R S; simp only [no_sem]
  exact ⟨fun h x hS hR => h x hR hS, fun h x hR hS => h x hS hR⟩

/-! ### Intersectivity (CONSERV + SYMM bridge) -/

theorem some_intersective : IntersectionCondition ⟦some⟧ := by
  intro R S R' S' hInt
  simp only [some_sem]
  exact ⟨fun ⟨x, hR, hS⟩ => let ⟨hR', hS'⟩ := (hInt x).mp ⟨hR, hS⟩; ⟨x, hR', hS'⟩,
         fun ⟨x, hR', hS'⟩ => let ⟨hR, hS⟩ := (hInt x).mpr ⟨hR', hS'⟩; ⟨x, hR, hS⟩⟩

theorem no_intersective : IntersectionCondition ⟦no⟧ := by
  intro R S R' S' hInt
  simp only [no_sem]
  refine ⟨fun h x hR' hS' => h x ((hInt x).mpr ⟨hR', hS'⟩).1 ((hInt x).mpr ⟨hR', hS'⟩).2,
          fun h x hR hS => h x ((hInt x).mp ⟨hR, hS⟩).1 ((hInt x).mp ⟨hR, hS⟩).2⟩

/-! ### Left/right anti-additivity (P&W §5.8) -/

theorem every_laa : LeftAntiAdditive ⟦every⟧ := by
  intro R R' S; simp only [every_sem]
  refine ⟨fun h => ⟨fun x hR => h x (Or.inl hR), fun x hR' => h x (Or.inr hR')⟩,
          fun ⟨h1, h2⟩ x hRR' => hRR'.elim (h1 x) (h2 x)⟩

theorem no_laa : LeftAntiAdditive ⟦no⟧ := by
  intro R R' S; simp only [no_sem]
  refine ⟨fun h => ⟨fun x hR => h x (Or.inl hR), fun x hR' => h x (Or.inr hR')⟩,
          fun ⟨h1, h2⟩ x hRR' => hRR'.elim (h1 x) (h2 x)⟩

theorem no_raa : RightAntiAdditive ⟦no⟧ := by
  intro R S S'; simp only [no_sem]
  refine ⟨fun h => ⟨fun x hR hS => h x hR (Or.inl hS),
                    fun x hR hS' => h x hR (Or.inr hS')⟩,
          fun ⟨h1, h2⟩ x hR hSS' => hSS'.elim (h1 x hR) (h2 x hR)⟩

/-- [peters-westerstahl-2006] Prop 13: the only non-trivial CONSERV, EXT,
    and ISOM quantifiers satisfying LAA are `every` and `no` (and `A = ∅`). -/
theorem laa_characterization :
    LeftAntiAdditive ⟦every⟧ ∧
    LeftAntiAdditive ⟦no⟧ := ⟨every_laa, no_laa⟩

/-! ### Duality square (B&C §4.11) -/

/-- Inner negation maps `every` to `no`: every...not = no.
    `∀x. R(x) → ¬S(x)` = `¬∃x. R(x) ∧ S(x)`. -/
theorem innerNeg_every_eq_no :
    (innerNeg ⟦every⟧ : GQ α) = ⟦no⟧ := by
  funext R S; simp only [innerNeg, every_sem, no_sem]

/-- The dual of `every` is `some`: Q̌(every) = some. -/
theorem dualQ_every_eq_some :
    (dualQ ⟦every⟧ : GQ α) = ⟦some⟧ := by
  funext R S; simp only [dualQ, outerNeg_apply, innerNeg, every_sem, some_sem]
  exact propext ⟨fun h => by push_neg at h; exact h,
                 fun ⟨x, hR, hS⟩ h => h x hR hS⟩

/-- `outerNeg ⟦some⟧ = ⟦no⟧`: negating existence gives universal negation. -/
theorem outerNeg_some_eq_no :
    (outerNeg ⟦some⟧ : GQ α) = ⟦no⟧ := by
  funext R S; simp only [outerNeg_apply, some_sem, no_sem]
  exact propext ⟨fun h x hR hS => h ⟨x, hR, hS⟩,
                 fun h ⟨x, hR, hS⟩ => h x hR hS⟩

/-! ### Positive/negative strong (P&W Ch.6) -/

theorem every_positive_strong : PositiveStrong ⟦every⟧ := by
  intro R x hR; exact hR

/-- `⟦no⟧` is negative strong on non-empty restrictors:
    no(A,A) = false for all non-empty A. -/
theorem no_negative_strong_nonempty (R : α → Prop)
    (hR : ∃ x : α, R x) :
    ¬ ⟦no⟧ R R := by
  intro h; obtain ⟨x, hRx⟩ := hR; exact h x hRx hRx

/-! ### K&S existential det classification (§3.3, G3) -/

theorem some_existential : Existential ⟦some⟧ := by
  intro R S; simp only [some_sem]
  exact ⟨fun ⟨x, hR, hS⟩ => ⟨x, ⟨hR, hS⟩, trivial⟩,
         fun ⟨x, ⟨hR, hS⟩, _⟩ => ⟨x, hR, hS⟩⟩

theorem no_existential : Existential ⟦no⟧ := by
  intro R S; simp only [no_sem]
  exact ⟨fun h x ⟨hR, hS⟩ _ => h x hR hS,
         fun h x hR hS => h x ⟨hR, hS⟩ trivial⟩

/-! ### Relational properties ([van-benthem-1984]) -/

theorem every_transitive : QTransitive ⟦every⟧ := by
  intro A B C hAB hBC x hA; exact hBC x (hAB x hA)

theorem every_antisymmetric : QAntisymmetric ⟦every⟧ := by
  intro A B hAB hBA
  funext x; exact propext ⟨fun hA => hAB x hA, fun hB => hBA x hB⟩

theorem some_quasi_reflexive : QuasiReflexive ⟦some⟧ := by
  intro A B ⟨x, hA, _⟩; exact ⟨x, hA, hA⟩

theorem no_quasi_universal : QuasiUniversal ⟦no⟧ := by
  intro A B hAA x hA; exact absurd hA (hAA x hA)

/-! ### Double monotonicity classification ([van-benthem-1984] §4.2) -/

/-- `⟦every⟧` is restrictor-↓ (anti-persistent). Follows from Zwarts bridge:
    reflexive + transitive + CONSERV → ↓MON. -/
theorem every_restrictor_down : RestrictorDownwardMono ⟦every⟧ :=
  zwarts_refl_trans_restrictorDown _ every_conservative every_positive_strong
    every_transitive

theorem some_restrictor_up : RestrictorUpwardMono ⟦some⟧ := by
  intro R R' S hRR' ⟨x, hR, hS⟩; exact ⟨x, hRR' x hR, hS⟩

theorem no_restrictor_down : RestrictorDownwardMono ⟦no⟧ := by
  intro R R' S hRR' hQ x hR; exact hQ x (hRR' x hR)

theorem every_doubleMono :
    RestrictorDownwardMono ⟦every⟧ ∧
    ScopeUpwardMono ⟦every⟧ :=
  ⟨every_restrictor_down, every_scope_up⟩

theorem some_doubleMono :
    RestrictorUpwardMono ⟦some⟧ ∧
    ScopeUpwardMono ⟦some⟧ :=
  ⟨some_restrictor_up, some_scope_up⟩

theorem no_doubleMono :
    RestrictorDownwardMono ⟦no⟧ ∧
    ScopeDownwardMono ⟦no⟧ :=
  ⟨no_restrictor_down, no_scope_down⟩

theorem notAll_doubleMono :
    RestrictorUpwardMono (outerNeg ⟦every⟧) ∧
    ScopeDownwardMono (outerNeg ⟦every⟧) :=
  ⟨outerNeg_restrictorDown_to_up _ every_restrictor_down,
   outerNeg_up_to_down _ every_scope_up⟩

theorem every_filtrating : Filtrating ⟦every⟧ := by
  intro A B C hAB hAC x hA; exact ⟨hAB x hA, hAC x hA⟩

/-! ### Aristotelian square of opposition

The four Aristotelian relations among GQ denotations `(every_sem, some_sem, no_sem,
outerNeg every_sem)` at a fixed restrictor `R`, where the corners are elements of the
Pi-instance Boolean algebra `(α → Prop) → Prop`.

The **contradictory** diagonals are placed on the `Aristotelian` hub by construction:
since `outerNeg = ᶜ` (`Defs.outerNeg`), every quantifier is `Aristotelian.IsContradictory`
to its outer negation — `isContradictory_outerNeg`, which is just `isCompl_compl` — and the
A–O and E–I diagonals are instances. The pointwise `↔`-form theorems
(`every_contradicts_notEvery`, `no_contradicts_some`) are the unfolded readings.

**Contrariety** and **subalternation** are *not* hub relations: they hold only under
existential import (non-empty restrictor) and are `|R|`-sensitive — at a singleton `R`,
`every`/`no` are contradictory, not contrary — so the unconditional `IsContrary`/`IsSubaltern`
do not apply. They stay as the conditional theorems (`a_e_contrary`, `subalternation_a_i`, …),
the faithful Aristotelian-vs-Boolean existential-import treatment. -/

/-- Contradiction (A vs O): the A-form and O-form are contradictories. -/
theorem every_contradicts_notEvery (R S : α → Prop) :
    ⟦every⟧ R S ↔ ¬ (outerNeg ⟦every⟧ R S) := by
  simp [outerNeg, Classical.not_not]

/-- Contradiction (E vs I): the E-form and I-form are contradictories. -/
theorem no_contradicts_some (R S : α → Prop) :
    ⟦no⟧ R S ↔ ¬ (⟦some⟧ R S) := by
  simp only [no_sem, some_sem]; push_neg; rfl

/-- Contrariety (A ∧ E): the A-form and E-form can't both hold unless the
    restrictor is empty. -/
theorem a_e_contrary (R S : α → Prop) :
    ⟦every⟧ R S → ⟦no⟧ R S →
    ∀ x : α, ¬ R x := by
  intro hA hE x hR; exact hE x hR (hA x hR)

/-- Subalternation (A → I): the A-form entails the I-form when the
    restrictor is non-empty. -/
theorem subalternation_a_i (R S : α → Prop)
    (hR : ∃ x : α, R x) :
    ⟦every⟧ R S → ⟦some⟧ R S := by
  intro hA; obtain ⟨x, hRx⟩ := hR; exact ⟨x, hRx, hA x hRx⟩

/-- Subalternation (E → O): the E-form entails the O-form when the
    restrictor is non-empty. -/
theorem subalternation_e_o (R S : α → Prop)
    (hR : ∃ x : α, R x) :
    ⟦no⟧ R S → outerNeg ⟦every⟧ R S := by
  intro hE hA; obtain ⟨x, hRx⟩ := hR; exact hE x hRx (hA x hRx)

/-- Subcontrariety (I ∨ O): the I-form and O-form can't both fail when the
    restrictor is non-empty. -/
theorem subcontrariety_i_o (R S : α → Prop)
    (hR : ∃ x : α, R x) :
    ⟦some⟧ R S ∨ outerNeg ⟦every⟧ R S := by
  by_cases h : ⟦some⟧ R S
  · exact Or.inl h
  · right; intro hA; apply h
    obtain ⟨x, hRx⟩ := hR; exact ⟨x, hRx, hA x hRx⟩

/-- Every quantifier is `Aristotelian.IsContradictory` to its outer negation: the Boolean
    complement law `isCompl_compl` on the Pi-instance Boolean algebra `(α → Prop) → Prop`
    (where `outerNeg = ᶜ`). The square's contradictory diagonals are instances — this is the
    "single home" for the diagonals, by construction rather than re-derivation. -/
theorem isContradictory_outerNeg (q : GQ α) (R : α → Prop) :
    Aristotelian.IsContradictory ((q R) : (α → Prop) → Prop) (outerNeg q R) :=
  isCompl_compl

/-- A–O diagonal: `every` and `not-every` are contradictory. -/
theorem every_satisfies_isContradictory_pointwise (R : α → Prop) :
    Aristotelian.IsContradictory
      ((⟦every⟧ R) : (α → Prop) → Prop)
      (outerNeg ⟦every⟧ R) :=
  isContradictory_outerNeg _ R

/-- E–I diagonal: `no` and `some` are contradictory, since `some = ~no`. -/
theorem no_satisfies_isContradictory_pointwise (R : α → Prop) :
    Aristotelian.IsContradictory
      ((⟦no⟧ R) : (α → Prop) → Prop)
      (⟦some⟧ R) := by
  have hno : outerNeg ⟦no⟧ = some_sem := by
    rw [← innerNeg_every_eq_no]; exact dualQ_every_eq_some
  rw [← hno]; exact isContradictory_outerNeg _ R

/-! ### Basic left monotonicities ([peters-westerstahl-2006] §5.5) -/

theorem some_upSE : UpSEMon ⟦some⟧ :=
  restrictorUpMono_to_upSE _ some_restrictor_up

theorem some_upSW : UpSWMon ⟦some⟧ :=
  restrictorUpMono_to_upSW _ some_restrictor_up

theorem every_downNW : DownNWMon ⟦every⟧ :=
  restrictorDownMono_to_downNW _ every_restrictor_down

theorem every_downNE : DownNEMon ⟦every⟧ :=
  restrictorDownMono_to_downNE _ every_restrictor_down

theorem no_downNW : DownNWMon ⟦no⟧ :=
  restrictorDownMono_to_downNW _ no_restrictor_down

theorem no_downNE : DownNEMon ⟦no⟧ :=
  restrictorDownMono_to_downNE _ no_restrictor_down

/-! ### Smooth quantifiers ([peters-westerstahl-2006] §5.6) -/

/-- `⟦some⟧` is ↓_NE Mon (direct proof). -/
theorem some_downNE : DownNEMon ⟦some⟧ := by
  intro R S R' _ hKeep ⟨x, hR, hS⟩
  exact ⟨x, hKeep x hR hS, hS⟩

theorem some_smooth : Smooth ⟦some⟧ :=
  ⟨some_downNE, restrictorUpMono_to_upSE _ some_restrictor_up⟩

/-- `⟦every⟧` is ↑_SE Mon (direct proof). -/
theorem every_upSE_direct : UpSEMon ⟦every⟧ := by
  intro R S R' _ hDiff hQ x hR'
  by_cases hS : S x
  · exact hS
  · exact hQ x (hDiff x hR' hS)

theorem every_smooth : Smooth ⟦every⟧ :=
  ⟨every_downNE, every_upSE_direct⟩

theorem no_coSmooth_partial :
    DownNWMon ⟦no⟧ ∧ DownNEMon ⟦no⟧ :=
  ⟨restrictorDownMono_to_downNW _ no_restrictor_down,
   restrictorDownMono_to_downNE _ no_restrictor_down⟩

/-! ### Satisfies universals: B&C's CONS + MON ([barwise-cooper-1981]; used as a
learnability/complexity target by [van-de-pol-etal-2023]) -/

theorem some_satisfiesUniversals : SatisfiesUniversals ⟦some⟧ :=
  ⟨some_conservative, Or.inl some_scope_up⟩

theorem every_satisfiesUniversals : SatisfiesUniversals ⟦every⟧ :=
  ⟨every_conservative, Or.inl every_scope_up⟩

theorem no_satisfiesUniversals : SatisfiesUniversals ⟦no⟧ :=
  ⟨no_conservative, Or.inr no_scope_down⟩

end Quantification
