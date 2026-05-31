import Linglib.Core.Logic.Quantification.Defs
import Linglib.Core.Logic.Quantification.Properties
import Linglib.Core.Logic.Aristotelian.Basic

/-!
# Concrete propositional generalized quantifiers
@cite{barwise-cooper-1981} @cite{keenan-stavi-1986} @cite{peters-westerstahl-2006}

The three propositional GQs `every_sem`, `some_sem`, `no_sem` and the property
proofs that don't need `Fintype`. Counting GQs (`most_sem`, `few_sem`, etc.) and
their proofs live in `Core.Logic.Quantification.Counting`.

## Main declarations

* `every_sem`, `some_sem`, `no_sem` — the three propositional GQ denotations.
* `SatisfiesUniversals` — B&C universals: conservativity + monotonicity in scope.
* Conservativity/monotonicity/symmetry/intersectivity/duality/etc. proofs.
-/

namespace Core.Quantification

/-! ### Denotations -/

/-- ⟦every⟧ = λR.λS. ∀x. R(x) → S(x). -/
def every_sem {α : Type*} : GQ α := fun R S => ∀ x : α, R x → S x

/-- ⟦some⟧ = λR.λS. ∃x. R(x) ∧ S(x). -/
def some_sem {α : Type*} : GQ α := fun R S => ∃ x : α, R x ∧ S x

/-- ⟦no⟧ = λR.λS. ∀x. R(x) → ¬S(x). -/
def no_sem {α : Type*} : GQ α := fun R S => ∀ x : α, R x → ¬ S x

/-- B&C semantic universals (@cite{barwise-cooper-1981}): conservativity plus
    monotonicity in scope. Convenience conjunction of three Core predicates. -/
def SatisfiesUniversals {α : Type*} (q : GQ α) : Prop :=
  Conservative q ∧ (ScopeUpwardMono q ∨ ScopeDownwardMono q)

variable {α : Type*}

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

theorem every_conservative : Conservative (every_sem (α := α)) := by
  intro R S; simp only [every_sem]
  exact ⟨fun h x hR => ⟨hR, h x hR⟩, fun h x hR => (h x hR).2⟩

theorem some_conservative : Conservative (some_sem (α := α)) := by
  intro R S; simp only [some_sem]
  exact ⟨fun ⟨x, hR, hS⟩ => ⟨x, hR, hR, hS⟩, fun ⟨x, hR, _, hS⟩ => ⟨x, hR, hS⟩⟩

theorem no_conservative : Conservative (no_sem (α := α)) := by
  intro R S; simp only [no_sem]
  exact ⟨fun h x hR ⟨_, hS⟩ => h x hR hS, fun h x hR hS => h x hR ⟨hR, hS⟩⟩

/-! ### Scope monotonicity -/

theorem every_scope_up : ScopeUpwardMono (every_sem (α := α)) := by
  intro R S S' hSS' h x hR; exact hSS' x (h x hR)

theorem some_scope_up : ScopeUpwardMono (some_sem (α := α)) := by
  intro R S S' hSS' ⟨x, hR, hS⟩; exact ⟨x, hR, hSS' x hS⟩

theorem no_scope_down : ScopeDownwardMono (no_sem (α := α)) := by
  intro R S S' hSS' h x hR hS; exact h x hR (hSS' x hS)

/-! ### Symmetry (P&W Ch.6) -/

theorem some_symmetric : QSymmetric (some_sem (α := α)) := by
  intro R S; simp only [some_sem]
  exact ⟨fun ⟨x, hR, hS⟩ => ⟨x, hS, hR⟩, fun ⟨x, hS, hR⟩ => ⟨x, hR, hS⟩⟩

theorem no_symmetric : QSymmetric (no_sem (α := α)) := by
  intro R S; simp only [no_sem]
  exact ⟨fun h x hS hR => h x hR hS, fun h x hR hS => h x hS hR⟩

/-! ### Intersectivity (CONSERV + SYMM bridge) -/

theorem some_intersective : IntersectionCondition (some_sem (α := α)) := by
  intro R S R' S' hInt
  simp only [some_sem]
  exact ⟨fun ⟨x, hR, hS⟩ => let ⟨hR', hS'⟩ := (hInt x).mp ⟨hR, hS⟩; ⟨x, hR', hS'⟩,
         fun ⟨x, hR', hS'⟩ => let ⟨hR, hS⟩ := (hInt x).mpr ⟨hR', hS'⟩; ⟨x, hR, hS⟩⟩

theorem no_intersective : IntersectionCondition (no_sem (α := α)) := by
  intro R S R' S' hInt
  simp only [no_sem]
  refine ⟨fun h x hR' hS' => h x ((hInt x).mpr ⟨hR', hS'⟩).1 ((hInt x).mpr ⟨hR', hS'⟩).2,
          fun h x hR hS => h x ((hInt x).mp ⟨hR, hS⟩).1 ((hInt x).mp ⟨hR, hS⟩).2⟩

/-! ### Left/right anti-additivity (P&W §5.8) -/

theorem every_laa : LeftAntiAdditive (every_sem (α := α)) := by
  intro R R' S; simp only [every_sem]
  refine ⟨fun h => ⟨fun x hR => h x (Or.inl hR), fun x hR' => h x (Or.inr hR')⟩,
          fun ⟨h1, h2⟩ x hRR' => hRR'.elim (h1 x) (h2 x)⟩

theorem no_laa : LeftAntiAdditive (no_sem (α := α)) := by
  intro R R' S; simp only [no_sem]
  refine ⟨fun h => ⟨fun x hR => h x (Or.inl hR), fun x hR' => h x (Or.inr hR')⟩,
          fun ⟨h1, h2⟩ x hRR' => hRR'.elim (h1 x) (h2 x)⟩

theorem no_raa : RightAntiAdditive (no_sem (α := α)) := by
  intro R S S'; simp only [no_sem]
  refine ⟨fun h => ⟨fun x hR hS => h x hR (Or.inl hS),
                    fun x hR hS' => h x hR (Or.inr hS')⟩,
          fun ⟨h1, h2⟩ x hR hSS' => hSS'.elim (h1 x hR) (h2 x hR)⟩

/-- @cite{peters-westerstahl-2006} Prop 13: the only non-trivial CONSERV, EXT,
    and ISOM quantifiers satisfying LAA are `every` and `no` (and `A = ∅`). -/
theorem laa_characterization :
    LeftAntiAdditive (every_sem (α := α)) ∧
    LeftAntiAdditive (no_sem (α := α)) := ⟨every_laa, no_laa⟩

/-! ### Duality square (B&C §4.11) -/

/-- Inner negation maps `every` to `no`: every...not = no.
    `∀x. R(x) → ¬S(x)` = `¬∃x. R(x) ∧ S(x)`. -/
theorem innerNeg_every_eq_no :
    (innerNeg (every_sem (α := α)) : GQ α) = (no_sem (α := α) : GQ α) := by
  funext R S; simp only [innerNeg, every_sem, no_sem]

/-- The dual of `every` is `some`: Q̌(every) = some. -/
theorem dualQ_every_eq_some :
    (dualQ (every_sem (α := α)) : GQ α) = (some_sem (α := α) : GQ α) := by
  funext R S; simp only [dualQ, outerNeg, innerNeg, every_sem, some_sem]
  exact propext ⟨fun h => by push_neg at h; exact h,
                 fun ⟨x, hR, hS⟩ h => h x hR hS⟩

/-- `outerNeg ⟦some⟧ = ⟦no⟧`: negating existence gives universal negation. -/
theorem outerNeg_some_eq_no :
    (outerNeg (some_sem (α := α)) : GQ α) = (no_sem (α := α) : GQ α) := by
  funext R S; simp only [outerNeg, some_sem, no_sem]
  exact propext ⟨fun h x hR hS => h ⟨x, hR, hS⟩,
                 fun h ⟨x, hR, hS⟩ => h x hR hS⟩

/-! ### Positive/negative strong (P&W Ch.6) -/

theorem every_positive_strong : PositiveStrong (every_sem (α := α)) := by
  intro R x hR; exact hR

/-- `⟦no⟧` is negative strong on non-empty restrictors:
    no(A,A) = false for all non-empty A. -/
theorem no_negative_strong_nonempty (R : α → Prop)
    (hR : ∃ x : α, R x) :
    ¬ no_sem (α := α) R R := by
  intro h; obtain ⟨x, hRx⟩ := hR; exact h x hRx hRx

/-! ### K&S existential det classification (§3.3, G3) -/

theorem some_existential : Existential (some_sem (α := α)) := by
  intro R S; simp only [some_sem]
  exact ⟨fun ⟨x, hR, hS⟩ => ⟨x, ⟨hR, hS⟩, trivial⟩,
         fun ⟨x, ⟨hR, hS⟩, _⟩ => ⟨x, hR, hS⟩⟩

theorem no_existential : Existential (no_sem (α := α)) := by
  intro R S; simp only [no_sem]
  exact ⟨fun h x ⟨hR, hS⟩ _ => h x hR hS,
         fun h x hR hS => h x ⟨hR, hS⟩ trivial⟩

/-! ### Relational properties (@cite{van-benthem-1984}) -/

theorem every_transitive : QTransitive (every_sem (α := α)) := by
  intro A B C hAB hBC x hA; exact hBC x (hAB x hA)

theorem every_antisymmetric : QAntisymmetric (every_sem (α := α)) := by
  intro A B hAB hBA
  funext x; exact propext ⟨fun hA => hAB x hA, fun hB => hBA x hB⟩

theorem some_quasi_reflexive : QuasiReflexive (some_sem (α := α)) := by
  intro A B ⟨x, hA, _⟩; exact ⟨x, hA, hA⟩

theorem no_quasi_universal : QuasiUniversal (no_sem (α := α)) := by
  intro A B hAA x hA; exact absurd hA (hAA x hA)

/-! ### Double monotonicity classification (@cite{van-benthem-1984} §4.2) -/

/-- `⟦every⟧` is restrictor-↓ (anti-persistent). Follows from Zwarts bridge:
    reflexive + transitive + CONSERV → ↓MON. -/
theorem every_restrictor_down : RestrictorDownwardMono (every_sem (α := α)) :=
  zwarts_refl_trans_restrictorDown _ every_conservative every_positive_strong
    every_transitive

theorem some_restrictor_up : RestrictorUpwardMono (some_sem (α := α)) := by
  intro R R' S hRR' ⟨x, hR, hS⟩; exact ⟨x, hRR' x hR, hS⟩

theorem no_restrictor_down : RestrictorDownwardMono (no_sem (α := α)) := by
  intro R R' S hRR' hQ x hR; exact hQ x (hRR' x hR)

theorem every_doubleMono :
    RestrictorDownwardMono (every_sem (α := α)) ∧
    ScopeUpwardMono (every_sem (α := α)) :=
  ⟨every_restrictor_down, every_scope_up⟩

theorem some_doubleMono :
    RestrictorUpwardMono (some_sem (α := α)) ∧
    ScopeUpwardMono (some_sem (α := α)) :=
  ⟨some_restrictor_up, some_scope_up⟩

theorem no_doubleMono :
    RestrictorDownwardMono (no_sem (α := α)) ∧
    ScopeDownwardMono (no_sem (α := α)) :=
  ⟨no_restrictor_down, no_scope_down⟩

theorem notAll_doubleMono :
    RestrictorUpwardMono (outerNeg (every_sem (α := α))) ∧
    ScopeDownwardMono (outerNeg (every_sem (α := α))) :=
  ⟨outerNeg_restrictorDown_to_up _ every_restrictor_down,
   outerNeg_up_to_down _ every_scope_up⟩

theorem every_filtrating : Filtrating (every_sem (α := α)) := by
  intro A B C hAB hAC x hA; exact ⟨hAB x hA, hAC x hA⟩

/-! ### Aristotelian square of opposition

The six theorems below establish the four Aristotelian relations among GQ
denotations `(every_sem, some_sem, no_sem, outerNeg every_sem)` at fixed
restrictor `R`. They work over `Prop`-valued predicates, while
`Core.Logic.Aristotelian.Basic` formulates the same relations over
`Bool`-valued predicates. The two frameworks are mathematically equivalent
but type-different. -/

/-- Contradiction (A vs O): the A-form and O-form are contradictories. -/
theorem every_contradicts_notEvery (R S : α → Prop) :
    every_sem (α := α) R S ↔ ¬ (outerNeg (every_sem (α := α)) R S) := by
  simp [outerNeg, Classical.not_not]

/-- Contradiction (E vs I): the E-form and I-form are contradictories. -/
theorem no_contradicts_some (R S : α → Prop) :
    no_sem (α := α) R S ↔ ¬ (some_sem (α := α) R S) := by
  simp only [no_sem, some_sem]; push_neg; rfl

/-- Contrariety (A ∧ E): the A-form and E-form can't both hold unless the
    restrictor is empty. -/
theorem a_e_contrary (R S : α → Prop) :
    every_sem (α := α) R S → no_sem (α := α) R S →
    ∀ x : α, ¬ R x := by
  intro hA hE x hR; exact hE x hR (hA x hR)

/-- Subalternation (A → I): the A-form entails the I-form when the
    restrictor is non-empty. -/
theorem subalternation_a_i (R S : α → Prop)
    (hR : ∃ x : α, R x) :
    every_sem (α := α) R S → some_sem (α := α) R S := by
  intro hA; obtain ⟨x, hRx⟩ := hR; exact ⟨x, hRx, hA x hRx⟩

/-- Subalternation (E → O): the E-form entails the O-form when the
    restrictor is non-empty. -/
theorem subalternation_e_o (R S : α → Prop)
    (hR : ∃ x : α, R x) :
    no_sem (α := α) R S → outerNeg (every_sem (α := α)) R S := by
  intro hE hA; obtain ⟨x, hRx⟩ := hR; exact hE x hRx (hA x hRx)

/-- Subcontrariety (I ∨ O): the I-form and O-form can't both fail when the
    restrictor is non-empty. -/
theorem subcontrariety_i_o (R S : α → Prop)
    (hR : ∃ x : α, R x) :
    some_sem (α := α) R S ∨ outerNeg (every_sem (α := α)) R S := by
  by_cases h : some_sem (α := α) R S
  · exact Or.inl h
  · right; intro hA; apply h
    obtain ⟨x, hRx⟩ := hR; exact ⟨x, hRx, hA x hRx⟩

/-- The canonical A↔O contradiction diagonal, packaged as
    `Aristotelian.IsContradictory` over the Pi-instance Boolean algebra
    on `(α → Prop) → Prop`. -/
theorem every_satisfies_isContradictory_pointwise (R : α → Prop) :
    Aristotelian.IsContradictory
      ((every_sem (α := α) R) : (α → Prop) → Prop)
      (outerNeg (every_sem (α := α)) R) := by
  unfold Aristotelian.IsContradictory
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  refine ⟨?_, ?_⟩
  · funext S
    exact propext ⟨fun ⟨h1, h2⟩ => h2 h1, fun h => h.elim⟩
  · funext S
    exact propext ⟨fun _ => trivial, fun _ =>
      (Classical.em (every_sem (α := α) R S)).elim Or.inl Or.inr⟩

/-! ### Basic left monotonicities (@cite{peters-westerstahl-2006} §5.5) -/

theorem some_upSE : UpSEMon (some_sem (α := α)) :=
  restrictorUpMono_to_upSE _ some_restrictor_up

theorem some_upSW : UpSWMon (some_sem (α := α)) :=
  restrictorUpMono_to_upSW _ some_restrictor_up

theorem every_downNW : DownNWMon (every_sem (α := α)) :=
  restrictorDownMono_to_downNW _ every_restrictor_down

theorem every_downNE : DownNEMon (every_sem (α := α)) :=
  restrictorDownMono_to_downNE _ every_restrictor_down

theorem no_downNW : DownNWMon (no_sem (α := α)) :=
  restrictorDownMono_to_downNW _ no_restrictor_down

theorem no_downNE : DownNEMon (no_sem (α := α)) :=
  restrictorDownMono_to_downNE _ no_restrictor_down

/-! ### Smooth quantifiers (@cite{peters-westerstahl-2006} §5.6) -/

/-- `⟦some⟧` is ↓_NE Mon (direct proof). -/
theorem some_downNE : DownNEMon (some_sem (α := α)) := by
  intro R S R' _ hKeep ⟨x, hR, hS⟩
  exact ⟨x, hKeep x hR hS, hS⟩

theorem some_smooth : Smooth (some_sem (α := α)) :=
  ⟨some_downNE, restrictorUpMono_to_upSE _ some_restrictor_up⟩

/-- `⟦every⟧` is ↑_SE Mon (direct proof). -/
theorem every_upSE_direct : UpSEMon (every_sem (α := α)) := by
  intro R S R' _ hDiff hQ x hR'
  by_cases hS : S x
  · exact hS
  · exact hQ x (hDiff x hR' hS)

theorem every_smooth : Smooth (every_sem (α := α)) :=
  ⟨every_downNE, every_upSE_direct⟩

theorem no_coSmooth_partial :
    DownNWMon (no_sem (α := α)) ∧ DownNEMon (no_sem (α := α)) :=
  ⟨restrictorDownMono_to_downNW _ no_restrictor_down,
   restrictorDownMono_to_downNE _ no_restrictor_down⟩

/-! ### Satisfies universals (@cite{van-de-pol-etal-2023}) -/

theorem some_satisfiesUniversals : SatisfiesUniversals (some_sem (α := α)) :=
  ⟨some_conservative, Or.inl some_scope_up⟩

theorem every_satisfiesUniversals : SatisfiesUniversals (every_sem (α := α)) :=
  ⟨every_conservative, Or.inl every_scope_up⟩

theorem no_satisfiesUniversals : SatisfiesUniversals (no_sem (α := α)) :=
  ⟨no_conservative, Or.inr no_scope_down⟩

end Core.Quantification
