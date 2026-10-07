module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Order.UpperLower.Closure
public import Linglib.Semantics.Degree.Background
public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Degree.Delineation
public import Linglib.Semantics.Degree.Measure.Dimensioned

/-!
# Morphisms between gradability representations

The maps between the framework objects for gradable predicates, with their faithfulness
theorems — the degree-semantic analogue of the representation maps in
`Phonology/Autosegmental` (AR ↔ tone strings):

```
Klein (Delineation)             — most general
  ↑ upper sets as extensions: monotone iff the background is total
States-based (background preorder, threshold upper sets)
  ↑ pullback of degree thresholds: exact iff the measure reflects the background
Kennedy (measure functions)     — specialization: single linear scale
  ↑ DimensionedMeasure.apply
Scontras / Bale & Schwarz (typed measurement)
```

Kennedy embeds in Klein directly by `Delineation.measureDelineation`, whose ordering is degree
comparison (`Delineation.ordering_iff_degree`). Delineation expresses nonlinear adjectives
("clever") that no degree function induces, since a measure induces a monotone delineation and a
monotone delineation is never nonlinear
(`Delineation.IsMonotoneDelineation.not_isNonlinearDelineation`), and a non-total background has
thresholds that no degree threshold induces (`exists_isUpperSet_forall_ne_preimage`).

## What each framework adds

| Framework    | Ontology          | Comparative          | Unique capacity             |
|--------------|-------------------|----------------------|-----------------------------|
| Klein        | No degrees        | ∃C. A(x,C) ∧ ¬A(y,C) | Nonlinear adjectives        |
| States-based | Preordered states | μ(s) > max, μ admissible | Positive form without *pos* |
| Kennedy      | Degrees (D,≤)     | μ(x) > μ(y)          | Measure phrases, DegP       |
| Measurement  | Degrees + dim     | μ_d(x) > μ_d(y)      | Typed dimensions, CARD      |

## Main results

* `isMonotoneDelineation_upperSets_iff`: the thresholds of a background form a monotone
  delineation iff the background is total.
* `maxComparative_iff_exists_isUpperSet`: on a total background the comparative is Klein's.
* `forall_isUpperSet_exists_preimage_iff`, `total_of_reflect_le`: thresholds are pulled-back
  degree thresholds iff the measure reflects the background, which forces totality.
* `Comparison.ge_over_eq_Ici`: a threshold above a contrast state is the degree-threshold
  positive form at its degree.
* `cresswellSetoid_le_iff`: Cresswell's degrees are the antisymmetrization of the comparison; on
  an equivalence relation the construction returns its classes (`cresswellSetoid_setoid`).
* `maxComparative_comp`, `positive_not_natural`, `cross_scale_not_natural`: which operators
  survive a change of scale.

## References

* [kamp-1975]
* [klein-1980]
* [kennedy-1999]
* [kennedy-2007]
* [scontras-2014]
* [bale-schwarz-2022]
* [cresswell-1976]
* [cariani-santorio-wellwood-2023]
* [mendia-2020]
-/

@[expose] public section

namespace Degree

open Degree.Delineation

/-! ### Measurement → Degree → Delineation

The maps themselves carry no new definitions: measurement forgets to a
bare degree function by the `DimensionedMeasure.apply` projection
([scontras-2014]'s insight that measure terms and CARD are one
degree-assigning operation), and any degree function `μ` over a linear
order induces a Klein delineation via `Degree.Delineation.measureDelineation`
— the embedding of measure-function degree semantics ([kennedy-1999],
developed in [kennedy-2007]) into [klein-1980]'s framework. The embedding is faithful
(`ordering_iff_degree`: Klein's ordering under the induced delineation
is exactly degree comparison) and lands in the monotone, linear
fragment (`measureDelineation_monotone`, `measureDelineation_is_linear`).
-/

/-! ### Background orderings ([cariani-santorio-wellwood-2023])

The states-based framework of `Semantics/Degree/Background.lean` has a background preorder of
states whose threshold properties are its upper sets. Read as extensions, the thresholds form a
monotone delineation exactly when the background is total, which makes precise the parallel the
paper draws between its monotonicity postulate and [klein-1980]'s Consistency Postulate; with a
monotone admissible measure the comparative is then Klein's, some threshold separating the two.
The thresholds are degree thresholds pulled back along the measure exactly when the measure
reflects the background, and such a measure into a linear scale forces the background to be
total; a threshold above a contrast state is then the degree-threshold positive form at that
state's degree. -/

section Background

open Set

variable {S X D : Type*} [Preorder S] [Preorder D] {ρ : S → X} {μ : S → D}

/-- The upper sets of a background, as extensions, form a monotone delineation iff the
background is total. Two incomparable states give the cycle of a nonlinear delineation. -/
theorem isMonotoneDelineation_upperSets_iff :
    IsMonotoneDelineation (fun (C : Set S) s ↦ s ∈ C) {C | IsUpperSet C} ↔
      ∀ s t : S, s ≤ t ∨ t ≤ s := by
  refine ⟨fun h s t ↦ by_contra fun hst ↦ ?_, fun htot C₁ C₂ h₁ h₂ a b ha hb hb₂ ↦ ?_⟩
  · obtain ⟨hst, hts⟩ := not_or.1 hst
    exact hts (h (Ici s) (Ici t) (isUpperSet_Ici s) (isUpperSet_Ici t) s t le_rfl hst le_rfl)
  · exact (htot a b).elim (fun hab ↦ absurd (h₁ hab ha) hb) fun hba ↦ h₂ hba hb₂

/-- With a monotone measure the comparative yields a separating threshold: if `a` has more than
`b`, some threshold property holds of `a` and not of `b`. -/
theorem exists_isUpperSet_of_maxComparative (hm : Monotone μ) {a b : X}
    (h : maxComparative (ρ · = a) (ρ · = b) μ) :
    ∃ T, IsUpperSet T ∧ a ∈ ρ '' T ∧ b ∉ ρ '' T := by
  obtain ⟨δ, hδ, s, hsa, hlt⟩ := h
  refine ⟨Ici s, isUpperSet_Ici s, ⟨s, mem_Ici.2 le_rfl, hsa⟩, ?_⟩
  rintro ⟨t, hst, htb⟩
  exact ((hδ.2 ⟨t, htb, le_rfl⟩).trans_lt hlt).not_ge (hm hst)

/-- Admissibility alone does not yield a separating threshold: with two tied states every
measure is admissible and every threshold holding of one holds of the other. The preorder is
passed explicitly, since `Bool`'s own order would otherwise be found. -/
example :
    let tied : Preorder Bool := Preorder.lift fun _ ↦ ()
    @admissibleMeasure _ _ tied _ Bool.toNat ∧ maxComparative (· = true) (· = false) Bool.toNat ∧
      ∀ T : Set Bool, @IsUpperSet _ tied.toLE T → true ∈ T → false ∈ T :=
  ⟨fun _ _ h ↦ absurd h (lt_irrefl ()), (maxComparative_eq_iff _ _ _).2 Nat.zero_lt_one,
    fun _ hT ht ↦ hT trivial ht⟩

/-- On a total background with an admissible measure a separating threshold yields the
comparative, when the degrees of `b`'s states have a greatest element. -/
theorem maxComparative_of_exists_isUpperSet [@Std.Total S (· ≤ ·)] (hμ : admissibleMeasure μ)
    {a b : X} (hb : ∃ δ, IsGreatest (thanDegrees (ρ · = b) μ) δ)
    (h : ∃ T, IsUpperSet T ∧ a ∈ ρ '' T ∧ b ∉ ρ '' T) :
    maxComparative (ρ · = a) (ρ · = b) μ := by
  obtain ⟨δ, hδ⟩ := hb
  obtain ⟨T, hT, ⟨s, hsT, hsa⟩, hbT⟩ := h
  obtain ⟨t, htb, hδt⟩ := hδ.1
  have hst : ¬ s ≤ t := fun hst ↦ hbT ⟨t, hT hst hsT, htb⟩
  exact ⟨δ, hδ, s, hsa, hδt.trans_lt (hμ (lt_of_le_not_ge
    ((total_of (· ≤ ·) t s).resolve_right hst) hst))⟩

/-- On a total background with a monotone admissible measure the comparative is Klein's: `a`
has more than `b` iff some threshold property holds of `a` and not of `b`. -/
theorem maxComparative_iff_exists_isUpperSet [@Std.Total S (· ≤ ·)] (hμ : admissibleMeasure μ)
    (hm : Monotone μ) {a b : X} (hb : ∃ δ, IsGreatest (thanDegrees (ρ · = b) μ) δ) :
    maxComparative (ρ · = a) (ρ · = b) μ ↔ ∃ T, IsUpperSet T ∧ a ∈ ρ '' T ∧ b ∉ ρ '' T :=
  ⟨exists_isUpperSet_of_maxComparative hm, maxComparative_of_exists_isUpperSet hμ hb⟩

/-- Every threshold property of the background is a degree threshold pulled back along the
measure iff the measure reflects the background. -/
theorem forall_isUpperSet_exists_preimage_iff :
    (∀ T : Set S, IsUpperSet T → ∃ U : Set D, IsUpperSet U ∧ T = μ ⁻¹' U) ↔
      ∀ a b, μ a ≤ μ b → a ≤ b := by
  refine ⟨fun h a b hab ↦ ?_, fun h T hT ↦ ⟨upperClosure (μ '' T), (upperClosure _).upper, ?_⟩⟩
  · obtain ⟨U, hU, hT⟩ := h (Ici a) (isUpperSet_Ici a)
    exact (Set.ext_iff.1 hT b).2 (hU hab ((Set.ext_iff.1 hT a).1 (mem_Ici.2 le_rfl)))
  · refine Set.ext fun s ↦ ⟨fun hs ↦ subset_upperClosure ⟨s, hs, rfl⟩, ?_⟩
    rintro ⟨_, ⟨t, ht, rfl⟩, hts⟩
    exact hT (h t s hts) ht

/-- A measure into a linear scale that reflects the background makes it total. -/
theorem total_of_reflect_le {D : Type*} [LinearOrder D] {μ : S → D}
    (h : ∀ a b, μ a ≤ μ b → a ≤ b) (s t : S) : s ≤ t ∨ t ≤ s :=
  (le_total (μ s) (μ t)).imp (h s t) (h t s)

/-- On a non-total background some threshold property is no degree threshold pulled back along
any measure into a linear scale. -/
theorem exists_isUpperSet_forall_ne_preimage {D : Type*} [LinearOrder D] (μ : S → D) {s t : S}
    (hst : ¬ s ≤ t) (hts : ¬ t ≤ s) :
    ∃ T : Set S, IsUpperSet T ∧ ∀ U : Set D, IsUpperSet U → T ≠ μ ⁻¹' U := by
  by_contra h
  push Not at h
  obtain h | h := total_of_reflect_le (forall_isUpperSet_exists_preimage_iff.1 h) s t
  exacts [hst h, hts h]

/-- When the measure reflects the background and respects ties, the threshold above a contrast
state `c` is the degree-threshold positive form at the degree of `c`. -/
theorem Comparison.ge_over_eq_Ici (h : ∀ a b, μ a ≤ μ b → a ≤ b) (hm : Monotone μ) (c : S) :
    Comparison.ge.over μ (μ c) = Ici c :=
  Set.ext fun s ↦ ⟨h c s, fun hs ↦ hm hs⟩

end Background

/-! ### Measurement = Degree + Dimension Typing -/

/-! The relationship between measurement semantics ([scontras-2014],
    [bale-schwarz-2022]) and degree semantics ([kennedy-2007])
    is simple: measurement adds typed dimensions to degree functions.

    A `DimensionedMeasure E` is a degree function `apply : E → ℚ` PLUS a
    `dimension : Dimension` label. The degree function is recoverable
    via `DimensionedMeasure.toHasDegree`, but the dimension label is lost.

    What dimension typing buys you:
    - Multiple measure functions per entity (weight AND volume AND count)
    - The No Division Hypothesis: compositional operations respect dimension types
    - Measure term semantics: ⟦kilo⟧ = λn.λx. μ_kg(x) = n, typed to mass

    What it does NOT buy you: any new ordering structure. Measurement
    adjectives are still degree adjectives under the hood. -/

/-! ### The degree construction ([cresswell-1976] §4)

Degrees built from comparisons rather than assumed: [cresswell-1976]
(4.1) quotients an arbitrary comparison relation `φ` by two-sided
φ-indistinguishability, and (4.2) shows the induced comparison on
classes is well-defined. On a preorder the construction coincides with
mathlib's `Antisymmetrization` (`cresswellSetoid_le_iff`). -/

/-- Two pairs are indistinguishable under a comparison `φ` when they have the same φ-profile on the
left and on the right, [cresswell-1976] (4.1). -/
def cresswellSetoid {E : Type*} (φ : E → E → Prop) : Setoid E where
  r a b := (∀ c, φ a c ↔ φ b c) ∧ (∀ c, φ c a ↔ φ c b)
  iseqv :=
    ⟨fun _ => ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩,
     fun h => ⟨fun c => (h.1 c).symm, fun c => (h.2 c).symm⟩,
     fun h₁ h₂ => ⟨fun c => (h₁.1 c).trans (h₂.1 c),
                   fun c => (h₁.2 c).trans (h₂.2 c)⟩⟩

/-- Degrees of comparison as φ-equivalence classes ([cresswell-1976] (4.1)). -/
abbrev CresswellDegree {E : Type*} (φ : E → E → Prop) : Type _ :=
  Quotient (cresswellSetoid φ)

/-- The comparison a relation induces on its degrees, `⟦a⟧ < ⟦b⟧` iff `φ b a`, strict exactly
when `φ` is; well-definedness is [cresswell-1976]'s own consistency proof for (4.2). -/
instance {E : Type*} {φ : E → E → Prop} : LT (CresswellDegree φ) :=
  ⟨Quotient.lift₂ (fun a b ↦ φ b a) fun a₁ _ _ b₂ hac hbd ↦ propext ((hbd.1 a₁).trans (hac.2 b₂))⟩

/-- The degree of `a` exceeds that of `b` exactly when `φ(a, b)`, [cresswell-1976] (4.2). -/
@[simp] theorem CresswellDegree.mk_lt_mk {E : Type*} {φ : E → E → Prop} {a b : E} :
    (⟦a⟧ : CresswellDegree φ) < ⟦b⟧ ↔ φ b a :=
  Iff.rfl

/-- On a preorder, φ-indistinguishability under `≤` is mathlib's
    `AntisymmRel`: the Cresswell quotient IS `Antisymmetrization`. -/
theorem cresswellSetoid_le_iff {E : Type*} [Preorder E] (a b : E) :
    (cresswellSetoid (· ≤ ·)).r a b ↔ AntisymmRel (· ≤ ·) a b := by
  constructor
  · intro ⟨h₁, h₂⟩
    exact ⟨(h₁ b).mpr le_rfl, (h₁ a).mp le_rfl⟩
  · intro ⟨hab, hba⟩
    exact ⟨fun c => ⟨hba.trans, hab.trans⟩,
           fun c => ⟨(le_trans · hab), (le_trans · hba)⟩⟩

/-- On an equivalence relation, φ-indistinguishability is the relation itself: the construction
returns the cells of a partition as well as degrees, [mendia-2020]'s (17)–(18). -/
theorem cresswellSetoid_setoid {E : Type*} (s : Setoid E) : cresswellSetoid s = s :=
  Setoid.ext fun _ b ↦ ⟨fun h ↦ (h.1 b).2 (s.refl' b), fun h ↦
    ⟨fun _ ↦ ⟨s.trans' (s.symm' h), s.trans' h⟩,
      fun _ ↦ ⟨(s.trans' · h), (s.trans' · (s.symm' h))⟩⟩⟩

/-! ### Transport: which operators are natural in the scale

How degree operators fare under a change of scale, an order embedding `f : D ↪o D'` applied to
the measure. Comparatives, equatives and the max-quantified comparative are invariant
(`Comparison.over_comp`, `maxComparative_comp`). The positive form is invariant only when its
threshold moves with the measure, or under the automorphisms that fix the threshold
(`Comparison.over_comp_of_isFixedPt`); with a fixed threshold some rescaling changes the verdict
(`positive_not_natural`), the formal face of the positive form's need for a contextual standard.
A comparison between measures on two scales survives rescaling both together but not rescaling
one alone (`cross_scale_not_natural`); universal degrees survive independent rescalings
(`Degree/UniversalScale`). -/

section TransportMax

variable {Entity D D' : Type*} [LinearOrder D] [LinearOrder D'] {μ : Entity → D}

/-- The max-quantified comparative is invariant under an order embedding of the scale. Not
immediate: `thanDegrees` is a downset and images of downsets need not be downsets, but the
greatest element rides along. -/
theorem maxComparative_comp (f : D ↪o D') (Pmatrix Pthan : Entity → Prop) :
    maxComparative Pmatrix Pthan (f ∘ μ) ↔ maxComparative Pmatrix Pthan μ := by
  constructor
  · rintro ⟨δ', ⟨⟨x₀, hQ, hδx₀⟩, hub⟩, x, hP, hlt⟩
    have hδeq : δ' = f (μ x₀) := le_antisymm hδx₀ (hub ⟨x₀, hQ, le_rfl⟩)
    refine ⟨μ x₀, ⟨⟨x₀, hQ, le_rfl⟩, ?_⟩, x, hP, f.lt_iff_lt.mp (hδeq ▸ hlt)⟩
    rintro d ⟨y, hQy, hdy⟩
    exact hdy.trans (f.le_iff_le.mp (hδeq ▸ hub ⟨y, hQy, le_rfl⟩))
  · rintro ⟨δ, ⟨⟨y, hQy, hδy⟩, hub⟩, x, hP, hlt⟩
    refine ⟨f δ, ⟨⟨y, hQy, f.monotone hδy⟩, ?_⟩, x, hP, f.strictMono hlt⟩
    rintro d ⟨y, hQy, hdy⟩
    exact hdy.trans (f.monotone (hub ⟨y, hQy, le_rfl⟩))

/-- With a fixed threshold the positive form is not natural: some order embedding of the scale
changes the verdict. -/
theorem positive_not_natural :
    ∃ f : ℚ ↪o ℚ, ∃ (μ : ℚ → ℚ) (θ x : ℚ),
      x ∈ Comparison.ge.over μ θ ∧ x ∉ Comparison.ge.over (f ∘ μ) θ :=
  ⟨OrderEmbedding.ofStrictMono (· - 1) fun _ _ h ↦ by simpa, id, 0, 0, by simp,
    by simp [Comparison.mem_over, Comparison.rel]⟩

/-- Comparing two measures across scales is not invariant under an order embedding of one of
them, unlike comparing two measures on one scale rescaled together (`Comparison.over_comp`). -/
theorem cross_scale_not_natural :
    ∃ f : ℚ ↪o ℚ, ∃ (μ ν : ℚ → ℚ) (x y : ℚ),
      x ∈ Comparison.gt.over μ (ν y) ∧ x ∉ Comparison.gt.over (f ∘ μ) (ν y) :=
  ⟨OrderEmbedding.ofStrictMono (· - 1) fun _ _ h ↦ by simpa, id, id, 1, 0, by simp,
    by simp [Comparison.mem_over, Comparison.rel]⟩

end TransportMax

end Degree
