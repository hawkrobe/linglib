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
("clever") that no degree function induces (`delineation_strictly_more_general`,
`nonlinear_delineation_exists`), and a non-total background has thresholds that no degree
threshold induces (`exists_isUpperSet_forall_ne_preimage`).

## What each framework adds

| Framework    | Ontology          | Comparative          | Unique capacity             |
|--------------|-------------------|----------------------|-----------------------------|
| Klein        | No degrees        | ∃C. A(x,C) ∧ ¬A(y,C) | Nonlinear adjectives        |
| States-based | Preordered states | μ(s) > max, μ admissible | Positive form without *pos* |
| Kennedy      | Degrees (D,≤)     | μ(x) > μ(y)          | Measure phrases, DegP       |
| Measurement  | Degrees + dim     | μ_d(x) > μ_d(y)      | Typed dimensions, CARD      |

## Main results

* `delineation_strictly_more_general`, `monotone_excludes_nonlinear`: degree functions induce
  monotone delineations, and monotone delineations are never nonlinear.
* `isMonotoneDelineation_upperSets_iff`: the thresholds of a background form a monotone
  delineation iff the background is total.
* `maxComparative_iff_exists_isUpperSet`: on a total background the comparative is Klein's.
* `forall_isUpperSet_exists_preimage_iff`, `total_of_reflect_le`: thresholds are pulled-back
  degree thresholds iff the measure reflects the background, which forces totality.
* `Comparison.ge_over_eq_Ici`: a threshold above a contrast state is the degree-threshold
  positive form at its degree.
* `cresswellSetoid_le_iff`, `factors_through_cresswellDegree`: Cresswell's degrees are the
  antisymmetrization of the comparison; on an equivalence relation the construction returns
  its classes (`cresswellSetoid_setoid`).
* `maxComparative_comp`, `positive_not_natural`: which operators are natural in the scale.

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

/-! ### Strict Separation: Delineation > Degree -/

/-! Klein's delineation framework is STRICTLY more general than degree
    semantics. The key witness: **nonlinear adjectives** like "clever"
    produce cyclic orderings (both a > b and b > a for different
    comparison classes). This is impossible for any degree-induced
    delineation, since degree orderings are asymmetric.

    See `Studies/Klein1980.lean` for the empirical
    motivation and the concrete "clever" witness. Here we prove the
    theoretical separation at the framework level. -/

/-- Monotone delineations cannot be nonlinear: monotonicity forces
    asymmetry, which excludes cycles. This is the core constraint
    that degree semantics imposes — and that Klein's framework relaxes. -/
theorem monotone_excludes_nonlinear {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (hmono : IsMonotoneDelineation delineation Set.univ)
    (hnn : IsNonlinearDelineation delineation) : False := by
  obtain ⟨_, u, u', ⟨X₁, _, hu₁, hnu'₁⟩, ⟨X₂, _, hu'₂, hnu₂⟩⟩ := hnn
  exact hnu₂ (hmono X₁ X₂ (Set.mem_univ _) (Set.mem_univ _) u u' hu₁ hnu'₁ hu'₂)

/-- This nonlinear delineation orders two entities differently depending on which other entities are
in the comparison class, as multi-criteria adjectives like *clever* do when different subsets apply
different ranking criteria: `j` is clever in `C` when `m` is absent, where the mathematical
criterion dominates, and `m` is clever when `j` is absent, where the social one does; in `{j, m}`
the criteria conflict. -/
inductive NL2 | j | m

def nlDel : ComparisonClass NL2 → NL2 → Prop
  | C, .j => NL2.m ∉ C
  | C, .m => NL2.j ∉ C

theorem nonlinear_delineation_exists :
    IsNonlinearDelineation nlDel := by
  refine ⟨{NL2.j, NL2.m}, NL2.j, NL2.m, ?_, ?_⟩
  · -- j > m via X = {j}: j clever (m absent), m not clever (j present)
    refine ⟨{NL2.j}, Set.singleton_subset_iff.mpr (Set.mem_insert _ _), ?_, ?_⟩
    · show NL2.m ∉ ({NL2.j} : Set NL2)
      simp [Set.mem_singleton_iff]
    · show ¬(NL2.j ∉ ({NL2.j} : Set NL2))
      simp
  · -- m > j via X = {m}: m clever (j absent), j not clever (m present)
    refine ⟨{NL2.m}, Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl), ?_, ?_⟩
    · show NL2.j ∉ ({NL2.m} : Set NL2)
      simp [Set.mem_singleton_iff]
    · show ¬(NL2.m ∉ ({NL2.m} : Set NL2))
      simp

/-- Klein's delineation framework is strictly more general than degree-based frameworks. Every
degree function induces a monotone delineation (`measureDelineation_monotone`), but some nonlinear
delineations are induced by no degree function, since degree-induced delineations are monotone and
monotonicity excludes nonlinearity. This is the formal content of Klein's critique of degree
semantics: multi-criteria adjectives like *clever* need the richer delineation framework. -/
theorem delineation_strictly_more_general :
    -- (i) Degree → Delineation: every degree function induces a monotone delineation
    (∀ (E D : Type*) [LinearOrder D] (μ : E → D),
      IsMonotoneDelineation (measureDelineation μ) Set.univ) ∧
    -- (ii) Delineation ⊋ Degree: there exist delineations no degree function can induce
    (∃ (E : Type) (del : ComparisonClass E → E → Prop),
      IsNonlinearDelineation del) :=
  ⟨fun _ _ _ μ => measureDelineation_monotone μ,
   ⟨NL2, nlDel, nonlinear_delineation_exists⟩⟩

/-! ### Degree = Monotone Delineation (Characterization) -/

/-! The degree-based frameworks correspond EXACTLY to the monotone
    fragment of Klein's delineation theory. This is not a coincidence:
    monotonicity is what ensures a delineation induces a well-behaved
    ordering (strict weak order), which is exactly what a degree scale
    provides.

    - Forward: degree → monotone delineation (`measureDelineation_monotone`)
    - Backward: monotone delineation → degree-recoverable ([klein-1980] §4.2,
      proved in `Klein1980.lean` as `kleinDegree_measureDelineation`)

    Together: `degree semantics = monotone delineation semantics`.
    Klein's full framework adds the non-monotone fragment for
    multi-criteria adjectives. -/

/-- Degree functions always yield monotone delineations AND the
    ordering is faithful. This characterizes exactly what degree
    semantics buys you within the delineation framework. -/
theorem degree_characterization {E D : Type*} [LinearOrder D]
    (μ : E → D) :
    IsMonotoneDelineation (measureDelineation μ) Set.univ ∧
    IsLinearDelineation (measureDelineation μ) ∧
    (∀ cc a b, a ∈ cc → b ∈ cc →
      (ordering (measureDelineation μ) cc a b ↔ μ b < μ a)) :=
  ⟨measureDelineation_monotone μ,
   measureDelineation_is_linear μ,
   fun cc a b ha hb => ordering_iff_degree μ cc a b ha hb⟩

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

The functoriality table for degree operators under change of scale
representation (a `StrictMono` map between scales — precisely the
`admissibleMeasure` condition, so an admissible measure IS a
scale-morphism): comparatives, equatives, and the max-quantified
comparative are invariant; the positive form transports only if the
threshold rides along. This derives the classic observation that
comparatives are context-independent while the positive form needs a
contextually fixed standard: *pos* is the one non-natural operator. The
point-standard comparatives and equatives are `Comparison.over_comp`.
Comparisons across two scales are natural only between universal degrees
(`Degree/UniversalScale`). -/

section TransportMax

variable {Entity D D' : Type*} [LinearOrder D] [LinearOrder D']
  {f : D → D'} {μ : Entity → D}

/-- The max-quantified comparative is invariant under change of scale
    representation. Not immediate: `thanDegrees` is a downset and images
    of downsets need not be downsets, but the greatest element rides
    along (`f δ` is greatest in the transported set, and conversely any
    greatest transported degree is `f` of a witness measure). -/
theorem maxComparative_comp (hf : StrictMono f)
    (Pmatrix Pthan : Entity → Prop) :
    maxComparative Pmatrix Pthan (f ∘ μ) ↔ maxComparative Pmatrix Pthan μ := by
  constructor
  · rintro ⟨δ', ⟨⟨x₀, hQ, hδx₀⟩, hub⟩, x, hP, hlt⟩
    have hx₀mem : f (μ x₀) ∈ thanDegrees Pthan (f ∘ μ) := ⟨x₀, hQ, le_rfl⟩
    have hδeq : δ' = f (μ x₀) := le_antisymm hδx₀ (hub hx₀mem)
    refine ⟨μ x₀, ⟨⟨x₀, hQ, le_rfl⟩, ?_⟩, x, hP, ?_⟩
    · rintro d ⟨y, hQy, hdy⟩
      have : f (μ y) ≤ δ' := hub ⟨y, hQy, le_rfl⟩
      exact hdy.trans (hf.le_iff_le.mp (hδeq ▸ this))
    · exact hf.lt_iff_lt.mp (hδeq ▸ hlt)
  · rintro ⟨δ, ⟨hδmem, hub⟩, x, hP, hlt⟩
    refine ⟨f δ, ⟨?_, ?_⟩, x, hP, hf hlt⟩
    · obtain ⟨y, hQy, hδy⟩ := hδmem
      exact ⟨y, hQy, hf.monotone hδy⟩
    · rintro d ⟨y, hQy, hdy⟩
      exact hdy.trans (hf.monotone (hub ⟨y, hQy, le_rfl⟩))

/-- The positive form transports only as a *pair*: rescaling the measure
    commutes with membership when the threshold is rescaled too. -/
theorem mem_ge_over_comp (hf : StrictMono f) (θ : D) (x : Entity) :
    x ∈ Degree.Comparison.ge.over (f ∘ μ) (f θ) ↔ x ∈ Degree.Comparison.ge.over μ θ :=
  hf.le_iff_le

/-- With a *fixed* threshold the positive form is not natural: some
    strictly monotone rescaling changes the verdict. The one non-natural
    operator in the table — the formal face of the positive form's
    context-dependence. -/
theorem positive_not_natural :
    ∃ f : ℚ → ℚ, StrictMono f ∧ ∃ (μ : ℚ → ℚ) (θ x : ℚ),
      x ∈ Degree.Comparison.ge.over μ θ ∧ x ∉ Degree.Comparison.ge.over (f ∘ μ) θ := by
  refine ⟨(· - 1), fun a b h => by simpa, id, 0, 0, ?_, ?_⟩ <;>
    simp [Degree.Comparison.mem_over, Degree.Comparison.rel]

end TransportMax

/-- Any φ-invariant map factors through `CresswellDegree φ`, so the quotient is the initial scale a
comparison relation determines. -/
theorem factors_through_cresswellDegree {E X : Type*} {φ : E → E → Prop}
    (g : E → X) (hg : ∀ a b, (cresswellSetoid φ).r a b → g a = g b) :
    ∃ ĝ : CresswellDegree φ → X, ĝ ∘ (Quotient.mk (cresswellSetoid φ)) = g :=
  ⟨Quotient.lift g hg, rfl⟩


end Degree
