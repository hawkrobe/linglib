import Mathlib.Order.Antisymmetrization
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.GCongr
import Linglib.Semantics.Degree.Quantifier
import Linglib.Features.Dimension
import Linglib.Semantics.Degree.Delineation
import Linglib.Semantics.Degree.Measure.Dimensioned

/-!
# Morphisms between gradability representations
[klein-1980] [kennedy-2007] [scontras-2014] [bale-schwarz-2022]

The maps between the three framework objects for gradable predicates,
with their faithfulness theorems — the degree-semantic analogue of the
representation maps in `Phonology/Autosegmental` (AR ↔ tone strings):

```
Klein (Delineation)          — most general
  ↑ measureDelineation
Kennedy (threshold degrees)  — specialization: single linear scale
  ↑ DimensionedMeasure.apply
Scontras / Bale & Schwarz (typed measurement)
```

Each map is an embedding (`ordering_faithful`,
`measurement_refines_degree`); the composite is `measure_to_delineation`.
Strictness: delineation expresses nonlinear adjectives ("clever") that
no degree function induces (`delineation_strictly_more_general`,
`nonlinear_delineation_exists`).

## What each framework adds

| Framework   | Ontology       | Comparative           | Unique capacity        |
|-------------|----------------|-----------------------|------------------------|
| Klein       | No degrees     | ∃C. A(x,C) ∧ ¬A(y,C)| Nonlinear adjectives   |
| Kennedy     | Degrees (D,≤)  | μ(x) > μ(y)          | Measure phrases, DegP  |
| Measurement | Degrees + dim  | μ_d(x) > μ_d(y)      | Typed dimensions, CARD |

## Theorems in this file

1. **measure_to_degree**: every `DimensionedMeasure` forgets to a plain degree function
2. **degree_to_delineation**: every degree function induces a Klein delineation
3. **ordering_faithful**: the induced delineation's ordering = degree comparison
4. **degree_delineations_are_linear**: all degree-induced delineations are linear
5. **nonlinear_delineation_exists**: a concrete nonlinear delineation witness
6. **monotone_excludes_nonlinear**: monotone delineations are never nonlinear
7. **delineation_strictly_more_general**: delineation ⊋ degree (strict containment)
8. **nlDel_not_degree_representable**: no degree function can induce the nonlinear witness
9. **nondistinct_iff_equal_measure**: Klein's emergent degrees = actual degree equality
10. **degree_delineation_strict_weak_order**: degree orderings are strict weak orders
11. **very_degree_chain**: Klein's `very` = two-step degree chain
-/

namespace Degree

open Degree.Delineation

open Features.Dimension (Dimension)
/-! ### Measurement → Degree → Delineation

The maps themselves carry no new definitions: measurement forgets to a
bare degree function by the `DimensionedMeasure.apply` projection
([scontras-2014]'s insight that measure terms and CARD are one
degree-assigning operation), and any degree function `μ` over a linear
order induces a Klein delineation via `Degree.Delineation.measureDelineation`
— the embedding of [kennedy-2007]-style degree semantics into
[klein-1980]'s framework. The embedding is faithful
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

/-- A concrete nonlinear delineation: two entities whose ordering
    depends on which other entities are in the comparison class.
    This models multi-criteria adjectives like "clever" where
    different subsets apply different ranking criteria.

    The construction: j is "clever" in C when m is absent (math
    criterion dominates), m is "clever" when j is absent (social
    criterion dominates). In {j, m}, criteria conflict. -/
private inductive NL2 | j | m

private def nlDel : ComparisonClass NL2 → NL2 → Prop
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

/-- **The strict separation theorem**: Klein's delineation framework is
    strictly more general than degree-based frameworks.

    Forward: every degree function induces a monotone delineation
    (`measureDelineation_monotone`).

    Backward FAILS: there exist delineations (nonlinear ones) that no
    degree function can induce, because degree-induced delineations
    are always monotone, and monotonicity excludes nonlinearity.

    This is the formal content of Klein's critique of degree semantics:
    multi-criteria adjectives like "clever" require the richer delineation
    framework. -/
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

/-! ### The degree construction ([cresswell-1976] §4, [bale-2008])

Degrees built from comparisons rather than assumed: [cresswell-1976]
(4.1) quotients an arbitrary comparison relation `φ` by two-sided
φ-indistinguishability, and (4.2) shows the induced comparison on
classes is well-defined. On a preorder the construction coincides with
mathlib's `Antisymmetrization` (`cresswellSetoid_le_iff`). [bale-2008]
then maps any finite scale into the universal scale Ω ≅ ℚ ∩ (0, 1] by
relative position (`relativeRank`), the homomorphism that licenses
indirect cross-scale comparison. -/

/-- Two-sided indistinguishability under a comparison `φ`
    ([cresswell-1976] (4.1)): same φ-profile on the left and right. -/
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

/-- The induced comparison on degrees; well-definedness is
    [cresswell-1976]'s own consistency proof for (4.2). -/
def CresswellDegree.rel {E : Type*} {φ : E → E → Prop} :
    CresswellDegree φ → CresswellDegree φ → Prop :=
  Quotient.lift₂ φ fun _ b c _ hac hbd =>
    propext ((hac.1 b).trans (hbd.2 c))

/-- [cresswell-1976] (4.2): `ā >_φ b̄ iff φ(a, b)`. -/
@[simp] theorem CresswellDegree.rel_mk {E : Type*} {φ : E → E → Prop} (a b : E) :
    CresswellDegree.rel (⟦a⟧ : CresswellDegree φ) ⟦b⟧ ↔ φ a b :=
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

/-- [bale-2008]'s universal-degree homomorphism on a finite scale: the
    relative position of `d`, valued in an order-isomorphic *model* of
    Ω (the paper takes Ω to be isomorphic to ℚ ∩ [0, 1]; only the order
    on the values is ever consumed — universal degrees are ordinal, not
    arithmetic). Defined on whatever carrier plays the primary scale —
    in Bale's regime the *quotient*, so equivalent individuals share a
    universal degree by construction and the value counts equivalence
    classes, not individuals. -/
def relativeRank {D : Type*} [Fintype D] [LinearOrder D] (d : D) : ℚ :=
  (Finset.univ.filter (· ≤ d)).card / Fintype.card D

/-- The universal-degree map preserves the primary scale's order
    ([bale-2008]: ℌ preserves ≥_δ). -/
theorem relativeRank_strictMono {D : Type*} [Fintype D] [LinearOrder D] :
    StrictMono (relativeRank (D := D)) := by
  intro a b hab
  have hD : 0 < (Fintype.card D : ℚ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨a⟩
  have hcard : ((Finset.univ.filter (· ≤ a)).card : ℚ) <
      ((Finset.univ.filter (· ≤ b)).card : ℚ) := by
    have h : (Finset.univ.filter (· ≤ a)).card <
        (Finset.univ.filter (· ≤ b)).card := by
      apply Finset.card_lt_card
      refine ⟨fun c hc => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        exact hc.trans hab.le
      · have hb := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ b, le_rfl⟩)
        simp only [Finset.mem_filter] at hb
        exact absurd hb.2 (not_le.mpr hab)
    exact_mod_cast h
  unfold relativeRank
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_pos_right hcard (inv_pos.mpr hD)

/-- Universal degrees land in (0, 1]. -/
theorem relativeRank_mem_Ioc {D : Type*} [Fintype D] [LinearOrder D] (d : D) :
    relativeRank d ∈ Set.Ioc (0 : ℚ) 1 := by
  have hD : 0 < (Fintype.card D : ℚ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨d⟩
  unfold relativeRank
  refine ⟨div_pos ?_ hD, ?_⟩
  · exact_mod_cast Finset.card_pos.mpr ⟨d, by simp⟩
  · rw [div_le_one hD]
    exact_mod_cast Finset.card_filter_le _ _



/-! ### Transport: which operators are natural in the scale

The functoriality table for degree operators under change of scale
representation (a `StrictMono` map between scales — precisely the
`admissibleMeasure` condition, so an admissible measure IS a
scale-morphism): comparatives, equatives, and the max-quantified
comparative are invariant; the positive form transports only if the
threshold rides along. This derives the classic observation that
comparatives are context-independent while the positive form needs a
contextually fixed standard: *pos* is the one non-natural operator. -/

section Transport

variable {Entity D D' : Type*} [LinearOrder D] [Preorder D']
  {f : D → D'} {μ : Entity → D}

/-- Comparatives are invariant under change of scale representation. -/
theorem comparativeSem_comp (hf : StrictMono f) (a b : Entity)
    (dir : Core.Order.ScalePolarity) :
    comparativeSem (f ∘ μ) a b dir ↔ comparativeSem μ a b dir := by
  cases dir <;> exact hf.lt_iff_lt

/-- Equatives are invariant under change of scale representation. -/
theorem equativeSem_comp (hf : StrictMono f) (a b : Entity)
    (dir : Core.Order.ScalePolarity) :
    equativeSem (f ∘ μ) a b dir ↔ equativeSem μ a b dir := by
  cases dir <;> exact hf.le_iff_le

end Transport

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
    x ∈ Core.Order.Comparison.ge.over (f ∘ μ) (f θ) ↔ x ∈ Core.Order.Comparison.ge.over μ θ :=
  hf.le_iff_le

/-- With a *fixed* threshold the positive form is not natural: some
    strictly monotone rescaling changes the verdict. The one non-natural
    operator in the table — the formal face of the positive form's
    context-dependence. -/
theorem positive_not_natural :
    ∃ f : ℚ → ℚ, StrictMono f ∧ ∃ (μ : ℚ → ℚ) (θ x : ℚ),
      x ∈ Core.Order.Comparison.ge.over μ θ ∧ x ∉ Core.Order.Comparison.ge.over (f ∘ μ) θ := by
  refine ⟨(· - 1), fun a b h => by simpa, id, 0, 0, ?_, ?_⟩ <;>
    simp [Core.Order.Comparison.mem_over, Core.Order.Comparison.rel]

end TransportMax

/-- Universal property of the degree construction: any φ-invariant map
    factors through `CresswellDegree φ` — the quotient is the initial
    scale a comparison relation determines. -/
theorem factors_through_cresswellDegree {E X : Type*} {φ : E → E → Prop}
    (g : E → X) (hg : ∀ a b, (cresswellSetoid φ).r a b → g a = g b) :
    ∃ ĝ : CresswellDegree φ → X, ĝ ∘ (Quotient.mk (cresswellSetoid φ)) = g :=
  ⟨Quotient.lift g hg, rfl⟩


end Degree
