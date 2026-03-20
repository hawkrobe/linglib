import Linglib.Theories.Semantics.Comparison.Delineation
import Linglib.Theories.Semantics.Probabilistic.Measurement.Basic

/-!
# Degree Semantics Hierarchy
@cite{klein-1980} @cite{kennedy-2007} @cite{scontras-2014} @cite{bale-schwarz-2022}

Three frameworks for gradable predicate semantics form a strict
subsumption hierarchy:

```
Klein (Delineation)          — most general
  ↑ measureDelineation
Kennedy (Degree)             — specialization: single linear scale
  ↑ MeasureFn.toHasDegree
Scontras / Bale & Schwarz (Measurement) — specialization: typed dimension
```

Each arrow is an embedding: the lower framework's predictions are a
special case of the higher framework's. The hierarchy is **strict**:
delineation can express nonlinear adjectives ("clever") that no degree
function can induce.

## What each framework adds

| Framework   | Ontology       | Comparative           | Unique capacity        |
|-------------|----------------|-----------------------|------------------------|
| Klein       | No degrees     | ∃C. A(x,C) ∧ ¬A(y,C)| Nonlinear adjectives   |
| Kennedy     | Degrees (D,≤)  | μ(x) > μ(y)          | Measure phrases, DegP  |
| Measurement | Degrees + dim  | μ_d(x) > μ_d(y)      | Typed dimensions, CARD |

## Theorems in this file

1. **measure_to_degree**: every `MeasureFn` induces a `HasDegree` instance
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

namespace Semantics.Comparison.Hierarchy

open Semantics.Comparison.Delineation
open Semantics.Probabilistic.Measurement (MeasureFn Dimension)
open Core.Scale (HasDegree)

-- ════════════════════════════════════════════════════
-- § 1. Measurement → Degree
-- ════════════════════════════════════════════════════

/-! A `MeasureFn E` carries a typed dimension (mass, volume, cardinality, ...)
    and a non-negative measure `apply : E → ℚ`. Forgetting the dimension and
    non-negativity constraint yields a `HasDegree E` instance: the degree of
    an entity is its measure value.

    This is @cite{scontras-2014}'s key insight: measure terms (kilo, liter)
    and CARD are all instances of the same degree-assigning operation. -/

/-- Every measure function induces a degree assignment.
    This is `MeasureFn.toHasDegree` — restated here for the hierarchy. -/
def measure_to_degree {E : Type} (μ : MeasureFn E) : HasDegree E :=
  μ.toHasDegree

-- ════════════════════════════════════════════════════
-- § 2. Degree → Delineation
-- ════════════════════════════════════════════════════

/-! Any degree function `μ : E → D` over a linear order induces a Klein
    delineation via `measureDelineation`: entity x is "A-in-C" iff x
    strictly exceeds some member of C on μ. This is the embedding from
    @cite{kennedy-2007}'s degree semantics into @cite{klein-1980}'s
    delineation framework.

    The embedding is **faithful**: Klein's ordering under the induced
    delineation exactly matches degree comparison (`ordering_iff_degree`).
    No information is lost in the translation. -/

/-- Every degree function induces a Klein delineation. -/
def degree_to_delineation {E D : Type*} [LinearOrder D]
    (μ : E → D) : ComparisonClass E → E → Prop :=
  measureDelineation μ

/-- The full chain: measure function → delineation (composing the two steps). -/
def measure_to_delineation {E : Type} (μ : MeasureFn E) :
    ComparisonClass E → E → Prop :=
  measureDelineation μ.apply

-- ════════════════════════════════════════════════════
-- § 3. Faithfulness of the Embedding
-- ════════════════════════════════════════════════════

/-- The degree→delineation embedding is faithful: Klein's ordering
    under the induced delineation exactly matches degree comparison.
    This justifies Klein's claim (§4.2) that degrees are dispensable
    — and simultaneously justifies Kennedy's claim that degree
    semantics loses nothing over delineation for linear adjectives. -/
theorem ordering_faithful {E D : Type*} [LinearOrder D]
    (μ : E → D) (cc : ComparisonClass E) (a b : E)
    (ha : a ∈ cc) (hb : b ∈ cc) :
    ordering (degree_to_delineation μ) cc a b ↔ μ b < μ a :=
  ordering_iff_degree μ cc a b ha hb

/-- Every degree-induced delineation is monotone. -/
theorem degree_delineation_monotone {E D : Type*} [LinearOrder D]
    (μ : E → D) :
    IsMonotoneDelineation (degree_to_delineation μ) Set.univ :=
  measureDelineation_monotone μ

/-- Every degree-induced delineation is linear: for any two entities in
    a comparison class, either one ranks above the other or they are
    nondistinct (equal degree). -/
theorem degree_delineations_are_linear {E D : Type*} [LinearOrder D]
    (μ : E → D) :
    IsLinearDelineation (degree_to_delineation μ) :=
  measureDelineation_is_linear μ

-- ════════════════════════════════════════════════════
-- § 4. Strict Separation: Delineation > Degree
-- ════════════════════════════════════════════════════

/-! Klein's delineation framework is STRICTLY more general than degree
    semantics. The key witness: **nonlinear adjectives** like "clever"
    produce cyclic orderings (both a > b and b > a for different
    comparison classes). This is impossible for any degree-induced
    delineation, since degree orderings are asymmetric.

    See `Phenomena/Gradability/Studies/Klein1980.lean` for the empirical
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
    (§ 2–3 above).

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

-- ════════════════════════════════════════════════════
-- § 5. Degree = Monotone Delineation (Characterization)
-- ════════════════════════════════════════════════════

/-! The degree-based frameworks correspond EXACTLY to the monotone
    fragment of Klein's delineation theory. This is not a coincidence:
    monotonicity is what ensures a delineation induces a well-behaved
    ordering (strict weak order), which is exactly what a degree scale
    provides.

    - Forward: degree → monotone delineation (§ 2, `degree_delineation_monotone`)
    - Backward: monotone delineation → degree-recoverable (@cite{klein-1980} §4.2,
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

-- ════════════════════════════════════════════════════
-- § 6. Measurement = Degree + Dimension Typing
-- ════════════════════════════════════════════════════

/-! The relationship between measurement semantics (@cite{scontras-2014},
    @cite{bale-schwarz-2022}) and degree semantics (@cite{kennedy-2007})
    is simple: measurement adds typed dimensions to degree functions.

    A `MeasureFn E` is a degree function `apply : E → ℚ` PLUS a
    `dimension : Dimension` label. The degree function is recoverable
    via `MeasureFn.toHasDegree`, but the dimension label is lost.

    What dimension typing buys you:
    - Multiple measure functions per entity (weight AND volume AND count)
    - The No Division Hypothesis: compositional operations respect dimension types
    - Measure term semantics: ⟦kilo⟧ = λn.λx. μ_kg(x) = n, typed to mass

    What it does NOT buy you: any new ordering structure. Measurement
    adjectives are still degree adjectives under the hood. -/

/-- Measurement semantics is a refinement of degree semantics:
    every measure function has an underlying degree function. -/
theorem measurement_refines_degree :
    ∀ (E : Type) (μ : MeasureFn E),
      ∃ (deg : E → ℚ), deg = μ.apply :=
  fun _ μ => ⟨μ.apply, rfl⟩

/-- Measurement additionally provides non-negativity, which degree
    semantics does not require. -/
theorem measurement_nonneg {E : Type*} (μ : MeasureFn E) (x : E) :
    μ.apply x ≥ 0 := μ.nonneg x

/-- The full chain from measurement to delineation preserves
    ordering faithfully. -/
theorem measurement_to_delineation_faithful {E : Type}
    (μ : MeasureFn E) (cc : ComparisonClass E) (a b : E)
    (ha : a ∈ cc) (hb : b ∈ cc) :
    ordering (measure_to_delineation μ) cc a b ↔ μ.apply b < μ.apply a :=
  ordering_iff_degree μ.apply cc a b ha hb

-- ════════════════════════════════════════════════════
-- § 7. Impossibility: Nonlinear ≠ Degree-Representable
-- ════════════════════════════════════════════════════

/-! The strict separation theorem (§ 4) shows that nonlinear delineations
    exist. This section strengthens the result: the specific nonlinear
    witness `nlDel` is NOT representable by ANY degree function. This is
    the definitive impossibility result: no choice of degree type or
    measure function can produce the extension pattern of a multi-criteria
    adjective like "clever."

    The proof is by contradiction: if `nlDel` agreed extensionally with
    some `measureDelineation μ`, then monotonicity of `measureDelineation μ`
    would transfer to `nlDel`, contradicting its nonlinearity. -/

/-- Transfer monotonicity across extensionally equivalent delineations. -/
private theorem mono_transfer {E : Type*}
    (del₁ del₂ : ComparisonClass E → E → Prop)
    (h : ∀ C x, del₁ C x ↔ del₂ C x)
    (hmono : IsMonotoneDelineation del₂ Set.univ) :
    IsMonotoneDelineation del₁ Set.univ := by
  intro C₁ C₂ hC₁ hC₂ a b ha hnb hb
  exact (h C₂ a).mpr (hmono C₁ C₂ hC₁ hC₂ a b
    ((h C₁ a).mp ha) (fun h' => hnb ((h C₁ b).mpr h')) ((h C₂ b).mp hb))

/-- The nonlinear witness `nlDel` cannot be represented by any degree
    function over any linearly ordered degree type. No matter what
    degrees you assign to j and m, you cannot reproduce the extension
    pattern where j is "clever" in {j} and m is "clever" in {m}.

    This is the strongest form of the separation: not just "some
    delineations are nonlinear" but "this specific delineation is
    provably outside the degree-representable fragment." -/
theorem nlDel_not_degree_representable :
    ¬∃ (D : Type) (_ : LinearOrder D) (μ : NL2 → D),
      ∀ C x, nlDel C x ↔ measureDelineation μ C x := by
  intro ⟨_, _, μ, h⟩
  exact monotone_excludes_nonlinear nlDel
    (mono_transfer nlDel (measureDelineation μ) h (measureDelineation_monotone μ))
    nonlinear_delineation_exists

-- ════════════════════════════════════════════════════
-- § 8. Nondistinctness = Equal Degree
-- ════════════════════════════════════════════════════

/-! @cite{klein-1980} §4.2 defines degrees as equivalence classes under
    nondistinctness: `degree(u) = {u' : u ≈ u'}`. For measure-induced
    delineations, this collapses to measure equality: two entities are
    nondistinct iff they have the same degree.

    This theorem bridges Klein's degree-free framework with Kennedy's
    degree-based framework at the level of equivalence classes: Klein's
    emergent "degrees" ARE Kennedy's degrees, when the delineation
    happens to be measure-induced. -/

/-- Nondistinctness under a measure-induced delineation = equal measure.
    This is Klein's §4.2 insight formalized: degrees are dispensable
    because they are recoverable as nondistinctness classes.

    Forward: if μ(a) = μ(b), then no comparison class can distinguish them.
    Backward: if μ(a) ≠ μ(b), the two-element class {a,b} distinguishes them. -/
theorem nondistinct_iff_equal_measure {E D : Type*} [LinearOrder D]
    (μ : E → D) (cc : ComparisonClass E) (a b : E)
    (ha : a ∈ cc) (hb : b ∈ cc) :
    nondistinct (measureDelineation μ) cc a b ↔ μ a = μ b := by
  constructor
  · intro hnd
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- μ a < μ b: {a,b} separates b from a
      have hmem : ∀ x, x ∈ ({a, b} : Set E) → x ∈ cc := by
        intro x hx; rcases hx with rfl | rfl <;> assumption
      have hbpos : measureDelineation μ {a, b} b := ⟨a, Set.mem_insert _ _, hlt⟩
      have hapos := (hnd {a, b} (fun x hx => hmem x hx)
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)).mpr hbpos
      obtain ⟨y, hy, hlt_y⟩ := hapos
      rcases hy with rfl | rfl
      · exact absurd hlt_y (lt_irrefl _)
      · exact absurd (lt_trans hlt hlt_y) (lt_irrefl _)
    · -- μ b < μ a: {a,b} separates a from b
      have hmem : ∀ x, x ∈ ({a, b} : Set E) → x ∈ cc := by
        intro x hx; rcases hx with rfl | rfl <;> assumption
      have hapos : measureDelineation μ {a, b} a := ⟨b, Set.mem_insert_of_mem _ rfl, hgt⟩
      have hbpos := (hnd {a, b} (fun x hx => hmem x hx)
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)).mp hapos
      obtain ⟨y, hy, hlt_y⟩ := hbpos
      rcases hy with rfl | rfl
      · exact absurd (lt_trans hgt hlt_y) (lt_irrefl _)
      · exact absurd hlt_y (lt_irrefl _)
  · intro heq X _ _ _
    simp only [measureDelineation, heq]

-- ════════════════════════════════════════════════════
-- § 9. Strict Weak Order for Degree Delineations
-- ════════════════════════════════════════════════════

/-! Under a degree-induced delineation, Klein's ordering is a **strict
    weak order**: asymmetric and negatively transitive. These two
    properties fully characterize the ordering structure of linear
    adjectives and justify the dispensability of degrees.

    Asymmetry requires monotonicity (which degree delineations have).
    Negative transitivity holds unconditionally. Together they give
    transitivity and almost-connectedness as corollaries. -/

/-- The ordering under a degree delineation is a strict weak order. -/
theorem degree_delineation_strict_weak_order {E D : Type*} [LinearOrder D]
    (μ : E → D) (cc : ComparisonClass E) :
    -- (i) Asymmetric
    (∀ u v, ordering (measureDelineation μ) cc u v →
      ¬ordering (measureDelineation μ) cc v u) ∧
    -- (ii) Negatively transitive
    (∀ u v w, ordering (measureDelineation μ) cc u w →
      ordering (measureDelineation μ) cc u v ∨
      ordering (measureDelineation μ) cc v w) :=
  ⟨ordering_asymm (measureDelineation μ) (measureDelineation_monotone μ) cc,
   fun u v w => ordering_neg_trans (measureDelineation μ) cc u v w⟩

/-- Transitivity of degree-induced ordering (corollary of strict weak order). -/
theorem degree_ordering_trans {E D : Type*} [LinearOrder D]
    (μ : E → D) (cc : ComparisonClass E) (u v w : E) :
    ordering (measureDelineation μ) cc u v →
    ordering (measureDelineation μ) cc v w →
    ordering (measureDelineation μ) cc u w := by
  intro huv hvw
  rcases ordering_neg_trans (measureDelineation μ) cc v u w hvw with h | h
  · exact absurd h (ordering_asymm _ (measureDelineation_monotone μ) cc u v huv)
  · exact h

-- ════════════════════════════════════════════════════
-- § 10. Very = Threshold Chain (Degree Correspondence)
-- ════════════════════════════════════════════════════

/-! Klein's `very` (§4.1, eq 42) narrows the comparison class to the
    positive extension. Under a degree-induced delineation, this
    corresponds to raising the effective degree threshold: being "very
    tall" requires exceeding someone who is themselves tall — a
    transitive chain of strict degree comparisons.

    Formally: `veryDelineation (measureDelineation μ) C x` iff there
    exist y, z such that z ∈ C, μ(z) < μ(y), and μ(y) < μ(x). The
    "very" threshold is the minimum degree among entities in C that
    themselves exceed some C-member. -/

/-- Very under a degree delineation requires a two-step chain:
    x exceeds y, which itself exceeds some member z of C. -/
theorem very_degree_chain {E D : Type*} [LinearOrder D]
    (μ : E → D) (C : ComparisonClass E) (x : E) :
    veryDelineation (measureDelineation μ) C x ↔
    ∃ y, (∃ z ∈ C, μ z < μ y) ∧ μ y < μ x := by
  simp only [veryDelineation, measureDelineation, Set.mem_setOf_eq]

/-- Very entails the base predicate for degree delineations:
    if x exceeds someone who exceeds a C-member, then x exceeds
    a C-member (by transitivity of <). -/
theorem very_entails_base_degree {E D : Type*} [LinearOrder D]
    (μ : E → D) (C : ComparisonClass E) (x : E)
    (hv : veryDelineation (measureDelineation μ) C x) :
    measureDelineation μ C x := by
  obtain ⟨_, ⟨z, hz, hlt₁⟩, hlt₂⟩ := hv
  exact ⟨z, hz, lt_trans hlt₁ hlt₂⟩

/-- Very is strictly stronger than the base: there exist entities
    that are "tall" but not "very tall." This is the "fairly tall"
    zone — entities just above the basic threshold but below the
    very-threshold. -/
theorem very_strictly_stronger_degree :
    ∃ (E D : Type) (_ : LinearOrder D) (μ : E → D)
      (C : ComparisonClass E) (x : E),
      measureDelineation μ C x ∧
      ¬veryDelineation (measureDelineation μ) C x := by
  -- Three natural numbers {0, 1, 2}. Entity 1 is "tall" (exceeds 0)
  -- but not "very tall" (no tall entity that 1 exceeds).
  refine ⟨ℕ, ℕ, inferInstance, id, {0, 1, 2}, 1,
    ⟨⟨0, Set.mem_insert _ _, by show id 0 < id 1; decide⟩, ?_⟩⟩
  intro ⟨y, ⟨z, _, hlt_z⟩, hlt_y⟩
  simp only [id] at hlt_z hlt_y
  omega

end Semantics.Comparison.Hierarchy
