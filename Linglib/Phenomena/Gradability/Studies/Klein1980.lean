import Linglib.Theories.Semantics.Comparison.Delineation
import Linglib.Phenomena.Gradability.Studies.Kamp1975

/-!
# Klein (1980): A Semantics for Positive and Comparative Adjectives
@cite{klein-1980}

*Linguistics and Philosophy* 4(1): 1–45.

## Overview

The foundational "degreeless" alternative to degree semantics. Gradable
adjectives are simple predicates (type `⟨e,t⟩`) whose extension is
determined relative to a **comparison class** — a contextually supplied
set of entities. The comparative is derived FROM the positive via
existential quantification over comparison classes, not the other way
around (contra Cresswell's degree theory).

## Core Contributions Formalized

1. **Nonlinear delineation** (§ 1): concrete witness showing that non-monotone
   delineations ("clever") produce cyclic orderings — the hallmark of
   nonlinear adjectives
2. **Monotone → not nonlinear** (§ 1): monotonicity excludes cyclic orderings
3. **Very as CC-narrower** (§ 2): `very A → A` for measure-induced
   delineations (by transitivity of `<`, not domain restriction)
4. **Klein's degree definition** (§ 3): degrees as equivalence classes under
   nondistinctness (eq 62), shown equivalent to measure equality
5. **Non-triviality condition** (§ 5): delineations must discriminate in
   any CC with ≥2 members
6. **Main theorem: strict weak order** (§ 6): under monotonicity, the ordering
   is asymmetric + negatively transitive — a strict weak order. Transitivity
   and almost-connectedness follow as corollaries.
7. **Kamp→Klein bridge** (§ 7): `kleinPreorder` = `kampPreorder` over Set.univ

The measure-induced delineation bridge (monotonicity, ordering↔degree
equivalence) lives in the theory layer: `Delineation.lean` §10.

## Connections

- **Theory layer**: `Theories/Semantics/Comparison/Delineation.lean`
  (comparison classes, ordering, monotonicity, very/fairly, less/as)
- **Kamp (1975)**: `Studies/Kamp1975.lean` §3 (Kamp→Klein lineage,
  `kampPreorder` = `kleinPreorder` over Set.univ)
- **Fine (1975)**: `Studies/Fine1975.lean` (supervaluation ↔ delineation duality)
- **Kennedy (2007)**: `Studies/Kennedy2007Licensing.lean` (degree-based alternative)
- **Hierarchy**: `Theories/Semantics/Comparison/Hierarchy.lean` (Klein ← Kennedy ← Measurement)
- **Bochnak (2015)**: `Studies/Bochnak2015.lean` — typological attestation that
  the Klein-style degree-free type ⟨e, t⟩ is realized by a natural language
  (Washo, Hokan), not just a notational alternative for English-style data.
-/

namespace Klein1980

open Semantics.Comparison.Delineation

-- ════════════════════════════════════════════════════
-- § 1. Nonlinear Delineation Witness
-- ════════════════════════════════════════════════════

/-! Klein's distinction between LINEAR and NONLINEAR adjectives
    (§2.2, §3.3): "tall" induces a total ordering (single criterion,
    monotone delineation), while "clever" can produce cycles (multiple
    criteria, non-monotone delineation).

    We construct a minimal witness: two entities whose "cleverness"
    depends on which criterion is salient, determined by which other
    entities are present in the comparison class. -/

inductive Clever2 | j | m  -- Jude, Mona

/-- A non-monotone delineation modeling "clever" with two conflicting
    criteria: j (Jude) is clever when m (Mona) is absent from the CC
    (math criterion dominates), m is clever when j is absent (social
    criterion dominates). When both are present, criteria conflict
    and neither is classified as clever. -/
def cleverDel : ComparisonClass Clever2 → Clever2 → Prop
  | C, .j => Clever2.m ∉ C
  | C, .m => Clever2.j ∉ C

/-- The clever delineation is nonlinear: both `j >_{cc} m` and
    `m >_{cc} j` hold for cc = {j, m}. This is Klein's key
    prediction for multi-criteria adjectives. -/
theorem clever_nonlinear :
    IsNonlinearDelineation cleverDel := by
  refine ⟨{Clever2.j, Clever2.m}, Clever2.j, Clever2.m, ?_, ?_⟩
  · -- j > m: take X = {j}. j is clever in {j} (m absent), m is not (j absent? no, j present)
    refine ⟨{Clever2.j}, Set.singleton_subset_iff.mpr (Set.mem_insert _ _), ?_, ?_⟩
    · show Clever2.m ∉ ({Clever2.j} : Set Clever2)
      simp [Set.mem_singleton_iff]
    · show ¬(Clever2.j ∉ ({Clever2.j} : Set Clever2))
      simp
  · -- m > j: take X = {m}
    refine ⟨{Clever2.m}, Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl), ?_, ?_⟩
    · show Clever2.j ∉ ({Clever2.m} : Set Clever2)
      simp [Set.mem_singleton_iff]
    · show ¬(Clever2.m ∉ ({Clever2.m} : Set Clever2))
      simp

/-- Monotone delineations cannot be nonlinear. This connects Klein's
    monotonicity constraint to the linear/nonlinear typology: requiring
    monotonicity is exactly what forces a total ordering. -/
theorem monotone_not_nonlinear {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (hmono : IsMonotoneDelineation delineation Set.univ)
    (hnn : IsNonlinearDelineation delineation) : False := by
  obtain ⟨_, u, u', ⟨X₁, _, hu₁, hnu'₁⟩, ⟨X₂, _, hu'₂, hnu₂⟩⟩ := hnn
  exact hnu₂ (hmono X₁ X₂ (Set.mem_univ _) (Set.mem_univ _) u u' hu₁ hnu'₁ hu'₂)

-- ════════════════════════════════════════════════════
-- § 2. Very as CC-Narrower: Concrete Bridge
-- ════════════════════════════════════════════════════

/-! Klein's `very` (eq 42) narrows the comparison class to the positive
    extension. Under the degree correspondence, this is equivalent to
    raising the threshold. We verify this for a measure-induced
    delineation: if x is very-tall, then x exceeds some entity that is
    ITSELF taller than some entity — a transitive chain witnessing a
    higher effective threshold.

    The entailment `very A → A` is proved in the theory layer
    (`Delineation.very_entails_base`). Here we show the converse fails:
    being tall does not entail being very tall. -/

/-- Very-tall does NOT entail tall-among-the-tall vacuously: there
    exist entities that are tall but not very tall. This is the
    "fairly tall" zone — tall relative to everyone, but not tall
    relative to the tall people. -/
theorem very_strictly_stronger :
    ∃ (E : Type) (del : ComparisonClass E → E → Prop)
      (C : ComparisonClass E) (x : E),
      del C x ∧ ¬ veryDelineation del C x := by
  refine ⟨Fin 3,
    fun C x => ∃ y ∈ C, (y : Fin 3) < x,
    Set.univ,
    (1 : Fin 3),
    ⟨0, Set.mem_univ _, by omega⟩,
    ?_⟩
  intro ⟨y, hy, hlt⟩
  simp only [Set.mem_setOf_eq] at hy
  obtain ⟨z, _, hlt_z⟩ := hy
  omega

-- ════════════════════════════════════════════════════
-- § 3. Very → Base for Measure-Induced Delineations
-- ════════════════════════════════════════════════════

/-! The theory-layer `very_entails_base` requires Klein's domain
    restriction (delineation only classifies CC members).
    Measure-induced delineations do NOT satisfy this restriction
    (entities outside C can be classified), but `very → base` holds
    anyway: if x exceeds some member of {tall people}, and that
    member exceeds some member of C, then by transitivity of `<`,
    x exceeds some member of C. -/

/-- `very A → A` for measure-induced delineations: the witness
    chain `z ∈ C, μ z < μ y, μ y < μ x` gives `μ z < μ x`. -/
theorem measureDelineation_very_entails_base {E D : Type*} [LinearOrder D]
    (μ : E → D) (C : ComparisonClass E) (x : E)
    (hv : veryDelineation (measureDelineation μ) C x) :
    measureDelineation μ C x := by
  obtain ⟨y, hy, hlt⟩ := hv
  obtain ⟨z, hz, hlt'⟩ := hy
  exact ⟨z, hz, lt_trans hlt' hlt⟩

-- ════════════════════════════════════════════════════
-- § 4. Klein's Degree Definition (§4.2, eq 62)
-- ════════════════════════════════════════════════════

/-! Klein §4.2 shows that degrees are DISPENSABLE but RECOVERABLE:
    the degree of u in c is the equivalence class of entities that
    are nondistinct from u. For linear adjectives (where nondistinct
    = equivalent), this yields: `degree(u) = {u' : u ≈_{c,ζ} u'}`.

    Degrees thus EMERGE from comparison classes rather than being
    primitive. Cresswell (1976) goes the other way: degrees are
    primitive and the comparative is defined in terms of them. Klein
    shows both directions are available: the delineation framework
    can reconstruct degrees whenever it needs them. -/

/-- Klein's degree of u at comparison class cc (eq 62):
    the set of entities nondistinct from u. For measure-induced
    delineations, this reduces to `{u' : μ(u') = μ(u)}` — the
    usual notion of "same degree". -/
def kleinDegree {E : Type*}
    (delineation : ComparisonClass E → E → Prop)
    (cc : ComparisonClass E) (u : E) : Set E :=
  {u' | nondistinct delineation cc u u'}

/-- Klein's degree agrees with measure equality: for measure-induced
    delineations, two entities have the same Klein degree iff they
    have the same measure value. -/
theorem kleinDegree_measureDelineation {E D : Type*} [LinearOrder D]
    (μ : E → D) (cc : ComparisonClass E) (a b : E)
    (ha : a ∈ cc) (hb : b ∈ cc) :
    b ∈ kleinDegree (measureDelineation μ) cc a ↔ μ a = μ b := by
  simp only [kleinDegree, Set.mem_setOf_eq, nondistinct, measureDelineation]
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- μ a < μ b: witness ∃ y ∈ {a,b}, μ y < μ b (y=a), derive ∃ y ∈ {a,b}, μ y < μ a
      have := (h {a, b} (by intro x hx; rcases hx with rfl | rfl <;> assumption)
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)).mpr ⟨a, Set.mem_insert _ _, hlt⟩
      obtain ⟨y, hy, hlt_y⟩ := this
      rcases hy with rfl | rfl
      · exact absurd hlt_y (lt_irrefl _)
      · exact absurd hlt_y (not_lt.mpr (le_of_lt hlt))
    · -- μ b < μ a: witness ∃ y ∈ {a,b}, μ y < μ a (y=b), derive ∃ y ∈ {a,b}, μ y < μ b
      have := (h {a, b} (by intro x hx; rcases hx with rfl | rfl <;> assumption)
        (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)).mp ⟨b, Set.mem_insert_of_mem _ rfl, hgt⟩
      obtain ⟨y, hy, hlt_y⟩ := this
      rcases hy with rfl | rfl
      · exact absurd hlt_y (not_lt.mpr (le_of_lt hgt))
      · exact absurd hlt_y (lt_irrefl _)
  · intro heq X _ _ _
    simp [heq]

-- ════════════════════════════════════════════════════
-- § 5. Non-Triviality Condition
-- ════════════════════════════════════════════════════

/-! Klein requires delineation functions to be **non-trivial**: for any
    comparison class with at least two members, the delineation must
    actually discriminate — some entities are positive and some are not.
    This prevents degenerate delineations where everything (or nothing)
    is in the positive extension. -/

/-- Klein's non-triviality: for any CC with ≥2 members, there exist
    entities that the delineation separates. -/
def IsNontrivialDelineation {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop) : Prop :=
  ∀ C : ComparisonClass Entity,
    (∃ a b : Entity, a ∈ C ∧ b ∈ C ∧ a ≠ b) →
    ∃ u v : Entity, u ∈ C ∧ v ∈ C ∧ delineation C u ∧ ¬ delineation C v

-- ════════════════════════════════════════════════════
-- § 6. Klein's Main Theorem: Strict Weak Order
-- ════════════════════════════════════════════════════

/-! Klein's central structural result: under monotonicity, the
    context-relative ordering is a **strict weak order** — asymmetric
    and negatively transitive. This is what licenses his claim that
    degrees are dispensable: monotone delineations induce the SAME
    ordering structure as degree scales, without positing degrees
    in the ontology.

    The two defining properties:
    - **Asymmetry** (from monotonicity): if u > v, then v ≯ u
    - **Negative transitivity** (unconditional): if u > w, then
      for any v, either u > v or v > w

    From these, all other strict weak order properties follow:
    - Transitivity (from asymmetry + negative transitivity)
    - Almost connected (incomparability → nondistinctness)
    - Nondistinctness is a partial equivalence relation -/

/-- Klein's main theorem: under monotonicity, the ordering is a strict
    weak order (asymmetric + negatively transitive). These two properties
    fully characterize the ordering structure of linear adjectives and
    justify the dispensability of degrees. -/
theorem klein_strict_weak_order {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (hmono : IsMonotoneDelineation delineation Set.univ)
    (cc : ComparisonClass Entity) :
    -- (i) Asymmetric
    (∀ u v, ordering delineation cc u v → ¬ ordering delineation cc v u) ∧
    -- (ii) Negatively transitive
    (∀ u v w, ordering delineation cc u w →
      ordering delineation cc u v ∨ ordering delineation cc v w) :=
  ⟨ordering_asymm delineation hmono cc,
   fun u v w => ordering_neg_trans delineation cc u v w⟩

/-- Transitivity as a corollary of the strict weak order properties:
    asymmetry + negative transitivity → transitivity. This shows the
    two properties in `klein_strict_weak_order` are sufficient. -/
theorem klein_transitivity_derived {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (hmono : IsMonotoneDelineation delineation Set.univ)
    (cc : ComparisonClass Entity) (u v w : Entity) :
    ordering delineation cc u v → ordering delineation cc v w →
    ordering delineation cc u w := by
  intro huv hvw
  -- Apply negative transitivity on v > w with u as the middle entity:
  -- gives v > u ∨ u > w
  rcases ordering_neg_trans delineation cc v u w hvw with h | h
  · exact absurd h (ordering_asymm delineation hmono cc u v huv)
  · exact h

/-- Almost connected: incomparable entities are nondistinct. Combined
    with `klein_strict_weak_order`, this shows every pair of entities
    in a comparison class falls into one of three exclusive categories:
    u > v, v > u, or u ≈ v. -/
theorem klein_almost_connected {Entity : Type*}
    (delineation : ComparisonClass Entity → Entity → Prop)
    (cc : ComparisonClass Entity) (u v : Entity) :
    ordering delineation cc u v ∨
    ordering delineation cc v u ∨
    nondistinct delineation cc u v := by
  by_cases h1 : ordering delineation cc u v
  · exact Or.inl h1
  · by_cases h2 : ordering delineation cc v u
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (nondistinct_of_incomparable delineation cc u v h1 h2))

-- ════════════════════════════════════════════════════
-- § 7. Bridge: kleinPreorder = kampPreorder (over Set.univ)
-- ════════════════════════════════════════════════════

/-! Klein's `as...as` (§5.3) and Kamp's `at least as` (definition 12)
    are the SAME relation stated in different vocabularies:

    - Kamp: `∀ completions c ∈ S, ext(c)(u') → ext(c)(u)`
    - Klein: `∀ comparison classes C, tall(u', C) → tall(u, C)`

    Completions = comparison classes; both quantify universally over
    ways of making the predicate precise. When S = Set.univ, the two
    preorders coincide. -/

/-- Klein's preorder is exactly Kamp's preorder (over all completions)
    when both use the same extension function. -/
theorem kleinPreorder_eq_kampPreorder {E : Type*}
    (delineation : ComparisonClass E → E → Prop)
    [∀ C (x : E), Decidable (delineation C x)] (u u' : E) :
    (kleinPreorder delineation).le u u' ↔
    (Kamp1975.kampPreorder (fun C x => decide (delineation C x)) Set.univ).le u u' := by
  constructor
  · intro h c _ hext
    exact decide_eq_true_eq.mpr (h c (decide_eq_true_eq.mp hext))
  · intro h c hd
    exact decide_eq_true_eq.mp (h c (Set.mem_univ _) (decide_eq_true_eq.mpr hd))

end Klein1980
