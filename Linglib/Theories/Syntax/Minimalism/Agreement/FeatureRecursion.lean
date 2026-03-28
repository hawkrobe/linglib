import Linglib.Core.Number
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.UpperLower.Basic

/-!
# Feature Recursion
@cite{harbour-2016}

@cite{harbour-2016} Ch 6: extended number categories beyond the base three
(singular, dual, plural) arise from **feature recursion** — reapplying
[±minimal] to sublattice regions of the base [±atomic, ±minimal] partition.

## The Mechanism

The base partition divides the lattice of individual sums into three regions:
- **Singular** [+atomic, +minimal]: atoms (singletons)
- **Dual** [−atomic, +minimal]: minimal non-atoms (pairs)
- **Plural** [−atomic, −minimal]: non-minimal non-atoms (groups of 3+)

Feature recursion reapplies [±minimal] to a non-singleton region, splitting
it in two. This operation is constrained:
- Only [±minimal] can recurse (not [±atomic])
- The target region must have non-trivial lattice structure — atoms are
  singletons and cannot be further partitioned

## Derived Categories

Recursion on **plural** (the [−atomic, −minimal] region) yields:
- **Trial** [+minimalR]: the minimal elements of the plural region
  (groups of exactly 3)
- **Greater plural** [−minimalR]: non-minimal plurals (groups of 4+)

Recursion on **non-singular** (the [−atomic] region, before the base
[±minimal] split) yields:
- **Unit augmented** [+minimalR]: the minimal non-singulars (pairs)
- **Augmented** [−minimalR]: non-minimal non-singulars (groups of 3+)

## Implicational Universals as a Lower Set

The implicational universals (trial → dual → plural → singular, etc.) are
not stipulated — they are a theorem of the feature geometry. The generated
categories form a **lower set** in the markedness partial order on
`Category`: if a marked category is generated, all less-marked categories
it presupposes are also generated (§ 8).

This is a lattice-theoretic property: the partial order on categories is
the presupposition ordering, and the `IsLowerSet` formulation (Mathlib)
captures all implicational universals in a single statement.

-/

namespace Theories.Syntax.Minimalism.Agreement.FeatureRecursion

open Core.Number

-- ============================================================================
-- § 1: Recursion Regions
-- ============================================================================

/-- A region of the number lattice eligible for recursion.

    Only non-atomic ([−atomic]) regions have internal lattice structure
    that supports a meaningful [±minimal] split. Atoms are singletons
    and cannot be further partitioned. -/
structure Region where
  /-- The base number features defining this region. -/
  base : Features
  /-- The base features must be well-formed. -/
  base_wf : base.wellFormed = true
  /-- The region must be non-atomic: atoms cannot be recursed. -/
  base_nonatomic : base.isAtomic = false
  deriving DecidableEq

/-- The plural region: [−atomic, −minimal]. Groups of 3 or more. -/
def pluralRegion : Region := ⟨pluralF, rfl, rfl⟩

/-- The non-singular (dual) region: [−atomic, +minimal]. Minimal
    non-atoms (pairs). -/
def dualRegion : Region := ⟨dualF, rfl, rfl⟩

-- ============================================================================
-- § 2: Recursive Number Categories
-- ============================================================================

/-- A recursive number category: one application of [±minimal] within
    a base region.

    @cite{harbour-2016} Ch 6: reapplying [±minimal] to a sublattice
    region splits it into a minimal and non-minimal subregion, yielding
    two new number categories from one base category. -/
structure RecursiveNumber where
  /-- The target region for recursion. -/
  region : Region
  /-- [±minimal] within the target region. -/
  isMinimalInRegion : Bool
  deriving DecidableEq

/-- Trial: minimal element of the plural region.
    The smallest groups of 3+ = groups of exactly 3. -/
def trial : RecursiveNumber := ⟨pluralRegion, true⟩

/-- Greater plural: non-minimal element of the plural region.
    Groups of 4+. -/
def greaterPlural : RecursiveNumber := ⟨pluralRegion, false⟩

/-- Unit augmented: minimal element of the non-singular region.
    The smallest non-singulars = pairs. -/
def unitAugmented : RecursiveNumber := ⟨dualRegion, true⟩

/-- Augmented: non-minimal element of the non-singular region.
    Non-singulars that are not minimal = groups of 3+. -/
def augmented : RecursiveNumber := ⟨dualRegion, false⟩

-- ============================================================================
-- § 3: Mapping to Corbett Categories
-- ============================================================================

/-- Map recursive features to @cite{corbett-2000}'s number categories. -/
def RecursiveNumber.toCategory (r : RecursiveNumber) : Category :=
  if r.region.base.isMinimal then
    -- Recursion on the non-singular ([−atomic, +minimal]) region
    if r.isMinimalInRegion then .dual else .plural
  else
    -- Recursion on the plural ([−atomic, −minimal]) region
    if r.isMinimalInRegion then .trial else .greaterPlural

theorem trial_toCategory : trial.toCategory = .trial := rfl
theorem greaterPlural_toCategory : greaterPlural.toCategory = .greaterPlural := rfl

-- ============================================================================
-- § 4: Impossibility of Singular Recursion
-- ============================================================================

/-- Recursion on singular is impossible: [+atomic] regions cannot be
    further partitioned because they're singletons.

    This explains why no language has a "sub-singular" category: the
    singular region contains only atoms, which have no internal lattice
    structure to split via [±minimal]. -/
theorem no_singular_recursion : ¬∃ (r : Region), r.base = singularF := by
  intro ⟨r, hr⟩
  have := r.base_nonatomic
  rw [hr] at this
  exact absurd this (by decide)

-- ============================================================================
-- § 5: Recursion Properties
-- ============================================================================

/-- Each recursion yields exactly 2 new categories: the [+minimal] and
    [−minimal] subregions are always distinct. -/
theorem recursion_yields_two (reg : Region) :
    (⟨reg, true⟩ : RecursiveNumber).toCategory ≠
    (⟨reg, false⟩ : RecursiveNumber).toCategory := by
  simp only [RecursiveNumber.toCategory]
  have := reg.base_nonatomic
  cases ha : reg.base.isAtomic <;> cases hm : reg.base.isMinimal <;> simp_all

/-- Trial presupposes plural: the plural region must exist (i.e., the
    base partition must include [−atomic, −minimal]) for trial to arise
    from recursion on it. -/
theorem trial_presupposes_plural : trial.region.base = pluralF := rfl

/-- Unit augmented presupposes dual: the non-singular region must exist
    for unit augmented to arise from recursion on it. -/
theorem unitAug_presupposes_dual : unitAugmented.region.base = dualF := rfl

/-- The base partition is a prerequisite for any recursion: every
    recursive category's base region is a well-formed base number. -/
theorem recursion_presupposes_base (r : RecursiveNumber) :
    r.region.base.wellFormed = true := r.region.base_wf

/-- Base categories of recursive numbers map to Corbett categories. -/
theorem recursion_base_categories :
    trial.region.base.toCategory = some .plural ∧
    unitAugmented.region.base.toCategory = some .dual := ⟨rfl, rfl⟩

-- ============================================================================
-- § 6: Only Two Recursion Regions
-- ============================================================================

/-- There are exactly two recursion-eligible regions: the dual region
    ([−atomic, +minimal]) and the plural region ([−atomic, −minimal]).

    The singular region ([+atomic, +minimal]) is excluded by `base_nonatomic`,
    and the ill-formed [+atomic, −minimal] is excluded by `base_wf`. -/
theorem only_two_regions (r : Region) : r.base = dualF ∨ r.base = pluralF := by
  obtain ⟨⟨a, m⟩, _, hna⟩ := r
  cases a <;> cases m
  · exact Or.inr rfl  -- false, false → pluralF
  · exact Or.inl rfl  -- false, true → dualF
  · simp at hna  -- true, false → contradiction
  · simp at hna  -- true, true → contradiction

-- ============================================================================
-- § 7: Markedness Partial Order on Categories
-- ============================================================================

/-! The markedness ordering on number categories, derived from
    @cite{corbett-2000}'s implicational hierarchy. `a ≤ b` means b
    presupposes a: every number system containing b also contains a.

    Hasse diagram:
    ```
         trial   greaterPlural   greaterPaucal
           \        /               /    \
            dual  ─────────────────       paucal
              \                           /
               plural  ─────────────────
                 |
              singular
    ```
    `general` is isolated (incomparable with all in-system categories). -/

/-- The markedness ordering on number categories as a decidable relation. -/
def markednessLE (a b : Category) : Bool :=
  a == b || match a, b with
  | .singular, .plural | .singular, .dual | .singular, .trial
  | .singular, .paucal | .singular, .greaterPlural
  | .singular, .greaterPaucal => true
  | .plural, .dual | .plural, .trial | .plural, .greaterPlural
  | .plural, .paucal | .plural, .greaterPaucal => true
  | .dual, .trial | .dual, .greaterPlural | .dual, .greaterPaucal => true
  | .paucal, .greaterPaucal => true
  | _, _ => false

instance : LE Category where
  le a b := markednessLE a b = true

instance : DecidableRel (fun (a b : Category) => a ≤ b) :=
  fun a b => show Decidable (markednessLE a b = true) from inferInstance

instance : Fintype Category where
  elems := {.general, .singular, .dual, .trial, .paucal,
            .plural, .greaterPaucal, .greaterPlural}
  complete x := by cases x <;> simp [Finset.mem_insert, Finset.mem_singleton]

instance : PartialOrder Category where
  le_refl a := by cases a <;> decide
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide

-- ============================================================================
-- § 8: Harbour Configuration Space
-- ============================================================================

/-- A Harbour number configuration: which features and operations are active.

    @cite{harbour-2016} Ch 6: every attested number system can be described
    by activating a subset of these 4 parameters. The 2⁴ = 16 logically
    possible configurations reduce to 8 well-formed ones after applying
    the feature activation prerequisites. -/
structure HarbourConfig where
  /-- Whether [±atomic] is active. -/
  hasAtomic : Bool
  /-- Whether [±minimal] is active. -/
  hasMinimal : Bool
  /-- Whether [±additive] is active. -/
  hasAdditive : Bool
  /-- Whether [±minimal] recurses on the plural region. -/
  recurseOnPlural : Bool
  deriving DecidableEq, BEq, Repr

/-- Well-formedness: feature activation prerequisites.

    1. Recursion requires both [±atomic] and [±minimal] (the base partition
       must be fully specified for recursion to have a target region).
    2. [±additive] requires [±atomic] (additive closure operates on atomic
       vs non-atomic regions). -/
def HarbourConfig.wellFormed (c : HarbourConfig) : Bool :=
  (!c.recurseOnPlural || (c.hasAtomic && c.hasMinimal)) &&
  (!c.hasAdditive || c.hasAtomic)

/-- The number categories generated by a Harbour configuration.

    @cite{harbour-2016} Ch 6: features are activated cumulatively, and each
    activation adds categories to the system:
    - [±atomic] alone: singular vs non-singular (= plural)
    - [±minimal] alone: minimal (= singular) vs non-minimal (= plural)
    - [±atomic] + [±minimal]: singular, dual, plural (the base partition)
    - + recursion: trial, greater plural
    - + [±additive]: paucal (and greater paucal if [±minimal] is also active) -/
def HarbourConfig.categories (c : HarbourConfig) : List Category :=
  let base :=
    if c.hasAtomic && c.hasMinimal then [.singular, .dual, .plural]
    else if c.hasAtomic || c.hasMinimal then [.singular, .plural]
    else []
  let recursive :=
    if c.recurseOnPlural then [.trial, .greaterPlural] else []
  let additive :=
    if c.hasAdditive then
      if c.hasMinimal then [.paucal, .greaterPaucal]
      else [.paucal]
    else []
  base ++ recursive ++ additive

-- ============================================================================
-- § 9: The Main Theorem — Lower Set Property
-- ============================================================================

/-! **The main impossibility theorem.** @cite{corbett-2000}'s implicational
    universals (trial → dual → plural → singular, greaterPaucal → paucal,
    etc.) are not stipulated constraints — they are a THEOREM of
    @cite{harbour-2016}'s feature geometry.

    The categories generated by any well-formed Harbour configuration form
    a **lower set** (`IsLowerSet`) in the markedness partial order. This
    single theorem subsumes ALL implicational universals: if a category is
    generated, everything it presupposes is also generated.

    The proof is exhaustive: 4 Bool parameters × 8² category pairs,
    verified by `decide` after case-splitting. -/

/-- The categories generated by any well-formed Harbour configuration form
    a lower set in the markedness partial order: if `b` is generated and
    `a ≤ b`, then `a` is also generated. -/
theorem categories_lowerSet (c : HarbourConfig) (hw : c.wellFormed = true)
    (a b : Category) (hab : a ≤ b) (hb : c.categories.contains b = true) :
    c.categories.contains a = true := by
  obtain ⟨ca, cm, cd, cr⟩ := c
  revert hw hab hb
  cases ca <;> cases cm <;> cases cd <;> cases cr <;>
    cases a <;> cases b <;> decide

/-- The lower set property stated via Mathlib's `IsLowerSet`. -/
theorem categories_isLowerSet (c : HarbourConfig) (hw : c.wellFormed = true) :
    IsLowerSet {cat : Category | c.categories.contains cat = true} := by
  intro a b hab ha
  exact categories_lowerSet c hw b a hab ha

-- ============================================================================
-- § 10: Corollaries
-- ============================================================================

/-- General number is outside the Harbour feature system entirely: no
    configuration generates it. -/
theorem general_not_generated (c : HarbourConfig) :
    c.categories.contains .general = false := by
  obtain ⟨a, m, d, r⟩ := c
  cases a <;> cases m <;> cases d <;> cases r <;> decide

/-- Exactly 8 of the 16 logically possible configurations are well-formed. -/
theorem eight_wellformed_configs :
    let allConfigs := [false, true].flatMap fun a =>
      [false, true].flatMap fun m =>
        [false, true].flatMap fun d =>
          [false, true].map fun r =>
            HarbourConfig.mk a m d r
    (allConfigs.filter HarbourConfig.wellFormed).length = 8 := by native_decide

end Theories.Syntax.Minimalism.Agreement.FeatureRecursion
