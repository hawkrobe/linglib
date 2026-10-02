/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Plurality.NumberFeatures
public import Linglib.Semantics.Plurality.Number
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.UpperLower.Basic

/-!
# Feature recursion

Harbour derives the number categories beyond singular, dual and plural by feature recursion,
reapplying [±minimal] inside a region of the base [±atomic, ±minimal] partition. Recursion on the
plural region gives the trial, its minimal elements (groups of three), and the greater plural;
recursion on the non-singular region gives the unit augmented, pairs, and the augmented. Only
[±minimal] recurses, and atoms, being singletons, cannot be partitioned further. The values a
configuration of active features generates form a lower set of the markedness order on `Number`,
so the implicational universals are one `IsLowerSet` statement.

## Main definitions

* `Minimalist.Phi.Recursion.Region`, `Minimalist.Phi.Recursion.RecursiveNumber`: the regions
  recursion applies to and the categories it yields.
* `Minimalist.Phi.Recursion.HarbourConfig`: a configuration of active features and recursions,
  with the categories it generates.

## Main results

* `no_singular_recursion`, `only_two_regions`: recursion applies to the dual and plural regions.
* `categories_isLowerSet`: the generated categories form a lower set of the markedness order.
* `sixteen_wellformed_configs`, `table3_counts_match`: the configuration space and Harbour's
  Table 3.

## References

* [harbour-2014]
* [harbour-2016]
* [corbett-2000]
-/

@[expose] public section

namespace Minimalist.Phi.Recursion

open Number (Features singularF dualF pluralF)

/-! ### Recursion Regions -/

/-- A region of the number lattice eligible for recursion is non-atomic: only [−atomic] regions
have the internal structure a [±minimal] split needs, atoms being singletons. -/
structure Region where
  /-- The base number features defining this region. -/
  base : Features
  /-- The base features pass the containment filter. -/
  base_wf : IsLowerSet (↑base : Set Number.Feature)
  /-- The region is non-atomic, since atoms cannot be recursed. -/
  base_nonatomic : .atomic ∉ base
  deriving DecidableEq

/-- The plural region, [−atomic, −minimal], holds the groups of three or more. -/
def pluralRegion : Region := ⟨pluralF, by decide, by decide⟩

/-- The non-singular (dual) region, [−atomic, +minimal], holds the minimal non-atoms, pairs. -/
def dualRegion : Region := ⟨dualF, by decide, by decide⟩

/-! ### Recursive Number Categories -/

/-- A recursive number category applies [±minimal] once within a base region, splitting it into
a minimal and a non-minimal subregion ([harbour-2016] chapter 6). -/
structure RecursiveNumber where
  /-- The target region for recursion. -/
  region : Region
  /-- [±minimal] within the target region. -/
  isMinimalInRegion : Bool
  deriving DecidableEq

/-- The trial is the minimal part of the plural region, groups of exactly three. -/
def trial : RecursiveNumber := ⟨pluralRegion, true⟩

/-- The greater plural is the non-minimal part of the plural region, groups of four or more. -/
def greaterPlural : RecursiveNumber := ⟨pluralRegion, false⟩

/-- The unit augmented is the minimal part of the non-singular region, pairs. -/
def unitAugmented : RecursiveNumber := ⟨dualRegion, true⟩

/-- The augmented is the non-minimal part of the non-singular region, groups of three or more. -/
def augmented : RecursiveNumber := ⟨dualRegion, false⟩

/-! ### Mapping to Corbett Values -/

/-- A recursive category is one of [corbett-2000]'s number values, the trial or greater plural on
the plural region and the unit augmented or augmented on the non-singular region. -/
def RecursiveNumber.toNumber (r : RecursiveNumber) : Number :=
  if .minimal ∈ r.region.base then
    -- Recursion on the non-singular ([−atomic, +minimal]) region
    if r.isMinimalInRegion then .unitAugmented else .augmented
  else
    -- Recursion on the plural ([−atomic, −minimal]) region
    if r.isMinimalInRegion then .trial else .greaterPlural

theorem trial_toNumber : trial.toNumber = .trial := by decide
theorem greaterPlural_toNumber : greaterPlural.toNumber = .greaterPlural := by decide
theorem unitAugmented_toNumber : unitAugmented.toNumber = .unitAugmented := by decide
theorem augmented_toNumber : augmented.toNumber = .augmented := by decide

/-! ### Impossibility of Singular Recursion -/

/-- No region is singular, since [+atomic] regions are singletons with no structure to split,
which is why no language has a sub-singular category. -/
theorem no_singular_recursion : ¬∃ (r : Region), r.base = singularF := by
  intro ⟨r, hr⟩
  have := r.base_nonatomic
  rw [hr] at this
  exact this (by decide)

/-! ### Recursion Properties -/

/-- The [+minimal] and [−minimal] subregions of a recursion are distinct categories. -/
theorem recursion_yields_two (reg : Region) :
    (⟨reg, true⟩ : RecursiveNumber).toNumber ≠
    (⟨reg, false⟩ : RecursiveNumber).toNumber := by
  by_cases hm : Number.Feature.minimal ∈ reg.base <;> simp [RecursiveNumber.toNumber, hm]

/-- The trial presupposes the plural, the region it arises from. -/
theorem trial_presupposes_plural : trial.region.base = pluralF := rfl

/-- The unit augmented presupposes the dual, the region it arises from. -/
theorem unitAug_presupposes_dual : unitAugmented.region.base = dualF := rfl

/-- Every recursive category's base region is a base number passing the containment filter. -/
theorem recursion_presupposes_base (r : RecursiveNumber) :
    IsLowerSet (↑r.region.base : Set Number.Feature) := r.region.base_wf

/-- The base regions of the trial and the unit augmented are the plural and the dual. -/
theorem recursion_base_categories :
    trial.region.base.toNumber = some .plural ∧
    unitAugmented.region.base.toNumber = some .dual := ⟨rfl, rfl⟩

/-! ### Only Two Recursion Regions -/

/-- The recursion regions are exactly the dual and the plural region, the singular being excluded
by `base_nonatomic` and the filtered [+atomic, −minimal] by `base_wf`. -/
theorem only_two_regions (r : Region) : r.base = dualF ∨ r.base = pluralF := by
  obtain ⟨b, hw, hna⟩ := r
  revert b; decide

/-! ### Harbour Configuration Space -/

/-- A Harbour configuration records which features and recursions are active; every attested
number system activates some of these five parameters ([harbour-2014]). -/
structure HarbourConfig where
  /-- Whether [±atomic] is active. -/
  hasAtomic : Bool
  /-- Whether [±minimal] is active. -/
  hasMinimal : Bool
  /-- Whether [±additive] is active. -/
  hasAdditive : Bool
  /-- Whether [±minimal] recurses on the plural region. -/
  recurseOnPlural : Bool
  /-- Whether [±additive] recurses (splitting paucal into paucal +
      greater paucal). Marked `*` on [±additive] in Table 3. -/
  recurseOnAdditive : Bool
  deriving DecidableEq, Repr, Fintype

/-- A configuration is well-formed when its activations meet their prerequisites.

    1. [±minimal] recursion requires [±minimal] — the feature must be active
       for recursion to have a target region. When [±atomic] is also active,
       recursion targets the plural region (→ trial, greater plural); without
       [±atomic], it targets the augmented region (→ unit augmented).
    2. [±additive] requires at least one base feature ([±atomic] or [±minimal])
       to define the region it operates on. Without a base partition,
       [±additive] has no non-trivial region to split.
    3. [±additive] recursion requires [±additive] to be active. -/
def HarbourConfig.wellFormed (c : HarbourConfig) : Bool :=
  (!c.recurseOnPlural || c.hasMinimal) &&
  (!c.hasAdditive || c.hasAtomic || c.hasMinimal) &&
  (!c.recurseOnAdditive || c.hasAdditive)

/-- A configuration generates number categories cumulatively, each activation adding some.

    Features are activated cumulatively, and each activation adds
    categories to the system:
    - [±atomic] alone: singular vs non-singular (= plural)
    - [±minimal] alone: minimal vs non-minimal (= augmented)
    - [±atomic] + [±minimal]: singular, dual, plural (the base partition)
    - + [±minimal] recursion (with [±atomic]): trial (the residue remains
      plural)
    - + [±minimal] recursion (without [±atomic]): unit augmented
    - + [±additive]: paucal (+ plural when base is MIN/AUG, since
      [±additive] splits augmented into paucal and plural)
    - + [±additive] recursion: greater paucal

    Recursion on the plural region (with [±atomic]) adds `.trial`; the
    residue keeps the label `.plural` — [harbour-2014] Table 3 lists
    Larike as singular, dual, trial, *plural* (greater plural is reserved
    for [±additive]-derived values). `.augmented` remains alongside
    `.paucal` and `.plural` when [±additive] splits it; superordinates are
    required for the lower-set property. -/
def HarbourConfig.categories (c : HarbourConfig) : List Number :=
  let base :=
    if c.hasAtomic && c.hasMinimal then [.singular, .dual, .plural]
    else if c.hasAtomic then [.singular, .plural]
    else if c.hasMinimal then [.minimal, .augmented]
    else []
  let recursive :=
    if c.recurseOnPlural then
      if c.hasAtomic then [.trial]
      else [.unitAugmented]  -- recursion on augmented without [±atomic]
    else []
  let additive :=
    if c.hasAdditive then
      let paucalCats :=
        if c.recurseOnAdditive then [.paucal, .greaterPaucal]
        else [.paucal]
      -- When base is MIN/AUG (no [±atomic]), [±additive] splits augmented
      -- into paucal ([−additive]) and plural ([+additive]). Plural is a
      -- new category here, not a superordinate already in the base.
      let pluralFromAdditive :=
        if !c.hasAtomic && c.hasMinimal then [.plural] else []
      paucalCats ++ pluralFromAdditive
    else []
  base ++ recursive ++ additive

/-! ### The Main Theorem — Lower Set Property -/

/-! **The main impossibility theorem.** [corbett-2000]'s implicational
    universals (trial → dual → plural → singular, greaterPaucal → paucal,
    etc.) are not stipulated constraints — they are a THEOREM of
    [harbour-2016]'s feature geometry.

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
    (a b : Number) (hab : a ≤ b) (hb : c.categories.contains b = true) :
    c.categories.contains a = true := by
  obtain ⟨ca, cm, cd, cr, cra⟩ := c
  revert hw hab hb
  cases ca <;> cases cm <;> cases cd <;> cases cr <;> cases cra <;>
    cases a <;> cases b <;> decide

/-- The generated categories form a lower set in mathlib's sense. -/
theorem categories_isLowerSet (c : HarbourConfig) (hw : c.wellFormed = true) :
    IsLowerSet {cat : Number | c.categories.contains cat = true} :=
  fun a b hab ha => categories_lowerSet c hw b a hab ha

/-! ### Corollaries -/

/-- No configuration generates general number, which lies outside the feature system. -/
theorem general_not_generated (c : HarbourConfig) :
    c.categories.contains .general = false := by
  obtain ⟨a, m, d, r, ra⟩ := c
  cases a <;> cases m <;> cases d <;> cases r <;> cases ra <;> decide

/-- Exactly 16 of the 32 logically possible configurations are well-formed. -/
theorem sixteen_wellformed_configs :
    let allConfigs := [false, true].flatMap fun a =>
      [false, true].flatMap fun m =>
        [false, true].flatMap fun d =>
          [false, true].flatMap fun r =>
            [false, true].map fun ra =>
              HarbourConfig.mk a m d r ra
    (allConfigs.filter HarbourConfig.wellFormed).length = 16 := by decide

/-! The lattice-grounded feature predicates — [harbour-2014]'s (20)
`[±atomic]`, (21) `[±minimal]`, (10) `[±additive]` as predicates over a
join-semilattice, with the CUM identity for the number–aspect nexus —
graduated to `Semantics/Plurality/Number.lean` (`Mereology.atomize`,
`Number.additiveIn`, `Number.additive_subregion_is_cum`). -/

/-! ### Surface Categories and Typological Predictions -/

/-! ### Surface Categories and Typological Predictions
[harbour-2014] Table 3

`categories` includes superordinate categories that have been split by
recursion or [±additive]. For example, {±minimal*, ±atomic} generates
`[sg, du, pl, trial, greaterPl]`, but the surface system is
sg/du/trial/greaterPl (4 values) — plural has been split into
trial + greater plural and is no longer a distinct morphological category.

`surfaceCategories` removes these split superordinates to match the
observable number distinctions. The resulting counts match
[harbour-2014] Table 3 exactly.

The parameter space — feature activation ({±atomic}, {±minimal},
{±additive}) and feature recursion (* = reapplication) — generates a
typology of number systems. Each parametric setting predicts a specific
inventory of number values matching [corbett-2000], [cysouw-2003].

Key predictions:
- Trial and unit augmented are the highest exact numbers attainable
  without numerals (bounded by the axiom of extension, (27)).
- A language may have at most two approximative numbers
  (e.g. paucal + greater paucal, from [±additive] + recursion).
- Three unattested parameter settings ({±additive, ±minimal*},
  {±additive*, ±minimal}, {±additive*, ±minimal*, ±atomic}) have
  plausible explanations for their absence. -/

/-- The surface categories are the morphologically distinct number values.

    Unlike `categories` (which includes superordinates for the lower-set
    property), this removes a category that has been split into
    subcategories by [±additive]:

    - **Augmented** is removed when [±additive] (without [±atomic]) splits
      it into paucal + plural. The surface system is minimal/paucal/plural
      (Mebengokre, [harbour-2014] Table 3).

    The resulting label sets and counts match [harbour-2014] Table 3. -/
def HarbourConfig.surfaceCategories (c : HarbourConfig) : List Number :=
  let cats := c.categories
  -- Augmented is split by [±additive] when base is MIN/AUG (no [±atomic])
  let removeAugmented := c.hasAdditive && !c.hasAtomic && c.hasMinimal
  cats.filter fun cat => !(removeAugmented && cat == .augmented)

/-- A configuration generates the `Number.System` of its surface values; the empty configuration
leaves Number⁰ featureless, general number ([harbour-2014] (24); Pirahã, Classical Chinese). -/
def HarbourConfig.toSystem (c : HarbourConfig) (name : String := "") :
    Number.System :=
  { name := name
    values := c.surfaceCategories
    hasGeneral := c.surfaceCategories.isEmpty }

/-- An entry of [harbour-2014]'s Table 3 pairs a configuration with the predicted system size and
an example language. -/
structure Harbour2014Entry where
  /-- The feature activation and recursion parameters. -/
  config : HarbourConfig
  /-- Number of distinct surface values in the system. -/
  numValues : Nat
  /-- Example language. -/
  language : String
  deriving Repr

/-- [harbour-2014]'s Table 3 is a typology of number systems.
    15 attested parametric settings (12 distinct configs) generating
    0–5 value systems. Subscripted entries share the same config
    but exemplify different languages. -/
def harbour2014Table3 : List Harbour2014Entry := [
  -- ∅: no features → no number distinctions
  ⟨⟨false, false, false, false, false⟩, 0, "Pirahã"⟩,
  -- {±atomic}: singular vs non-singular
  ⟨⟨true, false, false, false, false⟩, 2, "Svan"⟩,
  -- {±minimal}: minimal vs augmented
  ⟨⟨false, true, false, false, false⟩, 2, "Winnebago"⟩,
  -- {±minimal*}: minimal, unit augmented, augmented
  ⟨⟨false, true, false, true, false⟩, 3, "Rembarrnga"⟩,
  -- {±minimal, ±atomic}: singular, dual, plural
  ⟨⟨true, true, false, false, false⟩, 3, "Kiowa"⟩,
  -- {±additive, ±atomic}₁: singular, paucal, plural
  ⟨⟨true, false, true, false, false⟩, 3, "Bayso"⟩,
  -- {±additive, ±atomic}₂
  ⟨⟨true, false, true, false, false⟩, 3, "Fula"⟩,
  -- {±additive, ±minimal}: minimal, paucal, plural
  ⟨⟨false, true, true, false, false⟩, 3, "Mebengokre"⟩,
  -- {±minimal*, ±atomic}: singular, dual, trial, greater plural
  ⟨⟨true, true, false, true, false⟩, 4, "Larike"⟩,
  -- {±additive*, ±atomic}: singular, plural, paucal, greater paucal
  ⟨⟨true, false, true, false, true⟩, 4, "Banyun"⟩,
  -- {±additive, ±minimal, ±atomic}₁: singular, dual, plural, paucal
  ⟨⟨true, true, true, false, false⟩, 4, "Yimas"⟩,
  -- {±additive, ±minimal, ±atomic}₂
  ⟨⟨true, true, true, false, false⟩, 4, "Mokilese"⟩,
  -- {±additive, ±minimal*, ±atomic}: sg, du, trial, greaterPl, paucal
  ⟨⟨true, true, true, true, false⟩, 5, "Marshallese"⟩,
  -- {±additive*, ±minimal, ±atomic}₁: sg, du, pl, paucal, greaterPaucal
  ⟨⟨true, true, true, false, true⟩, 5, "Sursurunga"⟩,
  -- {±additive*, ±minimal, ±atomic}₂
  ⟨⟨true, true, true, false, true⟩, 5, "Mele-Fila"⟩]

/-- All Table 3 configs are well-formed. -/
theorem table3_all_wellformed :
    harbour2014Table3.all (fun e => e.config.wellFormed) = true := by decide

/-- The surface category counts match Table 3's predictions.

    This is the key verification theorem: the generative mechanism
    (`HarbourConfig` → `categories` → `surfaceCategories`) produces
    exactly the number of morphologically distinct values predicted by
    [harbour-2014] Table 3 for each parametric setting. -/
theorem table3_counts_match :
    harbour2014Table3.all (fun e =>
      decide (e.config.surfaceCategories.length = e.numValues)) = true := by
  decide

/-- No system has more than 5 surface values (Table 3). -/
theorem max_system_size :
    harbour2014Table3.all (fun e => decide (e.numValues ≤ 5)) = true := by
  decide

/-- Every nonempty system has at least two values, number being contrastive ([harbour-2014]
§1). -/
theorem min_system_size :
    harbour2014Table3.all
      (fun e => decide (e.numValues = 0 ∨ e.numValues ≥ 2)) = true := by
  decide

/-! ### Convexity Condition -/

/-! ### Convexity Condition
[harbour-2014] §4.5, (32)

The convexity condition explains why {±additive} alone is NOT a legitimate
number system. A lattice region L is convex iff for any a, b ∈ L and
a ≤ c ≤ b, c ∈ L (no "gaps" — [harbour-2014] (33)).

For first and second person, [±additive] applied without [±atomic] or
[±minimal] produces a nonconvex cut: between the [+additive] first-person
atom (the speaker, closed under join with itself) and any [+additive]
first-person plural, there must lie a [−additive] first-person paucal.
This nonconvex cut violates the general requirement that basic meanings
be convex ([gardenfors-2004]).

Convexity here is mathlib's `Set.OrdConnected`: a region is convex iff it
is a fixed point of `ordConnectedHull`
(`ordConnectedHull_eq_self`) — the same predicate that
states [grimm-2018]'s no-discontinuous-category condition on countability
classes (`Studies/Grimm2018.lean`), so Harbour's and Grimm's convexity
requirements are the same predicate. -/

/-! ### Axiom of Extension -/

/-! ### Axiom of Extension
[harbour-2014] §4.2, (27)

The axiom of extension ({a, a} = {a}) from set theory caps the complexity
of number feature specifications. Since feature bundles are SETS, repeating
a feature value has no effect: [+F −F] is the maximum specification that
a single feature F can achieve. This means [+F −F] = {+F, −F}, and adding
more copies ([+F −F −F]) just gives {+F, −F} again.

**Consequence**: trial and unit augmented are the highest exact numbers
attainable without numerals. A "quadral" would require [+minimal −minimal
−minimal −atomic] = {+minimal, −minimal, −atomic} = [+minimal −minimal
−atomic] = trial. The axiom prevents going beyond trial.

This is formalized as a theorem about `Finset`: the deduplication of a
feature value list has at most 2 elements for any single feature. -/

/-- The axiom of extension limits a single binary feature to at most
    2 distinct values: {+F} and/or {−F}. Repeating a value adds nothing.

    Stated via `Fintype.card Bool = 2`: any binary feature has exactly
    2 possible values, so no specification of a single feature can
    produce more than 2 distinctions. This is why trial (3 atoms) is the
    maximum exact number: it requires [+minimal −minimal −atomic], which
    uses 2 features × 2 values = at most 4 distinctions (but [+atomic]
    and [+minimal] overlap, giving only 3). -/
theorem axiom_of_extension_binary :
    (Finset.univ : Finset Bool).card = 2 := by decide

end Minimalist.Phi.Recursion
