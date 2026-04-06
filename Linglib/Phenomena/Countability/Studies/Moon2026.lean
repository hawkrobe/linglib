import Linglib.Core.Mereotopology
import Linglib.Core.Mereology
import Linglib.Theories.Interfaces.SyntaxSemantics.Borer2005
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# Moon 2026: Countability and Measured Parts in Mixed Drink Nouns
@cite{moon-2026}

Mixed drink nouns (*martini*, *cappuccino*) are count despite denoting
liquids. Moon proposes that their countability derives from a MEASURED
PART — an ingredient part (the shot of liquor/espresso) that provides
a unit for individuation. This contrasts with standard mass drink nouns
(*wine*, *coffee*) which lack such a part.

## Core Proposal (formula 28)

⟦mixed drink⟧ = λx ∃ȳ₀ⁿ ∃P̄₀ⁿ [x = ⊕ȳ ∧ ∀yᵢ∀Pᵢ[Pᵢ(yᵢ)]
  ∧ ∃r̄₀ⁿ ∀ȳ₀ⁿ [μ(yᵢ)/rᵢ = μ(yⱼ)/rⱼ]
  ∧ MEASURED PART(y₀) ∧ CONNECTED LIQUID(x)]

This is built from:
1. **Parts in mereological sum** — `SemilatticeSup` (⊔)
2. **Ratio constraint** — `ExtMeasure.μ` (extensive measure)
3. **Measured part** — a distinguished countable ingredient
4. **Connected liquid** — `IsConnected` from Mathlib topology

## Grounding

| Moon concept | Linglib/Mathlib |
|---|---|
| ⊕ (sum) | `⊔` (`SemilatticeSup`) |
| O (overlap) | `Mereology.Overlap` |
| μ (measure) | `ExtMeasure.μ` |
| SC (self-connection) | `Mereotopology.SelfConnected` = `IsConnected (Set.Iic x)` |
| CONNECTED LIQUID | `Mereotopology.ConnectedLiquid` |
| QUA/CUM | `Mereology.QUA` / `Mereology.CUM` |

## Key Empirical Claims

1. Mixed drink nouns are syntactically count: pluralize, take numerals,
   combine with *many* (not *much*), accept distributive predicates
2. This is NOT Universal Packager coercion: countability persists in
   *pitcher of martinis*, *bottomless mimosas* (Moon §3.5)
3. Multiplier *double* targets the MEASURED PART (*double americano*
   = double espresso, not double volume), following @cite{wagiel-2021}
4. Quantity judgments are ambiguous between volume, number of portions,
   and number of measured parts (Moon §4.3.2)
-/

namespace Phenomena.Countability.Studies.Moon2026

open Mereology Mereotopology

-- ════════════════════════════════════════════════════
-- § 1. Mixed Drink Recipe
-- ════════════════════════════════════════════════════

variable {α : Type*} [SemilatticeSup α] [TopologicalSpace α]

/-- A mixed drink recipe: ingredient predicates, ratio constants, and
    an index identifying which ingredient is the MEASURED PART.

    Example: a margarita has 3 ingredients (tequila, triple sec, lime juice)
    in ratio 5:2:1.5, and the measured part is the tequila (index 0). -/
structure Recipe (α : Type*) (n : ℕ) where
  /-- Ingredient predicates (e.g., TEQUILA, TRIPLE_SEC, LIME_JUICE) -/
  ingredients : Fin n → α → Prop
  /-- Ratio constants (e.g., 5, 2, 3/2 for a margarita). All positive. -/
  ratios : Fin n → ℚ
  /-- All ratio constants are positive. -/
  ratios_pos : ∀ i, 0 < ratios i
  /-- Index of the measured part (the individuating ingredient). -/
  measuredPart : Fin n

-- ════════════════════════════════════════════════════
-- § 2. Ratio Constraint
-- ════════════════════════════════════════════════════

/-- The ratio constraint between parts of a mixed drink:
    μ(yᵢ)/rᵢ = μ(yⱼ)/rⱼ for all pairs of parts.

    This captures that it is the *ratio* between ingredients that
    defines the drink, not the absolute measurements. A margarita
    is 5:2:1.5 whether made with 50ml, 20ml, 15ml or with 100ml,
    40ml, 30ml of the respective ingredients.

    Uses `ExtMeasure.μ` from `Core/Mereology.lean`. -/
def RatioHolds {n : ℕ} (μ : α → ℚ) (recipe : Recipe α n)
    (parts : Fin n → α) : Prop :=
  ∀ i j, μ (parts i) * recipe.ratios j = μ (parts j) * recipe.ratios i

-- Cross-multiply form avoids division; equivalent to μ(yᵢ)/rᵢ = μ(yⱼ)/rⱼ
-- when all ratios are positive.

-- ════════════════════════════════════════════════════
-- § 3. Mixed Drink Denotation (Formula 28)
-- ════════════════════════════════════════════════════

/-- Witness structure for a mixed drink: the ingredient parts that
    compose the drink, satisfying all constraints. -/
structure MixedDrinkWitness {n : ℕ} (recipe : Recipe α n)
    (μ : α → ℚ) (phase : α → Phase) (x : α) where
  /-- Assignment of entities to ingredient slots -/
  assign : Fin n → α
  /-- Each part is a part of the whole -/
  part_le : ∀ i, assign i ≤ x
  /-- Each part satisfies its ingredient predicate -/
  satisfies : ∀ i, recipe.ingredients i (assign i)
  /-- Ratio constraint holds between all parts -/
  ratio : RatioHolds μ recipe assign
  /-- Parts don't overlap pairwise (they are distinct ingredients) -/
  disjoint : ∀ i j, i ≠ j → ¬ Overlap (assign i) (assign j)
  /-- The parts exhaust the whole: every part of x overlaps some ingredient.
      Moon's x = ⊕ȳ requires the ingredients to cover x completely — no
      extra material beyond the recipe components. -/
  covers : ∀ z, z ≤ x → ∃ i, Overlap z (assign i)
  /-- The whole is a connected liquid -/
  connected : ConnectedLiquid phase x

/-- The denotation of a mixed drink noun, following Moon's formula (28).

    An entity x is a mixed drink if:
    1. It has ingredient parts satisfying the recipe predicates
    2. The parts stand in the correct ratio (via μ)
    3. The parts are pairwise non-overlapping
    4. The whole is a connected liquid (self-connected, all parts liquid)

    The MEASURED PART is the ingredient at `recipe.measuredPart` — it
    provides the unit for individuation and is what *double* targets
    (@cite{wagiel-2021}). -/
def mixedDrinkDen {n : ℕ} (recipe : Recipe α n)
    (μ : α → ℚ) (phase : α → Phase) (x : α) : Prop :=
  Nonempty (MixedDrinkWitness recipe μ phase x)

-- ════════════════════════════════════════════════════
-- § 4. CUM/DIV Failure (Source of Countability)
-- ════════════════════════════════════════════════════

/-- CUM fails for mixed drink denotations because the join of two
    disconnected mixed drinks is not a connected liquid.

    If m₁ and m₂ are two separate margaritas (in different glasses),
    their mereological sum m₁ ⊔ m₂ is not self-connected: the set
    `{y | y ≤ m₁ ⊔ m₂}` has a non-trivial open partition separating
    the two glasses. Therefore `ConnectedLiquid phase (m₁ ⊔ m₂)` fails,
    so `m₁ ⊔ m₂` does not satisfy the mixed drink denotation.

    This is the key asymmetry with mass nouns like *wine*: wine does
    not require self-connection, so pouring two wines together yields
    more wine (CUM holds). -/
theorem not_cum_of_disconnected {n : ℕ} (recipe : Recipe α n)
    (μ : α → ℚ) (phase : α → Phase)
    {m₁ m₂ : α}
    (_hm₁ : mixedDrinkDen recipe μ phase m₁)
    (_hm₂ : mixedDrinkDen recipe μ phase m₂)
    (hDisc : ¬ SelfConnected (m₁ ⊔ m₂)) :
    ¬ mixedDrinkDen recipe μ phase (m₁ ⊔ m₂) := by
  intro ⟨w⟩
  exact hDisc w.connected.selfConnected

/-- DIV fails for mixed drink denotations because a single ingredient
    part does not satisfy the full recipe (it lacks the other ingredients).

    For example, just the tequila in a margarita is not itself a margarita:
    it satisfies TEQUILA but not TRIPLE_SEC or LIME_JUICE. With n ≥ 2
    ingredients, no single part can fill all ingredient slots.

    This is why mixed drinks are count: proper parts fail the predicate
    (QUA-like behavior). -/
-- TODO: Full proof requires an ingredient exclusivity axiom —
-- that if y satisfies ingredient i, then no part of y satisfies
-- ingredient j ≠ i. This is implicit in Moon's setup (tequila-stuff
-- is not triple-sec-stuff).
theorem single_ingredient_not_mixed_drink {n : ℕ}
    (recipe : Recipe α (n + 2))
    (μ : α → ℚ) (phase : α → Phase)
    {y : α} (i : Fin (n + 2))
    (_hIngr : recipe.ingredients i y)
    (hExcl : ∀ j, j ≠ i → ∀ z, z ≤ y → ¬ recipe.ingredients j z) :
    ¬ mixedDrinkDen recipe μ phase y := by
  intro ⟨w⟩
  -- With n + 2 ≥ 2 ingredients, there exists j ≠ i
  have ⟨j, hj⟩ : ∃ j : Fin (n + 2), j ≠ i := by
    by_cases h : (⟨0, by omega⟩ : Fin (n + 2)) = i
    · exact ⟨⟨1, by omega⟩, by intro heq; rw [← heq] at h; exact absurd h (by simp)⟩
    · exact ⟨⟨0, by omega⟩, h⟩
  -- w.assign j is a part of y (w.part_le j) and satisfies ingredient j
  exact hExcl j hj (w.assign j) (w.part_le j) (w.satisfies j)

-- ════════════════════════════════════════════════════
-- § 5. Multiplier Modification (@cite{wagiel-2021})
-- ════════════════════════════════════════════════════

/-- The multiplier reading of *double*: scales the measured part.

    *Double americano* = an americano with 2× the measured part (espresso).
    The multiplier targets `recipe.measuredPart`, not the whole drink.
    Following @cite{wagiel-2021}'s subatomic quantification: multipliers
    access semantically salient parts of an entity.

    A *double* mixed drink has the same recipe but with the measured
    part's ratio constant doubled — changing the ratio between parts
    while keeping the recipe structure. -/
def doubleRecipe {n : ℕ} (recipe : Recipe α n) : Recipe α n where
  ingredients := recipe.ingredients
  ratios := fun i =>
    if i = recipe.measuredPart
    then 2 * recipe.ratios i
    else recipe.ratios i
  ratios_pos := by
    intro i
    show 0 < (if i = recipe.measuredPart then 2 * recipe.ratios i else recipe.ratios i)
    split
    · exact mul_pos (by norm_num : (0:ℚ) < 2) (recipe.ratios_pos _)
    · exact recipe.ratios_pos i
  measuredPart := recipe.measuredPart

/-- *Dry* martini: reduces the non-measured-part ratio (vermouth).
    Moon (27b): a modifier that changes the ratio relationship
    between parts. This is a recipe-level operation, not an
    entity-level one. -/
def modifyRatio {n : ℕ} (recipe : Recipe α n)
    (target : Fin n) (factor : ℚ) (hPos : 0 < factor) :
    Recipe α n where
  ingredients := recipe.ingredients
  ratios := fun i => if i = target then factor * recipe.ratios i else recipe.ratios i
  ratios_pos := by
    intro i
    show 0 < (if i = target then factor * recipe.ratios i else recipe.ratios i)
    split
    · exact mul_pos hPos (recipe.ratios_pos _)
    · exact recipe.ratios_pos i
  measuredPart := recipe.measuredPart

-- ════════════════════════════════════════════════════
-- § 6. Empirical Data
-- ════════════════════════════════════════════════════

/-- Countability diagnostic contexts for nouns.
    Moon §3: mixed drink nouns pattern with count nouns across all tests.
    Table 1 (Appendix A): COCA corpus percentages. -/
inductive CountabilityContext where
  /-- Bare singular (*a margarita, *milk) -/
  | bareSg
  /-- Bare plural (margaritas, *milks) -/
  | barePl
  /-- With unit/numeral (two martinis, *two milks) -/
  | unit
  /-- Container/measure singular (a glass of wine, a bottle of beer) -/
  | containerSg
  /-- Container/measure plural -/
  | containerPl
  deriving DecidableEq, Repr

/-- Corpus distribution for a noun across countability contexts.
    Percentages from Moon 2026, Table 1 (COCA data). -/
structure CorpusDistribution where
  noun : String
  bareSg : Float
  barePl : Float
  unit : Float
  containerSg : Float
  containerPl : Float
  deriving Repr

/-- Cocktail noun group averages (Moon Table 1). -/
def cocktailAvg : CorpusDistribution :=
  { noun := "cocktail_avg", bareSg := 2.17, barePl := 31.65,
    unit := 31.97, containerSg := 0.22, containerPl := 1.25 }

/-- Non-count drink noun group averages (Moon Table 1). -/
def nonCountDrinkAvg : CorpusDistribution :=
  { noun := "noncount_drink_avg", bareSg := 45.73, barePl := 1.94,
    unit := 5.15, containerSg := 14.96, containerPl := 0.0 }

/-- The key distributional asymmetry: cocktails have high bare-plural
    and unit/numeral rates (count behavior), while non-count drinks
    have high bare-singular and container rates (mass behavior).
    χ²(3, N = 1361) = 858.29, p < .001, V = .79 -/
def distributionalAsymmetry : Prop :=
  cocktailAvg.barePl > nonCountDrinkAvg.barePl ∧
  cocktailAvg.unit > nonCountDrinkAvg.unit ∧
  nonCountDrinkAvg.bareSg > cocktailAvg.bareSg ∧
  nonCountDrinkAvg.containerSg > cocktailAvg.containerSg

-- ════════════════════════════════════════════════════
-- § 7. Quantity Judgment Ambiguity (§4.3.2)
-- ════════════════════════════════════════════════════

/-- Dimensions along which "who has more margaritas?" can be judged.

    Moon §4.3.2: Traditional quantity judgment tests assume two
    dimensions (number vs volume). Mixed drink nouns reveal a third:
    number of measured parts (shots of alcohol/espresso). -/
inductive QuantityDimension where
  /-- Total volume of liquid -/
  | volume
  /-- Number of standard portions (glasses) -/
  | portions
  /-- Number of measured parts (shots of base spirit/espresso) -/
  | measuredParts
  deriving DecidableEq, Repr

/-- Moon's scenario: person A drinks two single-shot 16oz americanos,
    person B drinks two quadruple-shot 12oz americanos.

    - By volume: A drank more (32oz > 24oz)
    - By portions: tied (2 each)
    - By measured parts: B drank more (8 shots > 2 shots)

    "Who drank more americanos?" is genuinely ambiguous. -/
structure AmericanoScenario where
  personA_portions : ℕ := 2
  personA_shots_per : ℕ := 1
  personA_oz_per : ℕ := 16
  personB_portions : ℕ := 2
  personB_shots_per : ℕ := 4
  personB_oz_per : ℕ := 12

def americanoExample : AmericanoScenario := {}

theorem americano_volume_A_more :
    americanoExample.personA_portions * americanoExample.personA_oz_per >
    americanoExample.personB_portions * americanoExample.personB_oz_per := by
  decide

theorem americano_portions_tied :
    americanoExample.personA_portions =
    americanoExample.personB_portions := by
  decide

theorem americano_shots_B_more :
    americanoExample.personB_portions * americanoExample.personB_shots_per >
    americanoExample.personA_portions * americanoExample.personA_shots_per := by
  decide

-- ════════════════════════════════════════════════════
-- § 8. Example: Margarita Recipe
-- ════════════════════════════════════════════════════

/-- Margarita recipe: tequila (ratio 5), triple sec (ratio 2),
    lime juice (ratio 3/2). Measured part = tequila (index 0).
    IBA specification: 50ml tequila, 20ml triple sec, 15ml lime juice. -/
def margaritaRecipe (α : Type*) (tequila tripleSec limeJuice : α → Prop) :
    Recipe α 3 where
  ingredients := ![tequila, tripleSec, limeJuice]
  ratios := ![5, 2, 3/2]
  ratios_pos := by
    intro i; fin_cases i <;>
      (simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]; try norm_num)
  measuredPart := 0

-- ════════════════════════════════════════════════════
-- § 9. Substance Nouns: the CUM Contrast
-- ════════════════════════════════════════════════════

/-- Substance noun denotation (wine, coffee, water): the predicate holds
    of any portion of the substance, with no recipe, ratio, or connectivity
    constraint.

    This is the key contrast with mixed drink nouns. Wine-stuff satisfies
    WINE regardless of shape, contiguity, or internal structure. Two
    disconnected puddles of wine are still wine. This makes the denotation
    cumulative: combining wine with wine gives wine. -/
abbrev substanceNounDen (substancePred : α → Prop) := substancePred

section SubstanceNounCum
variable {β : Type*} [SemilatticeSup β]

/-- Substance noun denotations are CUM when the underlying substance
    predicate is CUM. This is trivially true because the denotation IS
    the substance predicate — no additional constraints to break closure.

    Contrast with `not_cum_of_disconnected`: mixed drink denotations fail
    CUM because `ConnectedLiquid` rejects disconnected sums.

    Since @cite{chierchia-1998}'s `IsMass` implies CUM (via `isMass_cum`
    in `Theories/Semantics/Lexical/Noun/Kind/Chierchia1998.lean`), this
    means substance nouns can be mass. Mixed drink nouns cannot — their
    denotation fails CUM, hence fails `IsMass`. -/
theorem substanceNoun_cum (substancePred : β → Prop)
    (hCum : CUM substancePred) :
    CUM (substanceNounDen substancePred) :=
  hCum

end SubstanceNounCum

/-- The core mass/count asymmetry from Moon 2026:

    - **Substance nouns** (wine, coffee): CUM holds, QUA fails →
      mass behavior (bare singular OK, *two wines needs coercion)
    - **Mixed drink nouns** (martini, americano): CUM fails (via
      ConnectedLiquid), QUA-like behavior → count (pluralizes,
      takes numerals, *much martini)

    The only structural difference is the ConnectedLiquid + recipe
    constraint. Both denote liquids. The measured part provides the
    individuation unit that makes mixed drinks countable. -/
theorem mass_count_asymmetry
    (substancePred : α → Prop) (hCum : CUM substancePred)
    {n : ℕ} (recipe : Recipe α n) (μ : α → ℚ) (phase : α → Phase)
    {m₁ m₂ : α}
    (_hm₁ : mixedDrinkDen recipe μ phase m₁)
    (_hm₂ : mixedDrinkDen recipe μ phase m₂)
    (hDisc : ¬ SelfConnected (m₁ ⊔ m₂)) :
    CUM (substanceNounDen substancePred) ∧
    ¬ mixedDrinkDen recipe μ phase (m₁ ⊔ m₂) :=
  ⟨substanceNoun_cum substancePred hCum,
   not_cum_of_disconnected recipe μ phase _hm₁ _hm₂ hDisc⟩

-- ════════════════════════════════════════════════════
-- § 10. Bridge to Borer 2005: Individuation Without Atomicity
-- ════════════════════════════════════════════════════

/-! ### Why Div fails for mixed drinks

@cite{borer-2005}'s individuation operator `Div(P) = {x ∈ P | Atom(x)}`
produces count readings by restricting a cumulative root to mereological
atoms — entities with no proper parts. This works for standard count
nouns: "a beer" is an atomic portion of beer-stuff, "a cat" is an
atomic cat-individual.

Mixed drink nouns break this pattern. A margarita is NOT a mereological
atom: it has proper parts (the tequila, the triple sec, the lime juice).
These ingredient parts are strictly below the whole in the parthood
ordering, so `Atom x` fails. Borer's standard `Div` therefore excludes
mixed drinks from the individuated extension.

Moon's recipe semantics provides an **alternative individuation mechanism**
that fills the same structural role (Borer's Q head) but operates through
topological connectivity rather than mereological atomicity:

| Mechanism | Q-head content | Source of ¬CUM |
|-----------|---------------|----------------|
| Borer Div | `P ∧ Atom` | Atoms have no proper parts → QUA |
| Moon recipe | `MixedDrinkWitness` | ConnectedLiquid rejects disconnected sums |

Both break cumulativity of the root predicate (the universal semantic
role of Q), but through orthogonal properties of the parthood lattice:
the algebraic (atomicity) versus the topological (connectivity).
-/

open Interfaces.SyntaxSemantics.Borer2005 (Div div_qua)

/-- Mixed drinks are not mereological atoms: they have proper parts
    (their ingredient components).

    A `MixedDrinkWitness` for a recipe with n + 2 ≥ 2 ingredients
    assigns at least two disjoint parts (assign 0, assign 1) below x.
    If x were an atom, both would equal x — but then they would
    overlap, contradicting `disjoint`. -/
theorem mixedDrink_not_atom {n : ℕ}
    (recipe : Recipe α (n + 2))
    (μ : α → ℚ) (phase : α → Phase)
    {x : α} (hx : mixedDrinkDen recipe μ phase x) :
    ¬ Atom x := by
  intro hAtom
  obtain ⟨w⟩ := hx
  have h0 : w.assign 0 = x := hAtom (w.assign 0) (w.part_le 0)
  have h1 : w.assign 1 = x := hAtom (w.assign 1) (w.part_le 1)
  have hne : (0 : Fin (n + 2)) ≠ 1 := by simp
  have hDisj := w.disjoint 0 1 hne
  rw [h0, h1] at hDisj
  exact hDisj (Overlap.refl x)

/-- Borer's standard `Div` excludes mixed drinks from the individuated
    extension. Since mixed drinks are not atoms (`mixedDrink_not_atom`),
    no mixed drink entity satisfies `Div(DRINK)` for any predicate DRINK.

    This is not a bug in Borer's theory — it reveals that the Q head
    for mixed drink nouns must be filled with a DIFFERENT individuation
    mechanism than standard Div. Moon's recipe structure provides this. -/
theorem div_excludes_mixed_drinks {n : ℕ}
    (recipe : Recipe α (n + 2))
    (μ : α → ℚ) (phase : α → Phase)
    (DRINK : α → Prop)
    {x : α} (hx : mixedDrinkDen recipe μ phase x) :
    ¬ Div DRINK x := by
  intro ⟨_, hAtom⟩
  exact mixedDrink_not_atom recipe μ phase hx hAtom

/-- Both Borer's Div and Moon's recipe semantics break cumulativity
    of the root predicate — the universal semantic role of Borer's Q head.

    - `Div(P)` is QUA (stronger: no proper part satisfies the predicate)
    - `mixedDrinkDen` fails CUM (weaker: disconnected sums are rejected)

    The asymmetry in strength reflects the different mechanisms:
    atomicity is a STRONGER individuation than connectivity. Atoms have
    no proper parts at all; connected liquids can have proper parts
    (the ingredients) but cannot be merged across spatial gaps.

    This means mixed drink nouns are "less quantized" than standard
    count nouns — a prediction that aligns with Moon's observation
    that quantity judgments for mixed drinks are genuinely ambiguous
    across volume, portions, and measured parts (§4.3.2). Standard
    count nouns like "cat" admit no such ambiguity. -/
theorem both_break_cum
    {n : ℕ} (recipe : Recipe α n) (μ : α → ℚ) (phase : α → Phase)
    (P : α → Prop) :
    -- Div produces QUA (stronger than ¬CUM)
    QUA (Div P) ∧
    -- Recipe semantics blocks CUM (given disconnected instances)
    (∀ m₁ m₂ : α,
      mixedDrinkDen recipe μ phase m₁ →
      mixedDrinkDen recipe μ phase m₂ →
      ¬ SelfConnected (m₁ ⊔ m₂) →
      ¬ mixedDrinkDen recipe μ phase (m₁ ⊔ m₂)) :=
  ⟨div_qua P,
   fun _ _ h₁ h₂ hDisc => not_cum_of_disconnected recipe μ phase h₁ h₂ hDisc⟩

/-- Mixed drinks are divisible: a proper part of a mixed drink can
    itself be a mixed drink (half a margarita is still a margarita,
    if the ratios and connectivity are preserved).

    This means mixed drink predicates are NOT QUA — unlike Div-based
    count nouns, which are QUA by `div_qua`. Mixed drinks occupy a
    middle ground: ¬CUM (from ConnectedLiquid) but also ¬QUA (from
    divisibility). This is the formal content of Moon's claim that
    mixed drinks require a novel individuation mechanism beyond
    standard mereological atomicity.

    Compare Borer's `same_root_mass_and_count`: the root √BEER is
    CUM ∧ Div(√BEER) is QUA. For mixed drinks: the recipe denotation
    is ¬CUM ∧ ¬QUA — neither mass nor count in Borer's strict sense,
    but count in DISTRIBUTIONAL behavior (pluralizes, takes numerals). -/
theorem mixedDrink_not_qua {n : ℕ}
    (recipe : Recipe α (n + 2))
    (μ : α → ℚ) (phase : α → Phase)
    {x y : α}
    (hx : mixedDrinkDen recipe μ phase x)
    (hy : mixedDrinkDen recipe μ phase y)
    (hlt : y < x) :
    -- NOT a counterexample to QUA — this is satisfiable when a proper
    -- part of a mixed drink is also a mixed drink (e.g., half a
    -- margarita with preserved ratios and connectivity)
    ¬ QUA (mixedDrinkDen recipe μ phase) :=
  fun hQ => hQ x y hx hlt hy

-- ════════════════════════════════════════════════════
-- § 11. Instantiating the General Principle
-- ════════════════════════════════════════════════════

/-! ### Mixed drinks as an instance of topological non-cumulativity

The general principle (`Mereotopology.connectivity_middle_ground`)
states that ANY predicate entailing self-connectivity occupies the
¬CUM ∧ ¬QUA middle ground given appropriate witnesses. Mixed drink
denotations are an instance: `ConnectedLiquid` entails `SelfConnected`,
providing the connectivity constraint.

This shows Moon's result is not ad hoc — it follows from a structural
theorem about the interaction of semilattice join and topological
connectivity. Any predicate that requires spatial contiguity of its
instances will exhibit the same pattern: non-cumulativity from
topology rather than atomicity.
-/

/-- The connectivity constraint on mixed drink denotations: any mixed
    drink is self-connected (extracted from `ConnectedLiquid` in the
    witness). This is the hypothesis that feeds the general
    `connectivity_breaks_cum` principle. -/
theorem mixedDrinkDen_selfConnected {n : ℕ}
    (recipe : Recipe α n) (μ : α → ℚ) (phase : α → Phase)
    (x : α) (hx : mixedDrinkDen recipe μ phase x) :
    SelfConnected x := by
  obtain ⟨w⟩ := hx
  exact w.connected.selfConnected

/-- Mixed drinks are in the ¬CUM ∧ ¬QUA middle ground: an instance
    of the general `connectivity_middle_ground` theorem.

    The general principle requires:
    1. A connectivity constraint (`mixedDrinkDen_selfConnected`)
    2. Two instances with a disconnected join (CUM failure witnesses)
    3. An instance with a proper part also satisfying P (QUA failure)

    Moon's empirical contribution is establishing that mixed drinks
    satisfy all three conditions. The formal contribution of
    `connectivity_middle_ground` is showing this pattern is necessary
    — not contingent on the specific recipe structure but a consequence
    of ANY predicate that requires topological connectivity. -/
theorem mixedDrink_middle_ground {n : ℕ}
    (recipe : Recipe α (n + 2))
    (μ : α → ℚ) (phase : α → Phase)
    -- CUM failure: two mixed drinks with a disconnected join
    {a b : α}
    (ha : mixedDrinkDen recipe μ phase a)
    (hb : mixedDrinkDen recipe μ phase b)
    (hDisc : ¬ SelfConnected (a ⊔ b))
    -- QUA failure: a mixed drink with a proper part also a mixed drink
    {x y : α}
    (hx : mixedDrinkDen recipe μ phase x)
    (hy : mixedDrinkDen recipe μ phase y)
    (hlt : y < x) :
    ¬ CUM (mixedDrinkDen recipe μ phase) ∧
    ¬ QUA (mixedDrinkDen recipe μ phase) :=
  connectivity_middle_ground
    (mixedDrinkDen_selfConnected recipe μ phase)
    ha hb hDisc hx hy hlt

end Phenomena.Countability.Studies.Moon2026
