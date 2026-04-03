import Linglib.Theories.Semantics.Lexical.Noun.Kind.Generics
import Linglib.Core.Genericity

/-!
# @cite{nickel-2009}: Generics and the Ways of Normality

Bernhard Nickel, "Generics and the Ways of Normality",
*Linguistics and Philosophy* 31 (2009), 629–648.

## The Problem: Conjunctive Generics

Nickel criticizes majority-based views of generics (including
@cite{cohen-1999a}'s probability-based GEN) by showing they cannot
handle conjunctive generics like:

    (1) Elephants live in Africa and Asia.

If (1) is equivalent to the sentential conjunction:

    (2) Elephants live in Africa AND Elephants live in Asia.

then a majority-based view would require both conjuncts to hold with
prevalence > 0.5 over the same domain. But African elephants and Asian
elephants are disjoint populations — most elephants can't live in BOTH
places. So the majority view predicts (1) is false, contrary to
speaker judgments.

## Nickel's Solution: Ways of Being Normal

Nickel proposes that normality is not a single binary predicate but
comes in multiple **ways**. For the elephant case:

- **Way w₁**: normal w.r.t. habitat → lives in Africa
- **Way w₂**: normal w.r.t. habitat → lives in Asia

GEN existentially quantifies over ways of being normal, then
universally quantifies over entities that are normal in that way:

    GEN[A][F] is true iff
    ∃w (way of being normal for As w.r.t. F).
      ∀x. normalIn(x, w) → F(x)

Conjunctive generics can then use different normality ways for each
conjunct:

    (1) is true iff
    (∃w₁. ∀x. normalIn(x, w₁) → livesInAfrica(x)) ∧
    (∃w₂. ∀x. normalIn(x, w₂) → livesInAsia(x))

This is discussed in the introduction to *Genericity* (OUP 2013).
-/

namespace Phenomena.Generics.Studies.Nickel2009

open Semantics.Lexical.Noun.Kind.Generics (prevalence thresholdGeneric)

-- Ways of Being Normal

/-- A way of being normal — an index that selects which entities count
    as "normal" for a given generalization. Different generic claims can
    appeal to different normality ways. -/
structure NormalcyWay where
  id : Nat
  deriving DecidableEq, Repr

/-- An entity in the domain of a generic. -/
structure Entity where
  id : Nat
  deriving DecidableEq, Repr

/-- Whether an entity is normal in a given way. -/
abbrev NormalIn := Entity → NormalcyWay → Bool

/-- A property of entities. -/
abbrev Property := Entity → Bool

-- Nickel's GEN

/-- Nickel's GEN with way-indexed normality:

    GEN[restrictor][scope] is true iff there exists a way of being normal
    such that all entities that are normal in that way AND satisfy the
    restrictor also satisfy the scope.

    The key innovation: the existential quantification over normality ways
    allows different conjuncts of a conjunctive generic to use different
    ways. -/
def nickelGEN
    (entities : List Entity)
    (normalIn : NormalIn)
    (ways : List NormalcyWay)
    (restrictor : Property)
    (scope : Property)
    : Bool :=
  ways.any λ w =>
    entities.all λ e =>
      !(restrictor e && normalIn e w) || scope e

/-- Conjunctive generic: both GEN[A][F₁] and GEN[A][F₂] hold,
    potentially via different normality ways. -/
def nickelConjunctiveGEN
    (entities : List Entity)
    (normalIn : NormalIn)
    (ways : List NormalcyWay)
    (restrictor : Property)
    (scope1 scope2 : Property)
    : Bool :=
  nickelGEN entities normalIn ways restrictor scope1 &&
  nickelGEN entities normalIn ways restrictor scope2

-- The Majority-Based View (for comparison)

/-- Majority-based GEN (@cite{cohen-1999a}'s view): generic is true iff
    prevalence exceeds 1/2. Structurally identical to `cohenGEN` in
    `Cohen1999.lean` — both are `thresholdGeneric` with θ = 1/2, just
    instantiated at different domain types (Entity here, Situation there). -/
def majorityGEN
    (entities : List Entity)
    (restrictor : Property)
    (scope : Property)
    : Bool :=
  thresholdGeneric entities restrictor scope (1/2)

-- The Elephant Example

section Elephants

/-- 10 elephants: 6 African (ids 0-5), 4 Asian (ids 6-9). -/
def elephants : List Entity :=
  (List.range 10).map (λ n => ⟨n⟩)

def isElephant : Property := λ _ => true

def livesInAfrica : Property := λ e => e.id < 6
def livesInAsia : Property := λ e => e.id ≥ 6

-- Two ways of being normal w.r.t. habitat
def africanWay : NormalcyWay := ⟨1⟩
def asianWay : NormalcyWay := ⟨2⟩
def ways : List NormalcyWay := [africanWay, asianWay]

/-- Normal in the "African way" = African elephants;
    Normal in the "Asian way" = Asian elephants. -/
def elephantNormalIn : NormalIn := λ e w =>
  match w.id with
  | 1 => e.id < 6   -- African way: African elephants are normal
  | 2 => e.id ≥ 6   -- Asian way: Asian elephants are normal
  | _ => false

end Elephants

-- The Bears Example (paper's primary motivating case, ex. 2a)

section Bears

/-- 20 bears across 4 continents: North America (0-4), South America (5-9),
    Europe (10-14), Asia (15-19). The majority view fails for ALL four
    habitat conjuncts since each subpopulation is only 5/20 = 25%. -/
def bears : List Entity :=
  (List.range 20).map (λ n => ⟨n⟩)

def isBear : Property := λ _ => true

def bearNA : Property := λ e => e.id < 5
def bearSA : Property := λ e => e.id ≥ 5 && e.id < 10
def bearEU : Property := λ e => e.id ≥ 10 && e.id < 15
def bearAS : Property := λ e => e.id ≥ 15

def naWay : NormalcyWay := ⟨1⟩
def saWay : NormalcyWay := ⟨2⟩
def euWay : NormalcyWay := ⟨3⟩
def asWay : NormalcyWay := ⟨4⟩
def bearWays : List NormalcyWay := [naWay, saWay, euWay, asWay]

def bearNormalIn : NormalIn := λ e w =>
  match w.id with
  | 1 => e.id < 5
  | 2 => e.id ≥ 5 && e.id < 10
  | 3 => e.id ≥ 10 && e.id < 15
  | 4 => e.id ≥ 15
  | _ => false

end Bears

-- Incompatibility Between Ways

/-- Normality ways are pairwise incompatible: no entity in the domain is
    normal in two distinct ways simultaneously. The paper (p.643) states:
    "Being F-normal in one way is (perhaps always) incompatible with being
    F-normal in any other way." -/
def waysIncompatible
    (entities : List Entity)
    (normalIn : NormalIn)
    (ways : List NormalcyWay)
    : Bool :=
  entities.all λ e =>
    ways.all λ w₁ =>
      ways.all λ w₂ =>
        (w₁ == w₂) || !(normalIn e w₁ && normalIn e w₂)

-- Key Theorems

/-- The majority view fails for the elephant example: "Elephants live in Asia"
    is false under majority semantics because only 4/10 < 1/2 are Asian. -/
theorem majority_fails_elephant_asia :
    majorityGEN elephants isElephant livesInAsia = false := by native_decide

/-- The conjunctive generic fails under the majority view. -/
theorem majority_fails_conjunction :
    (majorityGEN elephants isElephant livesInAfrica &&
     majorityGEN elephants isElephant livesInAsia) = false := by native_decide

/-- Nickel's view succeeds for the elephant conjunction. -/
theorem nickel_handles_elephant_conjunction :
    nickelConjunctiveGEN elephants elephantNormalIn ways
      isElephant livesInAfrica livesInAsia = true := by native_decide

/-- The bears example (paper's ex. 2a): majority view fails for ALL four
    habitat conjuncts (each is 25%), while Nickel's view succeeds. -/
theorem bears_majority_fails_nickel_succeeds :
    majorityGEN bears isBear bearNA = false ∧
    majorityGEN bears isBear bearSA = false ∧
    majorityGEN bears isBear bearEU = false ∧
    majorityGEN bears isBear bearAS = false ∧
    nickelGEN bears bearNormalIn bearWays isBear bearNA = true ∧
    nickelGEN bears bearNormalIn bearWays isBear bearSA = true ∧
    nickelGEN bears bearNormalIn bearWays isBear bearEU = true ∧
    nickelGEN bears bearNormalIn bearWays isBear bearAS = true := by native_decide

/-- Normality ways are pairwise incompatible in both examples. -/
theorem elephant_ways_incompatible :
    waysIncompatible elephants elephantNormalIn ways = true ∧
    waysIncompatible bears bearNormalIn bearWays = true := by native_decide

-- Connection to Traditional GEN

/-- Nickel's GEN with a single normality way reduces to traditional GEN:
    if there is only one way of being normal, the existential quantification
    is trivial and we get back ∀x. normal(x) ∧ restrictor(x) → scope(x). -/
theorem nickel_single_way_is_traditional
    (entities : List Entity)
    (normalIn : NormalIn)
    (w : NormalcyWay)
    (restrictor scope : Property)
    : nickelGEN entities normalIn [w] restrictor scope =
      entities.all (λ e => !(restrictor e && normalIn e w) || scope e) := by
  simp only [nickelGEN, List.any_cons, List.any_nil, Bool.or_false]

/-!
## Summary: Three Views of Normality

| View | Normality | GEN formula | Handles elephants? |
|------|-----------|-------------|-------------------|
| @cite{cohen-1999a} | Probability > 0.5 | P(Q\|P) > 0.5 | No |
| @cite{asher-pelletier-2012} | Modal ordering | ∀w ≤ w₀. P(x,w) → Q(x,w) | Partially |
| @cite{nickel-2009} | Ways of being normal | ∃w. ∀x. normal(x,w) → Q(x) | Yes |

The three views are formalized in:
- `Cohen1999.lean` (probability)
- `Comparisons/GenericModality.lean` (modal)
- This file (way-indexed normality)
-/

end Phenomena.Generics.Studies.Nickel2009
