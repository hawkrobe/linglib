import Linglib.Theories.Semantics.Lexical.Adjective.Aggregation
import Linglib.Phenomena.Gradability.Studies.Sassoon2013

/-!
# @cite{dambrosio-hedden-2024}

D'Ambrosio, J. & Hedden, B. (2024). Multidimensional Adjectives.
*Australasian Journal of Philosophy* 102(2): 253–277.
DOI: 10.1080/00048402.2023.2277923

## Key Claims

1. Multidimensional adjectives require explicit **aggregation functions**
   mapping dimensional assessments to overall assessments (§3).

2. Arrow's impossibility theorem (adapted): under constraints ONC + WO +
   U + P + I + D, no aggregation function exists for ≥3 dimensions and
   ≥3 objects. Multidimensional adjectives would be **incoherent** (§4.1).

3. Escape routes determine aggregation type (§4.2–4.3):
   - Reject WO (transitivity) → Majority Rule (May 1952)
   - Reject WO (completeness) → Strong Pareto Rule (Weymark 1984)
   - Reject ONC, accept IUC → Utilitarian / weighted sum (Sen 1970)
   - Reject ONC, accept RNC → Cobb-Douglas / weighted product (Tsui-Weymark 1997)

4. Multiple admissible aggregation functions → **comparative vagueness**,
   a source of vagueness specific to multidimensionality (§4.3).

## Formalization

- §1: Arrow's constraints
- §2: *athletic* example (majority rule and weighted aggregation)
- §3: Comparative vagueness from weight multiplicity
- §4: Connection to @cite{sassoon-2013} (binding types = counting)
-/

namespace Phenomena.Gradability.Studies.DAmbrosioHedden2024

open Semantics.Lexical.Adjective (DimensionBindingType conjunctiveBinding
  disjunctiveBinding)
open Semantics.Degree.Aggregation
open Semantics.Lexical.Adjective.Aggregation

-- ════════════════════════════════════════════════════
-- § 1. Arrow's Constraints
-- ════════════════════════════════════════════════════

/-- Arrow's constraints on dimensional aggregation (§4, adapted from
    social choice theory). -/
structure ArrowConstraints where
  /-- (U) Defined for all logically possible value profiles. -/
  unrestrictedDomain : Bool
  /-- (WO) Output is a weak ordering (reflexive, transitive, complete). -/
  weakOrdering : Bool
  /-- (P) Unanimous dimensional ranking → same overall ranking. -/
  weakPareto : Bool
  /-- (I) Overall ranking of x vs y depends only on their dim values. -/
  independence : Bool
  /-- (D) No single dimension dictates the overall ranking. -/
  nonDictatorship : Bool
  /-- (ONC) Only ordinal info used (invariant under monotone transforms). -/
  ordinalNonComparability : Bool
  deriving Repr, BEq

/-- The full Arrovian constraint set (§4.1). -/
def fullArrow : ArrowConstraints where
  unrestrictedDomain := true
  weakOrdering := true
  weakPareto := true
  independence := true
  nonDictatorship := true
  ordinalNonComparability := true

/-- `fullArrow` enables all six constraints. Arrow's impossibility
    theorem (adapted, §4.1) says these are jointly unsatisfiable for
    ≥3 dimensions and ≥3 objects — at least one must be abandoned,
    and each escape route yields a different aggregation type.

    This theorem only records the constraint *specification*; the
    impossibility proof itself would require formalizing aggregation
    over orderings and is not attempted here. -/
theorem fullArrow_all_enabled :
    fullArrow.unrestrictedDomain = true ∧
    fullArrow.weakOrdering = true ∧
    fullArrow.weakPareto = true ∧
    fullArrow.independence = true ∧
    fullArrow.nonDictatorship = true ∧
    fullArrow.ordinalNonComparability = true := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. *Athletic* Example
-- ════════════════════════════════════════════════════

/-! The adjective *athletic* has three dimensions: speed (F₁), agility (F₂),
    and endurance (F₃) (§3). We model two people and show how different
    aggregation mechanisms yield different verdicts. -/

inductive Person where | alice | bob
  deriving Repr, DecidableEq, BEq

/-- Dimensional profiles for *athletic*:
    - Alice: fast, agile, not enduring
    - Bob: not fast, not agile, enduring -/
def athleticDims : List (Person → Bool) :=
  [fun p => p == .alice,    -- speed: Alice fast, Bob slow
   fun p => p == .alice,    -- agility: Alice agile, Bob not
   fun p => p == .bob]      -- endurance: Bob enduring, Alice not

/-- Majority rule: Alice is athletic (2 of 3 dims). -/
theorem alice_athletic_majority :
    majorityBinding athleticDims .alice = true := by native_decide

/-- Majority rule: Bob is NOT athletic (1 of 3 dims). -/
theorem bob_not_athletic_majority :
    majorityBinding athleticDims .bob = false := by native_decide

/-- Under speed-heavy weights [3, 1, 1] with θ = 3, Alice IS athletic
    (score = 3 + 1 + 0 = 4 ≥ 3) but Bob is NOT (score = 0 + 0 + 1 = 1). -/
theorem alice_athletic_speed_heavy :
    weightedBinding [3, 1, 1] 3 athleticDims .alice = true := by native_decide

theorem bob_not_athletic_speed_heavy :
    weightedBinding [3, 1, 1] 3 athleticDims .bob = false := by native_decide

/-- Under endurance-heavy weights [1, 1, 3] with θ = 3, Alice is NOT
    athletic (score = 1 + 1 + 0 = 2 < 3) but Bob IS (0 + 0 + 3 = 3 ≥ 3). -/
theorem alice_not_athletic_endurance_heavy :
    weightedBinding [1, 1, 3] 3 athleticDims .alice = false := by native_decide

theorem bob_athletic_endurance_heavy :
    weightedBinding [1, 1, 3] 3 athleticDims .bob = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 3. Comparative Vagueness
-- ════════════════════════════════════════════════════

/-! When multiple weight vectors are admissible, the comparative form
    "x is more athletic than y" is **vague**: different admissible
    aggregation functions rank the entities differently.

    This is D&H's central prediction (§4.3): multidimensionality
    generates comparative vagueness through admissibility multiplicity. -/

/-- Under speed-heavy weights, Alice outscores Bob. -/
theorem speed_heavy_alice_wins :
    weightedScore [3, 1, 1] (boolMeasures athleticDims) .alice >
    weightedScore [3, 1, 1] (boolMeasures athleticDims) .bob := by native_decide

/-- Under endurance-heavy weights, Bob outscores Alice. -/
theorem endurance_heavy_bob_wins :
    weightedScore [1, 1, 3] (boolMeasures athleticDims) .bob >
    weightedScore [1, 1, 3] (boolMeasures athleticDims) .alice := by native_decide

/-- Comparative vagueness: when both weight vectors are admissible,
    "Alice is more athletic than Bob" is **indeterminate** — one
    aggregation function says yes, the other says no. -/
theorem comparative_vagueness :
    -- Speed-heavy: Alice > Bob
    weightedScore [3, 1, 1] (boolMeasures athleticDims) .alice >
    weightedScore [3, 1, 1] (boolMeasures athleticDims) .bob ∧
    -- Endurance-heavy: Bob > Alice
    weightedScore [1, 1, 3] (boolMeasures athleticDims) .bob >
    weightedScore [1, 1, 3] (boolMeasures athleticDims) .alice :=
  ⟨speed_heavy_alice_wins, endurance_heavy_bob_wins⟩

-- ════════════════════════════════════════════════════
-- § 4. Connection to Sassoon 2013
-- ════════════════════════════════════════════════════

/-! @cite{sassoon-2013}'s framework classifies binding as conjunctive
    (∀), disjunctive (∃), or mixed (dimension counting). D&H show all
    three are **counting aggregation** — a single escape route from
    Arrow's theorem. Utilitarian aggregation (weighted sum) is a
    genuinely different mechanism that Sassoon's typology misses. -/

/-- All of Sassoon 2013's binding types are counting aggregation. -/
theorem sassoon_framework_is_counting :
    ∀ b : DimensionBindingType, toAggregationType b = .counting :=
  sassoon_all_counting

/-- Utilitarian aggregation is NOT counting — it is a categorically
    different escape route from Arrow's impossibility. -/
theorem utilitarian_not_counting :
    AggregationType.utilitarian ≠ .counting := by decide

/-- *healthy* under conjunctive binding: must satisfy ALL dimensions.
    A person healthy on musculoskeletal and cardiovascular but with
    disease present is NOT healthy. -/
theorem healthy_conjunctive_rejects_partial :
    conjunctiveBinding
      [fun (_ : Unit) => true,   -- musculoskeletal: good
       fun (_ : Unit) => true,   -- cardiovascular: good
       fun (_ : Unit) => false]  -- freedom from disease: no
      () = false := rfl

/-- But under counting with k = 2, the same person IS healthy
    (passes on 2 of 3 dimensions). Counting and conjunctive diverge. -/
theorem counting_accepts_partial :
    countBinding 2
      [fun (_ : Unit) => true,
       fun (_ : Unit) => true,
       fun (_ : Unit) => false]
      () = true := by native_decide

end Phenomena.Gradability.Studies.DAmbrosioHedden2024
