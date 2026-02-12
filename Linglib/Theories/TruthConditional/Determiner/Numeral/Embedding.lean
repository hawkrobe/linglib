import Linglib.Theories.TruthConditional.Determiner.Numeral.Semantics

/-!
# Numeral Embedding Semantics

Formal predictions of lower-bound vs exact numeral theories under embedding:
negation, modals, "exactly" modification, conditionals, exhaustification,
approximators ("almost"), focus particles ("only"), and QUD-convexity.

The theories agree on bare numerals at the numeral's own cardinality but diverge
sharply in embedded environments. All embedding functions are parameterized by
`NumeralTheory` so divergence theorems compare `LowerBound` vs `Exact` directly.

## Key Results

| Embedding | LowerBound | Exact | Diverge? |
|-----------|-----------|-----------|----------|
| ¬(three) at 4 | false (4≥3, so ¬ fails) | true (4≠3) | ✓ |
| ◇(two) at [3] | true (3≥2) | false (3≠2) | ✓ |
| □(three) at [3,4] | true (both ≥3) | false (4≠3) | ✓ |
| exactly(three) | informative | redundant | ✓ |
| almost(three) at 4 | false (polar blocks) | true (4≠3, proximal) | ✓ |
| ¬(three) convexity | convex (<3) | non-convex (≠3) | ✓ |
| EXH(two) at 2 | true (≥2 ∧ ¬≥3) | true (=2) | ✗ (convergence) |

## References

- Horn, L. (1972). On the Semantic Properties of Logical Operators in English.
- Kennedy, C. (2015). A "de-Fregean" semantics for modified and unmodified numerals.
  *Semantics & Pragmatics* 8(10), 1–44.
- Bylinina, L. & Nouwen, R. (2020). Numeral semantics. *Language and Linguistics
  Compass* 14(8).
- Nouwen, R. (2006). Remarks on the Polar Orientation of Almost.
- Coppock, E. & Beaver, D. (2014). Principles of the Exclusive Muddle.
- Solt, S. & Waldon, B. (2019). Numerals under negation. *Glossa* 4(1).
- Musolino, J. (2004). The semantics and acquisition of number words.
- Kaufmann, M. (2012). Interpreting Imperatives. Springer.
- Gajewski, J. (2007). Neg-raising and polarity.
- Meier, C. (2003). The meaning of too, enough, and so...that.
-/

namespace TruthConditional.Determiner.Numeral

-- ============================================================================
-- Section 1: BareNumeral Successor (for EXH alternatives)
-- ============================================================================

/-- Next-higher BareNumeral (for computing scalar alternatives). -/
def BareNumeral.succ : BareNumeral → Option BareNumeral
  | .one => some .two
  | .two => some .three
  | .three => some .four
  | .four => some .five
  | .five => none

-- ============================================================================
-- Section 2: Embedding Functions
-- ============================================================================

/-- Negation: ¬(numeral meaning).

"John doesn't have three children"
- LB: ¬(n ≥ 3) = n < 3
- BL: ¬(n = 3) = n ≠ 3 -/
def negatedMeaning (T : NumeralTheory) (w : BareNumeral) (n : Nat) : Bool :=
  !T.meaning w n

/-- Modal possibility: ∃ accessible world where numeral holds.

"You are allowed to eat two biscuits" -/
def possibilityMeaning (T : NumeralTheory) (w : BareNumeral)
    (accessible : List Nat) : Bool :=
  accessible.any (T.meaning w)

/-- Modal necessity: ∀ accessible worlds, numeral holds.

"You must read three books" -/
def necessityMeaning (T : NumeralTheory) (w : BareNumeral)
    (accessible : List Nat) : Bool :=
  accessible.all (T.meaning w)

/-- "Exactly" modification: always exact regardless of base theory.

"John has exactly three children" — always means =n. -/
def exactlyMeaning (w : BareNumeral) (n : Nat) : Bool :=
  maxMeaning .eq w.toNat n

/-- Conditional antecedent: material conditional with numeral in restrictor.

"If you have three children, you qualify"
Conditional is true when antecedent is false OR consequent is true. -/
def conditionalMeaning (T : NumeralTheory) (w : BareNumeral) (n : Nat)
    (consequent : Nat → Bool) : Bool :=
  !T.meaning w n || consequent n

/-- Exhaustivity operator: strengthens meaning by negating the next stronger alternative.

Under LB: EXH(≥n) = ≥n ∧ ¬(≥(n+1)) = =n
Under BL: EXH(=n) = =n (vacuous, since =n already excludes n+1) -/
def exh (T : NumeralTheory) (w : BareNumeral) (n : Nat) : Bool :=
  T.meaning w n &&
    match w.succ with
    | some w' => !T.meaning w' n
    | none => true

/-- EXH-under-◇: ◇(EXH(numeral)) — exhaustification below the modal.

"It's possible to eat exactly two..." -/
def exhUnderPossibility (T : NumeralTheory) (w : BareNumeral)
    (accessible : List Nat) : Bool :=
  accessible.any (exh T w)

/-- EXH-over-◇: EXH(◇(numeral)) — exhaustification above the modal.

"It's possible to eat at-least-two but NOT possible to eat at-least-three"
Captures Bylinina & Nouwen's (35)/(36) scope distinction. -/
def exhOverPossibility (T : NumeralTheory) (w : BareNumeral)
    (accessible : List Nat) : Bool :=
  possibilityMeaning T w accessible &&
    match w.succ with
    | some w' => !possibilityMeaning T w' accessible
    | none => true

-- ============================================================================
-- Section 3: Negation Divergence Theorems
-- ============================================================================

/-- Core negation divergence: above the numeral.

"John doesn't have three children" in world with 4 children:
- LB: ¬(4 ≥ 3) = false (4 is at-least-3, so negation fails)
- BL: ¬(4 = 3) = true (4 is not-exactly-3, so negation succeeds) -/
theorem negation_divergence_above :
    negatedMeaning LowerBound .three 4 = false ∧
    negatedMeaning Exact .three 4 = true := by native_decide

/-- Negation agreement below the numeral.

Both theories agree: "doesn't have three" is true for someone with 2. -/
theorem negation_agreement_below :
    negatedMeaning LowerBound .three 2 = true ∧
    negatedMeaning Exact .three 2 = true := by native_decide

/-- Negation agreement at the numeral.

Both theories agree: "doesn't have three" is false for someone with exactly 3. -/
theorem negation_agreement_at :
    negatedMeaning LowerBound .three 3 = false ∧
    negatedMeaning Exact .three 3 = false := by native_decide

/-- Entailment reversal under negation.

In isolation: BL entails LB (=3 → ≥3).
Under negation: ¬(≥3) entails ¬(=3) but not vice versa.
World 4 witnesses the asymmetry. -/
theorem entailment_reversal_under_negation :
    -- In isolation at world 4: LB true, BL false (LB is weaker)
    (LowerBound.meaning .three 4 = true ∧ Exact.meaning .three 4 = false) ∧
    -- Under negation at world 4: LB false, BL true (direction reverses)
    (negatedMeaning LowerBound .three 4 = false ∧
     negatedMeaning Exact .three 4 = true) := by native_decide

-- ============================================================================
-- Section 4: "Exactly" Redundancy Theorems
-- ============================================================================

/-- "Exactly" is redundant under Exact: "exactly three" = "three" (BL).

Both reduce to `maxMeaning .eq` — definitionally equal. -/
theorem exactly_redundant_exact (w : BareNumeral) (n : Nat) :
    exactlyMeaning w n = Exact.meaning w n := rfl

/-- "Exactly" is informative under LowerBound: restricts ≥3 to =3.

At world 4: LB says "three" is true (4 ≥ 3), but "exactly three" is false (4 ≠ 3). -/
theorem exactly_informative_lowerBound :
    LowerBound.meaning .three 4 = true ∧ exactlyMeaning .three 4 = false := by
  native_decide

/-- Full "exactly" comparison: agrees at n, diverges above under LB. -/
theorem exactly_full_comparison :
    -- At the numeral: both agree
    (LowerBound.meaning .three 3 = true ∧ exactlyMeaning .three 3 = true) ∧
    -- Above the numeral: LB differs from "exactly"
    (LowerBound.meaning .three 4 = true ∧ exactlyMeaning .three 4 = false) ∧
    -- "Exactly" always equals Exact
    (Exact.meaning .three 4 = false ∧ exactlyMeaning .three 4 = false) := by
  native_decide

-- ============================================================================
-- Section 5: Modal Divergence Theorems
-- ============================================================================

/-- Modal possibility: LB is satisfiable by more worlds.

"You are allowed to eat two biscuits" with only world 3 accessible:
- LB: ◇(≥2) at [3] = true (3 ≥ 2)
- BL: ◇(=2) at [3] = false (3 ≠ 2) -/
theorem modal_possibility_divergence :
    possibilityMeaning LowerBound .two [3] = true ∧
    possibilityMeaning Exact .two [3] = false := by native_decide

/-- Modal necessity: BL is harder to satisfy.

"You must read three books" with accessible worlds [3, 4]:
- LB: □(≥3) = true (3 ≥ 3 ∧ 4 ≥ 3)
- BL: □(=3) = false (4 ≠ 3) -/
theorem modal_necessity_divergence :
    necessityMeaning LowerBound .three [3, 4] = true ∧
    necessityMeaning Exact .three [3, 4] = false := by native_decide

/-- Modal necessity agreement: when all worlds match exactly. -/
theorem modal_necessity_agreement_exact :
    necessityMeaning LowerBound .three [3] = true ∧
    necessityMeaning Exact .three [3] = true := by native_decide

-- ============================================================================
-- Section 6: Conditional / Restrictor Divergence
-- ============================================================================

/-- Conditional antecedent divergence.

"If you have three children, you qualify" — does having 4 children trigger it?
- LB: 4 ≥ 3 = true, so antecedent holds
- BL: 4 = 3 = false, so antecedent fails (conditional vacuously true) -/
theorem conditional_restrictor_divergence :
    LowerBound.meaning .three 4 = true ∧
    Exact.meaning .three 4 = false := by native_decide

/-- Universal restrictor: different domains.

"Every student who read three books passed"
- LB restrictor includes {3, 4, 5, ...}
- BL restrictor includes only {3} -/
theorem restrictor_domain_differs :
    (LowerBound.meaning .three 3 = true ∧ LowerBound.meaning .three 4 = true) ∧
    (Exact.meaning .three 3 = true ∧ Exact.meaning .three 4 = false) := by
  native_decide

-- ============================================================================
-- Section 7: Exhaustivity (EXH) Theorems
-- ============================================================================

/-- EXH strengthens LowerBound: ≥n → =n.

EXH("two" under LB) at world 2 = true, at world 3 = false. -/
theorem exh_strengthens_lowerBound :
    exh LowerBound .two 2 = true ∧ exh LowerBound .two 3 = false := by native_decide

/-- EXH is vacuous under Exact: =n is already exact.

exh(BL, "two", n) = BL.meaning("two", n) for n ∈ {1, 2, 3}. -/
theorem exh_vacuous_exact :
    (exh Exact .two 1 = Exact.meaning .two 1) ∧
    (exh Exact .two 2 = Exact.meaning .two 2) ∧
    (exh Exact .two 3 = Exact.meaning .two 3) := by native_decide

/-- After EXH, both theories converge: EXH(LB) = EXH(BL) = =n.

This is the key result: pragmatic strengthening under LB converges
to the BL bare-numeral meaning. -/
theorem exh_convergence :
    (exh LowerBound .two 1 = exh Exact .two 1) ∧
    (exh LowerBound .two 2 = exh Exact .two 2) ∧
    (exh LowerBound .two 3 = exh Exact .two 3) := by native_decide

-- ============================================================================
-- Section 8: EXH Scope Interaction with Modals
-- ============================================================================

/-- EXH-under-◇ vs EXH-over-◇ diverge under LB with worlds [2, 3].

"You are allowed to eat two biscuits":
- EXH-under-◇: ◇(EXH(≥2)) = ◇(=2) — possible to eat exactly 2 → true
- EXH-over-◇: EXH(◇(≥2)) = ◇(≥2) ∧ ¬◇(≥3) — false (world 3 makes ◇(≥3) true) -/
theorem exh_scope_diverges_lowerBound :
    exhUnderPossibility LowerBound .two [2, 3] = true ∧
    exhOverPossibility LowerBound .two [2, 3] = false := by native_decide

/-- Under restricted access [2], EXH scope doesn't matter for LB. -/
theorem exh_scope_agrees_restricted :
    exhUnderPossibility LowerBound .two [2] = true ∧
    exhOverPossibility LowerBound .two [2] = true := by native_decide

/-- EXH-scope divergence under BL with worlds [2, 3].

- EXH-under-◇: ◇(EXH(=2)) = ◇(=2) — true (world 2)
- EXH-over-◇: EXH(◇(=2)) = ◇(=2) ∧ ¬◇(=3) — false (world 3 exists) -/
theorem exh_scope_diverges_exact :
    exhUnderPossibility Exact .two [2, 3] = true ∧
    exhOverPossibility Exact .two [2, 3] = false := by native_decide

-- ============================================================================
-- Section 9: "Almost" / Approximators (Nouwen 2006)
-- ============================================================================

/-- Proximity to numeral value: within distance 1. -/
def isProximal (m n : Nat) : Bool :=
  n + 1 == m || n == m || n == m + 1

/-- "Almost n": proximal to n but the numeral's meaning is false.

Under LB: close to n AND ¬(≥n) → only values below n
Under BL: close to n AND ¬(=n) → values above OR below n -/
def almostMeaning (T : NumeralTheory) (w : BareNumeral) (n : Nat) : Bool :=
  isProximal w.toNat n && !T.meaning w n

/-- "Almost three" diverges above: LB excludes 4, BL includes 4.

Under LB: 4 ≥ 3 so the polar component blocks it.
Under BL: 4 ≠ 3 and 4 is proximal to 3, so "almost three" holds. -/
theorem almost_diverges_above :
    almostMeaning LowerBound .three 4 = false ∧
    almostMeaning Exact .three 4 = true := by native_decide

/-- Full "almost" asymmetry: both agree on 2, diverge on 4. -/
theorem almost_asymmetry :
    -- Both agree: 2 is "almost three"
    (almostMeaning LowerBound .three 2 = true ∧
     almostMeaning Exact .three 2 = true) ∧
    -- LB: 4 is NOT "almost three" (4 ≥ 3, polar blocks)
    -- BL: 4 IS "almost three" (4 ≠ 3 and proximal)
    (almostMeaning LowerBound .three 4 = false ∧
     almostMeaning Exact .three 4 = true) := by native_decide

-- ============================================================================
-- Section 10: "Only" + Focus (Coppock & Beaver 2014)
-- ============================================================================

/-- "Only n" with numeral in focus: assertion + exclusion of stronger alternatives.

Truth-conditionally equivalent to EXH on the numeral meaning. -/
def onlyMeaning (T : NumeralTheory) (w : BareNumeral) (n : Nat) : Bool :=
  exh T w n

/-- "Only" on numerals is truth-conditionally equivalent to EXH. -/
theorem only_eq_exh (T : NumeralTheory) (w : BareNumeral) (n : Nat) :
    onlyMeaning T w n = exh T w n := rfl

/-- "Only" is truth-conditionally informative under LB, vacuous under BL.

"Only three students passed":
- Under LB: "three" at 4 is true (4≥3), but "only three" at 4 is false → informative
- Under BL: "three" at 4 is already false (4≠3), "only three" also false → vacuous -/
theorem only_informative_lowerBound :
    -- LB without "only": "three" is true at 4
    (LowerBound.meaning .three 4 = true) ∧
    -- LB with "only": "only three" is false at 4
    (onlyMeaning LowerBound .three 4 = false) ∧
    -- BL: "only" is vacuous (same result with or without)
    (Exact.meaning .three 4 = false ∧ onlyMeaning Exact .three 4 = false) := by
  native_decide

-- ============================================================================
-- Section 11: QUD-Convexity (Solt & Waldon 2019)
-- ============================================================================

/-- Worlds 0 through 5 for extended embedding tests. -/
def extendedWorlds : List Nat := [0, 1, 2, 3, 4, 5]

/-- Convexity: the set of true values on sorted worlds has no internal gaps.

For every pair of true values a < c, all intermediate b must also be true.
Non-convex denotations are predicted to be infelicitous in neutral QUD contexts
(Solt & Waldon 2019). -/
def isConvex (worlds : List Nat) (f : Nat → Bool) : Bool :=
  worlds.all fun a => worlds.all fun c =>
    if f a && f c && decide (a < c) then
      worlds.all fun b => !(decide (a < b) && decide (b < c)) || f b
    else true

/-- Negation convexity divergence (Solt & Waldon 2019).

¬(≥3) on [0..5] = {0,1,2} — convex (no gaps).
¬(=3) on [0..5] = {0,1,2,4,5} — non-convex (gap at 3).

BL correctly predicts "She doesn't have 40 sheep" is infelicitous
in neutral context (non-convex answer). LB incorrectly predicts felicity. -/
theorem negation_convexity_divergence :
    isConvex extendedWorlds (negatedMeaning LowerBound .three) = true ∧
    isConvex extendedWorlds (negatedMeaning Exact .three) = false := by
  native_decide

-- ============================================================================
-- Section 12: Heim-Kennedy Generalization (Heim 2000; Bylinina & Nouwen 2020 §6)
-- ============================================================================

/-- EXH scoped under a nominal quantifier (∃): each individual is exhaustified.

"Some students answered exactly three questions"
Under LB: ∃x[student(x) ∧ EXH(≥3)(answers(x))] = some student answered exactly 3.
This is the WEAK reading — per-student exhaustification. -/
def exhUnderNominalQ (T : NumeralTheory) (w : BareNumeral)
    (individuals : List Nat) : Bool :=
  individuals.any (exh T w)

/-- EXH scoped over a nominal quantifier (∃): exhaustifies the existential claim.

"Some students answered exactly three questions" — strong reading:
EXH(∃x[student(x) ∧ ≥3(answers(x))]) = some answered ≥3 AND none answered ≥4.
Heim-Kennedy BLOCKS this reading for numerals. -/
def exhOverNominalQ (T : NumeralTheory) (w : BareNumeral)
    (individuals : List Nat) : Bool :=
  individuals.any (T.meaning w) &&
    match w.succ with
    | some w' => !individuals.any (T.meaning w')
    | none => true

/-- Heim-Kennedy generalization: degree operators scope over modals but NOT over
nominal quantifiers (Heim 2000, B&N 2020 §6, examples 40–41).

With individuals [3, 4] (one answered 3, one answered 4):
- Weak reading (EXH under ∃): true — the student with 3 answered exactly 3.
- Strong reading (EXH over ∃): false — blocked because someone answered 4 (≥4).

Contrast with the modal case (`exh_scope_diverges_lowerBound`), where BOTH
EXH-under-◇ and EXH-over-◇ are available. The asymmetry is precisely what
the degree quantifier analysis (Kennedy 2015) predicts via QR constraints. -/
theorem heimKennedy_nominal_blocked :
    exhUnderNominalQ LowerBound .three [3, 4] = true ∧
    exhOverNominalQ LowerBound .three [3, 4] = false := by native_decide

/-- The modal case allows both scope configurations (contrast with Heim-Kennedy). -/
theorem modal_both_scopes_available :
    exhUnderPossibility LowerBound .two [2] = true ∧
    exhOverPossibility LowerBound .two [2] = true := by native_decide

/-- Under Exact, Heim-Kennedy is vacuous: EXH adds nothing to =n,
so neither scope yields a strong reading over nominal quantifiers. -/
theorem heimKennedy_vacuous_exact :
    exhUnderNominalQ Exact .three [3, 4] = true ∧
    exhOverNominalQ Exact .three [3, 4] = false := by native_decide

-- ============================================================================
-- Section 13: Additional Embedding Divergences
-- ============================================================================

/-- Imperative compliance divergence (Kaufmann 2012).

"Read three books!" — reading 5 books:
- LB: 5 ≥ 3 → compliant
- BL: 5 ≠ 3 → non-compliant -/
theorem imperative_compliance_divergence :
    LowerBound.meaning .three 5 = true ∧
    Exact.meaning .three 5 = false := by native_decide

/-- Neg-raising "doubt" reduces to negation (Gajewski 2007).

"I doubt three students passed" ≈ believe(¬(three passed)). -/
theorem doubt_as_neg_raising :
    negatedMeaning LowerBound .three 4 = false ∧
    negatedMeaning Exact .three 4 = true := by native_decide

/-- Factive presupposition divergence (Kiparsky & Kiparsky 1970).

"I'm surprised three students passed" presupposes the numeral meaning.
At world 5: LB presupposition satisfied (5 ≥ 3), BL violated (5 ≠ 3). -/
theorem factive_presupposition_divergence :
    LowerBound.meaning .three 5 = true ∧
    Exact.meaning .three 5 = false := by native_decide

/-- Degree "too" monotonicity (Meier 2003).

"Three is too many" — under LB, entails "four is too many" (both satisfy ≥3).
Under BL, no such entailment (4 does not satisfy =3). -/
theorem degree_too_monotonicity :
    -- Under LB: both 3 and 4 satisfy "three"
    (LowerBound.meaning .three 3 = true ∧ LowerBound.meaning .three 4 = true) ∧
    -- Under BL: only 3 satisfies "three"
    (Exact.meaning .three 3 = true ∧ Exact.meaning .three 4 = false) := by
  native_decide

/-- Acquisition prediction (Musolino 2004).

"Two horses jumped" when 3 jumped:
- LB: 3 ≥ 2 → should be accepted
- BL: 3 ≠ 2 → should be rejected
Children reject, supporting BL. -/
theorem acquisition_musolino :
    LowerBound.meaning .two 3 = true ∧
    Exact.meaning .two 3 = false := by native_decide

-- ============================================================================
-- Section 14: Summary Comparison Infrastructure
-- ============================================================================

/-- A prediction for a specific embedding environment. -/
structure EmbeddingPrediction where
  embedding : String
  lowerBoundResult : Bool
  exactResult : Bool
  deriving Repr, BEq

/-- Do the theories diverge for this prediction? -/
def EmbeddingPrediction.diverges (p : EmbeddingPrediction) : Bool :=
  p.lowerBoundResult != p.exactResult

/-- Summary of key embedding divergence points. -/
def embeddingDivergences : List EmbeddingPrediction :=
  [ { embedding := "¬(three) at world 4"
    , lowerBoundResult := negatedMeaning LowerBound .three 4
    , exactResult := negatedMeaning Exact .three 4 }
  , { embedding := "¬(three) at world 2"
    , lowerBoundResult := negatedMeaning LowerBound .three 2
    , exactResult := negatedMeaning Exact .three 2 }
  , { embedding := "◇(two) at [3]"
    , lowerBoundResult := possibilityMeaning LowerBound .two [3]
    , exactResult := possibilityMeaning Exact .two [3] }
  , { embedding := "□(three) at [3, 4]"
    , lowerBoundResult := necessityMeaning LowerBound .three [3, 4]
    , exactResult := necessityMeaning Exact .three [3, 4] }
  , { embedding := "three in restrictor at 4"
    , lowerBoundResult := LowerBound.meaning .three 4
    , exactResult := Exact.meaning .three 4 }
  , { embedding := "EXH(two) at world 3"
    , lowerBoundResult := exh LowerBound .two 3
    , exactResult := exh Exact .two 3 }
  , { embedding := "almost(three) at world 4"
    , lowerBoundResult := almostMeaning LowerBound .three 4
    , exactResult := almostMeaning Exact .three 4 }
  , { embedding := "¬(three) convexity on [0..5]"
    , lowerBoundResult := isConvex extendedWorlds (negatedMeaning LowerBound .three)
    , exactResult := isConvex extendedWorlds (negatedMeaning Exact .three) }
  , { embedding := "imperative: three at 5"
    , lowerBoundResult := LowerBound.meaning .three 5
    , exactResult := Exact.meaning .three 5 }
  , { embedding := "acquisition: two at 3"
    , lowerBoundResult := LowerBound.meaning .two 3
    , exactResult := Exact.meaning .two 3 }
  ]

/-- 8 of 10 test points show theory divergence. -/
theorem divergence_point_count :
    (embeddingDivergences.filter EmbeddingPrediction.diverges).length = 8 := by
  native_decide

end TruthConditional.Determiner.Numeral
