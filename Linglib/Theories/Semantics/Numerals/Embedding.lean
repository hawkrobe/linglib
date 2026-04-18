import Linglib.Theories.Semantics.Numerals.Basic

/-!
# Numeral Embedding Semantics
@cite{bylinina-nouwen-2020} @cite{coppock-beaver-2014} @cite{gajewski-2007} @cite{horn-1972} @cite{kaufmann-2012} @cite{kennedy-2015} @cite{meier-2003} @cite{musolino-2004} @cite{nouwen-2006} @cite{penka-2006} @cite{solt-waldon-2019} @cite{kiparsky-kiparsky-1970} @cite{heim-2000}

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

-/

namespace Semantics.Numerals

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
def negatedMeaning (T : NumeralTheory) (w : BareNumeral) (n : Nat) : Prop :=
  ¬ T.meaning w n

instance (T : NumeralTheory) (w : BareNumeral) (n : Nat) :
    Decidable (negatedMeaning T w n) := by
  unfold negatedMeaning; infer_instance

/-- Modal possibility: ∃ accessible world where numeral holds.

"You are allowed to eat two biscuits" -/
def possibilityMeaning (T : NumeralTheory) (w : BareNumeral)
    (accessible : List Nat) : Prop :=
  ∃ n ∈ accessible, T.meaning w n

instance (T : NumeralTheory) (w : BareNumeral) (accessible : List Nat) :
    Decidable (possibilityMeaning T w accessible) := by
  unfold possibilityMeaning; infer_instance

/-- Modal necessity: ∀ accessible worlds, numeral holds.

"You must read three books" -/
def necessityMeaning (T : NumeralTheory) (w : BareNumeral)
    (accessible : List Nat) : Prop :=
  ∀ n ∈ accessible, T.meaning w n

instance (T : NumeralTheory) (w : BareNumeral) (accessible : List Nat) :
    Decidable (necessityMeaning T w accessible) := by
  unfold necessityMeaning; infer_instance

/-- "Exactly" modification: always exact regardless of base theory.

"John has exactly three children" — always means =n. -/
def exactlyMeaning (w : BareNumeral) (n : Nat) : Prop :=
  bareMeaning w.toNat n

instance (w : BareNumeral) (n : Nat) : Decidable (exactlyMeaning w n) := by
  unfold exactlyMeaning; infer_instance

/-- Conditional antecedent: material conditional with numeral in restrictor.

"If you have three children, you qualify"
Conditional is true when antecedent is false OR consequent is true. -/
def conditionalMeaning (T : NumeralTheory) (w : BareNumeral) (n : Nat)
    (consequent : Nat → Prop) : Prop :=
  ¬ T.meaning w n ∨ consequent n

instance (T : NumeralTheory) (w : BareNumeral) (n : Nat) (consequent : Nat → Prop)
    [Decidable (consequent n)] : Decidable (conditionalMeaning T w n consequent) := by
  unfold conditionalMeaning; infer_instance

/-- Exhaustivity operator: strengthens meaning by negating the next stronger alternative.

Under LB: EXH(≥n) = ≥n ∧ ¬(≥(n+1)) = =n
Under BL: EXH(=n) = =n (vacuous, since =n already excludes n+1) -/
def exh (T : NumeralTheory) (w : BareNumeral) (n : Nat) : Prop :=
  T.meaning w n ∧
    match w.succ with
    | some w' => ¬ T.meaning w' n
    | none => True

instance (T : NumeralTheory) (w : BareNumeral) (n : Nat) : Decidable (exh T w n) := by
  unfold exh
  generalize w.succ = succ
  cases succ <;> infer_instance

/-- EXH-under-◇: ◇(EXH(numeral)) — exhaustification below the modal.

"It's possible to eat exactly two..." -/
def exhUnderPossibility (T : NumeralTheory) (w : BareNumeral)
    (accessible : List Nat) : Prop :=
  ∃ n ∈ accessible, exh T w n

instance (T : NumeralTheory) (w : BareNumeral) (accessible : List Nat) :
    Decidable (exhUnderPossibility T w accessible) := by
  unfold exhUnderPossibility; infer_instance

/-- EXH-over-◇: EXH(◇(numeral)) — exhaustification above the modal.

"It's possible to eat at-least-two but NOT possible to eat at-least-three"
Captures Bylinina & Nouwen's (35)/(36) scope distinction. -/
def exhOverPossibility (T : NumeralTheory) (w : BareNumeral)
    (accessible : List Nat) : Prop :=
  possibilityMeaning T w accessible ∧
    match w.succ with
    | some w' => ¬ possibilityMeaning T w' accessible
    | none => True

instance (T : NumeralTheory) (w : BareNumeral) (accessible : List Nat) :
    Decidable (exhOverPossibility T w accessible) := by
  unfold exhOverPossibility
  generalize w.succ = succ
  cases succ <;> infer_instance

-- ============================================================================
-- Section 3: Negation Divergence Theorems
-- ============================================================================

/-- Core negation divergence: above the numeral.

"John doesn't have three children" in world with 4 children:
- LB: ¬(4 ≥ 3) = false (4 is at-least-3, so negation fails)
- BL: ¬(4 = 3) = true (4 is not-exactly-3, so negation succeeds) -/
theorem negation_divergence_above :
    ¬ negatedMeaning LowerBound .three 4 ∧
    negatedMeaning Exact .three 4 := by decide

/-- Negation agreement below the numeral.

Both theories agree: "doesn't have three" is true for someone with 2. -/
theorem negation_agreement_below :
    negatedMeaning LowerBound .three 2 ∧
    negatedMeaning Exact .three 2 := by decide

/-- Negation agreement at the numeral.

Both theories agree: "doesn't have three" is false for someone with exactly 3. -/
theorem negation_agreement_at :
    ¬ negatedMeaning LowerBound .three 3 ∧
    ¬ negatedMeaning Exact .three 3 := by decide

/-- Entailment reversal under negation.

In isolation: BL entails LB (=3 → ≥3).
Under negation: ¬(≥3) entails ¬(=3) but not vice versa.
World 4 witnesses the asymmetry. -/
theorem entailment_reversal_under_negation :
    -- In isolation at world 4: LB true, BL false (LB is weaker)
    (LowerBound.meaning .three 4 ∧ ¬ Exact.meaning .three 4) ∧
    -- Under negation at world 4: LB false, BL true (direction reverses)
    (¬ negatedMeaning LowerBound .three 4 ∧
     negatedMeaning Exact .three 4) := by decide

-- ============================================================================
-- Section 4: "Exactly" Redundancy Theorems
-- ============================================================================

/-- "Exactly" is redundant under Exact: "exactly three" = "three" (BL).

Both reduce to `bareMeaning` — definitionally equal. -/
theorem exactly_redundant_exact (w : BareNumeral) (n : Nat) :
    exactlyMeaning w n ↔ Exact.meaning w n := Iff.rfl

/-- "Exactly" is informative under LowerBound: restricts ≥3 to =3.

At world 4: LB says "three" is true (4 ≥ 3), but "exactly three" is false (4 ≠ 3). -/
theorem exactly_informative_lowerBound :
    LowerBound.meaning .three 4 ∧ ¬ exactlyMeaning .three 4 := by
  decide

/-- Full "exactly" comparison: agrees at n, diverges above under LB. -/
theorem exactly_full_comparison :
    -- At the numeral: both agree
    (LowerBound.meaning .three 3 ∧ exactlyMeaning .three 3) ∧
    -- Above the numeral: LB differs from "exactly"
    (LowerBound.meaning .three 4 ∧ ¬ exactlyMeaning .three 4) ∧
    -- "Exactly" always equals Exact
    (¬ Exact.meaning .three 4 ∧ ¬ exactlyMeaning .three 4) := by
  decide

-- ============================================================================
-- Section 5: Modal Divergence Theorems
-- ============================================================================

/-- Modal possibility: LB is satisfiable by more worlds.

"You are allowed to eat two biscuits" with only world 3 accessible:
- LB: ◇(≥2) at [3] = true (3 ≥ 2)
- BL: ◇(=2) at [3] = false (3 ≠ 2) -/
theorem modal_possibility_divergence :
    possibilityMeaning LowerBound .two [3] ∧
    ¬ possibilityMeaning Exact .two [3] := by decide

/-- Modal necessity: BL is harder to satisfy.

"You must read three books" with accessible worlds [3, 4]:
- LB: □(≥3) = true (3 ≥ 3 ∧ 4 ≥ 3)
- BL: □(=3) = false (4 ≠ 3) -/
theorem modal_necessity_divergence :
    necessityMeaning LowerBound .three [3, 4] ∧
    ¬ necessityMeaning Exact .three [3, 4] := by decide

/-- Modal necessity agreement: when all worlds match exactly. -/
theorem modal_necessity_agreement_exact :
    necessityMeaning LowerBound .three [3] ∧
    necessityMeaning Exact .three [3] := by decide

-- ============================================================================
-- Section 6: Conditional / Restrictor Divergence
-- ============================================================================

/-- Conditional antecedent divergence.

"If you have three children, you qualify" — does having 4 children trigger it?
- LB: 4 ≥ 3 = true, so antecedent holds
- BL: 4 = 3 = false, so antecedent fails (conditional vacuously true) -/
theorem conditional_restrictor_divergence :
    LowerBound.meaning .three 4 ∧
    ¬ Exact.meaning .three 4 := by decide

/-- Universal restrictor: different domains.

"Every student who read three books passed"
- LB restrictor includes {3, 4, 5,...}
- BL restrictor includes only {3} -/
theorem restrictor_domain_differs :
    (LowerBound.meaning .three 3 ∧ LowerBound.meaning .three 4) ∧
    (Exact.meaning .three 3 ∧ ¬ Exact.meaning .three 4) := by
  decide

-- ============================================================================
-- Section 7: Exhaustivity (EXH) Theorems
-- ============================================================================

/-- EXH strengthens LowerBound: ≥n → =n.

EXH("two" under LB) at world 2 = true, at world 3 = false. -/
theorem exh_strengthens_lowerBound :
    exh LowerBound .two 2 ∧ ¬ exh LowerBound .two 3 := by decide

/-- EXH is vacuous under Exact: =n is already exact.

exh(BL, "two", n) = BL.meaning("two", n) for n ∈ {1, 2, 3}. -/
theorem exh_vacuous_exact :
    (exh Exact .two 1 ↔ Exact.meaning .two 1) ∧
    (exh Exact .two 2 ↔ Exact.meaning .two 2) ∧
    (exh Exact .two 3 ↔ Exact.meaning .two 3) := by decide

/-- After EXH, both theories converge: EXH(LB) = EXH(BL) = =n.

This is the key result: pragmatic strengthening under LB converges
to the BL bare-numeral meaning. -/
theorem exh_convergence :
    (exh LowerBound .two 1 ↔ exh Exact .two 1) ∧
    (exh LowerBound .two 2 ↔ exh Exact .two 2) ∧
    (exh LowerBound .two 3 ↔ exh Exact .two 3) := by decide

-- ============================================================================
-- Section 8: EXH Scope Interaction with Modals
-- ============================================================================

/-- EXH-under-◇ vs EXH-over-◇ diverge under LB with worlds [2, 3].

"You are allowed to eat two biscuits":
- EXH-under-◇: ◇(EXH(≥2)) = ◇(=2) — possible to eat exactly 2 → true
- EXH-over-◇: EXH(◇(≥2)) = ◇(≥2) ∧ ¬◇(≥3) — false (world 3 makes ◇(≥3) true) -/
theorem exh_scope_diverges_lowerBound :
    exhUnderPossibility LowerBound .two [2, 3] ∧
    ¬ exhOverPossibility LowerBound .two [2, 3] := by decide

/-- Under restricted access [2], EXH scope doesn't matter for LB. -/
theorem exh_scope_agrees_restricted :
    exhUnderPossibility LowerBound .two [2] ∧
    exhOverPossibility LowerBound .two [2] := by decide

/-- EXH-scope divergence under BL with worlds [2, 3].

- EXH-under-◇: ◇(EXH(=2)) = ◇(=2) — true (world 2)
- EXH-over-◇: EXH(◇(=2)) = ◇(=2) ∧ ¬◇(=3) — false (world 3 exists) -/
theorem exh_scope_diverges_exact :
    exhUnderPossibility Exact .two [2, 3] ∧
    ¬ exhOverPossibility Exact .two [2, 3] := by decide

-- ============================================================================
-- Section 9: "Almost" / Approximators (@cite{penka-2006} @cite{nouwen-2006})
-- ============================================================================

/-- Proximity to numeral value: within distance 1. -/
def isProximal (m n : Nat) : Prop :=
  n + 1 = m ∨ n = m ∨ n = m + 1

instance (m n : Nat) : Decidable (isProximal m n) := by
  unfold isProximal; infer_instance

/-- "Almost n": proximal to n but the numeral's meaning is false.
Proximal/polar decomposition from @cite{nouwen-2006}.

Under LB: close to n AND ¬(≥n) → only values below n
Under BL: close to n AND ¬(=n) → values above OR below n

The LB/BL divergence argument is from @cite{penka-2006}. @cite{nouwen-2006}
shows that polar orientation is context-dependent in general (e.g.,
"almost that warm" vs "almost that cold" orient in opposite directions). -/
def almostMeaning (T : NumeralTheory) (w : BareNumeral) (n : Nat) : Prop :=
  isProximal w.toNat n ∧ ¬ T.meaning w n

instance (T : NumeralTheory) (w : BareNumeral) (n : Nat) :
    Decidable (almostMeaning T w n) := by
  unfold almostMeaning; infer_instance

/-- "Almost three" diverges above: LB excludes 4, BL includes 4.

Under LB: 4 ≥ 3 so the polar component blocks it.
Under BL: 4 ≠ 3 and 4 is proximal to 3, so "almost three" holds. -/
theorem almost_diverges_above :
    ¬ almostMeaning LowerBound .three 4 ∧
    almostMeaning Exact .three 4 := by decide

/-- Full "almost" asymmetry: both agree on 2, diverge on 4. -/
theorem almost_asymmetry :
    -- Both agree: 2 is "almost three"
    (almostMeaning LowerBound .three 2 ∧
     almostMeaning Exact .three 2) ∧
    -- LB: 4 is NOT "almost three" (4 ≥ 3, polar blocks)
    -- BL: 4 IS "almost three" (4 ≠ 3 and proximal)
    (¬ almostMeaning LowerBound .three 4 ∧
     almostMeaning Exact .three 4) := by decide

-- ============================================================================
-- Section 10: "Only" + Focus (@cite{coppock-beaver-2014})
-- ============================================================================

/-- "Only n" with numeral in focus: assertion + exclusion of stronger alternatives.

Truth-conditionally equivalent to EXH on the numeral meaning. -/
def onlyMeaning (T : NumeralTheory) (w : BareNumeral) (n : Nat) : Prop :=
  exh T w n

instance (T : NumeralTheory) (w : BareNumeral) (n : Nat) :
    Decidable (onlyMeaning T w n) := by
  unfold onlyMeaning; infer_instance

/-- "Only" on numerals is truth-conditionally equivalent to EXH. -/
theorem only_eq_exh (T : NumeralTheory) (w : BareNumeral) (n : Nat) :
    onlyMeaning T w n ↔ exh T w n := Iff.rfl

/-- "Only" is truth-conditionally informative under LB, vacuous under BL.

"Only three students passed":
- Under LB: "three" at 4 is true (4≥3), but "only three" at 4 is false → informative
- Under BL: "three" at 4 is already false (4≠3), "only three" also false → vacuous -/
theorem only_informative_lowerBound :
    -- LB without "only": "three" is true at 4
    LowerBound.meaning .three 4 ∧
    -- LB with "only": "only three" is false at 4
    ¬ onlyMeaning LowerBound .three 4 ∧
    -- BL: "only" is vacuous (same result with or without)
    (¬ Exact.meaning .three 4 ∧ ¬ onlyMeaning Exact .three 4) := by
  decide

-- ============================================================================
-- Section 11: QUD-Convexity (@cite{solt-waldon-2019})
-- ============================================================================

/-- Worlds 0 through 5 for extended embedding tests. -/
def extendedWorlds : List Nat := [0, 1, 2, 3, 4, 5]

/-- Convexity: the set of true values on sorted worlds has no internal gaps.

For every pair of true values a < c, all intermediate b must also be true.
Non-convex denotations are predicted to be infelicitous in neutral QUD contexts. -/
def isConvex (worlds : List Nat) (f : Nat → Prop) [DecidablePred f] : Prop :=
  ∀ a ∈ worlds, ∀ b ∈ worlds, ∀ c ∈ worlds,
    f a → f c → a < b → b < c → f b

instance (worlds : List Nat) (f : Nat → Prop) [DecidablePred f] :
    Decidable (isConvex worlds f) := by
  unfold isConvex; infer_instance

/-- Negation convexity divergence.

¬(≥3) on [0.5] = {0,1,2} — convex (no gaps).
¬(=3) on [0.5] = {0,1,2,4,5} — non-convex (gap at 3).

BL correctly predicts "She doesn't have 40 sheep" is infelicitous
in neutral context (non-convex answer). LB incorrectly predicts felicity. -/
theorem negation_convexity_divergence :
    isConvex extendedWorlds (negatedMeaning LowerBound .three) ∧
    ¬ isConvex extendedWorlds (negatedMeaning Exact .three) := by
  decide

-- ============================================================================
-- Section 12: Heim-Kennedy Generalization (@cite{heim-2000}; @cite{bylinina-nouwen-2020} §6)
-- ============================================================================

/-- EXH scoped under a nominal quantifier (∃): each individual is exhaustified.

"Some students answered exactly three questions"
Under LB: ∃x[student(x) ∧ EXH(≥3)(answers(x))] = some student answered exactly 3.
This is the WEAK reading — per-student exhaustification. -/
def exhUnderNominalQ (T : NumeralTheory) (w : BareNumeral)
    (individuals : List Nat) : Prop :=
  ∃ n ∈ individuals, exh T w n

instance (T : NumeralTheory) (w : BareNumeral) (individuals : List Nat) :
    Decidable (exhUnderNominalQ T w individuals) := by
  unfold exhUnderNominalQ; infer_instance

/-- EXH scoped over a nominal quantifier (∃): exhaustifies the existential claim.

"Some students answered exactly three questions" — strong reading:
EXH(∃x[student(x) ∧ ≥3(answers(x))]) = some answered ≥3 AND none answered ≥4.
Heim-Kennedy BLOCKS this reading for numerals. -/
def exhOverNominalQ (T : NumeralTheory) (w : BareNumeral)
    (individuals : List Nat) : Prop :=
  (∃ n ∈ individuals, T.meaning w n) ∧
    match w.succ with
    | some w' => ¬ ∃ n ∈ individuals, T.meaning w' n
    | none => True

instance (T : NumeralTheory) (w : BareNumeral) (individuals : List Nat) :
    Decidable (exhOverNominalQ T w individuals) := by
  unfold exhOverNominalQ
  generalize w.succ = succ
  cases succ <;> infer_instance

/-- Heim-Kennedy generalization: degree operators scope over modals but NOT over
nominal quantifiers (@cite{heim-2000}, @cite{bylinina-nouwen-2020} §6, examples 40–41).

With individuals [3, 4] (one answered 3, one answered 4):
- Weak reading (EXH under ∃): true — the student with 3 answered exactly 3.
- Strong reading (EXH over ∃): false — blocked because someone answered 4 (≥4).

Contrast with the modal case (`exh_scope_diverges_lowerBound`), where BOTH
EXH-under-◇ and EXH-over-◇ are available. The asymmetry is precisely what
the degree quantifier analysis predicts via QR constraints. -/
theorem heimKennedy_nominal_blocked :
    exhUnderNominalQ LowerBound .three [3, 4] ∧
    ¬ exhOverNominalQ LowerBound .three [3, 4] := by decide

/-- The modal case allows both scope configurations (contrast with Heim-Kennedy). -/
theorem modal_both_scopes_available :
    exhUnderPossibility LowerBound .two [2] ∧
    exhOverPossibility LowerBound .two [2] := by decide

/-- Under Exact, Heim-Kennedy is vacuous: EXH adds nothing to =n,
so neither scope yields a strong reading over nominal quantifiers. -/
theorem heimKennedy_vacuous_exact :
    exhUnderNominalQ Exact .three [3, 4] ∧
    ¬ exhOverNominalQ Exact .three [3, 4] := by decide

-- ============================================================================
-- Section 13: Additional Embedding Divergences
-- ============================================================================

/-- Imperative compliance divergence.

"Read three books!" — reading 5 books:
- LB: 5 ≥ 3 → compliant
- BL: 5 ≠ 3 → non-compliant -/
theorem imperative_compliance_divergence :
    LowerBound.meaning .three 5 ∧
    ¬ Exact.meaning .three 5 := by decide

/-- Neg-raising "doubt" reduces to negation.

"I doubt three students passed" ≈ believe(¬(three passed)). -/
theorem doubt_as_neg_raising :
    ¬ negatedMeaning LowerBound .three 4 ∧
    negatedMeaning Exact .three 4 := by decide

/-- Factive presupposition divergence.

"I'm surprised three students passed" presupposes the numeral meaning.
At world 5: LB presupposition satisfied (5 ≥ 3), BL violated (5 ≠ 3). -/
theorem factive_presupposition_divergence :
    LowerBound.meaning .three 5 ∧
    ¬ Exact.meaning .three 5 := by decide

/-- Degree "too" monotonicity.

"Three is too many" — under LB, entails "four is too many" (both satisfy ≥3).
Under BL, no such entailment (4 does not satisfy =3). -/
theorem degree_too_monotonicity :
    -- Under LB: both 3 and 4 satisfy "three"
    (LowerBound.meaning .three 3 ∧ LowerBound.meaning .three 4) ∧
    -- Under BL: only 3 satisfies "three"
    (Exact.meaning .three 3 ∧ ¬ Exact.meaning .three 4) := by
  decide

/-- Acquisition prediction.

"Two horses jumped" when 3 jumped:
- LB: 3 ≥ 2 → should be accepted
- BL: 3 ≠ 2 → should be rejected
Children reject, supporting BL. -/
theorem acquisition_musolino :
    LowerBound.meaning .two 3 ∧
    ¬ Exact.meaning .two 3 := by decide

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
    , lowerBoundResult := decide (negatedMeaning LowerBound .three 4)
    , exactResult := decide (negatedMeaning Exact .three 4) }
  , { embedding := "¬(three) at world 2"
    , lowerBoundResult := decide (negatedMeaning LowerBound .three 2)
    , exactResult := decide (negatedMeaning Exact .three 2) }
  , { embedding := "◇(two) at [3]"
    , lowerBoundResult := decide (possibilityMeaning LowerBound .two [3])
    , exactResult := decide (possibilityMeaning Exact .two [3]) }
  , { embedding := "□(three) at [3, 4]"
    , lowerBoundResult := decide (necessityMeaning LowerBound .three [3, 4])
    , exactResult := decide (necessityMeaning Exact .three [3, 4]) }
  , { embedding := "three in restrictor at 4"
    , lowerBoundResult := decide (LowerBound.meaning .three 4)
    , exactResult := decide (Exact.meaning .three 4) }
  , { embedding := "EXH(two) at world 3"
    , lowerBoundResult := decide (exh LowerBound .two 3)
    , exactResult := decide (exh Exact .two 3) }
  , { embedding := "almost(three) at world 4"
    , lowerBoundResult := decide (almostMeaning LowerBound .three 4)
    , exactResult := decide (almostMeaning Exact .three 4) }
  , { embedding := "¬(three) convexity on [0..5]"
    , lowerBoundResult := decide (isConvex extendedWorlds (negatedMeaning LowerBound .three))
    , exactResult := decide (isConvex extendedWorlds (negatedMeaning Exact .three)) }
  , { embedding := "imperative: three at 5"
    , lowerBoundResult := decide (LowerBound.meaning .three 5)
    , exactResult := decide (Exact.meaning .three 5) }
  , { embedding := "acquisition: two at 3"
    , lowerBoundResult := decide (LowerBound.meaning .two 3)
    , exactResult := decide (Exact.meaning .two 3) }
  ]

/-- 8 of 10 test points show theory divergence. -/
theorem divergence_point_count :
    (embeddingDivergences.filter EmbeddingPrediction.diverges).length = 8 := by
  decide

end Semantics.Numerals
