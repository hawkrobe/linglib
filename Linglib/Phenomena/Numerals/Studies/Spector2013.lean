import Linglib.Theories.Semantics.Numerals.Basic
import Linglib.Theories.Semantics.Numerals.Embedding
import Linglib.Theories.Semantics.Exhaustification.InnocentExclusion

/-!
# Spector 2013: Bare Numerals and Scalar Implicatures
@cite{spector-2013} @cite{horn-1972} @cite{kennedy-2015} @cite{chierchia-fox-spector-2012} @cite{fox-2007} @cite{carston-1988} @cite{breheny-2008}

Bare numerals and scalar implicatures. Language and Linguistics Compass
7(5): 273–294.

## Core Contribution

@cite{spector-2013} evaluates four approaches to bare numeral interpretation:

1. **Neo-Gricean** (@cite{horn-1972}): basic = ≥n, exact via scalar implicature
2. **Underspecification** (@cite{carston-1988}): context selects ≥n, =n, or ≤n
3. **Exactly-only** (@cite{breheny-2008}): basic = =n, other readings via context
4. **Ambiguity via EXH** (@cite{chierchia-fox-spector-2012}): numerals have an
   "at least" base meaning; a covert exhaustivity operator EXH generates the
   "exactly" reading; both are grammatically available

The paper argues that approach 4 is necessary and sufficient to capture three
generalizations about numeral interpretation (§5, (41a–c)):

- (a) "At least" readings available in all embedded environments
- (b) "Exactly" readings available in all syntactic environments
- (c) "At most" readings arise only in DE environments

## Formalization

- §1: The four approaches as an enum
- §2: The three generalizations as a checkable predicate
- §3: **EXH bridge** — proves `exhNumeral` agrees with the general `exhB`
  from @cite{fox-2007}'s innocent exclusion on numeral alternative sets
- §4: Neo-Gricean failure in DE contexts + discourse coherence against exactly-only
- §5: Against underspecification (no genuine "at most" readings)
- §6: Ambiguity via EXH captures all three generalizations
- §7: Intermediate embedded implicatures distinguish EXH-ambiguity
  from lexical ambiguity

## Integration

- **EXH bridge** (§3) connects `Theories/Semantics/Lexical/Numeral/Semantics.lean`'s
  `exhNumeral` to `Theories/Semantics/Exhaustification/InnocentExclusion.lean`'s `exhB`
- `Compare.lean` Bridge 9 independently shows RSA derives exact from LB
- `ExhaustivityLimit.lean` proves RSA at α→∞ = EXH for ⟨some, all⟩
- @cite{spector-2007} proves Max(P) = {Exhaust(P)} (Gricean ↔ exhaustive)
-/

namespace Spector2013

open Semantics.Numerals
open Exhaustification.InnocentExclusion (exhB ieIndices)

-- ============================================================================
-- § 1. The Four Approaches
-- ============================================================================

/-- The four theoretical approaches to bare numeral interpretation
    evaluated in @cite{spector-2013} §1. -/
inductive Approach where
  /-- Neo-Gricean (@cite{horn-1972}): basic = ≥n, exact via scalar implicature -/
  | neoGricean
  /-- Underspecification (@cite{carston-1988}): context selects ≥n, =n, or ≤n -/
  | underspecification
  /-- Exactly-only (@cite{breheny-2008}): basic = =n, other readings via context -/
  | exactlyOnly
  /-- Ambiguity via EXH (@cite{chierchia-fox-spector-2012}): base = ≥n,
      exact via covert exhaustivity operator; both readings available -/
  | ambiguityEXH
  deriving DecidableEq, Repr

/-- Maps each approach to its base `NumeralTheory`, where one exists.
    The underspecification view doesn't have a single base relation — it posits
    all three (≥n, =n, ≤n) as equally available. We return `none` for it. -/
def Approach.baseTheory : Approach → Option NumeralTheory
  | .neoGricean => some LowerBound
  | .underspecification => none
  | .exactlyOnly => some Exact
  | .ambiguityEXH => some LowerBound

/-- Does the approach derive the exact reading via EXH / implicature? -/
def Approach.derivesExactViaEXH : Approach → Bool
  | .neoGricean => true
  | .underspecification => false
  | .exactlyOnly => false
  | .ambiguityEXH => true

/-- Does the approach claim "at most" is a genuine bare-numeral reading? -/
def Approach.claimsAtMost : Approach → Bool
  | .underspecification => true
  | _ => false

-- ============================================================================
-- § 2. The Three Generalizations (41a–c)
-- ============================================================================

/-- @cite{spector-2013}'s three generalizations about numeral interpretation
    (41a–c). An adequate theory must satisfy all three. -/
structure ThreeGeneralizations where
  /-- (41a) "At least" readings available in all embedded environments. -/
  atLeastAvailable : Bool
  /-- (41b) "Exactly" readings available in all syntactic environments. -/
  exactlyAvailable : Bool
  /-- (41c) "At most" readings available only in DE environments. -/
  atMostOnlyInDE : Bool
  deriving DecidableEq, Repr

def ThreeGeneralizations.allSatisfied (g : ThreeGeneralizations) : Bool :=
  g.atLeastAvailable && g.exactlyAvailable && g.atMostOnlyInDE

/-- Neo-Gricean fails (41b): SIs are blocked/degraded in DE contexts,
    yet "exactly" readings persist there. -/
def neoGriceanPredictions : ThreeGeneralizations where
  atLeastAvailable := true
  exactlyAvailable := false
  atMostOnlyInDE := true

/-- Underspecification fails (41c): predicts "at most" should be freely
    available in all contexts, but it isn't (§3, example (30b)). -/
def underspecPredictions : ThreeGeneralizations where
  atLeastAvailable := true
  exactlyAvailable := true
  atMostOnlyInDE := false

/-- Exactly-only fails (41a): needs ad hoc mechanisms (implicit restriction,
    weakening) to derive "at least" readings (§4.2, examples (36)–(37)). -/
def exactlyOnlyPredictions : ThreeGeneralizations where
  atLeastAvailable := false
  exactlyAvailable := true
  atMostOnlyInDE := true

/-- Ambiguity via EXH satisfies all three: base = ≥n (always available),
    EXH derives =n (freely insertable), "at most" = =n + background. -/
def ambiguityEXHPredictions : ThreeGeneralizations where
  atLeastAvailable := true
  exactlyAvailable := true
  atMostOnlyInDE := true

/-- Only the ambiguity-via-EXH account satisfies all three generalizations. -/
theorem only_ambiguity_satisfies_all :
    ambiguityEXHPredictions.allSatisfied = true ∧
    neoGriceanPredictions.allSatisfied = false ∧
    underspecPredictions.allSatisfied = false ∧
    exactlyOnlyPredictions.allSatisfied = false := by native_decide

-- ============================================================================
-- § 3. EXH Bridge: exhNumeral ↔ exhB
-- ============================================================================

/-! ### Bridging numeral exhaustification to general innocent exclusion

The numeral-specific `exhNumeral` (in `Semantics.lean`) hard-codes the scalar
alternatives {≥k} and checks only the immediate successor. The general `exhB`
from @cite{fox-2007} operates on arbitrary alternative sets via innocent
exclusion.

We prove these agree on the standard numeral domain. This bridges two
previously disconnected parts of the library and validates that numerals
receive standard exhaustification — they are not a special case. -/

/-- Standard numeral domain for exhaustification. -/
def exhDomain : List Nat := [0, 1, 2, 3]

/-- Numeral alternatives for bare numeral m under LB: {≥0, ≥1, ..., ≥(m+1)}.
    Includes the prejacent and both weaker and stronger alternatives. -/
def lbAlts (m : Nat) : List (Nat → Bool) :=
  (List.range (m + 2)).map fun k => fun n => maxMeaning .ge k n

/-- Prejacent for bare numeral m under LB: ≥m. -/
def lbMeaning (m : Nat) : Nat → Bool := fun n => maxMeaning .ge m n

/-- Innocent exclusion identifies the successor as the only innocently
    excludable alternative for each numeral. -/
theorem ie_numerals :
    ieIndices exhDomain (lbMeaning 1) (lbAlts 1) = [2] ∧
    ieIndices exhDomain (lbMeaning 2) (lbAlts 2) = [3] ∧
    ieIndices exhDomain (lbMeaning 3) (lbAlts 3) = [4] := by native_decide

/-- **EXH bridge**: The numeral-specific `exhNumeral` agrees with the
    general `exhB` on the standard domain for all three bare numerals.

    This proves numerals get standard @cite{fox-2007} exhaustification —
    they are not a special case requiring a bespoke operator. -/
theorem exhNumeral_eq_exhB :
    (exhDomain.all fun n => exhNumeral 3 1 n == exhB exhDomain (lbAlts 1) (lbMeaning 1) n) ∧
    (exhDomain.all fun n => exhNumeral 3 2 n == exhB exhDomain (lbAlts 2) (lbMeaning 2) n) ∧
    (exhDomain.all fun n => exhNumeral 3 3 n == exhB exhDomain (lbAlts 3) (lbMeaning 3) n) := by
  native_decide

/-- The EXH bridge also holds for the `exh` function from `Embedding.lean`,
    connecting the `NumeralTheory`-parameterized version to `exhB`. -/
theorem exh_eq_exhB :
    (exhDomain.all fun n => exh LowerBound .one n == exhB exhDomain (lbAlts 1) (lbMeaning 1) n) ∧
    (exhDomain.all fun n => exh LowerBound .two n == exhB exhDomain (lbAlts 2) (lbMeaning 2) n) ∧
    (exhDomain.all fun n => exh LowerBound .three n == exhB exhDomain (lbAlts 3) (lbMeaning 3) n) := by
  native_decide

-- ============================================================================
-- § 4. Neo-Gricean Failure in DE Contexts
-- ============================================================================

/-! ### The conditional/tax problem (@cite{spector-2013} §2.2.2)

"If you have three children, you do not qualify for tax exemptions."

Under neo-Gricean (base = ≥3), pragmatic strengthening can only *narrow*
the literal meaning from ≥3 to =3. But the attested reading is "if 3 or
fewer" (≤3), which is *broader* than ≥3 along a different dimension.
The neo-Gricean approach has no mechanism to derive this. -/

/-- EXH narrows ≥3 to =3. Neither ≥3 nor =3 entails ≤3.
    The "at most" reading requires background knowledge about monotonicity
    of the relevant scale (tax exemptions decrease with more children),
    not pragmatic strengthening. -/
theorem exh_cannot_derive_atMost :
    -- EXH(≥3) = =3: narrowing, not broadening
    (exhNumeral 3 3 3 = true ∧ exhNumeral 3 3 4 = false) ∧
    -- Neither ≥3 nor =3 includes world 2 (fewer than 3)
    (maxMeaning .ge 3 2 = false ∧ maxMeaning .eq 3 2 = false) ∧
    -- Only ≤3 gets world 2
    maxMeaning .le 3 2 = true := by native_decide

/-- The indirect scalar implicature problem (@cite{spector-2013} §2.2.2).
    "Peter didn't solve three problems" — the neo-Gricean approach predicts
    an indirect SI: "Peter solved exactly two." But this is not perceived.
    Demonstrated on the small domain {0,1,2,3} with numeral "three". -/
theorem indirect_si_overgeneration :
    -- Under LB: ¬(≥3) at world 2 = true (fewer than 3)
    negatedMeaning LowerBound .three 2 = true ∧
    -- The scalar alternative "Peter didn't solve two problems" (= ¬(≥2))
    -- is strictly stronger than "didn't solve three" (= ¬(≥3))
    -- Negating this stronger alternative yields: solved ≥2
    -- Combined: ≥2 ∧ ¬(≥3) = exactly 2 — a spurious prediction
    (maxMeaning .ge 2 2 = true ∧ !(maxMeaning .ge 3 2) = true) := by
  native_decide

/-- Discourse coherence against exactly-only (@cite{spector-2013} §4.2).
    "I have four chairs. In fact, I have five."

    Under LB (≥4): the second sentence is consistent — 5 ≥ 4, so the
    speaker's first claim wasn't false. "In fact" cancels the implicature.

    Under exactly-only (=4): the second sentence contradicts the first —
    5 ≠ 4. The discourse should be infelicitous, but it isn't. -/
theorem discourse_coherence_against_exact :
    -- LB: "four" is true at world 5 (5 ≥ 4), so "in fact, five" is coherent
    LowerBound.meaning .four 5 = true ∧
    -- Exact: "four" is false at world 5 (5 ≠ 4), so "in fact, five" contradicts
    Exact.meaning .four 5 = false ∧
    -- LB: "five" is also true at world 5 — both claims hold simultaneously
    LowerBound.meaning .five 5 = true := by native_decide

-- ============================================================================
-- § 5. Against Underspecification
-- ============================================================================

/-! ### No genuine "at most" readings (@cite{spector-2013} §3)

The decisive argument: if bare numerals could mean ≤n, then "One must be
(at most) 40 to be eligible for the Fields medal" should be true. But
it's necessarily false — there IS no maximum age for Fields eligibility;
the constraint is a minimum (≤40 at time of award). The underspecification
view wrongly predicts ≤40 is available. -/

/-- The ≤n reading gives wrong truth conditions for minimum-threshold
    predicates. ≤40 makes ages 35, 30, ... eligible (wrong for Fields),
    while ≥40 correctly captures "at least 40" for voting thresholds. -/
theorem atMost_wrong_for_threshold :
    -- ≤40: age 35 counts as eligible (wrong for Fields)
    maxMeaning .le 40 35 = true ∧
    -- ≥40: age 35 does NOT count (correct for voting threshold)
    maxMeaning .ge 40 35 = false ∧
    -- The asymmetry: ≥18 for voting works, ≤40 for Fields doesn't
    maxMeaning .ge 18 19 = true ∧
    maxMeaning .le 40 45 = false := by simp [maxMeaning]

-- ============================================================================
-- § 6. Ambiguity via EXH Captures All Three Generalizations
-- ============================================================================

/-- (41a) "At least" = base meaning, always present.
    The base ≥n is true at n and above, and survives under all operators. -/
theorem gen41a_atLeast :
    LowerBound.meaning .three 3 = true ∧
    LowerBound.meaning .three 4 = true ∧
    -- Survives under necessity: □(≥3) at [3,4] = true
    necessityMeaning LowerBound .three [3, 4] = true := by native_decide

/-- (41b) "Exactly" = EXH(base), available wherever EXH can scope.
    @cite{spector-2013} suggests that numerals may intrinsically activate
    their alternatives (§6.2), which would explain why EXH doesn't require
    prosodic marking for numerals (unlike "or" in DE contexts). -/
theorem gen41b_exactly :
    -- EXH produces exact reading
    exhNumeral 3 3 3 = true ∧ exhNumeral 3 3 4 = false ∧
    -- EXH available under negation: NOT[EXH(≥3)] = NOT[=3]
    (!(exhNumeral 3 3 4)) = true ∧
    -- EXH available under modals
    exh LowerBound .three 3 = true ∧
    exh LowerBound .three 4 = false := by native_decide

/-- (41c) "At most" = =n + monotone background knowledge, only in DE.
    Under negation (DE): ¬(=3) is non-directional ({0,1,2,4,5,...}).
    Background monotonicity (e.g., tax exemptions decrease with children)
    restricts this to ≤3. In UE contexts, no such restriction applies,
    so the "at most" reading is unavailable. -/
theorem gen41c_atMost :
    -- ¬(=3) at world 2 (below): true
    negatedMeaning Exact .three 2 = true ∧
    -- ¬(=3) at world 4 (above): also true — non-directional
    negatedMeaning Exact .three 4 = true ∧
    -- Monotone background restricts to ≤3: world 2 passes, world 4 doesn't
    (negatedMeaning Exact .three 2 && maxMeaning .le 3 2) = true ∧
    (negatedMeaning Exact .three 4 && maxMeaning .le 3 4) = false := by
  native_decide

-- ============================================================================
-- § 7. Intermediate Embedded Implicatures
-- ============================================================================

/-! ### EXH-ambiguity predicts more readings than lexical ambiguity

(@cite{spector-2013} §6.2, examples (52)–(53))

Under lexical ambiguity, a numeral IS either ≥n or =n — no scope flexibility.
Under EXH-ambiguity, EXH is an operator that can scope at different positions.
For ◇(numeral), this yields three readings:

1. ◇(≥n): use base meaning — "possible to do at-least-n"
2. ◇(EXH(≥n)) = ◇(=n): EXH scopes under modal — "possible to do exactly n"
3. EXH(◇(≥n)) = ◇(≥n) ∧ ¬◇(≥n+1): EXH scopes over modal — "possible ≥n
   but NOT possible ≥n+1"

Lexical ambiguity only produces readings 1 and 2. Reading 3 — the
wide-scope EXH — is unique to the EXH-ambiguity account. -/

/-- Three distinct readings for ◇(numeral) under EXH-ambiguity.
    With accessible worlds [2, 3]:
    - ◇(≥2) = true (both worlds satisfy ≥2)
    - ◇(EXH(≥2)) = ◇(=2) = true (world 2 satisfies =2)
    - EXH(◇(≥2)) = ◇(≥2) ∧ ¬◇(≥3) = false (world 3 makes ◇(≥3) true) -/
theorem three_readings :
    -- Reading 1: ◇(≥2)
    possibilityMeaning LowerBound .two [2, 3] = true ∧
    -- Reading 2: ◇(EXH(≥2)) = ◇(=2) — EXH under modal
    exhUnderPossibility LowerBound .two [2, 3] = true ∧
    -- Reading 3: EXH(◇(≥2)) — EXH over modal (unique to EXH-ambiguity)
    exhOverPossibility LowerBound .two [2, 3] = false := by native_decide

/-- Lexical ambiguity can only produce readings 1 and 2.
    Reading 3 distinguishes the two accounts. Under lexical ambiguity,
    ◇(=2) ≠ EXH(◇(≥2)) — the wide-scope EXH reading is not derivable
    from either lexical entry alone. -/
theorem wide_scope_exh_not_lexical :
    -- ◇(=2) at [2, 3] = true (lexical =n reading)
    possibilityMeaning Exact .two [2, 3] = true ∧
    -- EXH(◇(≥2)) at [2, 3] = false (EXH over modal)
    exhOverPossibility LowerBound .two [2, 3] = false ∧
    -- These differ: lexical =n ≠ wide-scope EXH
    possibilityMeaning Exact .two [2, 3] ≠
      exhOverPossibility LowerBound .two [2, 3] := by native_decide

/-- The intermediate reading (§6.2, example (53)):
    □(EXH(≥n)) — "required to do exactly n."

    "Whenever the professor demanded [EXH(solve ≥3 problems)]"
    = "whenever demanded exactly 3 (not 4)"

    At accessible worlds [3, 4]:
    - □(≥3) = true — "required to solve at least 3" (too weak)
    - □(=3) = false — "required exactly 3 in every world" (4 ≠ 3)
    - □(EXH(≥3)) = false — "in every demand-world, exactly 3" (4 fails EXH)

    At accessible worlds [3]:
    - all three agree: true -/
theorem intermediate_embedded :
    -- At [3, 4]: base and intermediate diverge from lexical =n
    necessityMeaning LowerBound .three [3, 4] = true ∧
    necessityMeaning Exact .three [3, 4] = false ∧
    ([3, 4].all (exh LowerBound .three)) = false ∧
    -- At [3]: all readings converge
    necessityMeaning LowerBound .three [3] = true ∧
    necessityMeaning Exact .three [3] = true ∧
    ([3].all (exh LowerBound .three)) = true := by native_decide

-- ============================================================================
-- § 8. Summary
-- ============================================================================

/-! ### Integration with the rest of linglib

The results here connect to three independent lines of evidence in the library:

1. **EXH bridge** (§3): `exhNumeral` = `exhB` on numeral domains. This closes
   the gap between `Semantics/Lexical/Numeral/Semantics.lean` and
   `Semantics/Exhaustification/InnocentExclusion.lean` — numerals get standard
   @cite{fox-2007} exhaustification.

2. **RSA bridge** (`Compare.lean` Bridge 9): `lb_rsa_strengthens_two` proves
   L1("two") peaks at w=2 under LB semantics. This is the RSA derivation of
   the same exact reading that EXH derives grammatically.

3. **RSA=EXH limit** (`ExhaustivityLimit.lean`): `l1_weak_weakOnly_tendsto_one`
   proves RSA L1 at α→∞ recovers Fox's EXH for ⟨some, all⟩. Combined with the
   EXH bridge here, this means RSA at α→∞ on numerals should also recover
   `exhNumeral` — the three formalisms (EXH, `exhNumeral`, RSA-limit) converge.

4. **Gricean foundation** (@cite{spector-2007}): `max_eq_exhaust` proves
   Max(P) = {Exhaust(P)} — Gricean reasoning derives exhaustive interpretation.
   @cite{spector-2013}'s EXH operator is the grammaticalized version of the
   same operation.
-/

/-- @cite{spector-2013}: the ambiguity-via-EXH account uniquely captures all
    three generalizations, and the EXH bridge validates that numeral
    exhaustification is an instance of general innocent exclusion. -/
theorem spector2013_summary :
    -- Only ambiguity-via-EXH satisfies all three generalizations
    ambiguityEXHPredictions.allSatisfied = true ∧
    neoGriceanPredictions.allSatisfied = false ∧
    underspecPredictions.allSatisfied = false ∧
    exactlyOnlyPredictions.allSatisfied = false ∧
    -- EXH bridge: numeral EXH = general EXH (for all three numerals)
    (exhDomain.all fun n => exhNumeral 3 1 n == exhB exhDomain (lbAlts 1) (lbMeaning 1) n) ∧
    (exhDomain.all fun n => exhNumeral 3 2 n == exhB exhDomain (lbAlts 2) (lbMeaning 2) n) ∧
    (exhDomain.all fun n => exhNumeral 3 3 n == exhB exhDomain (lbAlts 3) (lbMeaning 3) n) ∧
    -- EXH derives exact from at-least
    (exhNumeral 3 3 3 = true ∧ exhNumeral 3 3 4 = false) ∧
    -- Discourse coherence refutes exactly-only
    (LowerBound.meaning .four 5 = true ∧ Exact.meaning .four 5 = false) ∧
    -- Three readings for ◇(numeral) — the third is unique to EXH-ambiguity
    (exhOverPossibility LowerBound .two [2, 3] ≠
      possibilityMeaning Exact .two [2, 3]) := by native_decide

end Spector2013
