import Linglib.Theories.Pragmatics.RSA.Extensions.ArgumentativeStrength
import Linglib.Theories.Pragmatics.RSA.Core.CombinedUtility
import Linglib.Theories.Pragmatics.RSA.Extensions.InformationTheory.Basic
import Mathlib.Data.Rat.Defs

/-!
# Barnett, Griffiths & Hawkins (2022): A Pragmatic Account of the Weak Evidence Effect
@cite{barnett-griffiths-hawkins-2022}

Extends RSA with a **persuasive speaker** who has a goal state w* that may differ
from the true world state w. The speaker's utility combines epistemic and persuasive
components (Eq. 6):

  U(u; w, w*) = U_epi(u; w) + β · U_pers(u; w*)

where U_epi = ln P_L0(w|u) and U_pers = ln P_L0(w*|u). The parameter β controls
persuasive bias (β=0 recovers standard RSA).

## Key Result: The Weak Evidence Effect

When β > 0, weak positive evidence can *backfire*: a pragmatic listener who expects
the speaker to show the strongest available evidence infers that the absence of
strong evidence means it doesn't exist, shifting beliefs in the opposite direction.

## Stick Contest Domain

We formalize a simplified Stick Contest (3 sticks from {1,...,5}, 10 worlds) and
verify the weak evidence effect computationally at β=2.

-/

namespace RSA.Implementations.BarnettEtAl2022

open RSA.ArgumentativeStrength
open RSA.CombinedUtility
open RSA.InformationTheory


-- ============================================================
-- Section 1: Persuasive RSA Framework (Eqs. 4–7)
-- ============================================================

/-- Persuasive utility: log-probability that the literal listener assigns
to the speaker's goal state w*. (Eq. 4)

  U_pers(u; w*) = ln P_L0(w*|u)

Higher when utterance u makes w* more likely under the literal listener. -/
def persuasiveUtility (l0Goal : ℚ) : ℚ :=
  log2Approx l0Goal

/-- Barnett et al.'s Eq. 6 is an instance of goalOrientedUtility
from CombinedUtility with U_goal = U_pers (persuasive utility):

  U(u; w, w*) = U_epi(u; w) + β · U_pers(u; w*)

At β=0, pure epistemic (standard RSA). As β grows, increasingly persuasive.
See CombinedUtility.goalOrientedUtility, goalOriented_cooperative, goalOriented_eq_combinedWeighted. -/
abbrev eq6 := goalOrientedUtility

/-- Weak evidence effect: positive evidence u (L0(goal|u) > prior) that
nonetheless decreases the pragmatic listener's belief below the prior. -/
def weakEvidenceOccurs (l0Goal priorGoal l1Goal : ℚ) : Prop :=
  l0Goal > priorGoal ∧ l1Goal < priorGoal

instance (a b c : ℚ) : Decidable (weakEvidenceOccurs a b c) :=
  inferInstanceAs (Decidable (_ ∧ _))


-- ============================================================
-- Section 2: Stick Contest Domain
-- ============================================================

-- Simplified from the paper's 5 sticks from {1,...,9} to 3 sticks from {1,...,5}.
-- This gives C(5,3) = 10 worlds, sufficient to demonstrate the weak evidence effect.

/-- Stick lengths 1–5 -/
inductive Stick where
  | s1 | s2 | s3 | s4 | s5
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Stick length as a natural number -/
def Stick.len : Stick → Nat
  | .s1 => 1 | .s2 => 2 | .s3 => 3 | .s4 => 4 | .s5 => 5

/-- All possible sticks -/
def allSticks : List Stick := [.s1, .s2, .s3, .s4, .s5]

/-- Worlds: sets of 3 distinct sticks from {1,...,5}. C(5,3) = 10 worlds. -/
inductive StickWorld where
  | w123 | w124 | w125 | w134 | w135
  | w145 | w234 | w235 | w245 | w345
  deriving DecidableEq, BEq, Repr, Inhabited

/-- All 10 worlds -/
def allWorlds : List StickWorld :=
  [.w123, .w124, .w125, .w134, .w135, .w145, .w234, .w235, .w245, .w345]

/-- Sticks available in each world -/
def worldSticks : StickWorld → List Stick
  | .w123 => [.s1, .s2, .s3]
  | .w124 => [.s1, .s2, .s4]
  | .w125 => [.s1, .s2, .s5]
  | .w134 => [.s1, .s3, .s4]
  | .w135 => [.s1, .s3, .s5]
  | .w145 => [.s1, .s4, .s5]
  | .w234 => [.s2, .s3, .s4]
  | .w235 => [.s2, .s3, .s5]
  | .w245 => [.s2, .s4, .s5]
  | .w345 => [.s3, .s4, .s5]

/-- Sum of stick lengths in a world -/
def worldSum : StickWorld → Nat
  | .w123 => 6 | .w124 => 7 | .w125 => 8 | .w134 => 8 | .w135 => 9
  | .w145 => 10 | .w234 => 9 | .w235 => 10 | .w245 => 11 | .w345 => 12

/-- A world is "longer" if the average exceeds the midpoint (3).
Equivalently, sum > 9 for 3 sticks. -/
def isLonger : StickWorld → Bool
  | .w145 | .w235 | .w245 | .w345 => true
  | _ => false

/-- Prior probability of "longer": 4 out of 10 worlds -/
def priorLonger : ℚ := 2 / 5


-- ============================================================
-- Section 3: L0, Persuasive Speaker, Pragmatic Listener
-- ============================================================

/-- L0(longer | u): fraction of worlds containing stick u that are "longer".

This is the literal listener's posterior probability that the average
exceeds the midpoint, given observing a single stick of length u. -/
def l0Longer (u : Stick) : ℚ :=
  let worldsWithU := allWorlds.filter (λ w => (worldSticks w).contains u)
  let longerWithU := worldsWithU.filter isLonger
  (longerWithU.length : ℚ) / (worldsWithU.length : ℚ)

/-- Speaker score for showing stick u in world w with bias β (Eq. 8).

Since all sticks are true observations (no lying), epistemic utility is
uniform across available sticks. The simplified speaker reduces to:

  S(u|w, longer, β) ∝ L0(longer|u)^β · 𝟙[u ∈ w] -/
def speakerScore (u : Stick) (w : StickWorld) (β : ℕ) : ℚ :=
  if (worldSticks w).contains u then (l0Longer u) ^ β else 0

/-- Normalizing constant for the speaker in world w -/
def speakerZ (w : StickWorld) (β : ℕ) : ℚ :=
  (worldSticks w).map (λ s => (l0Longer s) ^ β) |>.foldl (· + ·) 0

/-- Normalized speaker probability of showing stick u in world w -/
def speakerProb (u : Stick) (w : StickWorld) (β : ℕ) : ℚ :=
  let z := speakerZ w β
  if z = 0 then 0 else speakerScore u w β / z

/-- Pragmatic listener L1(longer | u, β).

  L1(w|u, β) ∝ P_S(u|w, longer, β) · P(w)

Then marginalize over worlds to get P(longer|u). (Eq. 7) -/
def l1Longer (u : Stick) (β : ℕ) : ℚ :=
  let worldsWithU := allWorlds.filter (λ w => (worldSticks w).contains u)
  let longerScore := worldsWithU.filter isLonger
    |>.map (λ w => speakerProb u w β)
    |>.foldl (· + ·) 0
  let totalScore := worldsWithU.map (λ w => speakerProb u w β)
    |>.foldl (· + ·) 0
  if totalScore = 0 then 0 else longerScore / totalScore


-- ============================================================
-- Section 4: Verification — Weak Evidence Effect
-- ============================================================

/-- Stick 4 is positive evidence for "longer" under the literal listener -/
theorem s4_positive_under_l0 : l0Longer .s4 > priorLonger := by native_decide

/-- Stick 5 is the strongest evidence for "longer" -/
theorem s5_strongest_evidence : l0Longer .s5 > l0Longer .s4 := by native_decide

/-- **Weak evidence effect**: at β=2, showing stick 4 (positive literal evidence)
*decreases* the pragmatic listener's belief in "longer" below the prior.

The listener reasons: "If the true average were high, the speaker would have
had stronger sticks (like 5) available and would have shown them instead.
The fact that they showed a 4 implies they lacked stronger evidence." -/
theorem weak_evidence_effect_s4 :
    weakEvidenceOccurs (l0Longer .s4) priorLonger (l1Longer .s4 2) := by native_decide

/-- Strong evidence does NOT backfire: stick 5 increases belief at β=2.

The strongest available evidence is always effective because it cannot
be "explained away" by the absence of something better. -/
theorem strong_evidence_works_s5 :
    l1Longer .s5 2 > priorLonger := by native_decide

/-- At β=0, the pragmatic listener reduces to the literal listener.
When the speaker has no persuasive bias, showing evidence is taken at face value. -/
theorem beta_zero_literal (u : Stick) :
    l1Longer u 0 = l0Longer u := by
  cases u <;> native_decide

/-- L0(longer|u) is weakly monotone in stick length.
Longer sticks provide more evidence for "longer" under the literal listener. -/
theorem l0Longer_monotone :
    l0Longer .s1 ≤ l0Longer .s2 ∧
    l0Longer .s2 ≤ l0Longer .s3 ∧
    l0Longer .s3 ≤ l0Longer .s4 ∧
    l0Longer .s4 ≤ l0Longer .s5 := by native_decide


-- ============================================================
-- Section 5: Bridges
-- ============================================================

/-- Connection to ArgumentativeStrength: in this domain, showing stick u
for the goal "longer" has positive argumentative strength iff L0(longer|u) > prior.
Sticks 4 and 5 are argumentatively positive; sticks 1–3 are not. -/
theorem s4_positive_argStr :
    hasPositiveArgStr (l0Longer .s4) priorLonger := by native_decide

theorem s3_not_positive_argStr :
    ¬ hasPositiveArgStr (l0Longer .s3) priorLonger := by native_decide

/-- The weak evidence effect shows that argumentatively positive evidence
can still backfire under a pragmatic listener model. This is the core
insight connecting Barnett et al. to Cummins & Franke's work on
argumentative strength: the *pragmatic* measure can reverse the ordering. -/
theorem argStr_positive_but_backfires :
    hasPositiveArgStr (l0Longer .s4) priorLonger ∧
    l1Longer .s4 2 < priorLonger := by native_decide

/-- Barnett et al.'s Eq. 6 is literally goalOrientedUtility. -/
theorem eq6_is_goalOriented (uEpi uPers β : ℚ) :
    eq6 uEpi uPers β = goalOrientedUtility uEpi uPers β := rfl

/-- At β=1 in CombinedUtility, persuasive utility equals combinedWeighted(1,1,...). -/
theorem eq6_at_one (uEpi uPers : ℚ) :
    eq6 uEpi uPers 1 = combinedWeighted 1 1 uEpi uPers :=
  goalOriented_eq_combinedWeighted uEpi uPers 1

/-- Barnett et al.'s Eq. 6 (additive: U_epi + β·U_pers) equals
(1+β) · combined(β/(1+β), U_epi, U_pers).

This bridges the paper's additive parameterization to the convex form
used by the unified `combined` framework. Since (1+β) > 0, the two
forms rank utterances identically. -/
theorem eq6_via_combined (uEpi uPers β : ℚ) (hβ : 0 ≤ β) :
    eq6 uEpi uPers β = (1 + β) * combined (betaToLam β) uEpi uPers :=
  goalOriented_eq_scaled_combined uEpi uPers β hβ

end RSA.Implementations.BarnettEtAl2022
