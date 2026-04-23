import Linglib.Phenomena.Negation.ExpletiveNegation

/-!
# Italian Expletive Negation Environments

Classification of Italian EN construction types from @cite{greco-2020}
Table 1 (weak EN) and Table 2 (strong EN, including surprise negation).

Italian has 11 EN construction types, divided into weak and strong based
on co-occurrence with polarity-sensitive elements. This data is language-
specific: the *constructions* are Italian, but the *classification*
(ENStrength, PolarityLicensing) comes from `Core.Negation`.

The syntactic analysis (why each construction falls into its class)
lives in `Greco2020`.
-/

namespace Fragments.Italian.ExpletiveNegation

open Phenomena.Negation.ExpletiveNegation (ENStrength PolarityLicensing weakENProfile strongENProfile)

-- ════════════════════════════════════════════════════
-- § 1. The 11 Italian EN construction types
-- ════════════════════════════════════════════════════

/-- The 11 Italian EN construction types classified by @cite{greco-2020}
    Table 1 (extended to include Snegs from Table 2). -/
inductive ENEnvironment where
  | untilClauses
  | whoKnowsClauses
  | unlessClauses
  | indirectInterrogatives
  | comparativeClauses
  | negativeExclamatives
  | rhetoricalQuestions
  | notThatClauses
  | ratherThanClauses
  | beforeClauses
  | snegs
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Strength and polarity classification
-- ════════════════════════════════════════════════════

/-- @cite{greco-2020} Table 1+2 classification. -/
def ENEnvironment.strength : ENEnvironment → ENStrength
  | .untilClauses          => .weak
  | .whoKnowsClauses       => .weak
  | .unlessClauses         => .weak
  | .indirectInterrogatives => .weak
  | .comparativeClauses    => .weak
  | .negativeExclamatives  => .strong
  | .rhetoricalQuestions   => .strong
  | .notThatClauses        => .strong
  | .ratherThanClauses     => .strong
  | .beforeClauses         => .strong
  | .snegs                 => .strong

/-- Table 1 data: map each environment to its polarity licensing. -/
def ENEnvironment.licensing : ENEnvironment → PolarityLicensing
  | .untilClauses          => weakENProfile
  | .whoKnowsClauses       => weakENProfile
  | .unlessClauses         => weakENProfile
  | .indirectInterrogatives => weakENProfile
  | .comparativeClauses    => weakENProfile
  | .negativeExclamatives  => strongENProfile
  | .rhetoricalQuestions   => strongENProfile
  | .notThatClauses        => strongENProfile
  | .ratherThanClauses     => strongENProfile
  | .beforeClauses         => strongENProfile
  | .snegs                 => strongENProfile

-- ════════════════════════════════════════════════════
-- § 3. Verification theorems
-- ════════════════════════════════════════════════════

/-- Strong EN ↔ rejects all four polarity classes. -/
theorem strong_rejects_all (e : ENEnvironment)
    (h : e.strength = .strong) :
    e.licensing = strongENProfile := by
  cases e <;> simp_all [ENEnvironment.strength, ENEnvironment.licensing]

/-- Snegs are strong EN: they reject all polarity-sensitive elements. -/
theorem snegs_are_strong : ENEnvironment.snegs.strength = .strong := rfl

end Fragments.Italian.ExpletiveNegation
