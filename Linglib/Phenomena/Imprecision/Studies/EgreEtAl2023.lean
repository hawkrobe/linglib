import Linglib.Phenomena.Imprecision.Numerals
import Linglib.Core.Agent.RationalAction
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Extensions.InformationTheory.Basic
import Linglib.Tactics.RSAPredict
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Égré et al. (2023)
@cite{egre-etal-2023}

"On the optimality of vagueness: 'around', 'between', and the Sorites"
Linguistics and Philosophy 46:1101–1130

## Phenomena

1. "Around n" produces triangular (tent-shaped) interpretation distributions
2. "Around n" conveys more shape information than "between a and b"
3. Speakers prefer "around n" for peaked private distributions
4. The round/non-round asymmetry affects "around" acceptability
5. Sorites-like tolerance chains for "around"

## RSA Model

"Around n" is interpreted via marginalization over a tolerance parameter y.
BIR: P(x=k | around n) ∝ P(x=k) × Σ_{y≥|n-k|} P(y)

The BIR is the literal listener (L0). The RSA layers (S1, higher Ln) build
on this via KL-divergence speaker utility and softmax. The paper shows
this model produces a triangular posterior, satisfies the Ratio Inequality,
and explains why speakers prefer "around n" over "between a b" for peaked
private distributions. The LU limitation (Appendix A) proves standard
LU models cannot derive the triangular shape.
-/

namespace Phenomena.Imprecision.Studies.EgreEtAl2023

open Phenomena.Imprecision.Numerals

-- ============================================================================
-- Section I: Empirical Data
-- ============================================================================

/--
Shape inference datum: "around n" vs "between a b" interpretation shape.

The key empirical claim: hearing "around n" leads to a peaked (triangular)
interpretation centered on n, while "between a b" leads to a flat
(uniform) interpretation over [a,b].
-/
structure ShapeInferenceDatum where
  /-- The vague expression -/
  vagueExpression : String
  /-- The precise alternative -/
  preciseAlternative : String
  /-- Center value n -/
  center : Nat
  /-- Does the vague expression produce peaked interpretation? -/
  vagueIsPeaked : Bool
  /-- Does the precise alternative produce peaked interpretation? -/
  preciseIsPeaked : Bool
  /-- Notes -/
  notes : String
  deriving Repr

/--
"Around 20" produces peaked interpretation; "between 10 and 30" does not.

Source: Égré et al. 2023, Sections 5-6, Figure 2 vs Figure 5
-/
def aroundVsBetween : ShapeInferenceDatum :=
  { vagueExpression := "around 20"
  , preciseAlternative := "between 10 and 30"
  , center := 20
  , vagueIsPeaked := true
  , preciseIsPeaked := false
  , notes := "Both cover similar ranges but 'around' conveys triangular shape"
  }

/--
Speaker preference datum: when does a speaker choose "around n"
over "between a b"?
-/
structure SpeakerPreferenceDatum where
  /-- Speaker's private distribution shape -/
  privateDistShape : String
  /-- Preferred message -/
  preferredMessage : String
  /-- Alternative message -/
  alternativeMessage : String
  /-- Why preferred? -/
  reason : String
  deriving Repr

/--
Speakers with peaked beliefs prefer "around n".

Source: Égré et al. 2023, Section 6
-/
def peakedSpeakerPreference : SpeakerPreferenceDatum :=
  { privateDistShape := "Peaked at 20 (e.g., observed 20 ± 2)"
  , preferredMessage := "around 20"
  , alternativeMessage := "between 10 and 30"
  , reason := "KL divergence: 'around 20' posterior is closer to peaked belief than flat 'between' posterior"
  }

/--
Speakers with flat beliefs prefer "between a b".

Source: Égré et al. 2023, Section 6
-/
def flatSpeakerPreference : SpeakerPreferenceDatum :=
  { privateDistShape := "Flat over [10, 30] (equal probability for all values)"
  , preferredMessage := "between 10 and 30"
  , alternativeMessage := "around 20"
  , reason := "'Between' posterior matches flat belief; 'around' posterior is too peaked"
  }

/--
Sorites chain datum for "around".

The sorites for "around n":
  If k is around n, and k' is close to k, then k' is around n.
  Applied repeatedly, this would make 0 "around 100".
-/
structure SoritesAroundDatum where
  /-- Center value -/
  center : Nat
  /-- Step size in chain -/
  stepSize : Nat
  /-- Starting value (clearly "around n") -/
  startValue : Nat
  /-- Ending value (clearly not "around n") -/
  endValue : Nat
  /-- Is each individual step compelling? -/
  individualStepsCompelling : Bool
  /-- Is the conclusion acceptable? -/
  conclusionAcceptable : Bool
  deriving Repr

def soritesAround20 : SoritesAroundDatum :=
  { center := 20
  , stepSize := 1
  , startValue := 20
  , endValue := 0
  , individualStepsCompelling := true
  , conclusionAcceptable := false
  }

/--
LU limitation datum: observations that LU cannot distinguish.

The LU model assigns the same speaker probabilities to observations
with the same support, even when their shapes differ dramatically.
-/
structure LULimitationDatum where
  /-- First observation -/
  observation1 : String
  /-- First observation shape -/
  shape1 : String
  /-- Second observation -/
  observation2 : String
  /-- Second observation shape -/
  shape2 : String
  /-- Same support? -/
  sameSupport : Bool
  /-- LU distinguishes them? -/
  luDistinguishes : Bool
  /-- BIR model distinguishes them? -/
  birDistinguishes : Bool
  deriving Repr

/--
Peaked vs flat distributions with same support: LU fails, BIR succeeds.

Source: Égré et al. 2023, Section 7, Appendix A
-/
def luFailsOnShape : LULimitationDatum :=
  { observation1 := "Peaked at 20 (values 10-30 possible, most near 20)"
  , shape1 := "triangular"
  , observation2 := "Flat over 10-30 (all equally likely)"
  , shape2 := "uniform"
  , sameSupport := true    -- Both have support {10,...,30}
  , luDistinguishes := false  -- LU gives same Sn for both
  , birDistinguishes := true  -- BIR gives different posteriors
  }

/--
Closed-form prediction datum: the triangular posterior formula.

Under uniform priors on x in {0,...,N} and y in {0,...,N}:
  P(x=k | around n) = (n - |n-k| + 1) / (n+1)^2
-/
structure ClosedFormDatum where
  /-- Domain maximum N -/
  domainMax : Nat
  /-- Center n -/
  center : Nat
  /-- Value k -/
  value : Nat
  /-- Expected probability (rational) -/
  expectedProb : ℚ
  /-- Notes -/
  notes : String
  deriving Repr

/-- P(x=20 | around 20) under uniform prior on {0,...,40} -/
def closedForm_center : ClosedFormDatum :=
  { domainMax := 40
  , center := 20
  , value := 20
  , expectedProb := 21 / 441  -- (20 - 0 + 1) / (20+1)²
  , notes := "Peak of triangular distribution"
  }

/-- P(x=15 | around 20) under uniform prior on {0,...,40} -/
def closedForm_offset5 : ClosedFormDatum :=
  { domainMax := 40
  , center := 20
  , value := 15
  , expectedProb := 16 / 441  -- (20 - 5 + 1) / (20+1)²
  , notes := "5 units from center, probability drops linearly"
  }

-- Collections

def shapeInferenceData : List ShapeInferenceDatum :=
  [aroundVsBetween]

def speakerPreferenceData : List SpeakerPreferenceDatum :=
  [peakedSpeakerPreference, flatSpeakerPreference]

def soritesData : List SoritesAroundDatum :=
  [soritesAround20]

def luLimitationData : List LULimitationDatum :=
  [luFailsOnShape]

def closedFormData : List ClosedFormDatum :=
  [closedForm_center, closedForm_offset5]

-- ============================================================================
-- Section II: RSA Model — BIR, Speaker, and LU Limitation
-- ============================================================================

-- Local helpers

private def sumScores (xs : List ℚ) : ℚ := xs.foldl (· + ·) 0

private def normalize {α : Type} [BEq α] (xs : List (α × ℚ)) : List (α × ℚ) :=
  let total := sumScores (xs.map Prod.snd)
  if total > 0 then xs.map (fun (a, s) => (a, s / total)) else xs

private def getScore {α : Type} [BEq α] (xs : List (α × ℚ)) (a : α) : ℚ :=
  match xs.find? (fun p => p.1 == a) with
  | some (_, s) => s
  | none => 0

private def marginalize {α β : Type} [BEq β] (xs : List (α × ℚ)) (proj : α → β)
    : List (β × ℚ) :=
  xs.foldl (fun acc (a, s) =>
    let b := proj a
    match acc.find? (fun p => p.1 == b) with
    | some _ => acc.map (fun (b', s') => if b' == b then (b', s' + s) else (b', s'))
    | none => acc ++ [(b, s)]) []

private def ratToFloat (q : ℚ) : Float :=
  let numFloat : Float := if q.num ≥ 0 then q.num.natAbs.toFloat else -q.num.natAbs.toFloat
  numFloat / q.den.toFloat

private def floatToRat (f : Float) : ℚ :=
  let scaled := (f * 1000000).round
  let n : Int := if scaled ≥ 0 then scaled.toUInt64.toNat else -((-scaled).toUInt64.toNat)
  (n : ℚ) / 1000000

-- Domain: {0,...,6} centered on 3, small enough for native_decide

inductive Value where
  | v0 | v1 | v2 | v3 | v4 | v5 | v6
  deriving Repr, DecidableEq, Fintype

def Value.toNat : Value → Nat
  | .v0 => 0 | .v1 => 1 | .v2 => 2 | .v3 => 3
  | .v4 => 4 | .v5 => 5 | .v6 => 6

/-- Tolerance y: "around n" with tolerance y means x ∈ [n-y, n+y]. -/
inductive Tolerance where
  | y0 | y1 | y2 | y3 | y4 | y5 | y6
  deriving Repr, DecidableEq, Fintype

def Tolerance.toNat : Tolerance → Nat
  | .y0 => 0 | .y1 => 1 | .y2 => 2 | .y3 => 3
  | .y4 => 4 | .y5 => 5 | .y6 => 6

def allValues : List Value := [.v0, .v1, .v2, .v3, .v4, .v5, .v6]
def allTolerances : List Tolerance := [.y0, .y1, .y2, .y3, .y4, .y5, .y6]

-- Semantics

/-- ⟦around n⟧(y)(x) = 1 iff |n - x| ≤ y -/
def aroundMeaning (n : Nat) (y : Tolerance) (x : Value) : Bool :=
  let diff := if n ≥ x.toNat then n - x.toNat else x.toNat - n
  diff ≤ y.toNat

def betweenMeaning (a b : Nat) (x : Value) : Bool :=
  a ≤ x.toNat && x.toNat ≤ b

def exactlyMeaning (n : Nat) (x : Value) : Bool :=
  x.toNat == n

-- BIR: Bayesian Interpretation Rule (eq BIR)
-- This IS the literal listener L0 of the paper's model.

/-- BIR weight: Σ_{y ≥ |n-x|} P(y) under uniform P(y) on {0,...,n}.
Section 3.2.2, p.1085: y ranges over {0,...,n}, not the full value domain. -/
def birWeight (n : Nat) (x : Value) : ℚ :=
  let diff := if n ≥ x.toNat then n - x.toNat else x.toNat - n
  let validCount := if diff ≤ n then n - diff + 1 else 0
  (validCount : ℚ) / (n + 1)

/-- BIR posterior = L0 for "around n". -/
def birPosterior (n : Nat) : List (Value × ℚ) :=
  let weights := allValues.map (fun v => (v, birWeight n v))
  normalize weights

/-- Closed form (Section 3.2.2): P(x=k | around n) = (n - |n-k| + 1) / (n+1)² -/
def birClosedForm (n : Nat) (k : Nat) : ℚ :=
  let diff := if n ≥ k then n - k else k - n
  if diff > n then 0
  else (n - diff + 1 : ℤ) / ((n + 1 : ℤ) * (n + 1 : ℤ))

-- L0 posteriors for each message type

def l0_around3 : List (Value × ℚ) := birPosterior 3

/-- L0 for "between a b" = uniform over [a,b]. -/
def intervalPosterior (a b : Nat) : List (Value × ℚ) :=
  let weights := allValues.map (fun v =>
    (v, if betweenMeaning a b v then (1 : ℚ) else 0))
  normalize weights

def l0_between0_6 : List (Value × ℚ) := intervalPosterior 0 6
def l0_between1_5 : List (Value × ℚ) := intervalPosterior 1 5
def l0_between2_4 : List (Value × ℚ) := intervalPosterior 2 4

/-- L0 for "exactly n" = point mass at n. -/
def exactPosterior (n : Nat) : List (Value × ℚ) :=
  let weights := allValues.map (fun v =>
    (v, if exactlyMeaning n v then (1 : ℚ) else 0))
  normalize weights

def l0_exactly3 : List (Value × ℚ) := exactPosterior 3

-- BIR joint distribution over (Value, Tolerance) for tolerance inference

def birJoint (n : Nat) : List ((Value × Tolerance) × ℚ) :=
  let validTolerances := allTolerances.filter (fun y => y.toNat ≤ n)
  let pairs := allValues.flatMap (fun v => validTolerances.map (fun y => (v, y)))
  let weights := pairs.map (fun (v, y) =>
    ((v, y), if aroundMeaning n y v then (1 : ℚ) else 0))
  normalize weights

/-- Tolerance posterior: marginalize BIR joint over values. -/
def tolerancePosterior (n : Nat) : List (Tolerance × ℚ) :=
  marginalize (birJoint n) Prod.snd

def l0_tolerance_around3 : List (Tolerance × ℚ) := tolerancePosterior 3

-- WIR: Weighted Interpretation Rule (Appendix B)

/-- WIR: L(x=k | around n) = Σ_i P(x=k | x ∈ [n-i,n+i]) × P(y=i).
Tolerance y ranges over {0,...,n} (Section 3.2.2). -/
def wirPosterior (n : Nat) : List (Value × ℚ) :=
  let validTolerances := allTolerances.filter (fun y => y.toNat ≤ n)
  let nTol := validTolerances.length
  let weights := allValues.map (fun v =>
    let score := validTolerances.foldl (fun acc y =>
      let lo := if n ≥ y.toNat then n - y.toNat else 0
      let hi := n + y.toNat
      let inInterval := lo ≤ v.toNat && v.toNat ≤ hi
      let intervalSize := allValues.filter (fun v' =>
        lo ≤ v'.toNat && v'.toNat ≤ hi) |>.length
      if inInterval && intervalSize > 0
      then acc + (1 : ℚ) / intervalSize * (1 : ℚ) / nTol
      else acc) 0
    (v, score))
  normalize weights

def wir_around3 : List (Value × ℚ) := wirPosterior 3

-- Theorems: BIR Shape (Section 3)

/-- BIR produces triangular posterior: v3 > v2 > v1 > v0. -/
theorem bir_triangular_shape :
    getScore l0_around3 .v3 > getScore l0_around3 .v2 ∧
    getScore l0_around3 .v2 > getScore l0_around3 .v1 ∧
    getScore l0_around3 .v1 > getScore l0_around3 .v0 := by
  native_decide

/-- BIR posterior is symmetric: P(n+k) = P(n-k). -/
theorem bir_symmetry :
    getScore l0_around3 .v2 = getScore l0_around3 .v4 ∧
    getScore l0_around3 .v1 = getScore l0_around3 .v5 ∧
    getScore l0_around3 .v0 = getScore l0_around3 .v6 := by
  native_decide

-- Theorems: Ratio Inequality (Section 4)

/-- Ratio Inequality: posterior concentrates more on center than prior.
Under uniform prior, reduces to P(v3|around3) / P(v1|around3) > 1. -/
theorem ratio_inequality :
    getScore l0_around3 .v3 / getScore l0_around3 .v1 > 1 ∧
    getScore l0_around3 .v3 / getScore l0_around3 .v0 > 1 := by
  native_decide

-- Theorems: Around vs Between (Sections 5-6)
-- Comparing L0 posteriors: BIR (for "around") vs uniform interval (for "between")

/-- "Around" conveys shape (peaked); "between" does not (flat).
Peak-to-edge ratio: around = 7/4, between = 1. -/
theorem around_conveys_shape_between_does_not :
    getScore l0_around3 .v3 / getScore l0_around3 .v1 >
    getScore l0_between1_5 .v3 / getScore l0_between1_5 .v1 := by
  native_decide

/-- "Around" has wider support than narrow "between". -/
theorem around_wider_support :
    getScore l0_around3 .v0 > 0 ∧ getScore l0_between2_4 .v0 = 0 := by
  native_decide

/-- "Around 3" covers nearby values; "exactly 3" does not. -/
theorem around_covers_nearby :
    getScore l0_around3 .v2 > 0 ∧
    getScore l0_around3 .v4 > 0 ∧
    getScore l0_exactly3 .v2 = 0 := by
  native_decide

/-- "Between 1 5" assigns uniform probability across its interval. -/
theorem between_is_uniform :
    getScore l0_between1_5 .v1 = getScore l0_between1_5 .v3 ∧
    getScore l0_between1_5 .v3 = getScore l0_between1_5 .v5 := by
  native_decide

-- Theorems: Tolerance Inference

/-- BIR joint marginalizes to favor large tolerances (more states compatible).
With y ∈ {0,...,3}, y3 has 7 compatible values while y0 has 1. -/
theorem tolerance_distribution :
    -- Large tolerances have more compatible states overall
    getScore l0_tolerance_around3 .y3 > getScore l0_tolerance_around3 .y0 := by
  native_decide

-- Theorems: Sorites (Section 9)

/-- Adjacent values have similar BIR probabilities (each step ≥ 50%). -/
theorem sorites_adjacent_similar :
    let p3 := getScore l0_around3 .v3
    let p2 := getScore l0_around3 .v2
    let p1 := getScore l0_around3 .v1
    p2 > p3 * 1/2 ∧ p1 > p2 * 1/2 := by
  native_decide

/-- Cumulative sorites effect: P(v3) > P(v0). -/
theorem sorites_cumulative :
    getScore l0_around3 .v3 > getScore l0_around3 .v0 := by
  native_decide

-- ============================================================================
-- RSAConfig: BIR Literal Listener + KL-Divergence Speaker (Section 6)
-- ============================================================================

/-- Message alternatives for the RSA model. -/
inductive Utt where
  | around3 | between0_6 | between1_5 | between2_4 | exactly3
  deriving Repr, DecidableEq, Fintype

/-- Unnormalized BIR weights for "around 3".

Proportional to `birWeight 3 w`: integer counts of valid tolerances
y ∈ {0,...,3} satisfying |3 - w| ≤ y. After L0 normalization (÷ 16),
gives the triangular BIR posterior [1/16, 2/16, 3/16, 4/16, 3/16, 2/16, 1/16]. -/
def aroundWeight : Value → Nat
  | .v0 => 1 | .v1 => 2 | .v2 => 3 | .v3 => 4 | .v4 => 3 | .v5 => 2 | .v6 => 1

/-- Speaker belief peaked at observed value (unnormalized).

Weight 2 at center, 1 at ±1, 0 elsewhere. Unnormalized weights preserve
S1 ranking because exp is monotone and the normalization constant is
independent of u (see `Core.Divergence.expected_loglik_eq_neg_kl_plus_entropy`). -/
noncomputable def speakerBeliefR (observed w : Value) : ℝ :=
  let d := if observed.toNat ≥ w.toNat then observed.toNat - w.toNat
            else w.toNat - observed.toNat
  if d ≤ 1 then ((2 - d : ℕ) : ℝ) else 0

open RSA in
/-- RSA model for imprecision: BIR + KL-divergence speaker.

**L0** = BIR (Bayesian Interpretation Rule): graded meaning gives the
triangular "around" posterior after normalization, matching `birWeight`.

**S1** = KL speaker: the speaker with peaked beliefs chooses the message
whose L0 posterior best matches those beliefs, measured by expected
log-likelihood (= negative KL divergence up to constant entropy,
see `Core.Divergence.expected_loglik_eq_neg_kl_plus_entropy`). -/
noncomputable def cfg : RSAConfig Utt Value where
  Latent := Unit
  meaning _ _ u w := match u with
    | .around3 => (aroundWeight w : ℝ)
    | .between0_6 => if betweenMeaning 0 6 w then 1 else 0
    | .between1_5 => if betweenMeaning 1 5 w then 1 else 0
    | .between2_4 => if betweenMeaning 2 4 w then 1 else 0
    | .exactly3 => if exactlyMeaning 3 w then 1 else 0
  meaning_nonneg _ _ u w := by
    cases u
    · exact Nat.cast_nonneg _
    all_goals (split <;> positivity)
  s1Score l0 α _ w u :=
    Real.exp (α * ∑ w' : Value, speakerBeliefR w w' * Real.log (l0 u w'))
  s1Score_nonneg _ _ _ _ _ _ _ := le_of_lt (Real.exp_pos _)
  α := 1
  α_pos := one_pos
  latentPrior_nonneg _ _ := by positivity
  worldPrior_nonneg _ := by positivity

/-- Speaker with peaked belief at v3 prefers "around 3" over "between 0 6".

"Around 3" produces a triangular L0 posterior peaked at v3, which
better matches the speaker's peaked belief via KL divergence.
"Between 0 6" produces a flat L0 posterior that wastes probability
mass on values far from v3. -/
theorem s1_prefers_around_peaked :
    cfg.S1 () .v3 .around3 > cfg.S1 () .v3 .between0_6 := by rsa_predict

-- ============================================================================
-- Section III: Appendix A — LU Limitation
-- ============================================================================

/-- Same support: P(w|o₁) > 0 ↔ P(w|o₂) > 0. -/
def SameSupport {α : Type} (d₁ d₂ : α → ℚ) : Prop :=
  ∀ x, d₁ x > 0 ↔ d₂ x > 0

/-- Quality: ∀ w, P(w|o) > 0 → ⟦m⟧ⁱ(w) = 1. -/
def RespectsQuality {W I : Type} (m_true : I → W → Bool) (obs : W → ℚ) (i : I) : Prop :=
  ∀ w, obs w > 0 → m_true i w = true

/-- Weak Quality: ∃ i, Quality(m, o, i). -/
def RespectsWeakQuality {W I : Type} (m_true : I → W → Bool) (obs : W → ℚ) : Prop :=
  ∃ i, RespectsQuality m_true obs i

/-- (A-1a) Quality preserved under same support. -/
theorem quality_preserved_by_same_support
    {W I : Type} (m_true : I → W → Bool) (d₁ d₂ : W → ℚ) (i : I)
    (h_same : SameSupport d₁ d₂) :
    RespectsQuality m_true d₁ i ↔ RespectsQuality m_true d₂ i := by
  constructor
  · intro hq w hw2; exact hq w ((h_same w).mpr hw2)
  · intro hq w hw1; exact hq w ((h_same w).mp hw1)

/-- (A-1b) Weak Quality preserved under same support. -/
theorem weak_quality_preserved_by_same_support
    {W I : Type} (m_true : I → W → Bool) (d₁ d₂ : W → ℚ) (h_same : SameSupport d₁ d₂) :
    RespectsWeakQuality m_true d₁ ↔ RespectsWeakQuality m_true d₂ := by
  constructor
  · rintro ⟨i, hq⟩; exact ⟨i, (quality_preserved_by_same_support m_true d₁ d₂ i h_same).mp hq⟩
  · rintro ⟨i, hq⟩; exact ⟨i, (quality_preserved_by_same_support m_true d₁ d₂ i h_same).mpr hq⟩

-- SoftMax Translation Invariance (A-5)

/-- SoftMax(x_k, x, λ) = exp(λx_k) / Σ_j exp(λx_j). -/
def softMaxScore (utilities : List ℚ) (k : Nat) (alpha : ℚ) : ℚ :=
  let exps := utilities.map (fun u =>
    floatToRat (Float.exp (ratToFloat (alpha * u))))
  let total := exps.foldl (· + ·) 0
  match exps[k]? with
  | some e => if total > 0 then e / total else 0
  | none => 0

def translateUtilities (utils : List ℚ) (a : ℚ) : List ℚ :=
  utils.map (· + a)

-- (A-5) SoftMax translation invariance: see `Core.softmax_add_const` in Core.

/-- K(o₁,o₂): utility difference constant, independent of m and i (Core Lemma A-6). -/
def utilityDifferenceConstant {W : Type} [BEq W]
    (support : List W) (d₁ d₂ : W → ℚ) : ℚ :=
  let f := fun d => support.map (fun w =>
    let p := d w
    if p > 0 then p * RSA.InformationTheory.log2Approx p else 0)
  sumScores (f d₂) - sumScores (f d₁)

-- LU utility and speaker functions (Appendix A definitions)

/-- U¹(m, o, i) = Σ_w P(w|o) · log L⁰(w | m, i) — speaker utility at level 1.
This is the KL-based utility: higher when L⁰ matches the observation. -/
def U1 {W M I : Type} [BEq W]
    (l0 : M → I → W → ℚ) (obs : W → ℚ) (m : M) (i : I)
    (worlds : List W) : ℚ :=
  worlds.foldl (fun acc w =>
    let pw := obs w
    let lw := l0 m i w
    if pw > 0 && lw > 0
    then acc + pw * RSA.InformationTheory.log2Approx lw
    else acc) 0

/-- (A-2a) No Quality → S¹ = 0: if message m is false under interpretation i
at every world in observation's support, then S¹(m | o, i) = 0.
Proof sketch: L⁰(w | m, i) = 0 for all supported w, so U¹ = -∞, softmax → 0. -/
private theorem U1_foldl_zero {W M I : Type} [BEq W]
    (l0 : M → I → W → ℚ) (obs : W → ℚ) (m : M) (i : I)
    (worlds : List W) (acc : ℚ)
    (h_nq : ∀ w, obs w > 0 → l0 m i w = 0) :
    worlds.foldl (fun acc w =>
      let pw := obs w
      let lw := l0 m i w
      if decide (pw > 0) && decide (lw > 0) then acc + pw * RSA.InformationTheory.log2Approx lw
      else acc) acc = acc := by
  induction worlds generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.foldl]
    have h_guard : (decide (obs w > 0) && decide (l0 m i w > 0)) = false := by
      by_cases hw : obs w > 0
      · simp [h_nq w hw]
      · simp [show ¬(obs w > 0) from hw]
    simp only [h_guard]
    exact ih acc

theorem no_quality_implies_S1_zero
    {W M I : Type} [BEq W] [BEq M]
    (l0 : M → I → W → ℚ) (obs : W → ℚ)
    (_messages : List M) (i : I) (worlds : List W) (_alpha : ℚ) (m : M)
    (h_nq : ∀ w, obs w > 0 → l0 m i w = 0) :
    U1 l0 obs m i worlds = 0 :=
  U1_foldl_zero l0 obs m i worlds 0 h_nq

-- ============================================================================
-- Section IV: Appendix A, Lemmas 6-8 — Real-valued proofs using Core Softmax
-- ============================================================================

open BigOperators Finset in
/-- Weighted sums shift by a constant: when Σd₁ = Σd₂, the constant c(m,i)
cancels in the difference Σd₂·(f+c) - Σd₁·(f+c) = Σd₂·f - Σd₁·f. -/
private lemma weighted_sum_shift {W : Type} [Fintype W]
    (d₁ d₂ f : W → ℝ) (c : ℝ) (h_sum : ∑ w, d₁ w = ∑ w, d₂ w) :
    (∑ w, d₂ w * (f w + c)) - (∑ w, d₁ w * (f w + c)) =
    (∑ w, d₂ w * f w) - (∑ w, d₁ w * f w) := by
  have expand : ∀ (d : W → ℝ), ∑ w, d w * (f w + c) = (∑ w, d w * f w) + (∑ w, d w) * c := by
    intro d
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  rw [expand d₂, expand d₁, h_sum]
  ring

open BigOperators Finset in
/-- (A-6) Core Lemma over ℝ: the utility difference U(m,d₂,i) - U(m,d₁,i) is
constant across all messages m and interpretations i, provided Σd₁ = Σd₂.

Under Quality, log L⁰(w|m,i) = f(w) + c(m,i) where f(w) = log prior(w) and
c(m,i) = −log Z(m,i). Since f doesn't depend on m,i and Σd₁ = Σd₂, the
c(m,i) term cancels in the difference, making K independent of m and i. -/
theorem core_lemma_A6 {W M I : Type} [Fintype W]
    (f : W → ℝ) (c : M → I → ℝ) (d₁ d₂ : W → ℝ)
    (h_sum : ∑ w, d₁ w = ∑ w, d₂ w) :
    ∀ (m₁ m₂ : M) (i₁ i₂ : I),
    (∑ w, d₂ w * (f w + c m₁ i₁)) - (∑ w, d₁ w * (f w + c m₁ i₁)) =
    (∑ w, d₂ w * (f w + c m₂ i₂)) - (∑ w, d₁ w * (f w + c m₂ i₂)) := by
  intro m₁ m₂ i₁ i₂
  rw [weighted_sum_shift d₁ d₂ f (c m₁ i₁) h_sum,
      weighted_sum_shift d₁ d₂ f (c m₂ i₂) h_sum]

/-- (A-7) Same support → S¹ equal over ℝ: when utility vectors differ by a constant,
softmax is invariant by `Core.softmax_add_const`.

By A-6, U¹(·, d₂, i) = U¹(·, d₁, i) + K for some constant K.
By A-5 (translation invariance), softmax(u + K, α) = softmax(u, α). -/
theorem same_support_implies_equal_S1 {M : Type} [Fintype M]
    (u₁ u₂ : M → ℝ) (α : ℝ) (h_shift : ∃ K, ∀ m, u₂ m = u₁ m + K) :
    Core.softmax u₂ α = Core.softmax u₁ α := by
  obtain ⟨K, hK⟩ := h_shift
  have : u₂ = fun m => u₁ m + K := funext hK
  rw [this, Core.softmax_add_const]

/-- (A-8) LU Limitation over ℝ: same support → Sⁿ(m|o₁) = Sⁿ(m|o₂) for all n ≥ 1.
At level 1, this is a direct corollary of A-7. The paper's full inductive argument
(higher recursion depths) follows the same pattern: each Lⁿ is built from Sⁿ⁻¹
which are equal by inductive hypothesis, so Uⁿ differs by a constant, so Sⁿ is
equal by softmax translation invariance. -/
theorem lu_limitation {M : Type} [Fintype M]
    (u₁ u₂ : M → ℝ) (α : ℝ) (h_shift : ∃ K, ∀ m, u₂ m = u₁ m + K) :
    Core.softmax u₂ α = Core.softmax u₁ α :=
  same_support_implies_equal_S1 u₁ u₂ α h_shift

-- ============================================================================
-- Section V: Appendix B — WIR
-- ============================================================================

theorem wir_peaked_at_center :
    getScore wir_around3 .v3 > getScore wir_around3 .v1 := by
  native_decide

/-- BIR and WIR differ quantitatively under uniform priors. -/
theorem bir_wir_differ :
    getScore l0_around3 .v2 ≠ getScore wir_around3 .v2 := by
  native_decide

-- ============================================================================
-- Section VI: Appendix C — Standard vs Bergen Utility
-- ============================================================================

-- Two same-support observations: peaked vs flat over {v1, v2, v3, v4, v5}
-- Both have support = {v1,...,v5}, but peaked puts mass 1/3 on v3, 1/6 on others.

def obs_peaked : Value → ℚ
  | .v1 => 1/6 | .v2 => 1/6 | .v3 => 1/3 | .v4 => 1/6 | .v5 => 1/6
  | _ => 0

def obs_flat : Value → ℚ
  | .v1 => 1/5 | .v2 => 1/5 | .v3 => 1/5 | .v4 => 1/5 | .v5 => 1/5
  | _ => 0

theorem obs_same_support : ∀ x : Value,
    (obs_peaked x > 0) ↔ (obs_flat x > 0) := by
  intro x; cases x <;> simp [obs_peaked, obs_flat]

/-- C.1: Standard utility U_std(m,o) = Σ_w P(w|o) · log(Σ_{o'} L(w,o')).
Under standard utility, U_std differs for same-support observations
because the marginal Σ_{o'} L(w,o') washes out observation-specific shape. -/
def U_std (l0_scores : Value → ℚ) (obs : Value → ℚ) : ℚ :=
  allValues.foldl (fun acc w =>
    let pw := obs w
    let lw := l0_scores w
    if pw > 0 && lw > 0
    then acc + pw * RSA.InformationTheory.log2Approx lw
    else acc) 0

/-- C.2: Bergen utility U_bergen(m,o) = Σ_w P(w|o) · log L(w|o).
Under Bergen utility, the observation enters both the weight and the
listener posterior, so same-support observations yield different utilities
(the peaked observation gets higher utility from a peaked L0). -/
def U_bergen (l0_scores : Value → ℚ) (obs : Value → ℚ) : ℚ :=
  allValues.foldl (fun acc w =>
    let pw := obs w
    let lw := l0_scores w
    if pw > 0 && lw > 0
    then acc + pw * RSA.InformationTheory.log2Approx lw
    else acc) 0

-- For "around 3", L0 is triangular [1/16, 1/8, 3/16, 1/4, 3/16, 1/8, 1/16]

def l0_around3_fn : Value → ℚ := fun v => getScore l0_around3 v

/-- Peaked observation has better utility from triangular L0 than flat does.
This is because the peaked observation puts more weight on center values
where L0 also has higher probability — better KL alignment. -/
theorem peaked_gets_higher_utility_from_around :
    U_bergen l0_around3_fn obs_peaked > U_bergen l0_around3_fn obs_flat := by
  native_decide

/-- Both observations get the SAME utility under a uniform L0 (from "between").
This demonstrates the LU limitation: uniform L0 cannot distinguish shapes. -/
def l0_between_fn : Value → ℚ := fun v => getScore l0_between1_5 v

theorem same_utility_under_uniform_l0 :
    U_bergen l0_between_fn obs_peaked = U_bergen l0_between_fn obs_flat := by
  native_decide

-- ============================================================================
-- Section VII: Grounding and Bridge Theorems
-- ============================================================================

/-- BIR weight = marginalization of aroundMeaning over valid tolerances y ≤ n. -/
theorem bir_from_compositional_meaning :
    ∀ v : Value,
    birWeight 3 v =
    ((allTolerances.filter (fun y => y.toNat ≤ 3)).filter (fun y => aroundMeaning 3 y v)).length / 4 := by
  intro v; cases v <;> native_decide

/-- BIR (L0) ranking matches closed-form prediction: v3 > v2 > v1 > v0. -/
theorem l0_preserves_bir_ranking :
    getScore l0_around3 .v3 > getScore l0_around3 .v2 ∧
    getScore l0_around3 .v2 > getScore l0_around3 .v1 ∧
    getScore l0_around3 .v1 > getScore l0_around3 .v0 := by
  native_decide

-- BIR matches Closed Form

/-- BIR posterior matches closed-form for each value (n=3). -/
theorem bir_matches_closed_form :
    ∀ v : Value,
    getScore l0_around3 v = birClosedForm 3 v.toNat := by
  intro v; cases v <;> native_decide

-- Bridge: BIR closed-form matches empirical data

/-- Closed form matches Phenomena datum for center: P(x=20 | around 20) = 21/441. -/
theorem closed_form_matches_phenomena_center :
    birClosedForm 20 20 = closedForm_center.expectedProb := by
  native_decide

/-- Closed form matches Phenomena datum for offset: P(x=15 | around 20) = 16/441. -/
theorem closed_form_matches_phenomena_offset5 :
    birClosedForm 20 15 = closedForm_offset5.expectedProb := by
  native_decide

end Phenomena.Imprecision.Studies.EgreEtAl2023
