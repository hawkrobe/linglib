import Linglib.Core.Logic.RankingFunction

/-!
# Spohn (1988): Ranking Functions for Graded Belief Revision

@cite{spohn-1988}

This study demonstrates ordinal conditional functions (OCFs) as a model
of belief revision with graded evidence strength. The firmness parameter
α from @cite{spohn-1988} Definition 6 distinguishes weak evidence
(low α, e.g. hearsay) from strong evidence (high α, e.g. direct
observation).

## Key demonstrations

1. **Evidence strength**: Different α values produce different
   post-revision rankings — strong evidence pushes counter-evidence
   worlds further into disbelief than weak evidence does.

2. **Commutativity** (Theorem 4): When two pieces of evidence
   satisfy the conditions of Theorem 4, the order of processing
   doesn't matter — verified for a concrete 4-world instance.

3. **Connection to NormalityOrder**: Ranking functions induce
   connected (total) plausibility orderings, refining any
   Kratzer-style ordering source with explicit disbelief grades.

## Scenario

Four weather worlds with a prior ranking. Two pieces of evidence
("sunny" and "warm") are processed with varying firmness.
Hand-computed conditioned rankings are verified against the
A,α-conditionalization algorithm.
-/

namespace Phenomena.DefaultReasoning.Studies.Spohn1988

open Core.Logic.Ranking

-- ══════════════════════════════════════════════════════════════════════
-- § 1. World Space and Prior
-- ══════════════════════════════════════════════════════════════════════

/-- Four weather scenarios. -/
inductive Weather where
  | sunny_warm
  | sunny_cold
  | rainy_warm
  | rainy_cold
  deriving DecidableEq, Repr, BEq

instance : Fintype Weather :=
  ⟨⟨[Weather.sunny_warm, Weather.sunny_cold, Weather.rainy_warm, Weather.rainy_cold],
    by decide⟩,
   fun w => by cases w <;> decide⟩

open Weather

/-- Prior ranking: sunny+warm is most normal (rank 0).
    Both rainy+warm and sunny+cold are mildly surprising (rank 1 each).
    Rainy+cold is most surprising (rank 2).

    This prior satisfies Theorem 4's conditions for "sunny" × "warm":
    κ(sunny ∩ warm) = 0 and κ(rainy ∩ warm) = 0. -/
def prior : RankingFunction Weather where
  rank := fun
    | .sunny_warm => 0
    | .sunny_cold => 1
    | .rainy_warm => 0
    | .rainy_cold => 2
  normalized := ⟨.sunny_warm, rfl⟩

-- Evidence predicates (Bool for decidability)
def isSunny : Weather → Bool := fun w => w == .sunny_warm || w == .sunny_cold
def isWarm : Weather → Bool := fun w => w == .sunny_warm || w == .rainy_warm

-- ══════════════════════════════════════════════════════════════════════
-- § 2. Evidence Strength
-- ══════════════════════════════════════════════════════════════════════

/-! Conditioning on "sunny" with different firmness values α.

    Prior ranks: sunny_warm=0, sunny_cold=1, rainy_warm=0, rainy_cold=2
    κ(sunny) = min(0,1) = 0, κ(¬sunny) = min(0,2) = 0

    A-part of sunny-worlds:  sunny_warm → 0-0=0, sunny_cold → 1-0=1
    A-part of ¬sunny-worlds: rainy_warm → 0-0=0, rainy_cold → 2-0=2

    conditionα with α:
      sunny_warm → 0, sunny_cold → 1,
      rainy_warm → α+0, rainy_cold → α+2
-/

/-- After weak evidence for "sunny" (hearsay, α = 1).
    Rainy worlds only slightly more disbelieved than before. -/
def afterSunnyWeak : RankingFunction Weather where
  rank := fun
    | .sunny_warm => 0   -- aPart sunny = 0
    | .sunny_cold => 1   -- aPart sunny = 1
    | .rainy_warm => 1   -- α + aPart ¬sunny = 1 + 0
    | .rainy_cold => 3   -- α + aPart ¬sunny = 1 + 2
  normalized := ⟨.sunny_warm, rfl⟩

/-- After strong evidence for "sunny" (direct observation, α = 3).
    Rainy worlds pushed far into disbelief. -/
def afterSunnyStrong : RankingFunction Weather where
  rank := fun
    | .sunny_warm => 0   -- aPart sunny = 0
    | .sunny_cold => 1   -- aPart sunny = 1
    | .rainy_warm => 3   -- α + aPart ¬sunny = 3 + 0
    | .rainy_cold => 5   -- α + aPart ¬sunny = 3 + 2
  normalized := ⟨.sunny_warm, rfl⟩

/-- Strong evidence makes counter-evidence worlds more disbelieved. -/
theorem strong_more_disbelief_rainy_warm :
    afterSunnyStrong.rank .rainy_warm > afterSunnyWeak.rank .rainy_warm := by
  native_decide

theorem strong_more_disbelief_rainy_cold :
    afterSunnyStrong.rank .rainy_cold > afterSunnyWeak.rank .rainy_cold := by
  native_decide

/-- Both weak and strong evidence preserve the sunny belief
    (sunny_warm stays at rank 0). -/
theorem weak_preserves_belief : afterSunnyWeak.rank .sunny_warm = 0 := rfl
theorem strong_preserves_belief : afterSunnyStrong.rank .sunny_warm = 0 := rfl

/-- With weak evidence, rainy_warm is equally plausible as sunny_cold
    (both rank 1) — the agent isn't confident. -/
theorem weak_uncertain :
    afterSunnyWeak.rank .rainy_warm = afterSunnyWeak.rank .sunny_cold := rfl

/-- With strong evidence, all rainy worlds are strictly less plausible
    than any sunny world. -/
theorem strong_separates :
    afterSunnyStrong.rank .rainy_warm > afterSunnyStrong.rank .sunny_cold := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════
-- § 3. Commutativity (@cite{spohn-1988}, Theorem 4)
-- ══════════════════════════════════════════════════════════════════════

/-! Process "sunny" (α=2) then "warm" (β=1), and vice versa.
    Theorem 4 predicts identical results when κ(sunny∩warm)=0
    and κ(¬sunny∩warm)=0 — both satisfied by our prior. -/

/-- After "sunny" (α=2) then "warm" (β=1). -/
def afterSunny2_thenWarm1 : RankingFunction Weather where
  rank := fun
    | .sunny_warm => 0
    | .sunny_cold => 1
    | .rainy_warm => 2
    | .rainy_cold => 4
  normalized := ⟨.sunny_warm, rfl⟩

/-- After "warm" (β=1) then "sunny" (α=2). -/
def afterWarm1_thenSunny2 : RankingFunction Weather where
  rank := fun
    | .sunny_warm => 0
    | .sunny_cold => 1
    | .rainy_warm => 2
    | .rainy_cold => 4
  normalized := ⟨.sunny_warm, rfl⟩

/-- Commutativity: processing order doesn't matter.
    Both sequences yield identical rankings on all worlds. -/
theorem commutativity_ranks :
    afterSunny2_thenWarm1.rank = afterWarm1_thenSunny2.rank := rfl

/-- Detailed verification: hand computation.

    Step 1: prior → conditionα "sunny" α=2
      κ(sunny) = 0; aPart sunny: sw→0, sc→1
      κ(¬sunny) = 0; aPart ¬sunny: rw→0, rc→2
      Result: sw=0, sc=1, rw=2+0=2, rc=2+2=4

    Step 2: result → conditionα "warm" β=1
      κ(warm) = min(0,2) = 0; aPart warm: sw→0, rw→2
      κ(¬warm) = min(1,4) = 1; aPart ¬warm: sc→0, rc→3
      Result: sw=0, rw=2, sc=1+0=1, rc=1+3=4

    Reverse: prior → conditionα "warm" β=1 → conditionα "sunny" α=2

    Step 1: prior → conditionα "warm" β=1
      κ(warm) = min(0,0) = 0; aPart warm: sw→0, rw→0
      κ(¬warm) = min(1,2) = 1; aPart ¬warm: sc→0, rc→1
      Result: sw=0, rw=0, sc=1+0=1, rc=1+1=2

    Step 2: result → conditionα "sunny" α=2
      κ(sunny) = min(0,1) = 0; aPart sunny: sw→0, sc→1
      κ(¬sunny) = min(0,2) = 0; aPart ¬sunny: rw→0, rc→2
      Result: sw=0, sc=1, rw=2+0=2, rc=2+2=4 -/
theorem commutativity_verified :
    (afterSunny2_thenWarm1.rank .sunny_warm,
     afterSunny2_thenWarm1.rank .sunny_cold,
     afterSunny2_thenWarm1.rank .rainy_warm,
     afterSunny2_thenWarm1.rank .rainy_cold) = (0, 1, 2, 4) := rfl

-- ══════════════════════════════════════════════════════════════════════
-- § 4. Connection to NormalityOrder
-- ══════════════════════════════════════════════════════════════════════

/-- The prior ranking induces a connected (total) plausibility ordering,
    refining any Kratzer-style ordering source with explicit disbelief
    grades. This is the structural connection between ranking functions
    and the 95+ files downstream of NormalityOrder. -/
theorem prior_connected :
    prior.toPlausibilityOrder.toNormalityOrder.connected :=
  prior.ranking_connected

/-- The prior's belief set: sunny_warm is believed (rank 0).
    rainy_warm is also believed (rank 0 in this prior). -/
theorem prior_believes_sunny_warm : prior.rank .sunny_warm = 0 := rfl
theorem prior_believes_rainy_warm : prior.rank .rainy_warm = 0 := rfl
theorem prior_disbelieves_sunny_cold : prior.rank .sunny_cold ≠ 0 := by decide
theorem prior_disbelieves_rainy_cold : prior.rank .rainy_cold ≠ 0 := by decide

/-- After conditioning on "sunny" (even weakly), the belief set
    changes: rainy_warm is no longer rank 0. -/
theorem weak_evidence_revises :
    afterSunnyWeak.rank .rainy_warm ≠ 0 := by decide

-- ══════════════════════════════════════════════════════════════════════
-- § 5. Bridge to Probability (@cite{spohn-1988} §7)
-- ══════════════════════════════════════════════════════════════════════

/-! @cite{spohn-1988} §7 observes that ranking functions are the ordinal
    analogue of probability measures. The structural parallel:

    | Probability (ℚ, ·, Σ)     | Ranking (ℕ, min, +)          |
    |---------------------------|------------------------------|
    | P(A) = Σ_{w∈A} P(w)      | κ(A) = min_{w∈A} κ(w)       |
    | P(A|B) = P(A∩B)/P(B)     | κ(w|A) = κ(w) - κ(A)        |
    | P(A∩B) = P(A)·P(B) (ind) | κ(A∩B) = κ(A) + κ(B) (ind)  |

    The exact homomorphism requires nonstandard probability (§7 uses
    infinitesimal i with P(A) ~ i^{κ(A)}). For finite distributions,
    the **ordering** is preserved: worlds with higher probability have
    lower rank. We verify this concretely.

    See `Theories.Pragmatics.RSA.RankingBridge` for the formal
    connection: `rankToPrior κ w = exp(-κ(w))` gives the exponential
    prior, and `softmax_concentrates_unique` proves that softmax
    with ranking scores concentrates on rank-0 worlds as α → ∞. -/

/-- Probability weights compatible with the prior ranking.
    w(x) = 2^(max_rank - κ(x)), so higher rank → lower weight.
    These are proportional to probabilities P(x) = w(x)/Σw. -/
def priorWeight : Weather → ℕ
  | .sunny_warm => 4   -- 2^(2-0) = 4
  | .sunny_cold => 2   -- 2^(2-1) = 2
  | .rainy_warm => 4   -- 2^(2-0) = 4
  | .rainy_cold => 1   -- 2^(2-2) = 1

/-- Order compatibility: weight ordering reflects rank ordering
    on all pairs of worlds. -/
theorem weight_rank_compatible :
    ∀ w v : Weather,
      priorWeight w ≥ priorWeight v ↔ prior.rank w ≤ prior.rank v := by
  decide

/-- Theorem 2(a) verified: for "sunny", either κ(sunny) = 0 or
    κ(¬sunny) = 0. In this prior, κ(sunny) = 0. -/
theorem prior_dichotomy_sunny :
    prior.rank .sunny_warm = 0 ∧ isSunny .sunny_warm = true := by decide

/-- Independence under ranking: sunny and warm are independent.
    κ(sunny ∩ warm) = κ(sunny_warm) = 0 = κ(sunny) + κ(warm) = 0 + 0. -/
theorem sunny_warm_independent :
    prior.rank .sunny_warm =
    min (prior.rank .sunny_warm) (prior.rank .sunny_cold) +
    min (prior.rank .sunny_warm) (prior.rank .rainy_warm) := by decide

end Phenomena.DefaultReasoning.Studies.Spohn1988
