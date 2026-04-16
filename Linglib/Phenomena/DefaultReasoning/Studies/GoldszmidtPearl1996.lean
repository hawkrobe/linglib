import Linglib.Core.Logic.SystemZ
import Linglib.Phenomena.DefaultReasoning.TweetyNixon
import Linglib.Phenomena.DefaultReasoning.Studies.Veltman1996
import Linglib.Theories.Pragmatics.RSA.Core.RankingBridge

/-!
# Goldszmidt & Pearl (1996): Qualitative Probabilities for Default Reasoning

@cite{goldszmidt-pearl-1996}

This study demonstrates System Z — the constructive derivation of
minimal ranking functions from a knowledge base of default rules.
Where @cite{spohn-1988} defines ranking functions as primitive objects,
G&P show how to *compute* the unique minimal admissible ranking κ^z
from a set of defaults, using tolerance-based stratification.

## Key demonstrations

1. **Tolerance stratification**: Rules are partitioned by iteratively
   peeling off tolerated rules (Consistency-Test, Fig. 2). In the
   3-rule subset of the Tweety scenario (r₁–r₃ from Example 17),
   "birds fly" is tolerated first (Z = 0), while "penguins are birds"
   and "penguins don't fly" are tolerated only after removing the
   first stratum (Z = 1).

2. **κ^z ranking** (Definition 12): The minimal admissible ranking
   assigns each world the lowest possible rank. Worlds verifying all
   rules get rank 0; worlds falsifying only low-priority rules get
   low ranks.

3. **Specificity**: More specific defaults automatically override
   general ones — penguinNoFly outranks penguinFlies because the
   penguin-specific rule has higher Z-priority.

4. **Bridge to Veltman**: The κ^z ranking derives the same specificity
   result that @cite{veltman-1996} obtains by stipulating orderings.
   We prove the agreement directly.

## Scenario

We formalize rules r₁–r₃ from Example 17 (the paper's full example
has 5 rules including r₄: b→w and r₅: f→a, which would require
extending TweetyWorld with wings/airborne features). The 3-rule
subset is sufficient to demonstrate tolerance stratification, κ^z
construction, admissibility, and specificity.
-/

namespace Phenomena.DefaultReasoning.Studies.GoldszmidtPearl1996

open Core.Logic.SystemZ
open Core.Logic.Ranking
open Phenomena.DefaultReasoning

-- ══════════════════════════════════════════════════════════════════════
-- § 1. Bool Predicates for TweetyWorld
-- ══════════════════════════════════════════════════════════════════════

/-- All Tweety worlds are birds. -/
def isBirdB : TweetyWorld → Bool := fun _ => true

def isPenguinB : TweetyWorld → Bool
  | .penguinFlies | .penguinNoFly => true
  | _ => false

def fliesB : TweetyWorld → Bool
  | .birdFlies | .penguinFlies => true
  | _ => false

/-- Bool predicates agree with the Prop predicates in TweetyNixon. -/
theorem isBirdB_iff (w : TweetyWorld) : isBirdB w = true ↔ isBird w := by
  cases w <;> simp [isBirdB, isBird]

theorem isPenguinB_iff (w : TweetyWorld) : isPenguinB w = true ↔ isPenguin w := by
  cases w <;> simp [isPenguinB, isPenguin]

theorem fliesB_iff (w : TweetyWorld) : fliesB w = true ↔ flies w := by
  cases w <;> simp [fliesB, flies]

-- ══════════════════════════════════════════════════════════════════════
-- § 2. Knowledge Base (rules r₁–r₃ from Example 17)
-- ══════════════════════════════════════════════════════════════════════

/-- r₁: "Birds fly" (b → f). -/
def r₁ : DefaultRule TweetyWorld := ⟨isBirdB, fliesB⟩

/-- r₂: "Penguins are birds" (p → b). Strict: no world falsifies it
    in TweetyWorld since all penguins are birds by construction. -/
def r₂ : DefaultRule TweetyWorld := ⟨isPenguinB, isBirdB⟩

/-- r₃: "Penguins don't fly" (p → ¬f). -/
def r₃ : DefaultRule TweetyWorld := ⟨isPenguinB, fun w => !fliesB w⟩

/-- The penguin-bird knowledge base Δ_pb (rules r₁–r₃). -/
def Δ_pb : KnowledgeBase TweetyWorld := [r₁, r₂, r₃]

-- ══════════════════════════════════════════════════════════════════════
-- § 3. Tolerance and Z-Ordering (Consistency-Test, Fig. 2)
-- ══════════════════════════════════════════════════════════════════════

/-! Stratum 0: r₁ is tolerated by Δ_pb (birdFlies verifies r₁ and all
    material counterparts). r₂ and r₃ are not tolerated (no world
    satisfies their antecedent + consequent while also satisfying
    b → f as a material conditional).

    Stratum 1: After removing r₁, both r₂ and r₃ are tolerated
    (penguinNoFly verifies both and satisfies the remaining material
    counterparts).

    Z-priorities: Z(r₁) = 0, Z(r₂) = 1, Z(r₃) = 1. -/

theorem r₁_tolerated_by_Δ : tolerated r₁ Δ_pb :=
  ⟨.birdFlies, rfl, rfl, rfl⟩

theorem r₂_not_tolerated_by_Δ : ¬tolerated r₂ Δ_pb := by
  intro ⟨w, ha, hc, hall⟩; cases w <;> simp_all [r₂, isPenguinB, isBirdB, Δ_pb,
    r₁, r₂, r₃, DefaultRule.verified, fliesB, List.all]

theorem r₃_not_tolerated_by_Δ : ¬tolerated r₃ Δ_pb := by
  intro ⟨w, ha, hc, hall⟩; cases w <;> simp_all [r₃, isPenguinB, fliesB, Δ_pb,
    r₁, r₂, r₃, DefaultRule.verified, isBirdB, List.all]

/-- After removing stratum 0 (r₁), both r₂ and r₃ are tolerated. -/
def Δ₁ : KnowledgeBase TweetyWorld := [r₂, r₃]

theorem r₂_tolerated_by_Δ₁ : tolerated r₂ Δ₁ :=
  ⟨.penguinNoFly, rfl, rfl, rfl⟩

theorem r₃_tolerated_by_Δ₁ : tolerated r₃ Δ₁ :=
  ⟨.penguinNoFly, rfl, rfl, rfl⟩

-- ══════════════════════════════════════════════════════════════════════
-- § 4. Minimal Ranking κ^z (Definition 12)
-- ══════════════════════════════════════════════════════════════════════

/-- Z-prioritized rules: Z(r₁) = 0, Z(r₂) = 1, Z(r₃) = 1. -/
def prioritized : List (DefaultRule TweetyWorld × ℕ) :=
  [(r₁, 0), (r₂, 1), (r₃, 1)]

/-- The minimal ranking κ^z for the Tweety knowledge base.

    κ^z values (Definition 12):
    - birdFlies:    falsifies nothing → 0
    - birdNoFly:    falsifies r₁ (Z=0) → max(0)+1 = 1
    - penguinFlies: falsifies r₃ (Z=1) → max(1)+1 = 2
    - penguinNoFly: falsifies r₁ (Z=0) → max(0)+1 = 1 -/
def κ_z : RankingFunction TweetyWorld :=
  zRanking prioritized ⟨.birdFlies, by native_decide⟩

-- Verify rank values
theorem κz_birdFlies : κ_z.rank .birdFlies = 0 := by native_decide
theorem κz_birdNoFly : κ_z.rank .birdNoFly = 1 := by native_decide
theorem κz_penguinFlies : κ_z.rank .penguinFlies = 2 := by native_decide
theorem κz_penguinNoFly : κ_z.rank .penguinNoFly = 1 := by native_decide

-- ══════════════════════════════════════════════════════════════════════
-- § 5. Admissibility Verification (Definition 2)
-- ══════════════════════════════════════════════════════════════════════

/-- r₁ (b → f) is admissible: every world falsifying it (birdNoFly,
    penguinNoFly, both rank 1) is outranked by birdFlies (rank 0). -/
theorem r₁_admissible : ∀ w : TweetyWorld, r₁.falsified w = true →
    ∃ v, (r₁.ante v && r₁.cons v) = true ∧ κ_z.rank v < κ_z.rank w := by
  intro w hw
  cases w <;> simp_all [r₁, DefaultRule.falsified, isBirdB, fliesB]
  all_goals exact ⟨.birdFlies, rfl, by native_decide⟩

/-- r₂ (p → b) is vacuously admissible: no world falsifies it. -/
theorem r₂_admissible : ∀ w : TweetyWorld, r₂.falsified w = true →
    ∃ v, (r₂.ante v && r₂.cons v) = true ∧ κ_z.rank v < κ_z.rank w := by
  intro w hw
  cases w <;> simp_all [r₂, DefaultRule.falsified, isPenguinB, isBirdB]

/-- r₃ (p → ¬f) is admissible: the only falsifying world is
    penguinFlies (rank 2), outranked by penguinNoFly (rank 1). -/
theorem r₃_admissible : ∀ w : TweetyWorld, r₃.falsified w = true →
    ∃ v, (r₃.ante v && r₃.cons v) = true ∧ κ_z.rank v < κ_z.rank w := by
  intro w hw
  cases w <;> simp_all [r₃, DefaultRule.falsified, isPenguinB, fliesB]
  exact ⟨.penguinNoFly, by decide, by native_decide⟩

/-- κ^z is admissible relative to the full knowledge base Δ_pb
    (Definition 2). -/
theorem κz_admissible : admissible κ_z Δ_pb := by
  rw [admissible, List.forall_iff_forall_mem]
  intro r hr
  simp [Δ_pb] at hr
  rcases hr with rfl | rfl | rfl
  · exact r₁_admissible
  · exact r₂_admissible
  · exact r₃_admissible

-- ══════════════════════════════════════════════════════════════════════
-- § 6. Entailment Queries
-- ══════════════════════════════════════════════════════════════════════

/-! z-entailment queries on Δ_pb. These cover two of the five queries
    in Table 2 (the remaining three — red birds fly, birds airborne,
    penguins winged — require r₄/r₅ and a richer world type). -/

/-- "Do penguin-birds fly?" → NO (z-entailment). penguinNoFly (rank 1)
    outranks penguinFlies (rank 2). The more specific default wins. -/
theorem penguin_birds_dont_fly :
    rankEntails κ_z (fun w => isPenguinB w && isBirdB w)
                     (fun w => !fliesB w) := by
  intro w hw
  cases w <;> simp_all [isPenguinB, isBirdB, fliesB]
  exact ⟨.penguinNoFly, by decide, by native_decide⟩

/-- "Are birds typically penguins?" → NO (z-entailment). birdFlies
    (rank 0) is a non-penguin bird, outranking all penguin worlds. -/
theorem birds_not_typically_penguins :
    ¬rankEntails κ_z isBirdB isPenguinB := by
  intro h
  have := h .birdFlies rfl
  obtain ⟨v, hv, hlt⟩ := this
  cases v <;> simp_all [isPenguinB, isBirdB] <;>
    simp [κ_z, zRanking, zRankValue, zRankValue.maxFalsifiedPriority,
      prioritized, r₁, r₂, r₃, DefaultRule.falsified, isBirdB, fliesB, isPenguinB] at hlt

/-- "Do birds fly?" → YES (z-entailment). birdFlies (rank 0) is the
    most normal bird world and it flies. -/
theorem birds_fly :
    rankEntails κ_z isBirdB fliesB := by
  intro w hw
  cases w <;> simp_all [isBirdB, fliesB]
  all_goals exact ⟨.birdFlies, rfl, by native_decide⟩

-- ══════════════════════════════════════════════════════════════════════
-- § 7. Specificity: κ^z Derives What Veltman Stipulates
-- ══════════════════════════════════════════════════════════════════════

/-- The κ^z ranking makes penguinNoFly strictly more plausible than
    penguinFlies. -/
theorem specificity_penguinNoFly_beats_penguinFlies :
    κ_z.rank .penguinNoFly < κ_z.rank .penguinFlies := by native_decide

/-- The κ^z ranking preserves the general default: among non-penguin
    birds, flying is more normal than not flying. -/
theorem general_default_preserved :
    κ_z.rank .birdFlies < κ_z.rank .birdNoFly := by native_decide

/-- The induced plausibility ordering is connected (total), so
    Rational Monotonicity holds. -/
theorem κz_connected :
    κ_z.toPlausibilityOrder.toNormalityOrder.connected :=
  κ_z.ranking_connected

-- ══════════════════════════════════════════════════════════════════════
-- § 8. Bridge to Veltman 1996
-- ══════════════════════════════════════════════════════════════════════

/-! @cite{veltman-1996} manually stipulates subdomain orderings to
    resolve the Tweety Triangle: `birdOrd` promotes flying,
    `penguinOrd` promotes not-flying. The key result is
    `penguinFlies_not_normal_in_birds` — penguinFlies fails the
    normality test because the penguin subdomain ordering demotes it.

    G&P's System Z *derives* the same specificity result from the
    rules alone, without any stipulated orderings. The following
    theorem makes this derivation-vs-stipulation relationship explicit
    by combining both papers' conclusions. -/

open Phenomena.DefaultReasoning.Studies.Veltman1996 in

/-- What @cite{veltman-1996} stipulates about penguin normality,
    @cite{goldszmidt-pearl-1996}'s System Z derives:
    - Veltman: penguinFlies is not normal among birds (via stipulated
      penguin subdomain ordering)
    - G&P: penguinFlies has strictly higher κ^z rank than birdFlies
      (derived from tolerance stratification alone)
    Both reach the same conclusion: flying penguins are less normal
    than non-flying penguins in a bird context. -/
theorem gp_derives_veltman_specificity :
    TweetyWorld.penguinFlies ∉ tweetyFrame.normal birdDomain ∧
    κ_z.rank .penguinFlies > κ_z.rank .birdFlies :=
  ⟨penguinFlies_not_normal_in_birds, by native_decide⟩

-- ══════════════════════════════════════════════════════════════════════
-- § 9. Bridge to RSA: κ^z as Infinite-Rationality Limit
-- ══════════════════════════════════════════════════════════════════════

/-! @cite{frank-goodman-2012}'s RSA framework uses softmax-based
    Bayesian inference with a finite rationality parameter α.
    @cite{goldszmidt-pearl-1996}'s System Z uses ranking functions
    for qualitative default reasoning.

    The two frameworks are endpoints of the same continuum: as
    α → ∞, softmax concentrates on the most normal (rank-0) worlds,
    recovering ranking-based entailment from probabilistic inference.

    We demonstrate this concretely: the softmax distribution with
    scores derived from κ^z concentrates on birdFlies (the unique
    rank-0 world) as α → ∞. This means RSA's pragmatic listener
    with infinite rationality reasons exactly like System Z. -/

open Pragmatics.RSA.RankingBridge

instance : Nonempty TweetyWorld := ⟨.birdFlies⟩

/-- birdFlies is the unique rank-0 world under κ^z. -/
theorem κz_unique_rank_zero :
    ∀ v : TweetyWorld, v ≠ .birdFlies → 0 < κ_z.rank v := by
  intro v hv; cases v <;> simp_all <;> native_decide

/-- The softmax distribution softmax(-κ^z, α) concentrates on
    birdFlies as α → ∞. This is the core RSA–ranking bridge for
    the Tweety scenario: an RSA listener with infinite rationality
    assigns probability 1 to the most normal world. -/
theorem κz_softmax_concentrates :
    ∀ w, Filter.Tendsto (fun α => Core.softmax (rankToScore κ_z) α w)
      Filter.atTop (nhds (if w = .birdFlies then 1 else 0)) :=
  softmax_concentrates_unique κ_z .birdFlies κz_birdFlies κz_unique_rank_zero

/-- Under κ^z, all minimum-rank bird-worlds fly. This connects
    the ranking entailment `birds_fly` to the softmax limit:
    as α → ∞, the softmax listener restricted to bird-worlds
    assigns all probability to flying worlds. -/
theorem minRank_birds_fly :
    ∀ w : TweetyWorld, isBirdB w = true →
      κ_z.rank w = minRankBool κ_z isBirdB ⟨.birdFlies, rfl⟩ →
      fliesB w = true :=
  minRank_worlds_satisfy κ_z isBirdB fliesB birds_fly ⟨.birdFlies, rfl⟩

/-- Under κ^z, all minimum-rank penguin-worlds don't fly. The
    specificity result — penguins override the general bird default —
    is precisely the α → ∞ limit of RSA inference restricted to
    the penguin domain. -/
theorem minRank_penguins_dont_fly :
    ∀ w : TweetyWorld, (isPenguinB w && isBirdB w) = true →
      κ_z.rank w = minRankBool κ_z
        (fun w => isPenguinB w && isBirdB w) ⟨.penguinNoFly, rfl⟩ →
      (fun w => !fliesB w) w = true :=
  minRank_worlds_satisfy κ_z
    (fun w => isPenguinB w && isBirdB w)
    (fun w => !fliesB w)
    penguin_birds_dont_fly
    ⟨.penguinNoFly, rfl⟩

/-- **Conditional limit: "Do birds fly?" → probability 1.**
    As α → ∞, the conditional probability P_α(flies|bird) → 1
    under κ^z scores. This is the full conditional softmax limit
    theorem applied to the Tweety scenario. -/
theorem condProb_birds_fly :
    Filter.Tendsto
      (fun α => Pragmatics.RSA.RankingBridge.condProb
        (rankToScore κ_z) α isBirdB fliesB)
      Filter.atTop (nhds 1) :=
  Pragmatics.RSA.RankingBridge.condProb_tendsto_one
    κ_z isBirdB fliesB birds_fly ⟨.birdFlies, rfl⟩

/-- **Conditional limit: "Do penguin-birds fly?" → probability 0.**
    As α → ∞, the conditional probability P_α(flies|penguin∧bird) → 0,
    because ranking entailment says penguin-birds *don't* fly.
    We prove this by showing P_α(¬flies|penguin∧bird) → 1. -/
theorem condProb_penguins_dont_fly :
    Filter.Tendsto
      (fun α => Pragmatics.RSA.RankingBridge.condProb
        (rankToScore κ_z) α
        (fun w => isPenguinB w && isBirdB w) (fun w => !fliesB w))
      Filter.atTop (nhds 1) :=
  Pragmatics.RSA.RankingBridge.condProb_tendsto_one κ_z
    (fun w => isPenguinB w && isBirdB w) (fun w => !fliesB w)
    penguin_birds_dont_fly ⟨.penguinNoFly, rfl⟩

-- ══════════════════════════════════════════════════════════════════════
-- § 10. Computed Consistency-Test
-- ══════════════════════════════════════════════════════════════════════

/-- The Consistency-Test (Fig. 2) computes the same Z-priorities as
    our manually-verified `prioritized` list: Z(r₁)=0, Z(r₂)=1, Z(r₃)=1. -/
theorem Δ_pb_computed :
    (zPriorities Δ_pb).map Prod.snd = [0, 1, 1] := by native_decide

-- ══════════════════════════════════════════════════════════════════════
-- § 11. System Z⁺: Variable-Strength Defaults (Definition 18)
-- ══════════════════════════════════════════════════════════════════════

/-! System Z⁺ augments each rule with a strength parameter δ, requiring
    a wider gap between verifying and falsifying worlds. The Z⁺-priority
    of a rule accounts for δ, giving stronger rules higher priority and
    thus wider separation in the ranking. -/

/-- Strength-augmented rules: δ₁=1, δ₂=1, δ₃=2.
    "Penguins don't fly" (r₃) is strongest. -/
def sr₁ : StrengthRule TweetyWorld := ⟨r₁, 1⟩
def sr₂ : StrengthRule TweetyWorld := ⟨r₂, 1⟩
def sr₃ : StrengthRule TweetyWorld := ⟨r₃, 2⟩

def Δ_pb_plus : StrengthKB TweetyWorld := [sr₁, sr₂, sr₃]

/-- Z⁺ priorities computed via the Z⁺_order procedure (Fig. 4) to
    satisfy δ-admissibility constraints.
    z⁺(r₁) = 1, z⁺(r₂) = 3, z⁺(r₃) = 4.

    The constraint for r₃ (δ=2) is κ(penguinNoFly) + 2 < κ(penguinFlies).
    Since penguinNoFly falsifies r₁ giving rank z⁺(r₁)+1 = 2,
    we need 2 + 2 < z⁺(r₃) + 1, so z⁺(r₃) ≥ 4.

    Note: z⁺(r₂) = 3 because the verifying world for r₂ (penguinNoFly)
    has κ = z⁺(r₁) + 1 = 2, so z⁺(r₂) = 2 + δ₂ = 2 + 1 = 3. r₂ is
    never falsified in TweetyWorld, so its priority doesn't affect ranks. -/
def zPlus_prioritized : List (DefaultRule TweetyWorld × ℕ) :=
  [(r₁, 1), (r₂, 3), (r₃, 4)]

/-- κ⁺: the Z⁺ ranking with wider gaps than κ^z.
    - birdFlies:    falsifies nothing → 0
    - birdNoFly:    falsifies r₁ (z⁺=1) → 2
    - penguinFlies: falsifies r₃ (z⁺=4) → 5
    - penguinNoFly: falsifies r₁ (z⁺=1) → 2 -/
def κ_plus : RankingFunction TweetyWorld :=
  zRanking zPlus_prioritized ⟨.birdFlies, by native_decide⟩

theorem κplus_birdFlies : κ_plus.rank .birdFlies = 0 := by native_decide
theorem κplus_birdNoFly : κ_plus.rank .birdNoFly = 2 := by native_decide
theorem κplus_penguinFlies : κ_plus.rank .penguinFlies = 5 := by native_decide
theorem κplus_penguinNoFly : κ_plus.rank .penguinNoFly = 2 := by native_decide

/-- κ⁺ is δ-admissible relative to the strength rules. -/
theorem κplus_strength_admissible : strengthAdmissible κ_plus Δ_pb_plus := by
  rw [strengthAdmissible, List.forall_iff_forall_mem]
  intro sr hsr
  simp [Δ_pb_plus] at hsr
  rcases hsr with rfl | rfl | rfl
  · -- sr₁ (b→f, δ=1): birdFlies (rank 0) witnesses 0+1 < 2
    intro w hw
    cases w <;> simp_all [sr₁, r₁, DefaultRule.falsified, isBirdB, fliesB]
    all_goals exact ⟨.birdFlies, rfl, by native_decide⟩
  · -- sr₂ (p→b, δ=1): vacuously true
    intro w hw
    cases w <;> simp_all [sr₂, r₂, DefaultRule.falsified, isPenguinB, isBirdB]
  · -- sr₃ (p→¬f, δ=2): penguinNoFly (rank 2) witnesses 2+2 < 5
    intro w hw
    cases w <;> simp_all [sr₃, r₃, DefaultRule.falsified, isPenguinB, fliesB]
    exact ⟨.penguinNoFly, by decide, by native_decide⟩

/-- κ^z's gap for r₃ is too small for δ₃=2: 1 + 2 ≥ 2.
    This motivates Z⁺ — the minimal ranking κ^z doesn't provide
    enough separation for variable-strength defaults. -/
theorem κz_gap_too_small_for_sr₃ :
    κ_z.rank .penguinNoFly + sr₃.strength ≥ κ_z.rank .penguinFlies := by native_decide

end Phenomena.DefaultReasoning.Studies.GoldszmidtPearl1996
