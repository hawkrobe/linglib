import Linglib.Core.Logic.SystemZ
import Linglib.Phenomena.DefaultReasoning.TweetyNixon

/-!
# Goldszmidt & Pearl (1996): Qualitative Probabilities for Default Reasoning

@cite{goldszmidt-pearl-1996}

This study demonstrates System Z — the constructive derivation of
minimal ranking functions from a knowledge base of default rules.
Where @cite{spohn-1988} defines ranking functions as primitive objects,
G&P show how to *compute* the unique minimal admissible ranking κ^z
from a set of defaults, using tolerance-based stratification.

## Key demonstrations

1. **Tolerance stratification** (Example 17): Rules are partitioned by
   iteratively peeling off tolerated rules. In the Tweety scenario,
   "birds fly" is tolerated first (Z = 0), while "penguins are birds"
   and "penguins don't fly" are tolerated only after removing the
   first stratum (Z = 1).

2. **κ^z ranking**: The minimal admissible ranking assigns each world
   the lowest possible rank. Worlds verifying all rules get rank 0;
   worlds falsifying only low-priority rules get low ranks.

3. **Specificity**: More specific defaults automatically override
   general ones — penguinNoFly outranks penguinFlies because the
   penguin-specific rule has higher Z-priority.

4. **Bridge to Veltman**: The κ^z ranking derives the same specificity
   result that @cite{veltman-1996} obtains by stipulating orderings.

## Scenario

The Tweety Triangle with three rules: birds fly, penguins are birds,
penguins don't fly. The Z-ordering stratifies them, and κ^z resolves
the conflict in favor of the more specific default.
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

-- ══════════════════════════════════════════════════════════════════════
-- § 2. Knowledge Base (Example 17)
-- ══════════════════════════════════════════════════════════════════════

/-- r₁: "Birds fly" (b → f). -/
def r₁ : DefaultRule TweetyWorld := ⟨isBirdB, fliesB⟩

/-- r₂: "Penguins are birds" (p → b). Strict: no world falsifies it
    in TweetyWorld since all penguins are birds by construction. -/
def r₂ : DefaultRule TweetyWorld := ⟨isPenguinB, isBirdB⟩

/-- r₃: "Penguins don't fly" (p → ¬f). -/
def r₃ : DefaultRule TweetyWorld := ⟨isPenguinB, fun w => !fliesB w⟩

/-- The penguin-bird knowledge base Δ_pb. -/
def Δ_pb : KnowledgeBase TweetyWorld := [r₁, r₂, r₃]

-- ══════════════════════════════════════════════════════════════════════
-- § 3. Tolerance and Z-Ordering
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
-- § 4. Minimal Ranking κ^z
-- ══════════════════════════════════════════════════════════════════════

/-- Z-prioritized rules: Z(r₁) = 0, Z(r₂) = 1, Z(r₃) = 1. -/
def prioritized : List (DefaultRule TweetyWorld × ℕ) :=
  [(r₁, 0), (r₂, 1), (r₃, 1)]

/-- The minimal ranking κ^z for the Tweety knowledge base.

    κ^z values (Def. 12):
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
-- § 5. Admissibility Verification
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

-- ══════════════════════════════════════════════════════════════════════
-- § 6. Entailment Queries (Table 2)
-- ══════════════════════════════════════════════════════════════════════

/-! Plausible conclusions from Δ_pb, verified via z-entailment.
    These correspond to Table 2 of @cite{goldszmidt-pearl-1996}. -/

/-- "Do penguin-birds fly?" → NO. penguinNoFly (rank 1) outranks
    penguinFlies (rank 2). The more specific default wins. -/
theorem penguin_birds_dont_fly :
    rankEntails κ_z (fun w => isPenguinB w && isBirdB w)
                     (fun w => !fliesB w) := by
  intro w hw
  cases w <;> simp_all [isPenguinB, isBirdB, fliesB]
  exact ⟨.penguinNoFly, by decide, by native_decide⟩

/-- "Are birds typically penguins?" → NO. birdFlies (rank 0) is a
    non-penguin bird, outranking all penguin worlds. -/
theorem birds_not_typically_penguins :
    ¬rankEntails κ_z isBirdB isPenguinB := by
  intro h
  have := h .birdFlies rfl
  obtain ⟨v, hv, hlt⟩ := this
  cases v <;> simp_all [isPenguinB, isBirdB] <;>
    simp [κ_z, zRanking, zRankValue, zRankValue.maxFalsifiedPriority,
      prioritized, r₁, r₂, r₃, DefaultRule.falsified, isBirdB, fliesB, isPenguinB] at hlt

/-- "Do birds fly?" → YES. birdFlies (rank 0) is the most normal
    bird world and it flies. -/
theorem birds_fly :
    rankEntails κ_z isBirdB fliesB := by
  intro w hw
  cases w <;> simp_all [isBirdB, fliesB]
  all_goals exact ⟨.birdFlies, rfl, by native_decide⟩

-- ══════════════════════════════════════════════════════════════════════
-- § 7. Specificity: κ^z Derives What Veltman Stipulates
-- ══════════════════════════════════════════════════════════════════════

/-- The κ^z ranking makes penguinNoFly strictly more plausible than
    penguinFlies. This is the specificity result that @cite{veltman-1996}
    obtains by manually stipulating a penguin-domain ordering. -/
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

end Phenomena.DefaultReasoning.Studies.GoldszmidtPearl1996
