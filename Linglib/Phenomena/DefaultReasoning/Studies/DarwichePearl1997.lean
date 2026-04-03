import Linglib.Core.Logic.RankingFunction

/-!
# Darwiche & Pearl (1997): On the Logic of Iterated Belief Revision

@cite{darwiche-pearl-1997}

AGM belief revision constrains how a *single* revision should update
an agent's beliefs, but says nothing about how the agent's *disposition
to revise* should change. @cite{darwiche-pearl-1997} show that AGM-
compatible revision operators can behave pathologically under iteration,
and propose four additional postulates C1–C4 that rule out these
pathologies.

## Representation Theorem (Theorem 13)

C1–C4 are equivalent to conditions CR1–CR4 on the faithful assignment
(total pre-order) that represents an epistemic state:

- **CR1**: The ordering among μ-worlds is preserved.
- **CR2**: The ordering among ¬μ-worlds is preserved.
- **CR3**: If a μ-world was strictly below a ¬μ-world, it stays so.
- **CR4**: If a μ-world was ≤ a ¬μ-world, it stays so.

## Counterexamples (Tables A.1–A.4)

For each CR_i, there exists an AGM-compatible revision operator that
violates CR_i while satisfying the other three. This shows the four
conditions are logically independent — none is derivable from the rest.

## Bridge to Ranking Functions

`Core.Logic.Ranking.ranking_satisfies_C1..C4` proves that Spohn's
A,α-conditionalization satisfies all four postulates. The counterexamples
here use *non-ranking* revision operators — arbitrary total pre-order
transformations that respect AGM success but violate the D&P constraints.

## Linguistic Connection

Ranking functions → `PlausibilityOrder` → `NormalityOrder` → Kratzer's
ordering sources for modals/conditionals. The D&P postulates constrain
how modal bases evolve under discourse update — without them, an
agent's conditional beliefs can shift arbitrarily between utterances.
Dynamic semantics (DRT/DPL context update) is iterated revision:
each sentence revises the common ground, and C1–C4 ensure that
the ordering of live possibilities evolves rationally.
-/

namespace Phenomena.DefaultReasoning.Studies.DarwichePearl1997

open Core.Logic.Ranking
open Core.Order (NormalityOrder)

-- ══════════════════════════════════════════════════════════════════════
-- § 1. World Type
-- ══════════════════════════════════════════════════════════════════════

/-- Four-element world type for counterexamples. -/
inductive W4 where | w1 | w2 | w3 | w4
  deriving DecidableEq, Repr

instance : Fintype W4 :=
  ⟨⟨[W4.w1, W4.w2, W4.w3, W4.w4], by decide⟩,
   fun w => by cases w <;> decide⟩

open W4

-- ══════════════════════════════════════════════════════════════════════
-- § 2. Ranking → NormalityOrder Bridge
-- ══════════════════════════════════════════════════════════════════════

/-- Convert a ranking function to its induced normality ordering.
    `le w v ↔ κ(w) ≤ κ(v)`. Defined directly (not via `toPlausibilityOrder`)
    so that `le` reduces for `native_decide`. -/
@[reducible] def rankToOrder (κ : RankingFunction W4) : NormalityOrder W4 where
  le w v := κ.rank w ≤ κ.rank v
  le_refl _ := Nat.le_refl _
  le_trans _ _ _ h1 h2 := Nat.le_trans h1 h2

/-- `rankToOrder` agrees with the canonical path through `PlausibilityOrder`. -/
theorem rankToOrder_eq_canonical (κ : RankingFunction W4) :
    rankToOrder κ = κ.toPlausibilityOrder.toNormalityOrder :=
  NormalityOrder.ext fun _ _ => Iff.rfl

/-- AGM success: all rank-0 worlds in the posterior satisfy μ. -/
@[reducible] def agmSuccess (post : RankingFunction W4)
    (μ : W4 → Bool) : Prop :=
  ∀ w, post.rank w = 0 → μ w = true

-- ══════════════════════════════════════════════════════════════════════
-- § 3. Table A.1 — CR1 Violation
-- ══════════════════════════════════════════════════════════════════════

/-! Prior: w1=0, w2=1, w3=2, w4=3. Revise by μ = {w2,w3,w4}.
    Posterior: w1=1, w2=0, w3=2, w4=1.
    Within μ, the ordering of w3 vs w4 flips (2<3 → 2>1). -/

def prior_A1 : RankingFunction W4 where
  rank := fun | .w1 => 0 | .w2 => 1 | .w3 => 2 | .w4 => 3
  normalized := ⟨.w1, rfl⟩

def post_A1 : RankingFunction W4 where
  rank := fun | .w1 => 1 | .w2 => 0 | .w3 => 2 | .w4 => 1
  normalized := ⟨.w2, rfl⟩

def mu_A1 : W4 → Bool | .w1 => false | _ => true

theorem A1_agm : agmSuccess post_A1 mu_A1 := by native_decide
theorem A1_violates_CR1 :
    ¬NormalityOrder.satisfies_CR1 (rankToOrder prior_A1) (rankToOrder post_A1) mu_A1 := by
  native_decide
theorem A1_satisfies_CR2 :
    NormalityOrder.satisfies_CR2 (rankToOrder prior_A1) (rankToOrder post_A1) mu_A1 := by
  native_decide
theorem A1_satisfies_CR3 :
    NormalityOrder.satisfies_CR3 (rankToOrder prior_A1) (rankToOrder post_A1) mu_A1 := by
  native_decide
theorem A1_satisfies_CR4 :
    NormalityOrder.satisfies_CR4 (rankToOrder prior_A1) (rankToOrder post_A1) mu_A1 := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════
-- § 4. Table A.2 — CR2 Violation
-- ══════════════════════════════════════════════════════════════════════

/-! Prior: w1=0, w2=1, w3=1, w4=2. Revise by μ = {w3,w4}.
    Posterior: w1=2, w2=1, w3=0, w4=1.
    Within ¬μ = {w1,w2}, the ordering flips (0<1 → 2>1). -/

def prior_A2 : RankingFunction W4 where
  rank := fun | .w1 => 0 | .w2 => 1 | .w3 => 1 | .w4 => 2
  normalized := ⟨.w1, rfl⟩

def post_A2 : RankingFunction W4 where
  rank := fun | .w1 => 2 | .w2 => 1 | .w3 => 0 | .w4 => 1
  normalized := ⟨.w3, rfl⟩

def mu_A2 : W4 → Bool | .w3 => true | .w4 => true | _ => false

theorem A2_agm : agmSuccess post_A2 mu_A2 := by native_decide
theorem A2_satisfies_CR1 :
    NormalityOrder.satisfies_CR1 (rankToOrder prior_A2) (rankToOrder post_A2) mu_A2 := by
  native_decide
theorem A2_violates_CR2 :
    ¬NormalityOrder.satisfies_CR2 (rankToOrder prior_A2) (rankToOrder post_A2) mu_A2 := by
  native_decide
theorem A2_satisfies_CR3 :
    NormalityOrder.satisfies_CR3 (rankToOrder prior_A2) (rankToOrder post_A2) mu_A2 := by
  native_decide
theorem A2_satisfies_CR4 :
    NormalityOrder.satisfies_CR4 (rankToOrder prior_A2) (rankToOrder post_A2) mu_A2 := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════
-- § 5. Table A.3 — CR3 Violation
-- ══════════════════════════════════════════════════════════════════════

/-! Prior: w1=0, w2=1, w3=2, w4=3. Revise by μ = {w1,w2}.
    Posterior: w1=0, w2=2, w3=2, w4=3.
    w2 ∈ μ, w3 ∈ ¬μ: prior 1 < 2 (strict), posterior 2 ≤ 2 (not strict). -/

def prior_A3 : RankingFunction W4 where
  rank := fun | .w1 => 0 | .w2 => 1 | .w3 => 2 | .w4 => 3
  normalized := ⟨.w1, rfl⟩

def post_A3 : RankingFunction W4 where
  rank := fun | .w1 => 0 | .w2 => 2 | .w3 => 2 | .w4 => 3
  normalized := ⟨.w1, rfl⟩

def mu_A3 : W4 → Bool | .w1 => true | .w2 => true | _ => false

theorem A3_agm : agmSuccess post_A3 mu_A3 := by native_decide
theorem A3_satisfies_CR1 :
    NormalityOrder.satisfies_CR1 (rankToOrder prior_A3) (rankToOrder post_A3) mu_A3 := by
  native_decide
theorem A3_satisfies_CR2 :
    NormalityOrder.satisfies_CR2 (rankToOrder prior_A3) (rankToOrder post_A3) mu_A3 := by
  native_decide
theorem A3_violates_CR3 :
    ¬NormalityOrder.satisfies_CR3 (rankToOrder prior_A3) (rankToOrder post_A3) mu_A3 := by
  native_decide
theorem A3_satisfies_CR4 :
    NormalityOrder.satisfies_CR4 (rankToOrder prior_A3) (rankToOrder post_A3) mu_A3 := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════
-- § 6. Table A.4 — CR4 Violation
-- ══════════════════════════════════════════════════════════════════════

/-! Prior: w1=0, w2=1, w3=1, w4=2. Revise by μ = {w1,w2}.
    Posterior: w1=0, w2=2, w3=1, w4=3.
    w2 ∈ μ, w3 ∈ ¬μ: prior 1 ≤ 1, but posterior 2 > 1. -/

def prior_A4 : RankingFunction W4 where
  rank := fun | .w1 => 0 | .w2 => 1 | .w3 => 1 | .w4 => 2
  normalized := ⟨.w1, rfl⟩

def post_A4 : RankingFunction W4 where
  rank := fun | .w1 => 0 | .w2 => 2 | .w3 => 1 | .w4 => 3
  normalized := ⟨.w1, rfl⟩

def mu_A4 : W4 → Bool | .w1 => true | .w2 => true | _ => false

theorem A4_agm : agmSuccess post_A4 mu_A4 := by native_decide
theorem A4_satisfies_CR1 :
    NormalityOrder.satisfies_CR1 (rankToOrder prior_A4) (rankToOrder post_A4) mu_A4 := by
  native_decide
theorem A4_satisfies_CR2 :
    NormalityOrder.satisfies_CR2 (rankToOrder prior_A4) (rankToOrder post_A4) mu_A4 := by
  native_decide
theorem A4_satisfies_CR3 :
    NormalityOrder.satisfies_CR3 (rankToOrder prior_A4) (rankToOrder post_A4) mu_A4 := by
  native_decide
theorem A4_violates_CR4 :
    ¬NormalityOrder.satisfies_CR4 (rankToOrder prior_A4) (rankToOrder post_A4) mu_A4 := by
  native_decide

-- ══════════════════════════════════════════════════════════════════════
-- § 7. Independence of CR1–CR4
-- ══════════════════════════════════════════════════════════════════════

/-- The four conditions are logically independent: for each CR_i,
    there exists an AGM-compatible revision that violates CR_i alone.

    This is the content of @cite{darwiche-pearl-1997}, Appendix A. -/
theorem CR_independence :
    -- CR1 independent: violated alone
    (∃ p q : NormalityOrder W4, ∃ μ,
      ¬NormalityOrder.satisfies_CR1 p q μ ∧
      NormalityOrder.satisfies_CR2 p q μ ∧
      NormalityOrder.satisfies_CR3 p q μ ∧
      NormalityOrder.satisfies_CR4 p q μ) ∧
    -- CR2 independent: violated alone
    (∃ p q : NormalityOrder W4, ∃ μ,
      NormalityOrder.satisfies_CR1 p q μ ∧
      ¬NormalityOrder.satisfies_CR2 p q μ ∧
      NormalityOrder.satisfies_CR3 p q μ ∧
      NormalityOrder.satisfies_CR4 p q μ) ∧
    -- CR3 independent: violated alone
    (∃ p q : NormalityOrder W4, ∃ μ,
      NormalityOrder.satisfies_CR1 p q μ ∧
      NormalityOrder.satisfies_CR2 p q μ ∧
      ¬NormalityOrder.satisfies_CR3 p q μ ∧
      NormalityOrder.satisfies_CR4 p q μ) ∧
    -- CR4 independent: violated alone
    (∃ p q : NormalityOrder W4, ∃ μ,
      NormalityOrder.satisfies_CR1 p q μ ∧
      NormalityOrder.satisfies_CR2 p q μ ∧
      NormalityOrder.satisfies_CR3 p q μ ∧
      ¬NormalityOrder.satisfies_CR4 p q μ) :=
  ⟨⟨rankToOrder prior_A1, rankToOrder post_A1, mu_A1,
    A1_violates_CR1, A1_satisfies_CR2, A1_satisfies_CR3, A1_satisfies_CR4⟩,
   ⟨rankToOrder prior_A2, rankToOrder post_A2, mu_A2,
    A2_satisfies_CR1, A2_violates_CR2, A2_satisfies_CR3, A2_satisfies_CR4⟩,
   ⟨rankToOrder prior_A3, rankToOrder post_A3, mu_A3,
    A3_satisfies_CR1, A3_satisfies_CR2, A3_violates_CR3, A3_satisfies_CR4⟩,
   ⟨rankToOrder prior_A4, rankToOrder post_A4, mu_A4,
    A4_satisfies_CR1, A4_satisfies_CR2, A4_satisfies_CR3, A4_violates_CR4⟩⟩

-- ══════════════════════════════════════════════════════════════════════
-- § 8. Bridge: Ranking Conditioning Satisfies All C_i
-- ══════════════════════════════════════════════════════════════════════

/-! @cite{darwiche-pearl-1997}, Theorem 17: Spohn's ranking conditioning
    satisfies C1–C4 (equivalently CR1–CR4). The proofs are in
    `Core.Logic.Ranking`:

    - `ranking_satisfies_C1` — C1 holds for `conditionα` with any α, β
    - `ranking_satisfies_C2` — C2 holds for `conditionα` with any α, β
    - `ranking_satisfies_C3` — C3 holds for canonical `revise`
    - `ranking_satisfies_C4` — C4 holds for canonical `revise`

    Together with the counterexamples above, this shows that ranking
    conditioning is the *tightest* well-behaved revision operator:
    it satisfies all four independence conditions that AGM alone
    leaves unconstrained.

    The chain to linguistics:
    ```
    RankingFunction.revise
      → satisfies C1–C4 (this file's counterexamples show AGM alone doesn't)
      → PlausibilityOrder (via toPlausibilityOrder)
      → NormalityOrder (via toNormalityOrder)
      → Kratzer ordering sources (via fromProps)
      → modal/conditional semantics
    ```
-/

example : ∀ (κ : RankingFunction W4), κ.satisfies_C1 :=
  fun κ => RankingFunction.ranking_satisfies_C1 κ

example : ∀ (κ : RankingFunction W4), κ.satisfies_C2 :=
  fun κ => RankingFunction.ranking_satisfies_C2 κ

example : ∀ (κ : RankingFunction W4), κ.satisfies_C3 :=
  fun κ => RankingFunction.ranking_satisfies_C3 κ

example : ∀ (κ : RankingFunction W4), κ.satisfies_C4 :=
  fun κ => RankingFunction.ranking_satisfies_C4 κ

end Phenomena.DefaultReasoning.Studies.DarwichePearl1997
