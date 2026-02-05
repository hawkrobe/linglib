/-
# Conflicting Presuppositions in Disjunction

Formalizes Yagi (2025) "Conflicting presuppositions in disjunction" (S&P 18:7).

## Problem

Disjunctions φ_p ∨ ψ_q where p ∧ q = ⊥ (conflicting presuppositions) have
two empirical properties:
  (2a) They presuppose p ∨ q
  (2b) They can be false

Four major theories of presupposition projection all fail to predict (2b):
Strong Kleene, two-dimensional semantics, update semantics, and Schlenker's
local contexts all predict the disjunction is never false.

## Bridge Theorems

This module proves failure theorems against three existing linglib modules:
- `Core.Kleene.TVal.or` (Strong Kleene): disjunction is never false
- `Core.Presupposition.PrProp.or` (classical): disjunction is never defined
- `Core.Presupposition.PrProp.orFilter` (filtering): wrong presupposition

It then shows `PrProp.orFlex` (flexible accommodation) handles both observations.

## References

- Yagi, Y. (2025). Conflicting presuppositions in disjunction. S&P 18:7.
- Hausser, R. (1976). Presuppositions in Montague grammar.
- Landman, F. (1986). Conflicting presuppositions and modal subordination.
- Beaver, D. (2001). Presupposition and assertion in dynamic semantics.
- Geurts, B. (2005). Entertaining alternatives.
- Aloni, M. (2022). Logic and conversation.
-/

import Linglib.Core.Presupposition
import Linglib.Core.Kleene

namespace Phenomena.Presupposition.Studies.Yagi2025

open Core.Kleene
open Core.Presupposition
open Core.Proposition

-- ══════════════════════════════════════════════════════════
-- § World type
-- Example (1c): "Either the King of Buganda is now opening
-- parliament or the President of Buganda is conducting the
-- ceremony." (Beaver 2001:44)
-- ══════════════════════════════════════════════════════════

/-- Possible states for the Buganda scenario. -/
inductive W where
  | kingOpens         -- has king, king is opening parliament
  | kingDoesnt        -- has king, king is NOT opening parliament
  | presidentConducts -- has president, president conducting ceremony
  | presidentDoesnt   -- has president, president NOT conducting
  deriving DecidableEq, Repr, Inhabited

instance : FiniteWorlds W where
  worlds := [.kingOpens, .kingDoesnt, .presidentConducts, .presidentDoesnt]
  complete := fun w => by cases w <;> simp

/-- Presupposition p: the nation has a king. -/
def hasKing : BProp W
  | .kingOpens | .kingDoesnt => true
  | _ => false

/-- Presupposition q: the nation has a president. -/
def hasPresident : BProp W
  | .presidentConducts | .presidentDoesnt => true
  | _ => false

/-- p ∧ q = ⊥: the presuppositions conflict. -/
theorem presups_conflict : ∀ w, ¬(hasKing w = true ∧ hasPresident w = true) := by
  intro w; cases w <;> simp [hasKing, hasPresident]

/-- φ_p: "The King is opening parliament" — presupposes hasKing. -/
def kingOpensParl : PrProp W where
  presup := hasKing
  assertion := fun | .kingOpens => true | _ => false

/-- ψ_q: "The President is conducting the ceremony" — presupposes hasPresident. -/
def presConductsCeremony : PrProp W where
  presup := hasPresident
  assertion := fun | .presidentConducts => true | _ => false


-- ══════════════════════════════════════════════════════════
-- § Empirical observations (Yagi 2025, observation (2))
-- ══════════════════════════════════════════════════════════

/-- The expected presupposition: the nation has some head of state. -/
def expectedPresup : BProp W := fun w => hasKing w || hasPresident w

/-- Observation (2a): the presupposition p ∨ q holds at every world. -/
theorem presup_universal : ∀ w, expectedPresup w = true := by
  intro w; cases w <;> rfl

/-- Observation (2b): the disjunction can be false.
At kingDoesnt the presupposition is satisfied but both disjuncts fail. -/
theorem can_be_false :
    expectedPresup W.kingDoesnt = true ∧
    kingOpensParl.assertion W.kingDoesnt = false ∧
    presConductsCeremony.assertion W.kingDoesnt = false :=
  ⟨rfl, rfl, rfl⟩


-- ══════════════════════════════════════════════════════════
-- § Failure 1: Strong Kleene (Yagi §2.1)
-- ══════════════════════════════════════════════════════════

/-- Strong Kleene disjunction of the two presuppositional propositions. -/
def skDisj : Prop3 W :=
  Prop3.or kingOpensParl.eval presConductsCeremony.eval

/-- Strong Kleene never produces false for this disjunction.
Because presuppositions conflict, at least one disjunct is always undefined,
so the table never reaches the 0 ∨ 0 = 0 row. -/
theorem strong_kleene_never_false : ∀ w, skDisj w ≠ TVal.ff := by
  intro w; cases w <;> native_decide


-- ══════════════════════════════════════════════════════════
-- § Failure 2: Classical disjunction / PrProp.or (Yagi §2.2)
-- ══════════════════════════════════════════════════════════

/-- Classical disjunction requires both presuppositions: presup = p ∧ q. -/
def classicalDisj : PrProp W := PrProp.or kingOpensParl presConductsCeremony

/-- PrProp.or is never defined when presuppositions conflict. -/
theorem classical_never_defined : ∀ w, classicalDisj.presup w = false := by
  intro w; cases w <;> rfl


-- ══════════════════════════════════════════════════════════
-- § Failure 3: Filtering disjunction / PrProp.orFilter
-- ══════════════════════════════════════════════════════════

/-- Filtering disjunction (Heim/Schlenker-style symmetric filtering). -/
def filterDisj : PrProp W := PrProp.orFilter kingOpensParl presConductsCeremony

/-- orFilter predicts presupposition failure at kingOpens, where the
disjunction should clearly be true. The filtering condition demands
the second presupposition hold when the first assertion is true. -/
theorem filter_wrong_at_kingOpens :
    filterDisj.presup W.kingOpens = false := by rfl

/-- But the expected presupposition IS satisfied there. -/
theorem expected_satisfied_at_kingOpens :
    expectedPresup W.kingOpens = true := by rfl


-- ══════════════════════════════════════════════════════════
-- § Flexible accommodation succeeds (Yagi §3.2)
-- Uses PrProp.orFlex from Core.Presupposition
-- ══════════════════════════════════════════════════════════

/-- The flexible accommodation disjunction. -/
def flexDisj : PrProp W := PrProp.orFlex kingOpensParl presConductsCeremony

/-- Flexible accommodation gives the correct presupposition p ∨ q. -/
theorem flex_correct_presup :
    flexDisj.presup = expectedPresup := by
  funext w; cases w <;> rfl

/-- Complete truth table: flexible accommodation predicts the right
value at every world. -/
theorem flex_truth_table :
    flexDisj.eval W.kingOpens = TVal.tt ∧
    flexDisj.eval W.kingDoesnt = TVal.ff ∧
    flexDisj.eval W.presidentConducts = TVal.tt ∧
    flexDisj.eval W.presidentDoesnt = TVal.ff := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [flexDisj, PrProp.orFlex, PrProp.eval, kingOpensParl, presConductsCeremony,
      hasKing, hasPresident, TVal.ofBool, TVal.tt, TVal.ff]

/-- Flexible accommodation is always defined (never undefined). -/
theorem flex_always_defined : ∀ w, flexDisj.eval w ≠ TVal.unk := by
  intro w
  cases w <;> simp [flexDisj, PrProp.orFlex, PrProp.eval, kingOpensParl, presConductsCeremony,
    hasKing, hasPresident, TVal.ofBool, TVal.unk]


-- ══════════════════════════════════════════════════════════
-- § Meta-assertion operator (Yagi §3.1)
-- Beaver & Krahmer (2001): maps * to 0, making disjuncts
-- bivalent. Can make the disjunction false but loses the
-- presupposition entirely.
-- ══════════════════════════════════════════════════════════

/-- Weak Kleene disjunction with meta-assertion on each disjunct. -/
def metaAssertDisj : Prop3 W :=
  Prop3.or (Prop3.metaAssert kingOpensParl.eval) (Prop3.metaAssert presConductsCeremony.eval)

/-- Meta-assertion allows falsity (unlike Strong Kleene). -/
theorem metaAssert_allows_falsity :
    metaAssertDisj W.kingDoesnt = TVal.ff := by
  simp [metaAssertDisj, Prop3.or, Prop3.metaAssert, TVal.metaAssert,
    PrProp.eval, kingOpensParl, presConductsCeremony, hasKing, hasPresident,
    TVal.or, TVal.ofBool, TVal.ff]

/-- But meta-assertion loses the presupposition: the disjunction is false
even when neither presupposition holds (if we had such a world). More
concretely, 𝒜φ_p ∨_s ψ_q presupposes only ¬𝒜ψ_q → p (Yagi (11)),
not the expected p ∨ q. -/
theorem metaAssert_loses_presup :
    -- At kingDoesnt, the meta-asserted disjunction is simply false (value 0),
    -- indistinguishable from a world where neither head of state exists.
    metaAssertDisj W.kingDoesnt = TVal.ff := by
  simp [metaAssertDisj, Prop3.or, Prop3.metaAssert, TVal.metaAssert,
    PrProp.eval, kingOpensParl, presConductsCeremony, hasKing, hasPresident,
    TVal.or, TVal.ofBool, TVal.ff]

end Phenomena.Presupposition.Studies.Yagi2025
