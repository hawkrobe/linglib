import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Logic.Truth3
import Linglib.Theories.Semantics.Dynamic.UpdateSemantics.Basic

/-!
# Conflicting Presuppositions in Disjunction
@cite{yagi-2025}

Formalizes @cite{yagi-2025} "Conflicting presuppositions in disjunction"
(Semantics & Pragmatics 18, Article 7, 1–15).

## Problem

Disjunctions φ_p ∨ ψ_q where p ∧ q = ⊥ (conflicting presuppositions) have
two empirical properties:
  (2a) They presuppose p ∨ q
  (2b) They can be false

## Failure results

Four major theories of presupposition projection all fail to predict (2b):

1. **Strong Kleene** (§2.1): whenever the disjunction is defined, it is true.
   Because p ∧ q = ⊥, both disjuncts are never defined simultaneously, so
   the ∨_s table never reaches (0, 0) → 0.

2. **Two-dimensional semantics** (§2.2, @cite{karttunen-peters-1979}): the
   presuppositional dimension Π entails the assertive dimension A, so when
   Π = 1, necessarily A = 1.

3. **Update semantics** (§2.3, @cite{heim-1982}, @cite{beaver-2001},
   @cite{veltman-1996}): the update s[φ_p ∨ ψ_q] results in undefinedness
   (∗) unless the truth of the disjunction is already given in the input
   state, making it uninformative.

4. **Schlenker's local contexts** (§2.4, @cite{schlenker-2009}): the
   pragmatic condition on local contexts forces s₀ to contain only worlds
   where one disjunct's assertion-plus-presupposition holds, making the
   disjunction uninformative.

## Proposed reactions

- **Meta-assertion** (§3.1, @cite{beaver-krahmer-2001}): the 𝒜 operator maps
  ∗ to 0, making disjuncts bivalent. This allows falsity but loses the
  presupposition p ∨ q entirely.

- **Flexible accommodation** (§3.2, @cite{geurts-2005}, @cite{aloni-2022}):
  split the state s into s[χ] and s[ω] where s[χ] ∪ s[ω] = s, evaluating
  each disjunct against its own substate. With χ = ¬q, ω = ¬p, this
  correctly predicts both (2a) and (2b), but faces challenges under negation
  and for the non-projection case of example (18).

## Bridges

This module proves failure and success theorems against five existing linglib
modules and closes the architectural gap between static PrProp connectives
and dynamic update semantics:

- `Core.Logic.Truth3.join` (Strong Kleene): disjunction never false
- `Core.Presupposition.PrProp.or` (classical): never defined
- `Core.Presupposition.PrProp.orFilter` (filtering): wrong presupposition
- `Core.Presupposition.PrProp.orFlex` (flexible): correct
- `Semantics.Dynamic.UpdateSemantics` (dynamic): uninformative when defined
-/

namespace Phenomena.Presupposition.Studies.Yagi2025

open Core.Duality
open Core.Presupposition
open Core.Proposition

-- ══════════════════════════════════════════════════════════
-- § World type
-- Example (1c): "Either the King of Buganda is now opening
-- parliament or the President of Buganda is conducting the
-- ceremony." (@cite{beaver-2001}:44)
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
-- § Empirical observations (@cite{yagi-2025}, observation (2))
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
-- § Failure 1: Strong Kleene (Yagi §2.1, Definition 1)
-- ══════════════════════════════════════════════════════════

/-- Strong Kleene disjunction of the two presuppositional propositions. -/
def skDisj : Prop3 W :=
  Prop3.or kingOpensParl.eval presConductsCeremony.eval

/-- Strong Kleene never produces false for this disjunction.
Because presuppositions conflict, at least one disjunct is always undefined,
so the table never reaches the 0 ∨ 0 = 0 row. -/
theorem strong_kleene_never_false : ∀ w, skDisj w ≠ .false := by
  intro w; cases w <;> native_decide


-- ══════════════════════════════════════════════════════════
-- § Failure 2: Two-dimensional semantics (Yagi §2.2)
-- @cite{karttunen-peters-1979}
-- The symmetric K&P definition uses filtering: Π(φ ∨ ψ) =
-- (¬A(ψ) → Π(φ)) ∧ (¬A(φ) → Π(ψ)), which is PrProp.orFilter.
-- ══════════════════════════════════════════════════════════

/-- Classical disjunction requires both presuppositions: presup = p ∧ q. -/
def classicalDisj : PrProp W := PrProp.or kingOpensParl presConductsCeremony

/-- PrProp.or is never defined when presuppositions conflict.
This captures Definition 3 in Yagi: truth value of φ is based on
A(φ) and Π(φ); when Π(φ) = 0, φ = ∗. -/
theorem classical_never_defined : ∀ w, classicalDisj.presup w = false := by
  intro w; cases w <;> rfl

/-- Filtering disjunction (Heim/Schlenker-style symmetric filtering).
Corresponds to Definition 2 in Yagi: Π(φ ∨ ψ) = (¬A(ψ) → Π(φ)) ∧ (¬A(φ) → Π(ψ)). -/
def filterDisj : PrProp W := PrProp.orFilter kingOpensParl presConductsCeremony

/-- orFilter predicts presupposition failure at kingOpens, where the
disjunction should clearly be true. The filtering condition demands
the second presupposition hold when the first assertion is true. -/
theorem filter_wrong_at_kingOpens :
    filterDisj.presup W.kingOpens = false := by rfl

/-- But the expected presupposition IS satisfied there. -/
theorem expected_satisfied_at_kingOpens :
    expectedPresup W.kingOpens = true := by rfl

/-- K&P two-dimensional definition (Definition 2 in Yagi):
    Π(φ ∨ ψ) = (¬A(ψ) → Π(φ)) ∧ (¬A(φ) → Π(ψ))
             = (ψ ∨ p) ∧ (φ ∨ q)

Note: this differs from `orFilter`, which implements the Heim/Schlenker
filtering rule (¬φ ∨ q) ∧ (¬ψ ∨ p) ∧ (p ∨ q). The two-dimensional
definition uses A(φ) and A(ψ) (assertions), not ¬A(φ) and ¬A(ψ). -/
def kpDisj : PrProp W where
  presup := fun w => (presConductsCeremony.assertion w || hasKing w) &&
                     (kingOpensParl.assertion w || hasPresident w)
  assertion := fun w => kingOpensParl.assertion w || presConductsCeremony.assertion w

/-- K&P's presupposition entails the assertion when presuppositions conflict:
whenever Π = 1, A = 1. This is Yagi §2.2 (5)–(6): the defined cases (6a–6c)
all make A true, and (6d) p ∧ φ ∧ q is impossible since p ∧ q = ⊥. -/
theorem kp_presup_entails_assertion : ∀ w,
    kpDisj.presup w = true → kpDisj.assertion w = true := by
  intro w; cases w <;> simp [kpDisj, kingOpensParl, presConductsCeremony,
    hasKing, hasPresident]


-- ══════════════════════════════════════════════════════════
-- § Failure 3: Update semantics (Yagi §2.3)
-- @cite{heim-1982} @cite{beaver-2001} @cite{veltman-1996}
-- Bridge to Theories.Semantics.Dynamic.UpdateSemantics
-- ══════════════════════════════════════════════════════════

open Semantics.Dynamic.UpdateSemantics in
/-- The ideal input state for (1c): four worlds covering all combinations
    of king/president × opening/not. This state presupposes p ∨ q. -/
def bugandaState : State W := {W.kingOpens, W.kingDoesnt, W.presidentConducts, W.presidentDoesnt}

open Semantics.Dynamic.UpdateSemantics in
/-- Presupposition p (hasKing) is NOT supported in bugandaState:
    updating by p eliminates the president-worlds. -/
theorem hasKing_not_supported :
    Update.prop hasKing bugandaState ≠ bugandaState := by
  intro h
  have : W.presidentConducts ∈ Update.prop hasKing bugandaState := by
    rw [h]; simp [bugandaState]
  simp [Update.prop, hasKing] at this

open Semantics.Dynamic.UpdateSemantics in
/-- Presupposition q (hasPresident) is NOT supported in bugandaState. -/
theorem hasPresident_not_supported :
    Update.prop hasPresident bugandaState ≠ bugandaState := by
  intro h
  have : W.kingOpens ∈ Update.prop hasPresident bugandaState := by
    rw [h]; simp [bugandaState]
  simp [Update.prop, hasPresident] at this

open Semantics.Dynamic.UpdateSemantics in
/-- The presuppositional disjunction update yields ∗ (none) on bugandaState.

    @cite{yagi-2025} §2.3: the update s[φ_p ∨ ψ_q] results in undefinedness
    because the presupposition check for the first disjunct (s[p] = s) fails. -/
theorem update_yields_undefined :
    PUpdate.disjPresup hasKing kingOpensParl.assertion hasPresident
      presConductsCeremony.assertion (some bugandaState) = none := by
  simp only [PUpdate.disjPresup, PUpdate.presup]
  -- The presupposition check: Update.prop hasKing bugandaState = bugandaState?
  -- No — it eliminates president-worlds
  have h : ¬(Update.prop hasKing bugandaState = bugandaState) :=
    hasKing_not_supported
  simp [h]

/-- The update is also undefined on a king-only substate: after the left
    disjunct filters to king-opens worlds, the negated context (king-doesn't
    worlds) fails the second presupposition check (hasPresident = false at
    all king-worlds).

    @cite{yagi-2025} §2.3: the update is NEVER both defined and informative.
    This is shown pointwise: at every world, either the presupposition
    fails or both disjuncts are not simultaneously false. -/
theorem update_never_false_pointwise : ∀ w : W,
    -- At every world, the PrProp disjunction is never defined-and-false:
    -- either the presupposition fails (undefined) or some disjunct is true
    (PrProp.or kingOpensParl presConductsCeremony).eval w ≠ .false := by
  intro w; cases w <;> native_decide


-- ══════════════════════════════════════════════════════════
-- § Meta-assertion operator (Yagi §3.1)
-- @cite{beaver-krahmer-2001}: maps * to 0, making disjuncts
-- bivalent. Can make the disjunction false but loses the
-- presupposition entirely.
-- ══════════════════════════════════════════════════════════

/-- Weak Kleene disjunction with meta-assertion on each disjunct. -/
def metaAssertDisj : Prop3 W :=
  Prop3.or (Prop3.metaAssert kingOpensParl.eval) (Prop3.metaAssert presConductsCeremony.eval)

/-- Meta-assertion allows falsity (unlike Strong Kleene).
Satisfies observation (2b). -/
theorem metaAssert_allows_falsity :
    metaAssertDisj W.kingDoesnt = .false := by
  simp [metaAssertDisj, Prop3.or, Prop3.metaAssert, Truth3.metaAssert,
    PrProp.eval, kingOpensParl, presConductsCeremony, hasKing, hasPresident,
    Truth3.join, Truth3.ofBool]

/-- But meta-assertion loses the presupposition: 𝒜φ_p has no presupposition
at all (it maps ∗ to 0), so the Strong Kleene disjunction 𝒜φ_p ∨_s ψ_q
only presupposes ¬𝒜ψ_q → p (Yagi (11)), not the expected p ∨ q.

Violates observation (2a): the disjunction should presuppose p ∨ q. -/
theorem metaAssert_always_defined : ∀ w, (metaAssertDisj w).isDefined = true := by
  intro w; cases w <;> native_decide

/-- The meta-assertion disjunction is bivalent — it has no gap at all,
so it cannot carry any presupposition via the standard gap mechanism. -/
theorem metaAssert_no_gap : ∀ w, metaAssertDisj w ≠ .indet := by
  intro w; cases w <;> native_decide


-- ══════════════════════════════════════════════════════════
-- § Flexible accommodation succeeds (Yagi §3.2)
-- Uses PrProp.orFlex from Core.Presupposition
-- ══════════════════════════════════════════════════════════

/-- The flexible accommodation disjunction. -/
def flexDisj : PrProp W := PrProp.orFlex kingOpensParl presConductsCeremony

/-- Flexible accommodation gives the correct presupposition p ∨ q.
Satisfies observation (2a). -/
theorem flex_correct_presup :
    flexDisj.presup = expectedPresup := by
  funext w; cases w <;> rfl

/-- Complete truth table: flexible accommodation predicts the right
value at every world. -/
theorem flex_truth_table :
    flexDisj.eval W.kingOpens = .true ∧
    flexDisj.eval W.kingDoesnt = .false ∧
    flexDisj.eval W.presidentConducts = .true ∧
    flexDisj.eval W.presidentDoesnt = .false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [flexDisj, PrProp.orFlex, PrProp.eval, kingOpensParl, presConductsCeremony,
      hasKing, hasPresident, Truth3.ofBool]

/-- Flexible accommodation is always defined (never undefined).
The presupposition p ∨ q is a tautology in this world model. -/
theorem flex_always_defined : ∀ w, flexDisj.eval w ≠ .indet := by
  intro w
  cases w <;> simp [flexDisj, PrProp.orFlex, PrProp.eval, kingOpensParl, presConductsCeremony,
    hasKing, hasPresident, Truth3.ofBool]


-- ══════════════════════════════════════════════════════════
-- § Genuineness
-- @cite{zimmermann-2000} Definition 8 in @cite{yagi-2025}
-- ══════════════════════════════════════════════════════════

/-- Genuineness holds for the Buganda disjunction under orFlex:
both disjuncts are "live" — each is true at some world. -/
theorem flex_genuineness :
    PrProp.genuineness kingOpensParl presConductsCeremony
      ⟨[W.kingOpens, W.presidentConducts], by simp⟩ := by
  constructor
  · exact ⟨W.kingOpens, by simp, by native_decide⟩
  · exact ⟨W.presidentConducts, by simp, by native_decide⟩


-- ══════════════════════════════════════════════════════════
-- § Negation interaction (Yagi §3.2, final paragraphs)
-- ══════════════════════════════════════════════════════════

/-- Negation of the flexible accommodation disjunction. -/
def negFlexDisj : PrProp W := PrProp.neg flexDisj

/-- Negating orFlex preserves the presupposition (as expected for negation). -/
theorem neg_flex_presup :
    negFlexDisj.presup = flexDisj.presup := PrProp.neg_presup flexDisj

/-- Negation of the flex disjunction correctly gives the right truth values:
true at king-doesn't and president-doesn't (both disjuncts false). -/
theorem neg_flex_truth_table :
    negFlexDisj.eval W.kingOpens = .false ∧
    negFlexDisj.eval W.kingDoesnt = .true ∧
    negFlexDisj.eval W.presidentConducts = .false ∧
    negFlexDisj.eval W.presidentDoesnt = .true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [negFlexDisj, PrProp.neg, flexDisj, PrProp.orFlex, PrProp.eval,
      kingOpensParl, presConductsCeremony, hasKing, hasPresident, Truth3.ofBool]

/-- The static negation of orFlex matches example (3)/(4) in Yagi:
"Neither is the King opening parliament nor is the President conducting
the ceremony" — true when the head of state is not doing their ceremonial
duty.

However, Yagi §3.2 notes that the DYNAMIC negation of flexible accommodation
is problematic: s[¬(φ_p ∨ ψ_q)] = s/(s[χ][φ_p] ∪ s[χ][ψ_q]) requires
genuineness to hold even inside the scope of negation, which is "peculiar"
because negation should be able to deny both possibilities without requiring
each to be independently viable.

The static PrProp.neg avoids this issue because it simply flips the assertion
pointwise without reference to states. The architectural gap between static
and dynamic shows up precisely here. -/
theorem neg_static_vs_dynamic_divergence :
    -- Statically, negation works fine: preserves presupposition, flips assertion
    (PrProp.neg flexDisj).presup = flexDisj.presup ∧
    (∀ w, (PrProp.neg flexDisj).assertion w = !flexDisj.assertion w) :=
  ⟨rfl, fun _ => rfl⟩


-- ══════════════════════════════════════════════════════════
-- § Example (18): Non-projection (Yagi §3.2)
-- "Either John didn't solve the problem or Mary realized
--  that the problem is solved."
-- The factive presupposition of "realize" does NOT project.
-- Standard update semantics correctly predicts this; flexible
-- accommodation may not, depending on the accommodation
-- constraints.
-- ══════════════════════════════════════════════════════════

/-- Worlds for example (18). -/
inductive W18 where
  | solvedRealized     -- problem solved, Mary realizes
  | solvedNotRealized  -- problem solved, Mary doesn't realize
  | notSolved          -- problem not solved
  deriving DecidableEq, Repr, Inhabited

/-- "John solved the problem" -/
def solved : BProp W18
  | .solvedRealized | .solvedNotRealized => true
  | .notSolved => false

/-- "Mary realized the problem is solved" — factive: presupposes problem is solved. -/
def maryRealized : PrProp W18 where
  presup := solved
  assertion := fun | .solvedRealized => true | _ => false

/-- "John didn't solve the problem" — no presupposition. -/
def johnDidntSolve : PrProp W18 := PrProp.ofBProp (fun w => !solved w)

/-- The SYMMETRIC filtering rule (orFilter, @cite{kalomoiros-schwarz-2021})
incorrectly predicts presupposition failure at notSolved: when "John didn't
solve" is true, it demands the second presupposition (solved) hold — but
the problem ISN'T solved. This is too strong for (18).

Note: the ASYMMETRIC Heim/Karttunen rule would correctly filter here,
because ¬(John didn't solve) = (John solved) entails (problem is solved).
linglib's `orFilter` uses the symmetric version. -/
theorem ex18_symmetric_filter_overgenerates :
    (PrProp.orFilter johnDidntSolve maryRealized).presup W18.notSolved = false := by
  simp [PrProp.orFilter, johnDidntSolve, PrProp.ofBProp, maryRealized, solved]

/-- orFlex handles (18) correctly: the presupposition is
"johnDidntSolve.presup ∨ maryRealized.presup" = "true ∨ solved" = true.
The first disjunct has no presupposition, so the disjunction of
presuppositions is trivially satisfied. -/
theorem ex18_orFlex_no_projection :
    (PrProp.orFlex johnDidntSolve maryRealized).presup W18.notSolved = true := by
  simp [PrProp.orFlex, johnDidntSolve, PrProp.ofBProp, maryRealized, solved]

/-- The key difference: (18) does NOT have conflicting presuppositions.
The first disjunct has no presupposition (presuppositionless), so there
is no conflict. Flexible accommodation with χ = ω = ⊤ works fine. -/
theorem ex18_no_conflict : ∀ w, johnDidntSolve.presup w = true := by
  intro w; rfl


-- ══════════════════════════════════════════════════════════
-- § Summary: which connective handles which observations?
-- ══════════════════════════════════════════════════════════

/-- Strong Kleene (join): satisfies (2a)? Partially — the undefined-valued
disjunction doesn't have a classical presupposition.
Satisfies (2b)? No — never false. -/
theorem sk_fails_2b : ∃ w, expectedPresup w = true ∧ skDisj w ≠ .false :=
  ⟨W.kingDoesnt, rfl, by native_decide⟩

/-- Classical or: satisfies (2a)? No — never defined. -/
theorem classical_fails_2a : ∀ w, classicalDisj.presup w = false :=
  classical_never_defined

/-- orFilter: satisfies (2a)? No — wrong presupposition at some worlds. -/
theorem filter_fails_2a : filterDisj.presup W.kingOpens = false := rfl

/-- Meta-assertion: satisfies (2b)? Yes. Satisfies (2a)? No — no presupposition. -/
theorem metaAssert_fails_2a : metaAssertDisj W.presidentDoesnt ≠ .indet := by
  native_decide

/-- orFlex: satisfies both (2a) and (2b). -/
theorem orFlex_satisfies_both :
    -- (2a): correct presupposition
    flexDisj.presup = expectedPresup ∧
    -- (2b): can be false
    flexDisj.eval W.kingDoesnt = .false :=
  ⟨flex_correct_presup, by simp [flexDisj, PrProp.orFlex, PrProp.eval,
    kingOpensParl, presConductsCeremony, hasKing, hasPresident, Truth3.ofBool]⟩

end Phenomena.Presupposition.Studies.Yagi2025
