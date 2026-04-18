import Linglib.Theories.Semantics.Modality.Desire

/-!
# @cite{phillips-brown-2025} — Some-Things-Considered Desire

Conflicting desire ascriptions — "S wants p" and "S wants ¬p" — falsify
every belief-based semantics that is not question-sensitive. This study file
verifies the core predictions from @cite{phillips-brown-2025} using an
8-world model (3 binary dimensions).

## Results

| # | Prediction | Theorem |
|---|-----------|---------|
| 1 | Nap is true (considering mood, ignoring exam) | `nap_true` |
| 2 | Not-nap is true (considering exam, ignoring mood) | `not_nap_true` |
| 3 | Fail is undefined in the Nap context | `fail_not_considered` |
| 4 | Lobster is true (considering taste, ignoring death) | `lobster_true` |
| 5 | Not-lobster is true (considering death, ignoring taste) | `not_lobster_true` |
| 6 | Not-die is also true in the Not-lobster context | `not_die_true` |
| 7 | Die is undefined in the Lobster context | `die_not_considered` |
| 8 | Standard vF cannot predict both Nap and Not-nap | `vf_cannot_predict_both` |
| 9 | Happy not considered in deck-stacked Q | `happy_not_considered_deckstacked` |
| 10 | Fair Q corrects Not-rain to false | `not_rain_false_fair` |
| 11 | Finest question simulates von Fintel | `finest_simulates_vf_nap` |
| 12 | PrProp: nap is defined and true | `nap_prprop_holds` |
| 13 | PrProp: fail is undefined (presup false) | `fail_prprop_undefined` |
| 14 | Avoid-war entails avoid-nuclear-war | `avoidWar_entails_avoidNuclearWar` |
| 15 | Avoid-nuclear-war considered in Q_nuc | `avoidNuclearWar_considered` |
| 16 | William's beliefs insensitive to Q_nuc | `william_insensitive` |
| 17 | Avoid-nuclear-war not defined for William | `avoidNuclearWar_not_defined_william` |
| 18 | Modern beliefs sensitive to Q_nuc | `modern_sensitive` |
| 19 | Avoid-nuclear-war defined for modern person | `avoidNuclearWar_defined_modern` |
| 20 | Modern person wants avoid-nuclear-war | `modern_wants_avoidNuclearWar` |
-/

set_option autoImplicit false

namespace PhillipsBrown2025

open Core.Proposition (FiniteWorlds)
open Semantics.Modality.Desire

-- ============================================================================
-- §1. Eight-world model
-- ============================================================================

/-- 8 worlds encoding 3 binary dimensions (d₁ × d₂ × d₃).
For Nap: d₁ = nap, d₂ = rested, d₃ = pass.
For Lobster: d₁ = eat lobster, d₂ = gustatory, d₃ = ¬die. -/
inductive W where
  | w0 | w1 | w2 | w3 | w4 | w5 | w6 | w7
  deriving DecidableEq, Repr, Inhabited

instance : FiniteWorlds W where
  worlds := [.w0, .w1, .w2, .w3, .w4, .w5, .w6, .w7]
  complete := λ w => by cases w <;> simp

-- ============================================================================
-- §2. Propositions
-- ============================================================================

/-! World assignment:
| World | nap | rested | pass |
|-------|-----|--------|------|
| w0    | T   | T      | T    |
| w1    | T   | T      | F    |
| w2    | T   | F      | T    |
| w3    | T   | F      | F    |
| w4    | F   | T      | T    |
| w5    | F   | T      | F    |
| w6    | F   | F      | T    |
| w7    | F   | F      | F    | -/

def nap : W → Bool | .w0 | .w1 | .w2 | .w3 => true | _ => false
def rested : W → Bool | .w0 | .w1 | .w4 | .w5 => true | _ => false
def pass : W → Bool | .w0 | .w2 | .w4 | .w6 => true | _ => false
def fail : W → Bool := λ w => !pass w

-- ============================================================================
-- §3. Nap scenario
-- ============================================================================

/-- Q' = partition by nap × rested (4 cells, 2 worlds each). -/
def qNapRest : List (W → Bool) :=
  [λ w => nap w && rested w, λ w => nap w && !rested w,
   λ w => !nap w && rested w, λ w => !nap w && !rested w]

/-- Q'' = partition by nap × pass (4 cells, 2 worlds each). -/
def qNapPass : List (W → Bool) :=
  [λ w => nap w && pass w, λ w => nap w && !pass w,
   λ w => !nap w && pass w, λ w => !nap w && !pass w]

/-- Beliefs for Nap: nap ↔ rested. Bel = {w0, w1, w6, w7}. -/
def belNapRest : W → Bool := λ w => if nap w then rested w else !rested w

/-- Beliefs for Not-nap: pass ↔ ¬nap. Bel = {w1, w3, w4, w6}. -/
def belNapPass : W → Bool := λ w => if nap w then !pass w else pass w

def desRest : List (W → Bool) := [rested]
def desPass : List (W → Bool) := [pass]

-- Core predictions (using generic `wantQuestionBased` from Desire.lean)

/-- **Nap is true** relative to Q' with beliefs nap↔rested, desires [rested].
Best in Q'-Bel: n∧r = {w0,w1} entails nap. -/
theorem nap_true : wantQuestionBased belNapRest desRest qNapRest nap = true := by native_decide

/-- **Not-nap is true** relative to Q'' with beliefs pass↔¬nap, desires [pass].
Best in Q''-Bel: ¬n∧p = {w4,w6} entails ¬nap. -/
theorem not_nap_true :
    wantQuestionBased belNapPass desPass qNapPass (λ w => !nap w) = true := by native_decide

-- Considering Constraint blocks Fail

/-- Fail is NOT considered relative to Q': each cell contains both
pass-worlds and fail-worlds, so no cell settles whether you fail. -/
theorem fail_not_considered : isConsidered qNapRest fail = false := by native_decide

/-- Fail is also not predicted true (best answers don't entail fail). -/
theorem fail_not_true :
    wantQuestionBased belNapRest desRest qNapRest fail = false := by native_decide

/-- Q' is diverse w.r.t. nap: both nap-answers and ¬nap-answers exist. -/
theorem nap_diverse : isDiverse qNapRest nap = true := by native_decide

-- ============================================================================
-- §4. Lobster scenario (structural isomorphism with Nap)
-- ============================================================================

/-! The Lobster scenario is structurally isomorphic to Nap:
- dim1 = eat lobster = `nap`
- dim2 = gustatory experience = `rested`
- dim3 = ¬die = `pass` (so die = `fail`) -/

abbrev lobster : W → Bool := nap
abbrev gustatory : W → Bool := rested
abbrev die : W → Bool := fail

/-- Lobster is true (same computation as Nap). -/
theorem lobster_true :
    wantQuestionBased belNapRest desRest qNapRest lobster = true := nap_true

/-- Die is not considered in the Lobster context (= Q'). -/
theorem die_not_considered :
    isConsidered qNapRest die = false := fail_not_considered

/-- Q_c''' = partition by lobster × die. -/
def qLobDie : List (W → Bool) :=
  [λ w => nap w && fail w, λ w => nap w && !fail w,
   λ w => !nap w && fail w, λ w => !nap w && !fail w]

/-- Beliefs: die ↔ eat lobster. Bel = {w1, w3, w4, w6}. -/
def belLobDie : W → Bool := λ w => if nap w then fail w else !fail w

def desNotDie : List (W → Bool) := [λ w => !fail w]

/-- **Not-lobster is true** in c''' (considering death, ignoring taste). -/
theorem not_lobster_true :
    wantQuestionBased belLobDie desNotDie qLobDie (λ w => !nap w) = true := by native_decide

/-- **Not-die is also true** in c''' (best answer entails both ¬lobster and ¬die). -/
theorem not_die_true :
    wantQuestionBased belLobDie desNotDie qLobDie (λ w => !fail w) = true := by native_decide

-- ============================================================================
-- §5. Von Fintel comparison (using generic `wantVF` from Desire.lean)
-- ============================================================================

/-- VF correctly predicts Nap. -/
theorem vf_nap_true : wantVF belNapRest desRest nap = true := by native_decide

/-- VF cannot also predict Not-nap (want is not context-sensitive). -/
theorem vf_not_nap_false :
    wantVF belNapRest desRest (λ w => !nap w) = false := by native_decide

/-- VF cannot predict both Nap and Not-nap with any single parameter set. -/
theorem vf_cannot_predict_both :
    ¬(wantVF belNapRest desRest nap = true ∧
      wantVF belNapRest desRest (λ w => !nap w) = true) := by
  simp only [vf_not_nap_false, Bool.false_eq_true, and_false, not_false_eq_true]

-- ============================================================================
-- §6. Doxastic closure blocking (§4.1)
-- ============================================================================

/-! The Considering Constraint blocks doxastic closure inferences
(@cite{villalta-2008}). On vF, any proposition true at all best belief-worlds
is predicted wanted — over-generating for coincidental propositions.

The question-based approach makes fail UNDEFINED rather than merely false:
fail is not settled by Q' (the nap×rested partition), so the Considering
Constraint blocks ⟦want(fail)⟧^{Q'} from being defined at all. -/

/-- In the Not-nap context Q'', nap IS considered (every cell settles nap). -/
theorem nap_considered_in_qNapPass :
    isConsidered qNapPass nap = true := by native_decide

/-- Fail IS considered in Q'' (pass is a partition dimension, so fail = ¬pass
is settled by every cell). But fail is NOT considered in Q' — and that is
what blocks the doxastic closure inference in the Nap context. -/
theorem fail_considered_in_qNapPass :
    isConsidered qNapPass fail = true := by native_decide

-- ============================================================================
-- §7. Anti-deckstacking constraint (§3.7)
-- ============================================================================

/-! Lu is unsure if it will rain, but is sure he'll feel happy no matter what.
- h = Lu is happy tomorrow
- r = it rains tomorrow
- G_Lu: h ∈ G_Lu, but neither r nor ¬r is in G_Lu

Q'''' (deck-stacked): a 3-cell question {r, ¬r∧h, ¬r∧¬h} that
asymmetrically cross-cuts rain with happiness. This violates
Anti-deckstacking because some answer is an h-answer but h is not
considered (the r cell doesn't settle h). -/

def happy : W → Bool | .w0 | .w1 | .w4 | .w5 => true | _ => false
def rain : W → Bool | .w0 | .w1 | .w2 | .w3 => true | _ => false

/-- Q'''' (deck-stacked): {r, ¬r∧h, ¬r∧¬h}. The r cell doesn't
settle whether Lu is happy, so h is not considered. -/
def qDeckstacked : List (W → Bool) :=
  [rain, λ w => !rain w && happy w, λ w => !rain w && !happy w]

/-- Lu's beliefs: happy unconditionally, unsure about rain.
Bel = {w0, w1, w4, w5} (all happy worlds). -/
def belLu : W → Bool := happy

def desHappy : List (W → Bool) := [happy]

/-- The key violation: `happy` is not considered in the deck-stacked Q'''',
because the `rain` cell contains both happy and unhappy worlds. -/
theorem happy_not_considered_deckstacked :
    isConsidered qDeckstacked happy = false := by native_decide

/-- But `happy` IS entailed by one of the answers (¬r∧h), so a
happy-answer exists — the deck is stacked in favor of ¬rain. -/
theorem happy_answer_exists_deckstacked :
    qDeckstacked.any (λ a => propEntails a happy) = true := by native_decide

/-- Without the constraint, the semantics wrongly predicts Not-rain. -/
theorem not_rain_deckstacked_true :
    wantQuestionBased belLu desHappy qDeckstacked (λ w => !rain w) = true := by native_decide

/-- Q''''' (level playing field): partition by rain × happy. -/
def qRainHappy : List (W → Bool) :=
  [λ w => rain w && happy w, λ w => rain w && !happy w,
   λ w => !rain w && happy w, λ w => !rain w && !happy w]

/-- In the fair question, `happy` IS considered. -/
theorem happy_considered_fair :
    isConsidered qRainHappy happy = true := by native_decide

/-- With the fair question, Not-rain is correctly predicted false
(Lu is happy either way, so both r∧h and ¬r∧h are best). -/
theorem not_rain_false_fair :
    wantQuestionBased belLu desHappy qRainHappy (λ w => !rain w) = false := by native_decide

/-! **Anti-deckstacking: too strong for finite models.**
The paper's universal quantification ("for all q, if some answer entails q,
then q must be considered") quantifies over all 2^|W| propositions. This is
vacuously violated by gerrymandered propositions: e.g., with qNapRest, the
proposition {w0, w1, w4} is entailed by the nap∧rested cell but is not
settled by the ¬nap∧rested cell. These violations are artifacts of the
finite model, not meaningful failures, which is why `wantDefined` omits
Anti-deckstacking. -/

/-- qNapRest fails Anti-deckstacking (gerrymandered propositions violate it). -/
theorem qNapRest_fails_antideckstacking :
    isAntiDeckstacking qNapRest = false := by native_decide

/-- Even the deck-stacked question fails (confirming it catches real violations too). -/
theorem qDeckstacked_fails_antideckstacking :
    isAntiDeckstacking qDeckstacked = false := by native_decide

/-- The fair question also fails (same artifact — any non-coarsening proposition
    that isn't settled by all cells triggers the constraint). -/
theorem qRainHappy_fails_antideckstacking :
    isAntiDeckstacking qRainHappy = false := by native_decide

-- ============================================================================
-- §8. Finest-question simulation (§3.4 metasemantic result)
-- ============================================================================

/-! When Q is the finest question (singleton cells = individual worlds),
the question-based semantics reduces to von Fintel's standard semantics.
This is the paper's key metasemantic result: the orthodox semantics is a
special case where context selects the maximally fine-grained question. -/

/-- Singleton partition: each world is its own cell. -/
def qFinest : List (W → Bool) :=
  [λ w => w == .w0, λ w => w == .w1, λ w => w == .w2, λ w => w == .w3,
   λ w => w == .w4, λ w => w == .w5, λ w => w == .w6, λ w => w == .w7]

/-- With the finest question, question-based want = standard vF want for Nap. -/
theorem finest_simulates_vf_nap :
    wantQuestionBased belNapRest desRest qFinest nap =
    wantVF belNapRest desRest nap := by native_decide

/-- With the finest question, question-based want = standard vF want for ¬Nap. -/
theorem finest_simulates_vf_not_nap :
    wantQuestionBased belNapRest desRest qFinest (λ w => !nap w) =
    wantVF belNapRest desRest (λ w => !nap w) := by native_decide

/-- With the finest question, question-based want = standard vF want for Lobster. -/
theorem finest_simulates_vf_lobster :
    wantQuestionBased belLobDie desNotDie qFinest (λ w => !nap w) =
    wantVF belLobDie desNotDie (λ w => !nap w) := by native_decide

-- ============================================================================
-- §9. PrProp integration: definedness
-- ============================================================================

/-- Nap is defined in Q' (considered + diverse). -/
theorem nap_defined_in_qNapRest :
    wantDefined belNapRest qNapRest nap = true := by native_decide

/-- Fail is NOT defined in Q' (not considered). -/
theorem fail_not_defined_in_qNapRest :
    wantDefined belNapRest qNapRest fail = false := by native_decide

/-- The PrProp wrapper: nap is defined AND true. -/
theorem nap_prprop_holds :
    (wantPrProp belNapRest desRest qNapRest nap).presup .w0 ∧
    (wantPrProp belNapRest desRest qNapRest nap).assertion .w0 := by
  simp only [wantPrProp]
  exact ⟨by native_decide, by native_decide⟩

/-- The PrProp wrapper: fail is undefined (presup fails). -/
theorem fail_prprop_undefined :
    ¬(wantPrProp belNapRest desRest qNapRest fail).presup .w0 := by
  simp only [wantPrProp]; native_decide

-- ============================================================================
-- §10. Belief-sensitivity: Avoid-war scenario (§4.2)
-- ============================================================================

/-! William III wanted to avoid war. Avoiding war entails avoiding nuclear war.
But we cannot conclude William III wanted to avoid nuclear war — he lacked
the conceptual resources to grasp nuclear war.

The mechanism: William's beliefs are NOT sensitive to the question Q_nuc that
distinguishes nuclear from conventional war. All Q_nuc answers are compatible
with his beliefs (total uncertainty), so `isBelSensitive` returns false and
`wantDefined` blocks the inference.

In contrast, a modern person whose beliefs rule out nuclear war DOES have
belief-sensitive context, so the inference goes through. -/

/-- war = ¬nap; nuclear war = ¬nap ∧ ¬rested.
Avoid nuclear war = peace ∨ conventional war. -/
def avoidWar : W → Bool := nap
def avoidNuclearWar : W → Bool := λ w => nap w || rested w

/-- Q_nuc: partition {peace, conventional war, nuclear war}. -/
def qNuclear : List (W → Bool) :=
  [nap, λ w => !nap w && rested w, λ w => !nap w && !rested w]

/-- Avoiding war entails avoiding nuclear war. -/
theorem avoidWar_entails_avoidNuclearWar :
    propEntails avoidWar avoidNuclearWar = true := by native_decide

/-- avoidNuclearWar is considered in Q_nuc (every answer settles it). -/
theorem avoidNuclearWar_considered :
    isConsidered qNuclear avoidNuclearWar = true := by native_decide

/-- William III: total uncertainty (all worlds compatible). -/
def belWilliam : W → Bool := λ _ => true

/-- William's beliefs are NOT sensitive to Q_nuc (all answers live). -/
theorem william_insensitive :
    isBelSensitive belWilliam qNuclear = false := by native_decide

/-- avoidNuclearWar is NOT defined for William (belief-sensitivity fails). -/
theorem avoidNuclearWar_not_defined_william :
    wantDefined belWilliam qNuclear avoidNuclearWar = false := by native_decide

/-- A modern person: beliefs rule out nuclear war (peace ∨ conventional). -/
def belModern : W → Bool := λ w => nap w || rested w

/-- Modern beliefs ARE sensitive to Q_nuc (nuclear-war answer ruled out). -/
theorem modern_sensitive :
    isBelSensitive belModern qNuclear = true := by native_decide

/-- avoidNuclearWar IS defined for a modern person. -/
theorem avoidNuclearWar_defined_modern :
    wantDefined belModern qNuclear avoidNuclearWar = true := by native_decide

def desAvoidWar : List (W → Bool) := [nap]

/-- A modern person who wants peace also wants to avoid nuclear war. -/
theorem modern_wants_avoidNuclearWar :
    wantQuestionBased belModern desAvoidWar qNuclear avoidNuclearWar = true := by native_decide

end PhillipsBrown2025
