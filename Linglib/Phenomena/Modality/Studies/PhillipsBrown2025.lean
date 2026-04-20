import Linglib.Theories.Semantics.Modality.Desire
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

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

instance : Fintype W where
  elems := {.w0, .w1, .w2, .w3, .w4, .w5, .w6, .w7}
  complete := λ w => by cases w <;> decide

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

def nap : Set W | .w0 | .w1 | .w2 | .w3 => True | _ => False
def rested : Set W | .w0 | .w1 | .w4 | .w5 => True | _ => False
def pass : Set W | .w0 | .w2 | .w4 | .w6 => True | _ => False
def fail : Set W := λ w => ¬ pass w

instance : DecidablePred nap := fun w => by cases w <;> unfold nap <;> infer_instance
instance : DecidablePred rested := fun w => by cases w <;> unfold rested <;> infer_instance
instance : DecidablePred pass := fun w => by cases w <;> unfold pass <;> infer_instance
instance : DecidablePred fail := fun w => by unfold fail; infer_instance

-- ============================================================================
-- §3. Nap scenario
-- ============================================================================

/-- Q' = partition by nap × rested (4 cells, 2 worlds each). -/
def qNapRest : List (DecProp W) :=
  [mkDec (fun w => nap w ∧ rested w),
   mkDec (fun w => nap w ∧ ¬ rested w),
   mkDec (fun w => ¬ nap w ∧ rested w),
   mkDec (fun w => ¬ nap w ∧ ¬ rested w)]

/-- Q'' = partition by nap × pass (4 cells, 2 worlds each). -/
def qNapPass : List (DecProp W) :=
  [mkDec (fun w => nap w ∧ pass w),
   mkDec (fun w => nap w ∧ ¬ pass w),
   mkDec (fun w => ¬ nap w ∧ pass w),
   mkDec (fun w => ¬ nap w ∧ ¬ pass w)]

/-- Beliefs for Nap: nap ↔ rested. Bel = {w0, w1, w6, w7}. -/
def belNapRest : Set W := fun w => if nap w then rested w else ¬ rested w
instance : DecidablePred belNapRest := fun w => by unfold belNapRest; infer_instance

/-- Beliefs for Not-nap: pass ↔ ¬nap. Bel = {w1, w3, w4, w6}. -/
def belNapPass : Set W := fun w => if nap w then ¬ pass w else pass w
instance : DecidablePred belNapPass := fun w => by unfold belNapPass; infer_instance

def desRest : List (DecProp W) := [mkDec rested]
def desPass : List (DecProp W) := [mkDec pass]

-- Core predictions (using generic `wantQuestionBased` from Desire.lean)

/-- **Nap is true** relative to Q' with beliefs nap↔rested, desires [rested].
Best in Q'-Bel: n∧r = {w0,w1} entails nap. -/
theorem nap_true : wantQuestionBased belNapRest desRest qNapRest nap := by decide

/-- **Not-nap is true** relative to Q'' with beliefs pass↔¬nap, desires [pass].
Best in Q''-Bel: ¬n∧p = {w4,w6} entails ¬nap. -/
theorem not_nap_true :
    wantQuestionBased belNapPass desPass qNapPass (fun w => ¬ nap w) := by decide

-- Considering Constraint blocks Fail

/-- Fail is NOT considered relative to Q': each cell contains both
pass-worlds and fail-worlds, so no cell settles whether you fail. -/
theorem fail_not_considered : ¬ isConsidered qNapRest fail := by decide

/-- Fail is also not predicted true (best answers don't entail fail). -/
theorem fail_not_true :
    ¬ wantQuestionBased belNapRest desRest qNapRest fail := by decide

/-- Q' is diverse w.r.t. nap: both nap-answers and ¬nap-answers exist. -/
theorem nap_diverse : isDiverse qNapRest nap := by decide

-- ============================================================================
-- §4. Lobster scenario (structural isomorphism with Nap)
-- ============================================================================

/-! The Lobster scenario is structurally isomorphic to Nap:
- dim1 = eat lobster = `nap`
- dim2 = gustatory experience = `rested`
- dim3 = ¬die = `pass` (so die = `fail`) -/

abbrev lobster : Set W := nap
abbrev gustatory : Set W := rested
abbrev die : Set W := fail

/-- Lobster is true (same computation as Nap). -/
theorem lobster_true :
    wantQuestionBased belNapRest desRest qNapRest lobster := nap_true

/-- Die is not considered in the Lobster context (= Q'). -/
theorem die_not_considered :
    ¬ isConsidered qNapRest die := fail_not_considered

/-- Q_c''' = partition by lobster × die. -/
def qLobDie : List (DecProp W) :=
  [mkDec (fun w => nap w ∧ fail w),
   mkDec (fun w => nap w ∧ ¬ fail w),
   mkDec (fun w => ¬ nap w ∧ fail w),
   mkDec (fun w => ¬ nap w ∧ ¬ fail w)]

/-- Beliefs: die ↔ eat lobster. Bel = {w1, w3, w4, w6}. -/
def belLobDie : Set W := fun w => if nap w then fail w else ¬ fail w
instance : DecidablePred belLobDie := fun w => by unfold belLobDie; infer_instance

def desNotDie : List (DecProp W) := [mkDec (fun w => ¬ fail w)]

/-- **Not-lobster is true** in c''' (considering death, ignoring taste). -/
theorem not_lobster_true :
    wantQuestionBased belLobDie desNotDie qLobDie (fun w => ¬ nap w) := by decide

/-- **Not-die is also true** in c''' (best answer entails both ¬lobster and ¬die). -/
theorem not_die_true :
    wantQuestionBased belLobDie desNotDie qLobDie (fun w => ¬ fail w) := by decide

-- ============================================================================
-- §5. Von Fintel comparison (using generic `wantVF` from Desire.lean)
-- ============================================================================

/-- VF correctly predicts Nap. -/
theorem vf_nap_true : wantVF belNapRest desRest nap := by decide

/-- VF cannot also predict Not-nap (want is not context-sensitive). -/
theorem vf_not_nap_false :
    ¬ wantVF belNapRest desRest (fun w => ¬ nap w) := by decide

/-- VF cannot predict both Nap and Not-nap with any single parameter set. -/
theorem vf_cannot_predict_both :
    ¬(wantVF belNapRest desRest nap ∧
      wantVF belNapRest desRest (fun w => ¬ nap w)) := by
  intro ⟨_, h⟩; exact vf_not_nap_false h

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
    isConsidered qNapPass nap := by decide

/-- Fail IS considered in Q'' (pass is a partition dimension, so fail = ¬pass
is settled by every cell). But fail is NOT considered in Q' — and that is
what blocks the doxastic closure inference in the Nap context. -/
theorem fail_considered_in_qNapPass :
    isConsidered qNapPass fail := by decide

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

def happy : Set W | .w0 | .w1 | .w4 | .w5 => True | _ => False
def rain : Set W | .w0 | .w1 | .w2 | .w3 => True | _ => False

instance : DecidablePred happy := fun w => by cases w <;> unfold happy <;> infer_instance
instance : DecidablePred rain := fun w => by cases w <;> unfold rain <;> infer_instance

/-- Q'''' (deck-stacked): {r, ¬r∧h, ¬r∧¬h}. The r cell doesn't
settle whether Lu is happy, so h is not considered. -/
def qDeckstacked : List (DecProp W) :=
  [mkDec rain,
   mkDec (fun w => ¬ rain w ∧ happy w),
   mkDec (fun w => ¬ rain w ∧ ¬ happy w)]

/-- Lu's beliefs: happy unconditionally, unsure about rain.
Bel = {w0, w1, w4, w5} (all happy worlds). -/
def belLu : Set W := happy
instance : DecidablePred belLu := inferInstanceAs (DecidablePred happy)

def desHappy : List (DecProp W) := [mkDec happy]

/-- The key violation: `happy` is not considered in the deck-stacked Q'''',
because the `rain` cell contains both happy and unhappy worlds. -/
theorem happy_not_considered_deckstacked :
    ¬ isConsidered qDeckstacked happy := by decide

/-- But `happy` IS entailed by one of the answers (¬r∧h), so a
happy-answer exists — the deck is stacked in favor of ¬rain. -/
theorem happy_answer_exists_deckstacked :
    ∃ a ∈ qDeckstacked, propEntails a.prop happy := by decide

/-- Without the constraint, the semantics wrongly predicts Not-rain. -/
theorem not_rain_deckstacked_true :
    wantQuestionBased belLu desHappy qDeckstacked (fun w => ¬ rain w) := by decide

/-- Q''''' (level playing field): partition by rain × happy. -/
def qRainHappy : List (DecProp W) :=
  [mkDec (fun w => rain w ∧ happy w),
   mkDec (fun w => rain w ∧ ¬ happy w),
   mkDec (fun w => ¬ rain w ∧ happy w),
   mkDec (fun w => ¬ rain w ∧ ¬ happy w)]

/-- In the fair question, `happy` IS considered. -/
theorem happy_considered_fair :
    isConsidered qRainHappy happy := by decide

/-- With the fair question, Not-rain is correctly predicted false
(Lu is happy either way, so both r∧h and ¬r∧h are best). -/
theorem not_rain_false_fair :
    ¬ wantQuestionBased belLu desHappy qRainHappy (fun w => ¬ rain w) := by decide

/-! **Anti-deckstacking: too strong for finite models.**
The paper's universal quantification ("for all q, if some answer entails q,
then q must be considered") quantifies over all 2^|W| propositions. This is
vacuously violated by gerrymandered propositions: e.g., with qNapRest, the
proposition {w0, w1, w4} is entailed by the nap∧rested cell but is not
settled by the ¬nap∧rested cell. These violations are artifacts of the
finite model, not meaningful failures, which is why `wantDefined` omits
Anti-deckstacking. -/

/-- Explicit world enumeration for `isAntiDeckstacking` (the constraint
    quantifies over all subsets of worlds, so a literal list is needed for
    `decide`-style reduction). -/
def allWorldsW : List W := [.w0, .w1, .w2, .w3, .w4, .w5, .w6, .w7]

/-- qNapRest fails Anti-deckstacking (gerrymandered propositions violate it). -/
theorem qNapRest_fails_antideckstacking :
    ¬ isAntiDeckstacking allWorldsW qNapRest := by decide

/-- Even the deck-stacked question fails (confirming it catches real violations too). -/
theorem qDeckstacked_fails_antideckstacking :
    ¬ isAntiDeckstacking allWorldsW qDeckstacked := by decide

/-- The fair question also fails (same artifact — any non-coarsening proposition
    that isn't settled by all cells triggers the constraint). -/
theorem qRainHappy_fails_antideckstacking :
    ¬ isAntiDeckstacking allWorldsW qRainHappy := by decide

-- ============================================================================
-- §8. Finest-question simulation (§3.4 metasemantic result)
-- ============================================================================

/-! When Q is the finest question (singleton cells = individual worlds),
the question-based semantics reduces to von Fintel's standard semantics.
This is the paper's key metasemantic result: the orthodox semantics is a
special case where context selects the maximally fine-grained question. -/

/-- Singleton partition: each world is its own cell. -/
def qFinest : List (DecProp W) :=
  [mkDec (fun w => w = .w0), mkDec (fun w => w = .w1),
   mkDec (fun w => w = .w2), mkDec (fun w => w = .w3),
   mkDec (fun w => w = .w4), mkDec (fun w => w = .w5),
   mkDec (fun w => w = .w6), mkDec (fun w => w = .w7)]

/-- With the finest question, question-based want = standard vF want for Nap. -/
theorem finest_simulates_vf_nap :
    wantQuestionBased belNapRest desRest qFinest nap ↔
    wantVF belNapRest desRest nap := by decide

/-- With the finest question, question-based want = standard vF want for ¬Nap. -/
theorem finest_simulates_vf_not_nap :
    wantQuestionBased belNapRest desRest qFinest (fun w => ¬ nap w) ↔
    wantVF belNapRest desRest (fun w => ¬ nap w) := by decide

/-- With the finest question, question-based want = standard vF want for Lobster. -/
theorem finest_simulates_vf_lobster :
    wantQuestionBased belLobDie desNotDie qFinest (fun w => ¬ nap w) ↔
    wantVF belLobDie desNotDie (fun w => ¬ nap w) := by decide

-- ============================================================================
-- §9. PrProp integration: definedness
-- ============================================================================

/-- Nap is defined in Q' (considered + diverse). -/
theorem nap_defined_in_qNapRest :
    wantDefined belNapRest qNapRest nap := by decide

/-- Fail is NOT defined in Q' (not considered). -/
theorem fail_not_defined_in_qNapRest :
    ¬ wantDefined belNapRest qNapRest fail := by decide

/-- The PrProp wrapper: nap is defined AND true. -/
theorem nap_prprop_holds :
    (wantPrProp belNapRest desRest qNapRest nap).presup .w0 ∧
    (wantPrProp belNapRest desRest qNapRest nap).assertion .w0 := by
  simp only [wantPrProp]
  exact ⟨by decide, by decide⟩

/-- The PrProp wrapper: fail is undefined (presup fails). -/
theorem fail_prprop_undefined :
    ¬(wantPrProp belNapRest desRest qNapRest fail).presup .w0 := by
  simp only [wantPrProp]; decide

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
def avoidWar : Set W := nap
def avoidNuclearWar : Set W := fun w => nap w ∨ rested w

instance : DecidablePred avoidWar := inferInstanceAs (DecidablePred nap)
instance : DecidablePred avoidNuclearWar := fun w => by unfold avoidNuclearWar; infer_instance

/-- Q_nuc: partition {peace, conventional war, nuclear war}. -/
def qNuclear : List (DecProp W) :=
  [mkDec nap,
   mkDec (fun w => ¬ nap w ∧ rested w),
   mkDec (fun w => ¬ nap w ∧ ¬ rested w)]

/-- Avoiding war entails avoiding nuclear war. -/
theorem avoidWar_entails_avoidNuclearWar :
    propEntails avoidWar avoidNuclearWar := by decide

/-- avoidNuclearWar is considered in Q_nuc (every answer settles it). -/
theorem avoidNuclearWar_considered :
    isConsidered qNuclear avoidNuclearWar := by decide

/-- William III: total uncertainty (all worlds compatible). -/
def belWilliam : Set W := fun _ => True
instance : DecidablePred belWilliam := fun _ => isTrue trivial

/-- William's beliefs are NOT sensitive to Q_nuc (all answers live). -/
theorem william_insensitive :
    ¬ isBelSensitive belWilliam qNuclear := by decide

/-- avoidNuclearWar is NOT defined for William (belief-sensitivity fails). -/
theorem avoidNuclearWar_not_defined_william :
    ¬ wantDefined belWilliam qNuclear avoidNuclearWar := by decide

/-- A modern person: beliefs rule out nuclear war (peace ∨ conventional). -/
def belModern : Set W := fun w => nap w ∨ rested w
instance : DecidablePred belModern := fun w => by unfold belModern; infer_instance

/-- Modern beliefs ARE sensitive to Q_nuc (nuclear-war answer ruled out). -/
theorem modern_sensitive :
    isBelSensitive belModern qNuclear := by decide

/-- avoidNuclearWar IS defined for a modern person. -/
theorem avoidNuclearWar_defined_modern :
    wantDefined belModern qNuclear avoidNuclearWar := by decide

def desAvoidWar : List (DecProp W) := [mkDec nap]

/-- A modern person who wants peace also wants to avoid nuclear war. -/
theorem modern_wants_avoidNuclearWar :
    wantQuestionBased belModern desAvoidWar qNuclear avoidNuclearWar := by decide

end PhillipsBrown2025
