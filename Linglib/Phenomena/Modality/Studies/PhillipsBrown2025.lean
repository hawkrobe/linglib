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
-/

set_option autoImplicit false

namespace Phenomena.Modality.Studies.PhillipsBrown2025

-- ============================================================================
-- §1. Eight-world model
-- ============================================================================

/-- 8 worlds encoding 3 binary dimensions (d₁ × d₂ × d₃).
For Nap: d₁ = nap, d₂ = rested, d₃ = pass.
For Lobster: d₁ = eat lobster, d₂ = gustatory, d₃ = ¬die. -/
inductive W where
  | w0 | w1 | w2 | w3 | w4 | w5 | w6 | w7
  deriving DecidableEq, Repr, Inhabited

def allW : List W := [.w0, .w1, .w2, .w3, .w4, .w5, .w6, .w7]

-- ============================================================================
-- §2. Semantic operations (mirroring Desire.lean for W)
-- ============================================================================

def entails (a p : W → Bool) : Bool :=
  allW.all λ w => !a w || p w

def overlap (a q : W → Bool) : Bool :=
  allW.any λ w => a w && q w

def satisfiedBy (GS : List (W → Bool)) (a : W → Bool) : List (W → Bool) :=
  GS.filter λ p => entails a p

def propEquiv (p q : W → Bool) : Bool :=
  allW.all λ w => p w == q w

def preferAnswer (GS : List (W → Bool)) (a a' : W → Bool) : Bool :=
  let dA := satisfiedBy GS a
  let dA' := satisfiedBy GS a'
  (dA'.all λ p => dA.any λ q => allW.all λ w => p w == q w) &&
  (dA.any λ p => dA'.all λ q => allW.any λ w => p w != q w)

def bestAnswers (GS : List (W → Bool)) (answers : List (W → Bool)) :
    List (W → Bool) :=
  answers.filter λ a =>
    answers.all λ a' => propEquiv a' a || !preferAnswer GS a' a

def qBel (answers : List (W → Bool)) (belS : W → Bool) : List (W → Bool) :=
  answers.filter λ a => overlap a belS

/-- ⟦S wants p⟧^c = all best answers in Q_c-Bel_S are p-answers. -/
def want (belS : W → Bool) (GS : List (W → Bool))
    (answers : List (W → Bool)) (p : W → Bool) : Bool :=
  let live := qBel answers belS
  let best := bestAnswers GS live
  best.all λ a => entails a p

-- ============================================================================
-- §3. Metasemantic constraints
-- ============================================================================

/-- p is *considered* relative to Q iff every answer settles p.
**Considering Constraint**: ⟦S wants p⟧^c is defined only if p is
considered relative to Q_c. -/
def isConsidered (answers : List (W → Bool)) (p : W → Bool) : Bool :=
  answers.all λ a => entails a p || entails a (λ w => !p w)

/-- **Diversity**: Q_c must contain both p-answers and ¬p-answers. -/
def isDiverse (answers : List (W → Bool)) (p : W → Bool) : Bool :=
  (answers.any λ a => entails a p) &&
  (answers.any λ a => entails a (λ w => !p w))

-- ============================================================================
-- §4. Nap scenario
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

-- Core predictions

/-- **Nap is true** relative to Q' with beliefs nap↔rested, desires [rested].
Best in Q'-Bel: n∧r = {w0,w1} entails nap. -/
theorem nap_true : want belNapRest desRest qNapRest nap = true := by native_decide

/-- **Not-nap is true** relative to Q'' with beliefs pass↔¬nap, desires [pass].
Best in Q''-Bel: ¬n∧p = {w4,w6} entails ¬nap. -/
theorem not_nap_true :
    want belNapPass desPass qNapPass (λ w => !nap w) = true := by native_decide

-- Considering Constraint blocks Fail

/-- Fail is NOT considered relative to Q': each cell contains both
pass-worlds and fail-worlds, so no cell settles whether you fail. -/
theorem fail_not_considered : isConsidered qNapRest fail = false := by native_decide

/-- Fail is also not predicted true (best answers don't entail fail). -/
theorem fail_not_true :
    want belNapRest desRest qNapRest fail = false := by native_decide

/-- Q' is diverse w.r.t. nap: both nap-answers and ¬nap-answers exist. -/
theorem nap_diverse : isDiverse qNapRest nap = true := by native_decide

-- ============================================================================
-- §5. Lobster scenario (structural isomorphism with Nap)
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
    want belNapRest desRest qNapRest lobster = true := nap_true

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
    want belLobDie desNotDie qLobDie (λ w => !nap w) = true := by native_decide

/-- **Not-die is also true** in c''' (best answer entails both ¬lobster and ¬die). -/
theorem not_die_true :
    want belLobDie desNotDie qLobDie (λ w => !fail w) = true := by native_decide

-- ============================================================================
-- §6. Von Fintel comparison
-- ============================================================================

/-- Kratzer-style world ordering: w at least as good as z iff w satisfies
every desire that z satisfies. -/
def atLeastAsGood (GS : List (W → Bool)) (w z : W) : Bool :=
  (GS.filter (· z)).all (· w)

/-- Standard von Fintel semantics (not question-based):
⟦S wants p⟧ = all best worlds in Bel_S are p-worlds. -/
def wantVF (belS : W → Bool) (GS : List (W → Bool)) (p : W → Bool) : Bool :=
  let belWorlds := allW.filter belS
  let best := belWorlds.filter λ w =>
    !(belWorlds.any λ z =>
      atLeastAsGood GS z w && !atLeastAsGood GS w z)
  best.all p

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
-- §7. Doxastic closure blocking (§4.1)
-- ============================================================================

/-! On standard vF, want(nap) + Bel(nap ↔ fail) → want(fail): the best
nap-worlds are also fail-worlds, so "all best are fail-worlds."

The question-based semantics blocks this: fail is not considered in Q',
so ⟦want(fail)⟧^Q' is undefined. The block is `fail_not_considered` above. -/

/-- In the Not-nap context Q'', nap IS considered (every cell settles nap). -/
theorem nap_considered_in_qNapPass :
    isConsidered qNapPass nap = true := by native_decide

/-- Fail IS considered in Q'' (pass is a partition dimension, so fail = ¬pass
is settled by every cell). But fail is NOT considered in Q' — and that is
what blocks the doxastic closure inference in the Nap context. -/
theorem fail_considered_in_qNapPass :
    isConsidered qNapPass fail = true := by native_decide

end Phenomena.Modality.Studies.PhillipsBrown2025
