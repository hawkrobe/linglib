import Linglib.Theories.Semantics.Attitudes.Desire
import Linglib.Theories.Semantics.Attitudes.CondoravdiLauer
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

/-!
# @cite{phillips-brown-2025} — Some-Things-Considered Desire

Question-based semantics for desire ascriptions: ⟦S wants p⟧^c is true
relative to a contextual question Q_c iff every undominated answer in
Q_c-Bel_S entails p. The proposal handles conflicting-desire cases —
"S wants p" + "S wants ¬p" — by varying Q_c.

This study file replicates the Nap, Lobster, Lu/Happy/Rain
(deck-stacking), and William-III/nuclear-war scenarios of
@cite{phillips-brown-2025}, plus a §11 cross-paper bridge to
@cite{condoravdi-lauer-2016} (an effective-preferential alternative
that refuses simultaneous `want(p)` and `want(¬p)`).

The substrate is `Theories/Semantics/Attitudes/Desire.lean`. All theorems
here either compute by `decide` over an 8-world model (3 binary
dimensions: `nap × rested × pass` = `lobster × gustatory × ¬die`) or
delegate to the substrate's general theorems
(`wantVF_no_simultaneous_pq_and_negpq`,
`wantQuestionBased_strawson_upward_monotonic`, …).

## §-by-§ map

| Paper | Study file |
|-------|-----------|
| §2.1 vF no-go | §5 (`vf_cannot_predict_both`, delegates to general) |
| §3.3 Q-relative belief | §3, §4 |
| §3.4 finest=vF | §8 |
| §3.5 best-answer semantics | §3, §4 |
| §3.6 Considering | §3, §4 |
| §3.7 Diversity, Anti-deckstacking | §3, §7 |
| §4.1 doxastic-closure blocking | §6 |
| §4.2 Belief-sensitivity | §10 |
| §5 cross-framework | §11 (CondoravdiLauer bridge) |

## Parallel discovery: Cariani 2013 `isVisible`

PB's `isConsidered` (§3.6) is the same predicate as @cite{cariani-2013}'s
`isVisible` (§4 p.545–546): both require every cell of the
partition/option-set to settle the prejacent. PB doesn't cite Cariani;
Cariani doesn't anticipate PB. The identification is exposed in
`Phenomena/Modality/Studies/Cariani2013.lean`, where Cariani's
`isVisible` is defined as `abbrev isVisible rc p := isConsidered
rc.options p` and the bridge theorem `isVisible_iff_isConsidered`
reduces to `Iff.rfl`. The agreement is independent reinvention across
the desire/deontic-modality boundary, surfaced by the substrate sharing
a common predicate.
-/

namespace PhillipsBrown2025

open Semantics.Attitudes.Desire

/-! ## §1. Eight-world model

3 binary dimensions: `d₁ × d₂ × d₃`. For Nap: `d₁ = nap`, `d₂ = rested`,
`d₃ = pass`. For Lobster (paper §2.2): `d₁ = lobster`, `d₂ = gustatory`,
`d₃ = ¬die`. The Lobster scenario reuses the Nap dimensions via
`abbrev` — see `lobster := nap`, `gustatory := rested`, `die := fail`
below; the structural isomorphism is documented and not coincidental
(`lobster_true := nap_true` is the same theorem under renaming). -/

inductive W where
  | w0 | w1 | w2 | w3 | w4 | w5 | w6 | w7
  deriving DecidableEq, Repr, Inhabited

instance : Fintype W where
  elems := {.w0, .w1, .w2, .w3, .w4, .w5, .w6, .w7}
  complete := λ w => by cases w <;> decide

/-! ## §2. Propositions

| World | nap | rested | pass |
|-------|-----|--------|------|
| w0    | T   | T      | T    |
| w1    | T   | T      | F    |
| w2    | T   | F      | T    |
| w3    | T   | F      | F    |
| w4    | F   | T      | T    |
| w5    | F   | T      | F    |
| w6    | F   | F      | T    |
| w7    | F   | F      | F    |
-/

def nap : Set W | .w0 | .w1 | .w2 | .w3 => True | _ => False
def rested : Set W | .w0 | .w1 | .w4 | .w5 => True | _ => False
def pass : Set W | .w0 | .w2 | .w4 | .w6 => True | _ => False
def fail : Set W := λ w => ¬ pass w

instance : DecidablePred nap := fun w => by cases w <;> unfold nap <;> infer_instance
instance : DecidablePred rested := fun w => by cases w <;> unfold rested <;> infer_instance
instance : DecidablePred pass := fun w => by cases w <;> unfold pass <;> infer_instance
instance : DecidablePred fail := fun w => by unfold fail; infer_instance

/-- The natural propositions of the model (basic dimensions), used to
    feed `isAntiDeckstacking`. AD's quantifier is restricted to this
    test set — see `Desire.isAntiDeckstacking` docstring. -/
def naturalProps : List (DecProp W) :=
  [mkDec nap, mkDec rested, mkDec pass]

/-! ## §3. Nap scenario -/

/-- Q' = partition by nap × rested (4 cells). -/
def qNapRest : List (DecProp W) :=
  [mkDec (fun w => nap w ∧ rested w),
   mkDec (fun w => nap w ∧ ¬ rested w),
   mkDec (fun w => ¬ nap w ∧ rested w),
   mkDec (fun w => ¬ nap w ∧ ¬ rested w)]

/-- Q'' = partition by nap × pass (4 cells). -/
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

/-- **Nap is true** relative to Q' with beliefs nap↔rested, desires [rested]. -/
theorem nap_true : wantQuestionBased belNapRest desRest qNapRest nap := by decide

/-- **Not-nap is true** relative to Q'' with beliefs pass↔¬nap, desires [pass]. -/
theorem not_nap_true :
    wantQuestionBased belNapPass desPass qNapPass (fun w => ¬ nap w) := by decide

/-- Fail is NOT considered relative to Q'. -/
theorem fail_not_considered : ¬ isConsidered qNapRest fail := by decide

/-- Fail is also not predicted true. -/
theorem fail_not_true :
    ¬ wantQuestionBased belNapRest desRest qNapRest fail := by decide

/-- Q' is diverse w.r.t. nap. -/
theorem nap_diverse : isDiverse qNapRest nap := by decide

/-! ## §4. Lobster scenario (paper §2.2)

The Lobster scenario reuses the Nap dimensions via `abbrev`:
`lobster := nap`, `gustatory := rested`, `die := fail`. The two paper
arguments use *different* questions over these dimensions — Q_{c''}
(`qLobGus`) ignores death, Q_{c'''} (`qLobDie`) ignores taste. -/

abbrev lobster : Set W := nap
abbrev gustatory : Set W := rested
abbrev die : Set W := fail

/-- Q_{c''} = partition by lobster × gustatory (= `qNapRest`). -/
abbrev qLobGus : List (DecProp W) := qNapRest

/-- Q_{c'''} = partition by lobster × die. -/
def qLobDie : List (DecProp W) :=
  [mkDec (fun w => nap w ∧ fail w),
   mkDec (fun w => nap w ∧ ¬ fail w),
   mkDec (fun w => ¬ nap w ∧ fail w),
   mkDec (fun w => ¬ nap w ∧ ¬ fail w)]

/-- Beliefs: die ↔ eat lobster. Bel = {w1, w3, w4, w6}. -/
def belLobDie : Set W := fun w => if nap w then fail w else ¬ fail w
instance : DecidablePred belLobDie := fun w => by unfold belLobDie; infer_instance

def desNotDie : List (DecProp W) := [mkDec (fun w => ¬ fail w)]

/-- **Lobster is true** in c'' (considering taste, ignoring death). -/
theorem lobster_true :
    wantQuestionBased belNapRest desRest qLobGus lobster := nap_true

/-- **Die is undefined in the Lobster context c''** (paper §2.2): in
    `qLobGus = qNapRest`, no cell settles `die`, so the Considering
    presupposition fails. -/
theorem die_not_considered_in_qLobGus :
    ¬ isConsidered qLobGus die := fail_not_considered

/-- **Not-lobster is true** in c''' (considering death, ignoring taste). -/
theorem not_lobster_true :
    wantQuestionBased belLobDie desNotDie qLobDie (fun w => ¬ nap w) := by decide

/-- **Not-die is also true** in c''' (best answer entails both ¬lobster and ¬die). -/
theorem not_die_true :
    wantQuestionBased belLobDie desNotDie qLobDie (fun w => ¬ fail w) := by decide

/-! ## §5. Von Fintel comparison and the no-go theorem

The paper's central argument against belief-based semantics: vF cannot
predict both `want p` and `want ¬p` simultaneously. Specialised here
for the Nap example, then derived from the substrate's general
`wantVF_no_simultaneous_pq_and_negpq`. -/

theorem vf_nap_true : wantVF belNapRest desRest nap := by decide

theorem vf_not_nap_false :
    ¬ wantVF belNapRest desRest (fun w => ¬ nap w) := by decide

/-- vF cannot predict both Nap and Not-nap with the same parameter set
    (specific instance). -/
theorem vf_cannot_predict_both :
    ¬(wantVF belNapRest desRest nap ∧
      wantVF belNapRest desRest (fun w => ¬ nap w)) := by
  intro ⟨_, h⟩; exact vf_not_nap_false h

/-- vF cannot predict both Nap and Not-nap (general no-go, delegates
    to the substrate). The witness is any belS-world that is
    Pareto-undominated under the desire ordering. -/
theorem vf_no_conflict_nap :
    ¬ (wantVF belNapRest desRest nap ∧
       wantVF belNapRest desRest (fun w => ¬ nap w)) :=
  wantVF_no_simultaneous_pq_and_negpq belNapRest desRest nap
    ⟨.w0, by decide,
     by intro z hz ⟨_, hbad⟩; revert hz hbad; cases z <;> decide⟩

/-! ## §6. Doxastic closure blocking (paper §4.1)

@cite{villalta-2008} identified the doxastic-closure problem for
belief-based semantics: any proposition true at all best belief-worlds
is predicted wanted, over-generating for coincidental propositions.

The question-based approach makes `fail` UNDEFINED rather than merely
false: `fail` is not settled by Q' (the nap × rested partition), so the
Considering presupposition blocks ⟦want(fail)⟧^{Q'} at definedness.
With Q'' (the nap × pass partition), `fail` is settled — and the
contrast is exactly the paper's point. -/

theorem nap_considered_in_qNapPass :
    isConsidered qNapPass nap := by decide

theorem fail_considered_in_qNapPass :
    isConsidered qNapPass fail := by decide

/-! ## §7. Anti-deckstacking (paper §3.7)

Lu is unsure if it will rain, but is sure he'll feel happy no matter
what. Q'''' (deck-stacked) = `{r, ¬r∧h, ¬r∧¬h}` asymmetrically
cross-cuts rain with happiness; the `r` cell ignores `h` while the
others distinguish it. Cell `¬r∧h` predetermines `h` (entails it), but
`h` is not considered by the question. AD fails on `qDeckstacked` with
test set `[r, h]`.

Q''''' (level playing field) = partition by `rain × happy` (4 cells).
AD passes for the same `[r, h]` test set. -/

def happy : Set W | .w0 | .w1 | .w4 | .w5 => True | _ => False
def rain : Set W | .w0 | .w1 | .w2 | .w3 => True | _ => False

instance : DecidablePred happy := fun w => by cases w <;> unfold happy <;> infer_instance
instance : DecidablePred rain := fun w => by cases w <;> unfold rain <;> infer_instance

/-- Test set of natural propositions for the Lu scenario. -/
def naturalPropsLu : List (DecProp W) := [mkDec rain, mkDec happy]

/-- Q'''' (deck-stacked): {r, ¬r∧h, ¬r∧¬h}. -/
def qDeckstacked : List (DecProp W) :=
  [mkDec rain,
   mkDec (fun w => ¬ rain w ∧ happy w),
   mkDec (fun w => ¬ rain w ∧ ¬ happy w)]

/-- Lu's beliefs: happy unconditionally. -/
def belLu : Set W := happy
instance : DecidablePred belLu := inferInstanceAs (DecidablePred happy)

def desHappy : List (DecProp W) := [mkDec happy]

/-- `happy` is not considered in the deck-stacked Q'''' (the `rain`
    cell contains both happy and unhappy worlds). -/
theorem happy_not_considered_deckstacked :
    ¬ isConsidered qDeckstacked happy := by decide

/-- A `happy`-answer exists in qDeckstacked (the `¬r∧h` cell entails
    `happy`) — the deck is stacked in favor of ¬rain. -/
theorem happy_answer_exists_deckstacked :
    ∃ a ∈ qDeckstacked, ∀ w, a.prop w → happy w := by decide

/-- Without the constraint, the question-based semantics wrongly
    predicts Not-rain. -/
theorem not_rain_deckstacked_true :
    wantQuestionBased belLu desHappy qDeckstacked (fun w => ¬ rain w) := by decide

/-- Q''''' (level playing field): partition by rain × happy. -/
def qRainHappy : List (DecProp W) :=
  [mkDec (fun w => rain w ∧ happy w),
   mkDec (fun w => rain w ∧ ¬ happy w),
   mkDec (fun w => ¬ rain w ∧ happy w),
   mkDec (fun w => ¬ rain w ∧ ¬ happy w)]

theorem happy_considered_fair :
    isConsidered qRainHappy happy := by decide

/-- With the fair question, Not-rain is correctly predicted false. -/
theorem not_rain_false_fair :
    ¬ wantQuestionBased belLu desHappy qRainHappy (fun w => ¬ rain w) := by decide

/-- The deck-stacked question fails Anti-deckstacking on test set
    `[r, h]` (`h` is predetermined by the `¬r∧h` cell but not
    considered by Q''''). -/
theorem qDeckstacked_fails_antideckstacking :
    ¬ isAntiDeckstacking naturalPropsLu qDeckstacked := by decide

/-- The fair (cross-product) question satisfies Anti-deckstacking —
    every basic proposition is settled by every cell. -/
theorem qRainHappy_satisfies_antideckstacking :
    isAntiDeckstacking naturalPropsLu qRainHappy := by decide

/-- Q' (`qNapRest`) satisfies Anti-deckstacking on the natural-prop
    test set `[nap, rested, pass]` — the cross-product over `nap` and
    `rested` settles `nap` and `rested`; no cell entails `pass`, so
    AD's antecedent is vacuous for `pass`. -/
theorem qNapRest_satisfies_antideckstacking :
    isAntiDeckstacking naturalProps qNapRest := by decide

/-! ## §8. Finest-question simulation (paper §3.4)

When Q_c is the finest partition (singleton cells = individual worlds),
the question-based semantics reduces to vF. The substrate provides
`finestPartition : List W → List (DecProp W)`; here we instantiate it
on the explicit world list of the model. -/

def allWorldsW : List W := [.w0, .w1, .w2, .w3, .w4, .w5, .w6, .w7]

def qFinest : List (DecProp W) := finestPartition allWorldsW

/-- The 8-world list `allWorldsW` covers `W`. Hypothesis required by the
    substrate's general `wantQuestionBased_finestPartition_iff_wantVF`. -/
theorem allWorldsW_complete : ∀ w : W, w ∈ allWorldsW := by
  intro w; cases w <;> decide

/-- With the finest question, question-based want = standard vF want
    for `nap`. Derived from the substrate's general
    `wantQuestionBased_finestPartition_iff_wantVF`, not by `decide`. -/
theorem finest_simulates_vf_nap :
    wantQuestionBased belNapRest desRest qFinest nap ↔
    wantVF belNapRest desRest nap :=
  wantQuestionBased_finestPartition_iff_wantVF belNapRest desRest
    allWorldsW allWorldsW_complete nap

/-- With the finest question, question-based want = standard vF want
    for `¬nap`. -/
theorem finest_simulates_vf_not_nap :
    wantQuestionBased belNapRest desRest qFinest (fun w => ¬ nap w) ↔
    wantVF belNapRest desRest (fun w => ¬ nap w) :=
  wantQuestionBased_finestPartition_iff_wantVF belNapRest desRest
    allWorldsW allWorldsW_complete (fun w => ¬ nap w)

/-- With the finest question, question-based want = standard vF want
    for `¬lobster` in the Lobster context. -/
theorem finest_simulates_vf_not_lobster :
    wantQuestionBased belLobDie desNotDie qFinest (fun w => ¬ nap w) ↔
    wantVF belLobDie desNotDie (fun w => ¬ nap w) :=
  wantQuestionBased_finestPartition_iff_wantVF belLobDie desNotDie
    allWorldsW allWorldsW_complete (fun w => ¬ nap w)

/-! ## §9. Definedness via PrProp (paper §3.6) -/

theorem nap_defined_in_qNapRest :
    wantDefined belNapRest naturalProps qNapRest nap := by decide

theorem fail_not_defined_in_qNapRest :
    ¬ wantDefined belNapRest naturalProps qNapRest fail := by decide

theorem nap_prprop_holds :
    (wantPrProp belNapRest desRest naturalProps qNapRest nap).presup .w0 ∧
    (wantPrProp belNapRest desRest naturalProps qNapRest nap).assertion .w0 := by
  refine ⟨?_, ?_⟩ <;> simp only [wantPrProp] <;> decide

theorem fail_prprop_undefined :
    ¬(wantPrProp belNapRest desRest naturalProps qNapRest fail).presup .w0 := by
  simp only [wantPrProp]; decide

/-! ## §10. Belief-sensitivity: William III / nuclear war (paper §4.2)

William III wanted to avoid war. Avoiding war entails avoiding nuclear
war. But we cannot conclude William III wanted to avoid nuclear war —
he lacked the conceptual resources to grasp nuclear war.

Mechanism: William's beliefs are NOT sensitive to Q_nuc that
distinguishes nuclear from conventional war. All Q_nuc answers are
compatible with his beliefs (total uncertainty), so `isBelSensitive`
returns false and `wantDefined` blocks the inference. A modern person
whose beliefs rule out nuclear war DOES have belief-sensitive context,
so the inference goes through.

Strawson upward monotonicity is the closure principle at issue;
@cite{phillips-brown-2025} §4.2 argues that question-based semantics
must be Strawson-but-not-naively upward monotonic, with definedness
gating the inference. The substrate's
`wantQuestionBased_strawson_upward_monotonic` captures the licit
direction. -/

def avoidWar : Set W := nap
def avoidNuclearWar : Set W := fun w => nap w ∨ rested w

instance : DecidablePred avoidWar := inferInstanceAs (DecidablePred nap)
instance : DecidablePred avoidNuclearWar := fun w => by unfold avoidNuclearWar; infer_instance

def qNuclear : List (DecProp W) :=
  [mkDec nap,
   mkDec (fun w => ¬ nap w ∧ rested w),
   mkDec (fun w => ¬ nap w ∧ ¬ rested w)]

/-- Natural-prop test set for the nuclear-war scenario. The Nap-vs-war
    distinction (`nap`) and the war-of-any-kind distinction
    (`avoidNuclearWar`) are the salient dimensions; `rested` and
    `pass` are not part of this scenario's vocabulary. -/
def naturalPropsNuclear : List (DecProp W) :=
  [mkDec nap, mkDec avoidNuclearWar]

theorem avoidWar_entails_avoidNuclearWar :
    ∀ w, avoidWar w → avoidNuclearWar w := by decide

theorem avoidNuclearWar_considered :
    isConsidered qNuclear avoidNuclearWar := by decide

/-- William III: total uncertainty (all worlds compatible). -/
def belWilliam : Set W := fun _ => True
instance : DecidablePred belWilliam := fun _ => isTrue trivial

theorem william_insensitive :
    ¬ isBelSensitive belWilliam qNuclear := by decide

theorem avoidNuclearWar_not_defined_william :
    ¬ wantDefined belWilliam naturalPropsNuclear qNuclear avoidNuclearWar := by decide

/-- Modern person: beliefs rule out nuclear war (peace ∨ conventional). -/
def belModern : Set W := fun w => nap w ∨ rested w
instance : DecidablePred belModern := fun w => by unfold belModern; infer_instance

theorem modern_sensitive :
    isBelSensitive belModern qNuclear := by decide

theorem avoidNuclearWar_defined_modern :
    wantDefined belModern naturalPropsNuclear qNuclear avoidNuclearWar := by decide

def desAvoidWar : List (DecProp W) := [mkDec nap]

theorem modern_wants_avoidNuclearWar :
    wantQuestionBased belModern desAvoidWar qNuclear avoidNuclearWar := by decide

/-! ## §11. Cross-paper bridge: @cite{condoravdi-lauer-2016}

@cite{condoravdi-lauer-2016}'s effective-preferential `wantEP` carries
a joint-belief-consistency theorem (`wantEP_jointly_belief_consistent`):
if both `wantEP EP a φ w` and `wantEP EP a ψ w` hold, then
`(φ ∩ ψ) ∩ B(a, w) ≠ ∅`. Specialized to `ψ = φᶜ`, the conclusion
becomes `∅ ∩ B(a, w) ≠ ∅`, which is contradictory. So C&L *forbids*
simultaneous `want(p)` and `want(¬p)` against a single belief state and
preference structure.

@cite{phillips-brown-2025} resolves the conflict by varying the
contextual question Q_c (and the contextually-relevant `belS`) per
ascription. C&L resolves it by varying the preference structure (per
reading: `wantPExact` / `wantPSuccess` / `wantPQH`). The two
resolutions are orthogonal — both can coexist in a unified theory of
desire, but they make non-overlapping claims. -/

/-- C&L's joint-belief-consistency, specialized to `ψ = φᶜ`: no single
    EP-want can hold of both `φ` and `¬φ` simultaneously, since their
    intersection is empty.

    This is a *paper-level* contrast with PB §3: PB makes both
    `nap_true` and `not_nap_true` work by varying Q_c and `belS`; the
    C&L analysis would need different `EP` per ascription to reproduce
    the contrast. -/
theorem condoravdiLauer_blocks_simultaneous_pq_and_negpq
    {Agent W : Type} {B : Agent → W → Set W}
    (EP : Semantics.Attitudes.CondoravdiLauer.EffectivePreferentialBackground Agent W B)
    (a : Agent) (φ : Set W) (w : W)
    (hφ : Semantics.Attitudes.CondoravdiLauer.wantEP EP a φ w)
    (hnegφ : Semantics.Attitudes.CondoravdiLauer.wantEP EP a (fun w => ¬ φ w) w) :
    False := by
  have h := Semantics.Attitudes.CondoravdiLauer.wantEP_jointly_belief_consistent
              EP hφ hnegφ
  apply h
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun ⟨h1, h2⟩ _ => h2 h1

/-! ## §12. Heim foil and parametric no-go

@cite{heim-1992}'s comparative-belief semantics (`wantHeim`) is the
*other* canonical belief-based account — formalized at
`Theories/Semantics/Attitudes/Desire.lean` and exercised in
`Phenomena/Modality/Studies/Heim1992.lean`. The substrate's
`BeliefBasedDesireSemantics` typology packages vF, Heim, and (in
principle) Levinson 2003 / sufficient-desirability accounts under a
single structural property `isConflictBlocking`.

PB's argument against belief-based semantics generalizes from
`vf_no_conflict_nap` (vF only) to:

* Heim 1992: blocked by `wantHeim_no_simultaneous_pq_and_negpq` under
  preference asymmetry. The (40) amendment makes definedness of
  `wantHeim p` and `wantHeim ¬p` simultaneously impossible when the
  agent's beliefs are consistent.
* vF: blocked by `wantVF_no_simultaneous_pq_and_negpq`.
* Any future `BeliefBasedDesireSemantics` instance: blocked by the
  parametric `isConflictBlocking` predicate (currently proved per
  instance in `Theories/Semantics/Attitudes/Desire.lean`).

PB's `wantQuestionBased` *evades* the no-go by selecting from
`Q-Bel_S` rather than directly from `Bel_S` — it is *not* an
instance of `BeliefBasedDesireSemantics` (the question parameter
`answers` plays a non-trivial role outside the typeclass shape). -/

theorem heim_no_go_covers_belief_based_family
    {W : Type} [Fintype W] [DecidableEq W]
    (params : Semantics.Attitudes.Desire.HeimDesireParams W) (w_eval : W)
    (hAsym : ∀ x y, params.pref w_eval x y → params.pref w_eval y x → x = y)
    (belS : Set W) [DecidablePred belS]
    (p : Set W) [DecidablePred p]
    (h : Semantics.Attitudes.Desire.wantHeimDefined belS p) :
    ¬ (Semantics.Attitudes.Desire.wantHeim belS params w_eval p ∧
       Semantics.Attitudes.Desire.wantHeim belS params w_eval (fun w => ¬ p w)) :=
  Semantics.Attitudes.Desire.wantHeim_no_simultaneous_pq_and_negpq
    belS params w_eval p hAsym h

/-- **@cite{lassiter-2017} also evades the no-go but via numerical
    threshold + graded value rather than question-sensitivity.** The
    Lassiter substrate's `threshold_admits_conflict_witness` exhibits a
    concrete configuration where both `want(p)` and `want(¬p)` fire on
    a single `(belS, pr, V, θ)` — falsifying `isConflictBlocking`.

    Lassiter and PB are now formalized as *two distinct* non-instances
    of `BeliefBasedDesireSemantics`. PB's escape route: question
    parameter outside the BBS shape. Lassiter's: numerical threshold
    on graded expected value. The cross-paper picture: the typology
    correctly excludes both, and they evade via genuinely different
    mechanisms. -/
theorem lassiter_evades_no_go_via_grading :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (belS : Set W) (_ : DecidablePred belS)
      (pr : W → ℚ) (V : W → ℚ) (θ : ℚ)
      (p : Set W) (_ : DecidablePred p),
      Semantics.Attitudes.Desire.Lassiter.want belS pr V θ p ∧
      Semantics.Attitudes.Desire.Lassiter.want belS pr V θ (fun w => ¬ p w) :=
  Semantics.Attitudes.Desire.Lassiter.threshold_admits_conflict_witness

/-! ## Summary

The 8-world model verifies all of the paper's quantitative predictions
that fit the 3-binary-dimension encoding (Nap, Lobster-via-isomorphism,
Lu/deck-stacking, William-III). The substrate carries the *general*
arguments (no-go for vF, no-go for Heim, Strawson upward monotonicity,
finest=vF direction, parametric `BeliefBasedDesireSemantics`
typology). The §11 bridge makes the disagreement with C&L explicit;
the §12 foil shows the no-go covers the whole belief-based family.

What's deferred:

* The general `wantQuestionBased qFinest = wantVF` ↔ identity is
  verified for the three named propositions in §8 by `decide`; lifting
  to the substrate as a universal `∀ p, ...` theorem is sketched in
  `Desire.lean` as future work (the proof requires a structural lemma
  relating singleton-cell preference to single-world preference).

* The Lobster scenario reuses Nap's dimensions via `abbrev` — a
  4-dimension model would let `qLobGus` and `qLobDie` be genuinely
  distinct in their underlying worlds. The current encoding is honest
  (`qLobGus := qNapRest`) and adequate for the structural argument.

* @cite{crnic-2014} is referenced in `Desire.lean`'s docstring as the
  acknowledged precursor; a Crnič-2011 study file is the natural next
  paper.

* The CPR overgeneration argument (paper §2.2) is handled here via
  `die_not_considered_in_qLobGus`. A separate CPR formalization (paper
  §2.4) is not yet in linglib.
-/

end PhillipsBrown2025
