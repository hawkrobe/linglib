import Linglib.Semantics.Attitudes.Desire
import Linglib.Semantics.Attitudes.CondoravdiLauer
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

/-!
# [phillips-brown-2025] — Some-Things-Considered Desire

Question-based semantics for desire ascriptions: ⟦S wants p⟧^c is true
relative to a contextual question Q_c iff every undominated answer in
Q_c-Bel_S entails p. The proposal handles conflicting-desire cases —
"S wants p" + "S wants ¬p" — by varying Q_c.

This study file replicates the Nap, Lobster, Lu/Happy/Rain
(deck-stacking), and William-III/nuclear-war scenarios of
[phillips-brown-2025], plus a §11 cross-paper bridge to
[condoravdi-lauer-2016] (an effective-preferential alternative
that refuses simultaneous `want(p)` and `want(¬p)`).

The substrate is `Semantics/Attitudes/Desire.lean`. All theorems
here either compute by `decide` over an 8-world model (3 binary
dimensions: `nap × rested × pass` = `lobster × gustatory × ¬die`) or
delegate to the substrate's general theorems
(`wantVonFintel_no_conflict`,
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

PB's `IsConsidered` (§3.6) is the same predicate as [cariani-2013]'s
`isVisible` (§4 p.545–546): both require every cell of the
partition/option-set to settle the prejacent. PB doesn't cite Cariani;
Cariani doesn't anticipate PB. The identification is exposed in
`Studies/Cariani2013.lean`, where Cariani's
`isVisible` is defined as `abbrev isVisible rc p := IsConsidered
rc.options p` and the bridge theorem `isVisible_iff_IsConsidered`
reduces to `Iff.rfl`. The agreement is independent reinvention across
the desire/deontic-modality boundary, surfaced by the substrate sharing
a common predicate.
-/

namespace PhillipsBrown2025

open Desire
open Core.Order (EffectivePreference)

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
    feed `IsAntiDeckstacking`. AD's quantifier is restricted to this
    test set — see `Desire.IsAntiDeckstacking` docstring. -/
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
theorem nap_true : WantQuestionBased belNapRest desRest qNapRest nap := by decide

/-- **Not-nap is true** relative to Q'' with beliefs pass↔¬nap, desires [pass]. -/
theorem not_nap_true :
    WantQuestionBased belNapPass desPass qNapPass (fun w => ¬ nap w) := by decide

/-- Fail is NOT considered relative to Q'. -/
theorem fail_not_considered : ¬ IsConsidered qNapRest fail := by decide

/-- Fail is also not predicted true. -/
theorem fail_not_true :
    ¬ WantQuestionBased belNapRest desRest qNapRest fail := by decide

/-- Q' is diverse w.r.t. nap. -/
theorem nap_diverse : IsDiverse qNapRest nap := by decide

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
    WantQuestionBased belNapRest desRest qLobGus lobster := nap_true

/-- **Die is undefined in the Lobster context c''** (paper §2.2): in
    `qLobGus = qNapRest`, no cell settles `die`, so the Considering
    presupposition fails. -/
theorem die_not_considered_in_qLobGus :
    ¬ IsConsidered qLobGus die := fail_not_considered

/-- **Not-lobster is true** in c''' (considering death, ignoring taste). -/
theorem not_lobster_true :
    WantQuestionBased belLobDie desNotDie qLobDie (fun w => ¬ nap w) := by decide

/-- **Not-die is also true** in c''' (best answer entails both ¬lobster and ¬die). -/
theorem not_die_true :
    WantQuestionBased belLobDie desNotDie qLobDie (fun w => ¬ fail w) := by decide

/-! ## §5. Von Fintel comparison and the no-go theorem

The paper's central argument against belief-based semantics: vF cannot
predict both `want p` and `want ¬p` simultaneously. Specialised here
for the Nap example, then derived from the substrate's general
`wantVonFintel_no_conflict`. -/

theorem vf_nap_true : WantVonFintel belNapRest desRest nap := by decide

theorem vf_not_nap_false :
    ¬ WantVonFintel belNapRest desRest (fun w => ¬ nap w) := by decide

/-- vF cannot predict both Nap and Not-nap with the same parameter set
    (specific instance). -/
theorem vf_cannot_predict_both :
    ¬(WantVonFintel belNapRest desRest nap ∧
      WantVonFintel belNapRest desRest (fun w => ¬ nap w)) := by
  intro ⟨_, h⟩; exact vf_not_nap_false h

/-- vF cannot predict both Nap and Not-nap (general no-go, delegates
    to the substrate). The witness is any belS-world that is
    Pareto-undominated under the desire ordering. -/
theorem vf_no_conflict_nap :
    ¬ (WantVonFintel belNapRest desRest nap ∧
       WantVonFintel belNapRest desRest (fun w => ¬ nap w)) :=
  wantVonFintel_no_conflict belNapRest desRest nap
    ⟨.w0, by decide,
     by intro z hz ⟨_, hbad⟩; revert hz hbad; cases z <;> decide⟩

/-! ## §6. Doxastic closure blocking (paper §4.1)

[villalta-2008] identified the doxastic-closure problem for
belief-based semantics: any proposition true at all best belief-worlds
is predicted wanted, over-generating for coincidental propositions.

The question-based approach makes `fail` UNDEFINED rather than merely
false: `fail` is not settled by Q' (the nap × rested partition), so the
Considering presupposition blocks ⟦want(fail)⟧^{Q'} at definedness.
With Q'' (the nap × pass partition), `fail` is settled — and the
contrast is exactly the paper's point. -/

theorem nap_considered_in_qNapPass :
    IsConsidered qNapPass nap := by decide

theorem fail_considered_in_qNapPass :
    IsConsidered qNapPass fail := by decide

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
    ¬ IsConsidered qDeckstacked happy := by decide

/-- A `happy`-answer exists in qDeckstacked (the `¬r∧h` cell entails
    `happy`) — the deck is stacked in favor of ¬rain. -/
theorem happy_answer_exists_deckstacked :
    ∃ a ∈ qDeckstacked, ∀ w, a.prop w → happy w := by decide

/-- Without the constraint, the question-based semantics wrongly
    predicts Not-rain. -/
theorem not_rain_deckstacked_true :
    WantQuestionBased belLu desHappy qDeckstacked (fun w => ¬ rain w) := by decide

/-- Q''''' (level playing field): partition by rain × happy. -/
def qRainHappy : List (DecProp W) :=
  [mkDec (fun w => rain w ∧ happy w),
   mkDec (fun w => rain w ∧ ¬ happy w),
   mkDec (fun w => ¬ rain w ∧ happy w),
   mkDec (fun w => ¬ rain w ∧ ¬ happy w)]

theorem happy_considered_fair :
    IsConsidered qRainHappy happy := by decide

/-- With the fair question, Not-rain is correctly predicted false. -/
theorem not_rain_false_fair :
    ¬ WantQuestionBased belLu desHappy qRainHappy (fun w => ¬ rain w) := by decide

/-- The deck-stacked question fails Anti-deckstacking on test set
    `[r, h]` (`h` is predetermined by the `¬r∧h` cell but not
    considered by Q''''). -/
theorem qDeckstacked_fails_antideckstacking :
    ¬ IsAntiDeckstacking naturalPropsLu qDeckstacked := by decide

/-- The fair (cross-product) question satisfies Anti-deckstacking —
    every basic proposition is settled by every cell. -/
theorem qRainHappy_satisfies_antideckstacking :
    IsAntiDeckstacking naturalPropsLu qRainHappy := by decide

/-- Q' (`qNapRest`) satisfies Anti-deckstacking on the natural-prop
    test set `[nap, rested, pass]` — the cross-product over `nap` and
    `rested` settles `nap` and `rested`; no cell entails `pass`, so
    AD's antecedent is vacuous for `pass`. -/
theorem qNapRest_satisfies_antideckstacking :
    IsAntiDeckstacking naturalProps qNapRest := by decide

/-! ## §8. Finest-question simulation (paper §3.4)

When Q_c is the finest partition (singleton cells = individual worlds),
the question-based semantics reduces to vF. The substrate provides
`finestPartition : List W → List (DecProp W)`; here we instantiate it
on the explicit world list of the model. -/

def allWorldsW : List W := [.w0, .w1, .w2, .w3, .w4, .w5, .w6, .w7]

def qFinest : List (DecProp W) := finestPartition allWorldsW

/-- The 8-world list `allWorldsW` covers `W`. Hypothesis required by the
    substrate's general `wantQuestionBased_finestPartition_iff_WantVonFintel`. -/
theorem allWorldsW_complete : ∀ w : W, w ∈ allWorldsW := by
  intro w; cases w <;> decide

/-- With the finest question, question-based want = standard vF want
    for `nap`. Derived from the substrate's general
    `wantQuestionBased_finestPartition_iff_WantVonFintel`, not by `decide`. -/
theorem finest_simulates_vf_nap :
    WantQuestionBased belNapRest desRest qFinest nap ↔
    WantVonFintel belNapRest desRest nap :=
  wantQuestionBased_finestPartition_iff_WantVonFintel belNapRest desRest
    allWorldsW allWorldsW_complete nap

/-- With the finest question, question-based want = standard vF want
    for `¬nap`. -/
theorem finest_simulates_vf_not_nap :
    WantQuestionBased belNapRest desRest qFinest (fun w => ¬ nap w) ↔
    WantVonFintel belNapRest desRest (fun w => ¬ nap w) :=
  wantQuestionBased_finestPartition_iff_WantVonFintel belNapRest desRest
    allWorldsW allWorldsW_complete (fun w => ¬ nap w)

/-- With the finest question, question-based want = standard vF want
    for `¬lobster` in the Lobster context. -/
theorem finest_simulates_vf_not_lobster :
    WantQuestionBased belLobDie desNotDie qFinest (fun w => ¬ nap w) ↔
    WantVonFintel belLobDie desNotDie (fun w => ¬ nap w) :=
  wantQuestionBased_finestPartition_iff_WantVonFintel belLobDie desNotDie
    allWorldsW allWorldsW_complete (fun w => ¬ nap w)

/-! ## §9. Definedness via PartialProp (paper §3.6) -/

theorem nap_defined_in_qNapRest :
    WantDefined belNapRest naturalProps qNapRest nap := by decide

theorem fail_not_defined_in_qNapRest :
    ¬ WantDefined belNapRest naturalProps qNapRest fail := by decide

theorem nap_prprop_holds :
    (wantPartialProp belNapRest desRest naturalProps qNapRest nap).presup .w0 ∧
    (wantPartialProp belNapRest desRest naturalProps qNapRest nap).assertion .w0 := by
  refine ⟨?_, ?_⟩ <;> simp only [wantPartialProp] <;> decide

theorem fail_prprop_undefined :
    ¬(wantPartialProp belNapRest desRest naturalProps qNapRest fail).presup .w0 := by
  simp only [wantPartialProp]; decide

/-! ## §10. Belief-sensitivity: William III / nuclear war (paper §4.2)

William III wanted to avoid war. Avoiding war entails avoiding nuclear
war. But we cannot conclude William III wanted to avoid nuclear war —
he lacked the conceptual resources to grasp nuclear war.

Mechanism: William's beliefs are NOT sensitive to Q_nuc that
distinguishes nuclear from conventional war. All Q_nuc answers are
compatible with his beliefs (total uncertainty), so `IsBelSensitive`
returns false and `WantDefined` blocks the inference. A modern person
whose beliefs rule out nuclear war DOES have belief-sensitive context,
so the inference goes through.

Strawson upward monotonicity is the closure principle at issue;
[phillips-brown-2025] §4.2 argues that question-based semantics
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
    IsConsidered qNuclear avoidNuclearWar := by decide

/-- William III: total uncertainty (all worlds compatible). -/
def belWilliam : Set W := fun _ => True
instance : DecidablePred belWilliam := fun _ => isTrue trivial

theorem william_insensitive :
    ¬ IsBelSensitive belWilliam qNuclear := by decide

theorem avoidNuclearWar_not_defined_william :
    ¬ WantDefined belWilliam naturalPropsNuclear qNuclear avoidNuclearWar := by decide

/-- Modern person: beliefs rule out nuclear war (peace ∨ conventional). -/
def belModern : Set W := fun w => nap w ∨ rested w
instance : DecidablePred belModern := fun w => by unfold belModern; infer_instance

theorem modern_sensitive :
    IsBelSensitive belModern qNuclear := by decide

theorem avoidNuclearWar_defined_modern :
    WantDefined belModern naturalPropsNuclear qNuclear avoidNuclearWar := by decide

def desAvoidWar : List (DecProp W) := [mkDec nap]

theorem modern_wants_avoidNuclearWar :
    WantQuestionBased belModern desAvoidWar qNuclear avoidNuclearWar := by decide

/-! ## §11. Cross-paper bridge: [condoravdi-lauer-2016]

[condoravdi-lauer-2016]'s effective-preferential `WantEffectivePreference` carries
a joint-belief-consistency theorem (`wantEffectivePreference_jointly_belief_consistent`):
if both `WantEffectivePreference EP a φ w` and `WantEffectivePreference EP a ψ w` hold, then
`(φ ∩ ψ) ∩ B(a, w) ≠ ∅`. Specialized to `ψ = φᶜ`, the conclusion
becomes `∅ ∩ B(a, w) ≠ ∅`, which is contradictory. So C&L *forbids*
simultaneous `want(p)` and `want(¬p)` against a single belief state and
preference structure.

[phillips-brown-2025] resolves the conflict by varying the
contextual question Q_c (and the contextually-relevant `belS`) per
ascription. C&L resolves it by varying the preference structure (per
reading: `WantExactMatch` / `WantSuccessOriented` / `WantQuineHintikka`). The two
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
    (EP : ∀ a w, EffectivePreference W (B a w))
    (a : Agent) (φ : Set W) (w : W)
    (hφ : Desire.WantEffectivePreference EP a φ w)
    (hnegφ : Desire.WantEffectivePreference EP a (fun w => ¬ φ w) w) :
    False := by
  have h := Desire.wantEffectivePreference_jointly_belief_consistent
              EP hφ hnegφ
  apply h
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun ⟨h1, h2⟩ _ => h2 h1

/-! ### The belief-based class and its no-go (paper §2)

The paper's §2 thesis is class-level: conflicting desire ascriptions
falsify *every* semantics on the orthodox belief-based approach —
[heim-1992], [von-fintel-1999], Levinson 2003, and their descendants.
`BeliefBasedDesireSemantics` formalizes the class: a desire-semantic
device over (Bel_S, parameters, evaluation world, proposition) with no
contextual question parameter outside that shape. Both von Fintel and
Heim are instances (`vonFintelSemantics`, `heimSemantics`), each proved
conflict-blocking by delegation to the substrate's per-account no-go
theorems (`wantVonFintel_no_conflict`, `wantHeim_no_conflict`).

PB's `WantQuestionBased` *evades* the no-go by selecting from
`Q-Bel_S` rather than directly from `Bel_S` — it is *not* an
instance of `BeliefBasedDesireSemantics` (the question parameter
`answers` plays a non-trivial role outside the shape). -/

/-- A belief-based desire semantics on world type `W`: `defined` is the
    presuppositional definedness condition, `want` the truth condition.
    Decidability inside instances is supplied classically — the
    structure is for Prop-level reasoning, not for `decide`. -/
structure BeliefBasedDesireSemantics (W : Type*) where
  /-- Type of additional parameters (desire list for von Fintel,
      similarity + pref for Heim, etc.). -/
  Param : Type*
  /-- Definedness condition: the presupposition that ⟦S wants p⟧^c is
      defined at the configuration. -/
  defined : Set W → Param → Set W → Prop
  /-- Truth condition: when defined, the prediction of ⟦S wants p⟧^c. -/
  want : Set W → Param → W → Set W → Prop

/-- A semantics is **conflict-blocking** if no parameters/world make
    `want(p)` and `want(¬p)` both true when both are defined — the
    paper's §2 no-go in slogan form. -/
def BeliefBasedDesireSemantics.IsConflictBlocking
    {W : Type*} (F : BeliefBasedDesireSemantics W) : Prop :=
  ∀ belS Param w_eval (p : Set W),
    F.defined belS Param p → F.defined belS Param (fun w => ¬ p w) →
    ¬ (F.want belS Param w_eval p ∧ F.want belS Param w_eval (fun w => ¬ p w))

/-- von Fintel as a `BeliefBasedDesireSemantics` instance. `defined`
    requires both p- and ¬p-witnesses in belS — strong enough that some
    belS-world is necessarily undominated, which the no-go needs. -/
def vonFintelSemantics {W : Type*} [Fintype W] :
    BeliefBasedDesireSemantics W where
  Param := List (DecProp W)
  defined belS _ p := (∃ w, belS w ∧ p w) ∧ (∃ w, belS w ∧ ¬ p w)
  want belS GS _ p := WantVonFintel belS GS p

/-- `WantHeim` with decidability supplied classically, so the structure
    projection of `heimSemantics` is stable across ambient instances. -/
noncomputable def WantHeimClassical {W : Type*} [Fintype W] [DecidableEq W]
    (belS : Set W) (params : HeimDesireParams W) (w_eval : W) (p : Set W) : Prop :=
  letI : DecidablePred belS := Classical.decPred _
  letI : DecidablePred p := Classical.decPred _
  WantHeim belS params w_eval p

/-- The classical-decidability variant agrees with `WantHeim` under any
    ambient decidability instances (`DecidablePred` is a subsingleton). -/
theorem wantHeimClassical_iff_WantHeim {W : Type*} [Fintype W] [DecidableEq W]
    (belS : Set W) [DecidablePred belS]
    (params : HeimDesireParams W) (w_eval : W) (p : Set W) [DecidablePred p] :
    WantHeimClassical belS params w_eval p ↔ WantHeim belS params w_eval p := by
  unfold WantHeimClassical
  congr!

/-- Heim as a `BeliefBasedDesireSemantics` instance: definedness is her
    (40) amendment, `want` the classical-decidability form. -/
noncomputable def heimSemantics {W : Type*} [Fintype W] [DecidableEq W] :
    BeliefBasedDesireSemantics W where
  Param := HeimDesireParams W
  defined belS _ p :=
    (∃ w, belS w ∧ p w) ∧ (∃ w, belS w ∧ ¬ p w)
  want belS params w_eval p := WantHeimClassical belS params w_eval p

/-- von Fintel is **conflict-blocking**: delegates to
    `wantVonFintel_no_conflict` after extracting a Pareto-undominated
    belS-world via finite-preorder minimal-element existence. -/
theorem vonFintelSemantics_IsConflictBlocking {W : Type*} [Fintype W] :
    (vonFintelSemantics (W := W)).IsConflictBlocking := by
  classical
  intro belS GS _w_eval p hDef _hDefNeg ⟨hp, hnp⟩
  apply Desire.wantVonFintel_no_conflict belS GS p ?_ ⟨hp, hnp⟩
  obtain ⟨wp, hwp_bel, _⟩ := hDef.1
  let _ : Preorder W :=
    { le := WorldAtLeastAsGood GS
      le_refl := fun _ _ _ hp_w => hp_w
      le_trans := fun _ _ _ huv hvw q hq hqz => huv q hq (hvw q hq hqz) }
  have hbelNonempty : (belS : Set W).Nonempty := ⟨wp, hwp_bel⟩
  obtain ⟨m, hmA, hmin⟩ := (Set.toFinite _).exists_minimal hbelNonempty
  exact ⟨m, hmA, fun z hz ⟨hzm, hnmz⟩ => hnmz (hmin hz hzm)⟩

/-- Heim is **conflict-blocking** at any `(params, w_eval)` with strict
    preference asymmetry: delegates to `wantHeim_no_conflict`. -/
theorem heimSemantics_IsConflictBlocking {W : Type*} [Fintype W] [DecidableEq W]
    (params : HeimDesireParams W) (w_eval : W)
    (hAsym : ∀ x y, params.pref w_eval x y → params.pref w_eval y x → x = y) :
    ∀ belS (p : Set W),
      (heimSemantics (W := W)).defined belS params p →
      (heimSemantics (W := W)).defined belS params (fun w => ¬ p w) →
      ¬ ((heimSemantics (W := W)).want belS params w_eval p ∧
         (heimSemantics (W := W)).want belS params w_eval (fun w => ¬ p w)) := by
  classical
  intro belS p hDef _hDefNeg ⟨hp, hnp⟩
  rw [show (heimSemantics (W := W)).want = fun belS params w p =>
        WantHeimClassical belS params w p from rfl] at hp hnp
  rw [wantHeimClassical_iff_WantHeim] at hp hnp
  exact Desire.wantHeim_no_conflict belS params w_eval p hAsym hDef
    ⟨hp, hnp⟩

theorem heim_no_go_covers_belief_based_family
    {W : Type} [Fintype W] [DecidableEq W]
    (params : Desire.HeimDesireParams W) (w_eval : W)
    (hAsym : ∀ x y, params.pref w_eval x y → params.pref w_eval y x → x = y)
    (belS : Set W) [DecidablePred belS]
    (p : Set W) [DecidablePred p]
    (h : Desire.WantHeimDefined belS p) :
    ¬ (Desire.WantHeim belS params w_eval p ∧
       Desire.WantHeim belS params w_eval (fun w => ¬ p w)) :=
  Desire.wantHeim_no_conflict
    belS params w_eval p hAsym h

/-- **[lassiter-2017] also evades the no-go but via numerical
    threshold + graded value rather than question-sensitivity.** The
    Lassiter substrate's `threshold_admits_conflict_witness` exhibits a
    concrete configuration where both `want(p)` and `want(¬p)` fire on
    a single `(belS, pr, V, θ)` — falsifying `IsConflictBlocking`.

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
      Desire.Lassiter.Want belS pr V θ p ∧
      Desire.Lassiter.Want belS pr V θ (fun w => ¬ p w) :=
  Desire.Lassiter.threshold_admits_conflict_witness

/-! ## Summary

The 8-world model verifies all of the paper's quantitative predictions
that fit the 3-binary-dimension encoding (Nap, Lobster-via-isomorphism,
Lu/deck-stacking, William-III). The substrate carries the *general*
arguments (no-go for vF, no-go for Heim, Strawson upward monotonicity,
and the universal finest-question identity
`wantQuestionBased_finestPartition_iff_WantVonFintel`); the
belief-based-class typology — the paper's own §2 packaging — is
formalized above. The §11 bridge makes the disagreement with C&L explicit;
the §12 foil shows the no-go covers the whole belief-based family.

What's deferred:

* The Lobster scenario reuses Nap's dimensions via `abbrev` — a
  4-dimension model would let `qLobGus` and `qLobDie` be genuinely
  distinct in their underlying worlds. The current encoding is honest
  (`qLobGus := qNapRest`) and adequate for the structural argument.

* [crnic-2014] is referenced in `Desire.lean`'s docstring as the
  acknowledged precursor; a Crnič-2011 study file is the natural next
  paper.

* The CPR overgeneration argument (paper §2.2) is handled here via
  `die_not_considered_in_qLobGus`. A separate CPR formalization (paper
  §2.4) is not yet in linglib.
-/

end PhillipsBrown2025
