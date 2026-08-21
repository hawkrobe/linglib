import Linglib.Semantics.Attitudes.Desire.QuestionBased
import Linglib.Semantics.Attitudes.Desire.Conditional
import Linglib.Semantics.Attitudes.Desire.Preferential
import Linglib.Semantics.Attitudes.Desire.ExpectedValue
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

The substrate is `Semantics/Attitudes/Desire/`. All theorems
here either compute by `decide` over an 8-world model (3 binary
dimensions: `nap × rested × pass` = `lobster × gustatory × ¬die`) or
delegate to the substrate's general theorems
(`BestWorlds.Want.not_compl`,
`toPartialProp_strawsonEntails`, …).

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

open Desire Desire.QuestionBased

/-! ## §1. Eight-world model

3 binary dimensions: `d₁ × d₂ × d₃`. For Nap: `d₁ = nap`, `d₂ = rested`,
`d₃ = pass`. For Lobster (paper §2.2): `d₁ = lobster`, `d₂ = gustatory`,
`d₃ = ¬die`. The Lobster scenario reuses the Nap dimensions via
`abbrev` — see `lobster := nap`, `gustatory := rested`, `die := fail`
below; the structural isomorphism is documented and not coincidental
(`lobster_true := nap_true` is the same theorem under renaming). -/

inductive W where
  | w0 | w1 | w2 | w3 | w4 | w5 | w6 | w7
  deriving DecidableEq, Fintype, Repr, Inhabited

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
def fail : Set W := passᶜ

instance : DecidablePred (· ∈ nap) := fun w => by
  cases w <;> first | exact isTrue trivial | exact isFalse id
instance : DecidablePred (· ∈ rested) := fun w => by
  cases w <;> first | exact isTrue trivial | exact isFalse id
instance : DecidablePred (· ∈ pass) := fun w => by
  cases w <;> first | exact isTrue trivial | exact isFalse id
instance : DecidablePred (· ∈ fail) := inferInstanceAs (DecidablePred (· ∈ passᶜ))

/-- The natural propositions of the model (basic dimensions), used to
    feed `IsAntiDeckstacking`. AD's quantifier is restricted to this
    test set — see `IsAntiDeckstacking`. -/
def naturalProps : List (Finset W) :=
  [Finset.univ.filter (· ∈ nap), Finset.univ.filter (· ∈ rested), Finset.univ.filter (· ∈ pass)]

/-! ## §3. Nap scenario -/

/-- Q' = partition by nap × rested (4 cells). -/
def qNapRest : List (Finset W) :=
  [Finset.univ.filter (fun w => w ∈ nap ∧ w ∈ rested),
   Finset.univ.filter (fun w => w ∈ nap ∧ w ∉ rested),
   Finset.univ.filter (fun w => w ∉ nap ∧ w ∈ rested),
   Finset.univ.filter (fun w => w ∉ nap ∧ w ∉ rested)]

/-- Q'' = partition by nap × pass (4 cells). -/
def qNapPass : List (Finset W) :=
  [Finset.univ.filter (fun w => w ∈ nap ∧ w ∈ pass),
   Finset.univ.filter (fun w => w ∈ nap ∧ w ∉ pass),
   Finset.univ.filter (fun w => w ∉ nap ∧ w ∈ pass),
   Finset.univ.filter (fun w => w ∉ nap ∧ w ∉ pass)]

/-- Beliefs for Nap: nap ↔ rested. Bel = {w0, w1, w6, w7}. -/
def belNapRest : Set W := {w | if w ∈ nap then w ∈ rested else w ∉ rested}
instance : DecidablePred (· ∈ belNapRest) :=
  fun w => inferInstanceAs (Decidable (if w ∈ nap then w ∈ rested else w ∉ rested))

/-- Beliefs for Not-nap: pass ↔ ¬nap. Bel = {w1, w3, w4, w6}. -/
def belNapPass : Set W := {w | if w ∈ nap then w ∉ pass else w ∈ pass}
instance : DecidablePred (· ∈ belNapPass) :=
  fun w => inferInstanceAs (Decidable (if w ∈ nap then w ∉ pass else w ∈ pass))

def desRest : List (Finset W) := [Finset.univ.filter (· ∈ rested)]
def desPass : List (Finset W) := [Finset.univ.filter (· ∈ pass)]

/-- **Nap is true** relative to Q' with beliefs nap↔rested, desires [rested]. -/
theorem nap_true : Want desRest qNapRest belNapRest nap := by decide +kernel

/-- **Not-nap is true** relative to Q'' with beliefs pass↔¬nap, desires [pass]. -/
theorem not_nap_true :
    Want desPass qNapPass belNapPass napᶜ := by decide +kernel

/-- Fail is NOT considered relative to Q'. -/
theorem fail_not_considered : ¬ IsConsidered qNapRest fail := by decide +kernel

/-- Fail is also not predicted true. -/
theorem fail_not_true :
    ¬ Want desRest qNapRest belNapRest fail := by decide +kernel

/-- Q' is diverse w.r.t. nap. -/
theorem nap_diverse : IsDiverse qNapRest nap := by decide +kernel

/-! ## §4. Lobster scenario (paper §2.2)

The Lobster scenario reuses the Nap dimensions via `abbrev`:
`lobster := nap`, `gustatory := rested`, `die := fail`. The two paper
arguments use *different* questions over these dimensions — Q_{c''}
(`qLobGus`) ignores death, Q_{c'''} (`qLobDie`) ignores taste. -/

abbrev lobster : Set W := nap
abbrev gustatory : Set W := rested
abbrev die : Set W := fail

/-- Q_{c''} = partition by lobster × gustatory (= `qNapRest`). -/
abbrev qLobGus : List (Finset W) := qNapRest

/-- Q_{c'''} = partition by lobster × die. -/
def qLobDie : List (Finset W) :=
  [Finset.univ.filter (fun w => w ∈ nap ∧ w ∈ fail),
   Finset.univ.filter (fun w => w ∈ nap ∧ w ∉ fail),
   Finset.univ.filter (fun w => w ∉ nap ∧ w ∈ fail),
   Finset.univ.filter (fun w => w ∉ nap ∧ w ∉ fail)]

/-- Beliefs: die ↔ eat lobster. Bel = {w1, w3, w4, w6}. -/
def belLobDie : Set W := {w | if w ∈ nap then w ∈ fail else w ∉ fail}
instance : DecidablePred (· ∈ belLobDie) :=
  fun w => inferInstanceAs (Decidable (if w ∈ nap then w ∈ fail else w ∉ fail))

def desNotDie : List (Finset W) := [Finset.univ.filter (· ∉ fail)]

/-- **Lobster is true** in c'' (considering taste, ignoring death). -/
theorem lobster_true :
    Want desRest qLobGus belNapRest lobster := nap_true

/-- **Die is undefined in the Lobster context c''** (paper §2.2): in
    `qLobGus = qNapRest`, no cell settles `die`, so the Considering
    presupposition fails. -/
theorem die_not_considered_in_qLobGus :
    ¬ IsConsidered qLobGus die := fail_not_considered

/-- **Not-lobster is true** in c''' (considering death, ignoring taste). -/
theorem not_lobster_true :
    Want desNotDie qLobDie belLobDie napᶜ := by decide +kernel

/-- **Not-die is also true** in c''' (best answer entails both ¬lobster and ¬die). -/
theorem not_die_true :
    Want desNotDie qLobDie belLobDie failᶜ := by decide +kernel

/-! ## §5. Von Fintel comparison and the no-go theorem

The paper's central argument against belief-based semantics: vF cannot
predict both `want p` and `want ¬p` simultaneously. Specialised here
for the Nap example, then derived from the substrate's general
`BestWorlds.Want.not_compl`. -/

theorem vf_nap_true : BestWorlds.Want desRest belNapRest nap := by decide +kernel

theorem vf_not_nap_false :
    ¬ BestWorlds.Want desRest belNapRest napᶜ := by decide +kernel

/-- vF cannot predict both Nap and Not-nap with the same parameter set
    (specific instance). -/
theorem vf_cannot_predict_both :
    ¬(BestWorlds.Want desRest belNapRest nap ∧
      BestWorlds.Want desRest belNapRest napᶜ) := by
  intro ⟨_, h⟩; exact vf_not_nap_false h

/-- vF cannot predict both Nap and Not-nap (general no-go, delegates
    to the substrate). The witness is any belS-world that is
    Pareto-undominated under the desire ordering. -/
theorem vf_no_conflict_nap :
    ¬ (BestWorlds.Want desRest belNapRest nap ∧
       BestWorlds.Want desRest belNapRest napᶜ) :=
  fun ⟨hp, hnp⟩ => hp.not_compl ⟨.w0, by decide⟩ hnp

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
    IsConsidered qNapPass nap := by decide +kernel

theorem fail_considered_in_qNapPass :
    IsConsidered qNapPass fail := by decide +kernel

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

instance : DecidablePred (· ∈ happy) := fun w => by
  cases w <;> first | exact isTrue trivial | exact isFalse id
instance : DecidablePred (· ∈ rain) := fun w => by
  cases w <;> first | exact isTrue trivial | exact isFalse id

/-- Test set of natural propositions for the Lu scenario. -/
def naturalPropsLu : List (Finset W) :=
  [Finset.univ.filter (· ∈ rain), Finset.univ.filter (· ∈ happy)]

/-- Q'''' (deck-stacked): {r, ¬r∧h, ¬r∧¬h}. -/
def qDeckstacked : List (Finset W) :=
  [Finset.univ.filter (· ∈ rain),
   Finset.univ.filter (fun w => w ∉ rain ∧ w ∈ happy),
   Finset.univ.filter (fun w => w ∉ rain ∧ w ∉ happy)]

/-- Lu's beliefs: happy unconditionally. -/
def belLu : Set W := happy
instance : DecidablePred (· ∈ belLu) := inferInstanceAs (DecidablePred (· ∈ happy))

def desHappy : List (Finset W) := [Finset.univ.filter (· ∈ happy)]

/-- `happy` is not considered in the deck-stacked Q'''' (the `rain`
    cell contains both happy and unhappy worlds). -/
theorem happy_not_considered_deckstacked :
    ¬ IsConsidered qDeckstacked happy := by decide +kernel

/-- A `happy`-answer exists in qDeckstacked (the `¬r∧h` cell entails
    `happy`) — the deck is stacked in favor of ¬rain. -/
theorem happy_answer_exists_deckstacked :
    ∃ a ∈ qDeckstacked, ∀ w ∈ a, w ∈ happy := by decide +kernel

/-- Without the constraint, the question-based semantics wrongly
    predicts Not-rain. -/
theorem not_rain_deckstacked_true :
    Want desHappy qDeckstacked belLu rainᶜ := by decide +kernel

/-- Q''''' (level playing field): partition by rain × happy. -/
def qRainHappy : List (Finset W) :=
  [Finset.univ.filter (fun w => w ∈ rain ∧ w ∈ happy),
   Finset.univ.filter (fun w => w ∈ rain ∧ w ∉ happy),
   Finset.univ.filter (fun w => w ∉ rain ∧ w ∈ happy),
   Finset.univ.filter (fun w => w ∉ rain ∧ w ∉ happy)]

theorem happy_considered_fair :
    IsConsidered qRainHappy happy := by decide +kernel

/-- With the fair question, Not-rain is correctly predicted false. -/
theorem not_rain_false_fair :
    ¬ Want desHappy qRainHappy belLu rainᶜ := by decide +kernel

/-- The deck-stacked question fails Anti-deckstacking on test set
    `[r, h]` (`h` is predetermined by the `¬r∧h` cell but not
    considered by Q''''). -/
theorem qDeckstacked_fails_antideckstacking :
    ¬ IsAntiDeckstacking naturalPropsLu qDeckstacked := by decide +kernel

/-- The fair (cross-product) question satisfies Anti-deckstacking —
    every basic proposition is settled by every cell. -/
theorem qRainHappy_satisfies_antideckstacking :
    IsAntiDeckstacking naturalPropsLu qRainHappy := by decide +kernel

/-- Q' (`qNapRest`) satisfies Anti-deckstacking on the natural-prop
    test set `[nap, rested, pass]` — the cross-product over `nap` and
    `rested` settles `nap` and `rested`; no cell entails `pass`, so
    AD's antecedent is vacuous for `pass`. -/
theorem qNapRest_satisfies_antideckstacking :
    IsAntiDeckstacking naturalProps qNapRest := by decide +kernel

/-! ## §8. Finest-question simulation (paper §3.4)

When Q_c is the finest partition (singleton cells = individual worlds),
the question-based semantics reduces to vF. The substrate provides
`finest : List W → List (Finset W)`; here we instantiate it
on the explicit world list of the model. -/

def allWorldsW : List W := [.w0, .w1, .w2, .w3, .w4, .w5, .w6, .w7]

def qFinest : List (Finset W) := finest allWorldsW

/-- The 8-world list `allWorldsW` covers `W`. Hypothesis required by the
    substrate's general `want_finest_iff`. -/
theorem allWorldsW_complete : ∀ w : W, w ∈ allWorldsW := by
  intro w; cases w <;> decide

/-- With the finest question, question-based want = standard vF want
    for `nap`. Derived from the substrate's general
    `want_finest_iff`, not by `decide`. -/
theorem finest_simulates_vf_nap :
    Want desRest qFinest belNapRest nap ↔
    BestWorlds.Want desRest belNapRest nap :=
  want_finest_iff allWorldsW_complete

/-- With the finest question, question-based want = standard vF want
    for `¬nap`. -/
theorem finest_simulates_vf_not_nap :
    Want desRest qFinest belNapRest napᶜ ↔
    BestWorlds.Want desRest belNapRest napᶜ :=
  want_finest_iff allWorldsW_complete

/-- With the finest question, question-based want = standard vF want
    for `¬lobster` in the Lobster context. -/
theorem finest_simulates_vf_not_lobster :
    Want desNotDie qFinest belLobDie napᶜ ↔
    BestWorlds.Want desNotDie belLobDie napᶜ :=
  want_finest_iff allWorldsW_complete

/-! ## §9. Definedness via PartialProp (paper §3.6) -/

theorem nap_defined_in_qNapRest :
    Defined naturalProps qNapRest belNapRest nap := by decide +kernel

theorem fail_not_defined_in_qNapRest :
    ¬ Defined naturalProps qNapRest belNapRest fail := by decide +kernel

theorem nap_prprop_holds :
    (toPartialProp desRest naturalProps qNapRest belNapRest nap).presup .w0 ∧
    (toPartialProp desRest naturalProps qNapRest belNapRest nap).assertion .w0 := by
  refine ⟨?_, ?_⟩ <;> simp only [toPartialProp] <;> decide +kernel

theorem fail_prprop_undefined :
    ¬(toPartialProp desRest naturalProps qNapRest belNapRest fail).presup .w0 := by
  simp only [toPartialProp]; decide +kernel

/-! ## §10. Belief-sensitivity: William III / nuclear war (paper §4.2)

William III wanted to avoid war. Avoiding war entails avoiding nuclear
war. But we cannot conclude William III wanted to avoid nuclear war —
he lacked the conceptual resources to grasp nuclear war.

Mechanism: William's beliefs are NOT sensitive to Q_nuc that
distinguishes nuclear from conventional war. All Q_nuc answers are
compatible with his beliefs (total uncertainty), so `IsBelSensitive`
returns false and `Defined` blocks the inference. A modern person
whose beliefs rule out nuclear war DOES have belief-sensitive context,
so the inference goes through.

Strawson upward monotonicity is the closure principle at issue;
[phillips-brown-2025] §4.2 argues that question-based semantics
must be Strawson-but-not-naively upward monotonic, with definedness
gating the inference. The substrate's
`toPartialProp_strawsonEntails` captures the licit
direction. -/

def avoidWar : Set W := nap
def avoidNuclearWar : Set W := nap ∪ rested

instance : DecidablePred (· ∈ avoidWar) := inferInstanceAs (DecidablePred (· ∈ nap))
instance : DecidablePred (· ∈ avoidNuclearWar) := inferInstanceAs (DecidablePred (· ∈ nap ∪ rested))

def qNuclear : List (Finset W) :=
  [Finset.univ.filter (· ∈ nap),
   Finset.univ.filter (fun w => w ∉ nap ∧ w ∈ rested),
   Finset.univ.filter (fun w => w ∉ nap ∧ w ∉ rested)]

/-- Natural-prop test set for the nuclear-war scenario. The Nap-vs-war
    distinction (`nap`) and the war-of-any-kind distinction
    (`avoidNuclearWar`) are the salient dimensions; `rested` and
    `pass` are not part of this scenario's vocabulary. -/
def naturalPropsNuclear : List (Finset W) :=
  [Finset.univ.filter (· ∈ nap), Finset.univ.filter (· ∈ avoidNuclearWar)]

theorem avoidWar_entails_avoidNuclearWar :
    avoidWar ⊆ avoidNuclearWar := Set.subset_union_left

theorem avoidNuclearWar_considered :
    IsConsidered qNuclear avoidNuclearWar := by decide +kernel

/-- William III: total uncertainty (all worlds compatible). -/
def belWilliam : Set W := Set.univ
instance : DecidablePred (· ∈ belWilliam) := fun _ => isTrue trivial

theorem william_insensitive :
    ¬ IsBelSensitive qNuclear belWilliam := by decide +kernel

theorem avoidNuclearWar_not_defined_william :
    ¬ Defined naturalPropsNuclear qNuclear belWilliam avoidNuclearWar := by decide +kernel

/-- Modern person: beliefs rule out nuclear war (peace ∨ conventional). -/
def belModern : Set W := nap ∪ rested
instance : DecidablePred (· ∈ belModern) := inferInstanceAs (DecidablePred (· ∈ nap ∪ rested))

theorem modern_sensitive :
    IsBelSensitive qNuclear belModern := by decide +kernel

theorem avoidNuclearWar_defined_modern :
    Defined naturalPropsNuclear qNuclear belModern avoidNuclearWar := by decide +kernel

def desAvoidWar : List (Finset W) := [Finset.univ.filter (· ∈ nap)]

theorem modern_wants_avoidNuclearWar :
    Want desAvoidWar qNuclear belModern avoidNuclearWar := by decide +kernel

/-! ## §11. Cross-paper bridge: [condoravdi-lauer-2016]

[condoravdi-lauer-2016]'s exact-match want over an *effective* —
pointwise consistent — preferential background is jointly
belief-consistent (`PreferenceStructure.maxElts_pair_belief_compatible`):
if both `Preferential.Want P a φ w` and `Preferential.Want P a ψ w` hold, then
`(φ ∩ ψ) ∩ B(a, w) ≠ ∅`. Specialized to `ψ = φᶜ`, the conclusion
becomes `∅ ∩ B(a, w) ≠ ∅`, which is contradictory. So C&L *forbids*
simultaneous `want(p)` and `want(¬p)` against a single belief state and
preference structure.

[phillips-brown-2025] resolves the conflict by varying the
contextual question Q_c (and the contextually-relevant `belS`) per
ascription. C&L resolves it by varying the preference structure (per
reading: `Preferential.Want` / `WantSufficient` / `WantNecessary`). The two
resolutions are orthogonal — both can coexist in a unified theory of
desire, but they make non-overlapping claims. -/

/-- C&L's joint-belief-consistency, specialized to `ψ = φᶜ`: no single
    exact-match want over a consistent background can hold of both `φ`
    and `¬φ` simultaneously, since their intersection is empty.

    This is a *paper-level* contrast with PB §3: PB makes both
    `nap_true` and `not_nap_true` work by varying Q_c and `belS`; the
    C&L analysis would need a different background per ascription to
    reproduce the contrast. -/
theorem condoravdiLauer_blocks_simultaneous_pq_and_negpq
    {Agent W : Type} {B : Agent → W → Set W}
    (P : Agent → W → PreferenceStructure W)
    (hC : ∀ a w, (P a w).consistent (B a w))
    (a : Agent) (φ : Set W) (w : W)
    (hφ : Preferential.Want P a φ w) (hnegφ : Preferential.Want P a φᶜ w) :
    False := by
  have h := (P a w).maxElts_pair_belief_compatible (hC a w) hφ hnegφ
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
theorems (`BestWorlds.Want.not_compl`, `Conditional.Want.not_compl`).

PB's `QuestionBased.Want` *evades* the no-go by selecting from
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
    F.defined belS Param p → F.defined belS Param pᶜ →
    ¬ (F.want belS Param w_eval p ∧ F.want belS Param w_eval pᶜ)

/-- von Fintel as a `BeliefBasedDesireSemantics` instance. `defined`
    requires both p- and ¬p-witnesses in belS — strong enough that some
    belS-world is necessarily undominated, which the no-go needs. -/
def vonFintelSemantics {W : Type*} : BeliefBasedDesireSemantics W where
  Param := List (Finset W)
  defined belS _ p := Conditional.Defined belS p
  want belS GS _ p := BestWorlds.Want GS belS p

/-- Heim as a `BeliefBasedDesireSemantics` instance: definedness is her
    (40) amendment. -/
def heimSemantics {W : Type*} : BeliefBasedDesireSemantics W where
  Param := Conditional.Frame W
  defined belS _ p := Conditional.Defined belS p
  want belS F w_eval p := Conditional.Want F belS w_eval p

/-- von Fintel is **conflict-blocking** (`BestWorlds.Want.not_compl`). -/
theorem vonFintelSemantics_IsConflictBlocking {W : Type*} [Finite W] :
    (vonFintelSemantics (W := W)).IsConflictBlocking :=
  fun _ _ _ _ hDef _ ⟨hp, hnp⟩ => hp.not_compl (let ⟨w, hw⟩ := hDef.1; ⟨w, hw.1⟩) hnp

/-- Heim is **conflict-blocking** at any frame and evaluation world with
    antisymmetric desirability (`Conditional.Want.not_compl`). -/
theorem heimSemantics_IsConflictBlocking {W : Type*} [Finite W] (F : Conditional.Frame W)
    (w_eval : W)
    [Std.Antisymm (F.pref w_eval)] :
    ∀ belS (p : Set W),
      (heimSemantics (W := W)).defined belS F p →
      (heimSemantics (W := W)).defined belS F pᶜ →
      ¬ ((heimSemantics (W := W)).want belS F w_eval p ∧
         (heimSemantics (W := W)).want belS F w_eval pᶜ) :=
  fun _ _ hDef _ ⟨hp, hnp⟩ => hp.not_compl hDef hnp

/-- **[lassiter-2017] also evades the no-go but via numerical
    threshold + graded value rather than question-sensitivity.** The
    Lassiter substrate's `exists_want_and_want_compl` exhibits a
    concrete configuration where both `want(p)` and `want(¬p)` fire on
    a single `(belS, pr, V, θ)` — falsifying `IsConflictBlocking`.

    Lassiter and PB are now formalized as *two distinct* non-instances
    of `BeliefBasedDesireSemantics`. PB's escape route: question
    parameter outside the BBS shape. Lassiter's: numerical threshold
    on graded expected value. The cross-paper picture: the typology
    correctly excludes both, and they evade via genuinely different
    mechanisms. -/
theorem lassiter_evades_no_go_via_grading :
    ∃ (W : Type) (_ : Fintype W) (pr V : W → ℚ) (θ : ℚ) (bel p : Set W)
      (_ : DecidablePred (· ∈ bel)) (_ : DecidablePred (· ∈ p)),
      ExpectedValue.Want pr V θ bel p ∧ ExpectedValue.Want pr V θ bel pᶜ :=
  ExpectedValue.exists_want_and_want_compl

/-! ## Summary

The 8-world model verifies all of the paper's quantitative predictions
that fit the 3-binary-dimension encoding (Nap, Lobster-via-isomorphism,
Lu/deck-stacking, William-III). The substrate carries the *general*
arguments (no-go for vF, no-go for Heim, Strawson upward monotonicity,
and the universal finest-question identity
`want_finest_iff`); the
belief-based-class typology — the paper's own §2 packaging — is
formalized above. The §11 bridge makes the disagreement with C&L explicit;
`heimSemantics_IsConflictBlocking` shows the no-go covers Heim as well.

What's deferred:

* The Lobster scenario reuses Nap's dimensions via `abbrev` — a
  4-dimension model would let `qLobGus` and `qLobDie` be genuinely
  distinct in their underlying worlds. The current encoding is honest
  (`qLobGus := qNapRest`) and adequate for the structural argument.

* [crnic-2014] is the acknowledged precursor of the question-based
  semantics; a Crnič-2011 study file is the natural next paper.

* The CPR overgeneration argument (paper §2.2) is handled here via
  `die_not_considered_in_qLobGus`. A separate CPR formalization (paper
  §2.4) is not yet in linglib.
-/

end PhillipsBrown2025
