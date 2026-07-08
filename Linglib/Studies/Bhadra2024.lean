import Linglib.Morphology.RootTypology
import Linglib.Semantics.ArgumentStructure.Affectedness
import Linglib.Semantics.ArgumentStructure.Thematic.Defs
import Linglib.Semantics.Events.Basic
import Linglib.Fragments.English.Predicates.Verbal
import Mathlib.Data.ENat.Basic

/-!
# Bhadra 2024: Verb roots encode outcomes

[bhadra-2024]

The reversative prefix *un-* and the restitutive prefix *re-* are result-state
modifiers sensitive to the **outcome set** a verb root lexically encodes
([bhadra-2024], §5). Every verb root carries a set of outcomes `O` — the
states its object can be in after the action — and a contextual set of
thresholds `T` of states it can start from.

The two affixes split along two independent axes:

* ***un-*** is driven by **outcome-set cardinality** (eq. 66): it needs
  `O.Nontrivial` (`|O| > 1`, the *potential-for-change* / PFC profile) plus
  inverse equivalence between the base result and the un-event's boundaries.
  Singleton or empty outcome sets block it.
* ***re-*** is *not* cardinality-sensitive (eq. 72); it needs result
  equivalence with a prior event (eq. 68 i) and that the object can re-enter a
  threshold state (eq. 68 ii). Consumption/destruction and impingement (IE)
  verbs block it ((25), (48)) because their outcome leaves the object outside
  every threshold.

One idealization: each `VerbOutcomes` fixes its outcome and threshold sets once
per root, freezing the [verb + object] unit that Bhadra's Level-2 story varies
with the object (✓*rebreak a limb* vs. #*rebreak a sewer*, her (73)).

## Main definitions

* `VerbOutcomes` — a root's base predicate (`EventRel`), outcome set, threshold set
* `resState` / `preState` — state at the right / left event boundary (eqs. 64–65)
* `unSem` / `reSem` — the *un-* and *re-* denotations (eqs. 66, 68)
* `LevinClass.outcomeCard` — the single Levin-class → outcome-cardinality bridge
  (`ℕ∞`; eq. 62 hierarchy multi > singleton > empty)

## Main results

* `subsingleton_blocks_un` — `¬ O.Nontrivial → ¬ unSem` (eq. 67), with the
  singleton and empty corollaries
* `*_un` / `*_re` per-verb predictions, derived compositionally and bridged from
  Fragment entries via `Verb.levinClass`

## References

* [bhadra-2024] (the Verb-Root-Outcomes framework)
* [beavers-2011] (the affectedness hierarchy and the PFC class)
* [beavers-2010], [dowty-1991] (ground the `profileToDegree` projection only)
* [levin-1993] (verb classes the outcome bridge keys on)
-/

namespace Bhadra2024

open Semantics.Lexical
open Semantics.Lexical.EventStructure
open ArgumentStructure (EventRel)
open ArgumentStructure
open ArgumentStructure.Affectedness

/-! ### The compositional verb root (eqs. 53–60)

A verb root lexically encodes its base predicate `P` (the `⟨v,⟨e,t⟩⟩` meaning the
affixes modify), its outcome set `O` (states at the right boundary, eq. 56a), and
its threshold set `T` (left boundary, eq. 56b) — the substrate `VerbOutcomes`
(`Semantics/Verb/Root/Outcomes.lean`), with `resState`/`preState` the eq. 64–65 boundary
operators and `StateFunction` the paper's *state* `k : t ↦ l(x)` (eq. 53).
`APPLIES` (eq. 59) is folded into `verb`. -/

variable {Entity State Time : Type*} [LinearOrder Time]

/-! ### *un-* and *re-* as result-state modifiers (eqs. 66, 68) -/

/-- Reversative *un-* (eq. 66). `unSem k vro e x` holds iff there is a prior
    base event `e'` whose result is the un-event's start state
    (`res(e') = pre(e)`), the outcome set is multi-membered (`O.Nontrivial`,
    `|O| > 1`), and the un-event undoes it (`res(e) = pre(e')`). The vacuous
    `∃Q. Q(e)(x)` — which sits in the *assertion* of eq. 66, not its
    presupposition — is dropped. -/
def unSem (k : StateFunction Entity State Time) (vro : VerbOutcomes Entity State Time)
    (e : Event Time) (x : Entity) : Prop :=
  ∃ e' : Event Time,
    vro.verb e' x ∧
    (Event.τ e').precedes (Event.τ e) ∧
    resState k e' x = preState k e x ∧
    vro.outcomes.Nontrivial ∧
    resState k e x = preState k e' x

/-- Restitutive *re-* (eq. 68). `reSem k vro e x` holds iff there is a prior
    base event `e'` with the same result (`res(e) = res(e')`, eq. 68 i), the
    re-event starts from a valid threshold state (`pre(e) ∈ T`), and the base
    predicate holds of the re-event (`P(e)(x)`). The threshold clause is a
    rational reconstruction — not a transcription — of eq. 68 ii's negative
    existential (no threshold state may render the re-action undefined; the
    cyclic-*re-* condition, eq. 72). Unlike `unSem`, this places no cardinality
    demand on `O`. -/
def reSem (k : StateFunction Entity State Time) (vro : VerbOutcomes Entity State Time)
    (e : Event Time) (x : Entity) : Prop :=
  (∃ e' : Event Time,
    vro.verb e' x ∧
    (Event.τ e').precedes (Event.τ e) ∧
    resState k e x = resState k e' x) ∧
  preState k e x ∈ vro.thresholds ∧
  vro.verb e x

/-! ### Cardinality blocks *un-* (eq. 67) -/

/-- The core asymmetry: a verb whose outcome set is *not* multi-membered cannot
    host *un-* ([bhadra-2024], eq. 67). The multi-membered presupposition of
    `unSem` fails. -/
theorem subsingleton_blocks_un (k : StateFunction Entity State Time)
    (vro : VerbOutcomes Entity State Time) (h : ¬ vro.outcomes.Nontrivial)
    (e : Event Time) (x : Entity) :
    ¬ unSem k vro e x := by
  rintro ⟨_, _, _, _, hnt, _⟩
  exact h hnt

/-- Singleton outcome sets (IE and COS verbs) block *un-*. -/
theorem singleton_blocks_un (k : StateFunction Entity State Time)
    (vro : VerbOutcomes Entity State Time) (s : State) (hs : vro.outcomes = {s})
    (e : Event Time) (x : Entity) :
    ¬ unSem k vro e x :=
  subsingleton_blocks_un k vro
    (by rw [Set.not_nontrivial_iff, hs]; exact Set.subsingleton_singleton) e x

/-- Empty outcome sets (no-change-specified verbs) block *un-*. -/
theorem empty_blocks_un (k : StateFunction Entity State Time)
    (vro : VerbOutcomes Entity State Time) (hs : vro.outcomes = ∅)
    (e : Event Time) (x : Entity) :
    ¬ unSem k vro e x :=
  subsingleton_blocks_un k vro
    (by rw [Set.not_nontrivial_iff, hs]; exact Set.subsingleton_empty) e x

/-- *un-*'s cardinality demand (eq. 67, `|O| > 1`) is exactly the substrate
    `OutcomeCardinality.multi` tier (eq. 62, `empty < singleton < multi`): hosting
    *un-* forces the verb root's outcome set into the top tier. Wires Bhadra's
    outcome cardinality to the `OutcomeCardinality` substrate. -/
theorem un_requires_multi_cardinality (k : StateFunction Entity State Time)
    (vro : VerbOutcomes Entity State Time) (e : Event Time) (x : Entity)
    (h : unSem k vro e x) : vro.cardinality = Verb.OutcomeCardinality.multi := by
  obtain ⟨_, _, _, _, hnt, _⟩ := h
  exact Verb.OutcomeCardinality.ofSet_eq_multi hnt

/-! ### The Levin-class → outcome-cardinality bridge (eq. 62)

The single per-class datum: the cardinality of a verb root's lexical outcome
set, valued in `ℕ∞`. PFC roots have open-ended outcome sets (eq. 60:
`O = {k | k = APPLIES(e)(x)}`, unbounded), idealized as `⊤`; IE and COS roots
have a single lexically-specified result (eqs. 61a–g); no-change roots have
none (eq. 61h). Only `1 < ·` is load-bearing (it drives *un-*); the three tiers
realize the eq. 62 hierarchy `multi > singleton > empty`. -/

/-- Outcome-set cardinality of a Levin verb class ([bhadra-2024], eq. 62). -/
def LevinClass.outcomeCard : LevinClass → ℕ∞
  -- PFC roots: her §2.4.1 exemplar list includes *coil*, *bend*, and *veil*
  -- (concealment), and *undress*/*redress* are fine (dressing verbs).
  | .coil | .bend | .conceal | .dress => ⊤
  -- IE roots (§2.4.2): a singleton impingement result (eq. 61g).
  | .hit | .swat | .wipe | .touch => 1
  -- COS roots (eqs. 61a–f): a single lexically-specified result. Caveat:
  -- *freeze* (Levin 45.4) is her (1b) ✓*unfreeze*, so the singleton tier
  -- over-blocks that member — 45.4 is heterogeneous under her taxonomy.
  | .break_ | .destroy | .cooking | .otherCoS | .entitySpecificCoS
  | .calibratableCoS | .color | .imageCreation | .build | .create | .grow
  | .knead | .turn | .cut | .carve | .eat | .devour | .murder | .poison
  | .mix | .amalgamate | .separate | .split | .clear => 1
  -- *load* is a degree achievement with a singleton outcome set (eq. 70).
  -- Caveat: Levin 9.7 also holds *pack*, on her un-✓ list ((12d) *unpack*) —
  -- the class is heterogeneous under her taxonomy.
  | .sprayLoad => 1
  -- Movement roots: singleton {displaced} sets (eq. 61c); their blocked
  -- un-/re- ((12c)) comes from cardinality/threshold failure, not from
  -- empty outcome sets.
  | .pushPull | .remove | .throw | .put => 1
  | _ => 0

/-- The eq. 62 hierarchy, witnessed on a representative of each tier:
    multi-membered (PFC) > singleton (IE, COS) > empty (no change). -/
theorem outcome_hierarchy :
    LevinClass.outcomeCard .bend = ⊤ ∧
    LevinClass.outcomeCard .hit = 1 ∧
    LevinClass.outcomeCard .break_ = 1 ∧
    LevinClass.outcomeCard .mannerOfMotion = 0 ∧
    (0 : ℕ∞) < 1 ∧ (1 : ℕ∞) < ⊤ := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> simp

/-- *un-* prediction is **derived** from cardinality: PFC classes have
    `1 < outcomeCard`, every other class does not. -/
theorem bend_predicts_un : 1 < LevinClass.outcomeCard .bend := by
  simp [LevinClass.outcomeCard]

theorem coil_predicts_un : 1 < LevinClass.outcomeCard .coil := by
  simp [LevinClass.outcomeCard]

theorem break_blocks_un_class : ¬ (1 < LevinClass.outcomeCard .break_) := by
  simp [LevinClass.outcomeCard]

theorem hit_blocks_un_class : ¬ (1 < LevinClass.outcomeCard .hit) := by
  simp [LevinClass.outcomeCard]

theorem destroy_blocks_un_class : ¬ (1 < LevinClass.outcomeCard .destroy) := by
  simp [LevinClass.outcomeCard]

theorem color_blocks_un_class : ¬ (1 < LevinClass.outcomeCard .color) := by
  simp [LevinClass.outcomeCard]

theorem mannerOfMotion_blocks_un_class :
    ¬ (1 < LevinClass.outcomeCard .mannerOfMotion) := by
  simp [LevinClass.outcomeCard]

/-! ### Worked examples (eqs. 60–61, 66–71) -/

section Examples

/-- Event from `t = 0` to `t = 5` (the base event). -/
private def ev₁ : Event ℤ where
  runtime := ⟨⟨0, 5⟩, by omega⟩
  sort := .dynamic

/-- Event from `t = 10` to `t = 15` (the reversal / restitution event). -/
private def ev₂ : Event ℤ where
  runtime := ⟨⟨10, 15⟩, by omega⟩
  sort := .dynamic

/-- Event from `t = 20` to `t = 25` (a third, re- event). -/
private def ev₃ : Event ℤ where
  runtime := ⟨⟨20, 25⟩, by omega⟩
  sort := .dynamic

private theorem ev₁_precedes_ev₂ : (Event.τ ev₁).precedes (Event.τ ev₂) := by
  show (5 : ℤ) < 10; omega

private theorem ev₁_precedes_ev₃ : (Event.τ ev₁).precedes (Event.τ ev₃) := by
  show (5 : ℤ) < 20; omega

/-! #### fold: a PFC root (multi-membered outcomes), *un-* and *re-* both attach -/

/-- States of a parchment under folding (eq. 54: a multi-membered outcome set). -/
inductive ParchmentState where
  | flat | slightlyCreased | folded | tightlyFolded
  deriving DecidableEq, Repr

/-- *fold* (Levin `bend` class): a multi-membered outcome set. -/
def foldVRO : VerbOutcomes Unit ParchmentState ℤ where
  verb := fun _ _ => True
  outcomes := {.slightlyCreased, .folded, .tightlyFolded}
  thresholds := {.flat, .slightlyCreased}

theorem fold_outcomes_multi : foldVRO.outcomes.Nontrivial :=
  ⟨.slightlyCreased, by simp [foldVRO], .folded, by simp [foldVRO], by decide⟩

/-- State of the parchment for a fold-then-unfold scenario:
    flat before `ev₁`, folded between the events, flat after `ev₂`. -/
private def foldUnfoldState : StateFunction Unit ParchmentState ℤ := fun t _ =>
  if t ≤ 0 then .flat else if t ≤ 10 then .folded else .flat

/-- **Positive: *un-* IS satisfiable for fold** (eq. 66 worked example,
    "Veena unfolded the parchment"). -/
theorem fold_un_satisfiable :
    unSem foldUnfoldState foldVRO ev₂ () :=
  ⟨ev₁, trivial, ev₁_precedes_ev₂, rfl, fold_outcomes_multi, rfl⟩

/-- State for a fold-then-refold scenario: the parchment comes loose (flat)
    between the events, so the refold starts from the `flat` threshold and
    restores the `folded` result. -/
private def foldRefoldState : StateFunction Unit ParchmentState ℤ := fun t _ =>
  if t ≤ 0 then .flat else if t ≤ 5 then .folded
  else if t ≤ 20 then .flat else .folded

/-- **Positive: *re-* IS satisfiable for fold** — the multi-membered (PFC)
    tier's *re-* cell, completing the Fig. 5 distribution: *re-* attaches
    across the multi and singleton tiers (eq. 72), where *un-* takes the multi
    tier only. Reuses the root of her worked *unfold* derivation (74)–(75). -/
theorem fold_re_satisfiable :
    reSem foldRefoldState foldVRO ev₃ () :=
  ⟨⟨ev₁, trivial, ev₁_precedes_ev₃, rfl⟩,
   by simp [foldVRO, preState, foldRefoldState, ev₃, Event.τ], trivial⟩

/-! #### break: a COS root (singleton outcome), *un-* blocked, *re-* allowed -/

inductive LimbState where
  | intact | broken
  deriving DecidableEq, Repr

/-- *break* (Levin `break_` class): a single lexically-specified result
    (eq. 61a). -/
def breakVRO : VerbOutcomes Unit LimbState ℤ where
  verb := fun _ _ => True
  outcomes := {.broken}
  thresholds := {.intact}

/-- *unbreak* is blocked: the singleton outcome set fails eq. 67. -/
theorem break_blocks_un (k : StateFunction Unit LimbState ℤ) (e : Event ℤ) :
    ¬ unSem k breakVRO e () :=
  singleton_blocks_un k breakVRO .broken rfl e ()

/-- State for a break / repair / rebreak scenario: the limb is repaired
    (intact) between the events, so the rebreak can start from a threshold. -/
private def breakRebreakState : StateFunction Unit LimbState ℤ := fun t _ =>
  if t ≤ 0 then .intact else if t ≤ 5 then .broken
  else if t ≤ 20 then .intact else .broken

/-- **Positive: *re-* IS satisfiable for break** (rebreak a limb): result
    equivalence holds and the re-event starts from the `intact` threshold. -/
theorem break_re_satisfiable :
    reSem breakRebreakState breakVRO ev₃ () :=
  ⟨⟨ev₁, trivial, ev₁_precedes_ev₃, rfl⟩,
   by simp [breakVRO, preState, breakRebreakState, ev₃, Event.τ], trivial⟩

/-! #### hit: an IE root (singleton outcome), *un-* and *re-* both blocked -/

inductive SurfaceState where
  | unaltered | surfaceAltered
  deriving DecidableEq, Repr

/-- *hit* (Levin `hit` class): impingement, a single surface-alteration result
    (eq. 61g). -/
def hitVRO : VerbOutcomes Unit SurfaceState ℤ where
  verb := fun _ _ => True
  outcomes := {.surfaceAltered}
  thresholds := {.unaltered}

theorem hit_blocks_un (k : StateFunction Unit SurfaceState ℤ) (e : Event ℤ) :
    ¬ unSem k hitVRO e () :=
  singleton_blocks_un k hitVRO .surfaceAltered rfl e ()

/-- State for an attempted *rehit*: impingement is irreversible (§2.4.2) — the
    surface stays altered, so the object never re-enters the `unaltered`
    threshold. -/
private def hitState : StateFunction Unit SurfaceState ℤ := fun t _ =>
  if t ≤ 0 then .unaltered else .surfaceAltered

/-- **Negative: *re-* is blocked for hit** — IE verbs block *re-* as well as
    *un-* ((25), (48)): the impingement outcome never re-enters the pre-state
    (threshold) set, so the cyclic-*re-* condition (eq. 68 ii) fails. -/
theorem hit_re_blocked : ¬ reSem hitState hitVRO ev₃ () := by
  rintro ⟨_, hthresh, _⟩
  simp [hitVRO, preState, hitState, ev₃, Event.τ] at hthresh

/-! #### load vs shatter: the *re-* minimal pair (eqs. 69–71)

Both are singleton-outcome (so both block *un-*); they differ on *re-* purely
through the threshold condition (eq. 68 ii). After loading, the truck can be
loaded again (it re-enters a threshold); after shattering, the mirror cannot. -/

inductive TruckState where
  | empty | partlyLoaded | full
  deriving DecidableEq, Repr

/-- *load* (degree achievement, eq. 70): a single contextually-salient result;
    the object stays loadable. -/
def loadVRO : VerbOutcomes Unit TruckState ℤ where
  verb := fun _ _ => True
  outcomes := {.full}
  thresholds := {.empty, .partlyLoaded}

/-- State for *reload*: the truck is partly unloaded between the events, so the
    reload starts from the `partlyLoaded` threshold. -/
private def loadReloadState : StateFunction Unit TruckState ℤ := fun t _ =>
  if t ≤ 0 then .empty else if t ≤ 5 then .full
  else if t ≤ 20 then .partlyLoaded else .full

/-- **Positive: *re-* IS satisfiable for load** (eq. 69a "reloaded the truck"). -/
theorem load_re_satisfiable :
    reSem loadReloadState loadVRO ev₃ () :=
  ⟨⟨ev₁, trivial, ev₁_precedes_ev₃, rfl⟩,
   by simp [loadVRO, preState, loadReloadState, ev₃, Event.τ], trivial⟩

inductive MirrorState where
  | intact | shattered
  deriving DecidableEq, Repr

/-- *shatter* (eq. 71): a single result that leaves the object outside every
    threshold — it cannot be shattered again. -/
def shatterVRO : VerbOutcomes Unit MirrorState ℤ where
  verb := fun _ _ => True
  outcomes := {.shattered}
  thresholds := {.intact}

/-- State for an attempted *reshatter*: the mirror stays shattered, so it never
    re-enters the `intact` threshold. -/
private def shatterState : StateFunction Unit MirrorState ℤ := fun t _ =>
  if t ≤ 0 then .intact else .shattered

/-- **Negative: *re-* is blocked for shatter** (eq. 69b "#reshattered the
    mirror"): the cyclic-*re-* threshold condition (eq. 68 ii) fails — the
    shattered mirror is never in the `intact` threshold the re-event needs. -/
theorem shatter_re_blocked : ¬ reSem shatterState shatterVRO ev₃ () := by
  rintro ⟨_, hthresh, _⟩
  simp [shatterVRO, preState, shatterState, ev₃, Event.τ] at hthresh

end Examples

/-! ### End-to-end: Fragment entry → Levin class → prediction

The Fragment verb's `levinClass` drives the outcome cardinality, which drives
the *un-* prediction. -/

open English.Predicates.Verbal in
/-- *kick* (Levin 18.1 `hit`) → singleton outcomes → *un-* blocked. -/
theorem kick_un_blocked :
    kick.toVerb.levinClass = some .hit ∧
    ¬ (1 < LevinClass.outcomeCard .hit) :=
  ⟨rfl, hit_blocks_un_class⟩

/-- *bend* (Levin 45.2) → multi-membered outcomes → *un-* predicted. -/
theorem bend_un_predicted :
    English.Predicates.Verbal.bend.toVerb.levinClass = some .bend ∧
    1 < LevinClass.outcomeCard .bend :=
  ⟨rfl, bend_predicts_un⟩

open English.Predicates.Verbal in
/-- *break* (Levin 45.1) → singleton outcomes → *un-* blocked. -/
theorem break_un_blocked :
    break_.toVerb.levinClass = some .break_ ∧
    ¬ (1 < LevinClass.outcomeCard .break_) :=
  ⟨rfl, break_blocks_un_class⟩

/-! ### Bridges to the substrate

The outcome-cardinality classification is finer than the change-of-state label
([bhadra-2024]'s central move): `bend` is CoS per [levin-1993] yet has a
multi-membered (PFC) outcome set. -/

/-- [bhadra-2024] reclassifies `bend` from a flat change-of-state verb to a
    potential-for-change root: CoS per [levin-1993]'s meaning components, but
    multi-membered (and hence *un-*-compatible) by outcome cardinality. -/
theorem bend_reclassification :
    (LevinClass.meaningComponents .bend).changeOfState = true ∧
    LevinClass.outcomeCard .bend = ⊤ ∧
    1 < LevinClass.outcomeCard .bend :=
  ⟨rfl, rfl, bend_predicts_un⟩

/-- The outcome-cardinality classification is orthogonal to event-template
    result states: `bend` and `coil` share the PFC profile but differ on
    whether their template carries a result state. -/
theorem outcomeCard_orthogonal_to_hasResultState :
    (LevinClass.eventTemplate .bend).HasResultState ∧
    ¬ (LevinClass.eventTemplate .coil).HasResultState ∧
    LevinClass.outcomeCard .bend = ⊤ ∧
    LevinClass.outcomeCard .coil = ⊤ := by
  refine ⟨?_, ?_, rfl, rfl⟩ <;> decide

/-- Affectedness bridge ([bhadra-2024] §2.4.2, §6.1): the affectedness
    projection cannot separate PFC roots from IE roots — the PFC object
    profile (causally affected, no entailed change) and *kick*'s object
    profile both land on Beavers's potential-for-change degree, whose
    exemplars include surface-contact *hit*/*kick*. Bhadra carves the IE
    class (*kick* is named in her (25)) out of exactly that cell (§2.4.2),
    and her §6.1 point is that the split needs outcome-set structure a bare
    latent-scale existential cannot see: outcome cardinality separates the
    two (`⊤` vs `1`) where the affectedness degree does not. -/
theorem affectedness_bridge :
    profileToDegree { causallyAffected := true, stationary := true }
      = profileToDegree Features.LevinClassProfiles.contactObject ∧
    1 < LevinClass.outcomeCard .bend ∧
    ¬ (1 < LevinClass.outcomeCard .hit) :=
  ⟨rfl, bend_predicts_un, hit_blocks_un_class⟩

/-- RootTypology bridge: result roots entail change and lack the restitutive
    *again* reading; property-concept roots are the reverse. -/
theorem roottype_bridge :
    RootType.entailsChange .result = true ∧
    RootType.allowsRestitutiveAgain .result = false ∧
    RootType.entailsChange .propertyConcept = false ∧
    RootType.allowsRestitutiveAgain .propertyConcept = true :=
  ⟨rfl, rfl, rfl, rfl⟩

end Bhadra2024
