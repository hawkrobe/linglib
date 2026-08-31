import Mathlib.Data.Set.Subsingleton
import Linglib.Semantics.ArgumentStructure.Affectedness
import Linglib.Semantics.ArgumentStructure.EventStructure
import Linglib.Semantics.ArgumentStructure.Thematic.Defs
import Linglib.Semantics.Events.Basic

/-!
# Bhadra 2024: verb roots encode outcomes

This file formalizes Bhadra's Verb-Root-Outcomes account of the reversative prefix *un-*
and the restitutive prefix *re-*. Every dynamic transitive root lexically carries a set of
outcomes — the states its object can be in at the right boundary of the event — while a
contextual set of thresholds collects the states an object can be in at the left boundary.
Potential-for-change roots (*fold*, *wrap*, *coil*) have multi-membered outcome sets;
change-of-state and impingement-effecting roots (*break*, *shatter*, *hit*) have a single
lexically specified outcome; roots unspecified for change have none. Both prefixes are
result-state modifiers: *un-* presupposes a prior base event whose result the object is
still in and a multi-membered outcome set, and asserts that the object returns to the base
event's initial state; *re-* presupposes a prior base event with the same result and demands
that the base action not leave the object in a state from which that result cannot be
restored. Cardinality thus governs *un-* alone, and threshold structure governs *re-*, so
the two prefixes overlap exactly on the potential-for-change class.

## Main definitions

* `OutcomeCardinality`, `OutcomeClass`, `OutcomeClass.tier`: the three-tier hierarchy of
  outcome sets and the paper's classes of dynamic transitive roots with their tiers.
* `StateFunction`, `resState`, `preState`: an object's state over time and its state at the
  right and left boundaries of an event.
* `VerbOutcomes`: a root's base predicate with its outcome and threshold sets.
* `unSem`, `reSem`: the two prefixes as result-state modifiers.

## Main results

* `tier_eq_multi_iff`: the potential-for-change class is the only multi-membered tier.
* `subsingleton_blocks_un`, `un_requires_multi`: a root without a multi-membered outcome
  set cannot host *un-*, and hosting it forces the top tier.
* `not_reSem_of_outcome_not_threshold`: a base action whose result is never an admissible
  start state blocks *re-*.
* The worked roots — *fold*, *break* (a limb versus a sewer), *hit*, *load*, *shatter* —
  instantiate the distribution: *un-* on the multi-membered tier only; *re-* across tiers
  wherever the result state can be restored.
* `affectedness_conflates_pfc_ie`: the affectedness hierarchy places potential-for-change
  and impingement objects on the same degree, where outcome structure separates them.

Each `VerbOutcomes` fixes its outcome and threshold sets once per root and object, so the
object-dependence the paper locates at the minimal-VP level is modelled by distinct
carriers for distinct objects.

## References

* [bhadra-2024]
* [beavers-2011]: the affectedness hierarchy and the potential-for-change class.
* [dowty-1991]: the *un-*/*re-* split in verb meaning.
-/

namespace Bhadra2024

open ArgumentStructure

/-! ### Outcome cardinality -/

/-- The cardinality tier of an outcome set: `empty < singleton < multi` (62). -/
inductive OutcomeCardinality where
  | empty
  | singleton
  | multi
  deriving Repr, DecidableEq

namespace OutcomeCardinality

/-- Rank embedding into `ℕ`. -/
def toNat : OutcomeCardinality → ℕ
  | .empty => 0
  | .singleton => 1
  | .multi => 2

theorem toNat_injective : Function.Injective toNat := by
  intro a b h; cases a <;> cases b <;> simp_all [toNat]

instance : LinearOrder OutcomeCardinality := LinearOrder.lift' toNat toNat_injective

theorem empty_lt_singleton : empty < singleton := by decide
theorem singleton_lt_multi : singleton < multi := by decide

/-- The tier of an outcome set: multi-membered iff nontrivial, empty iff empty. -/
noncomputable def ofSet {State : Type*} (O : Set State) : OutcomeCardinality :=
  open Classical in
  if O.Nontrivial then .multi else if O.Nonempty then .singleton else .empty

variable {State : Type*} {O : Set State}

theorem ofSet_eq_multi (h : O.Nontrivial) : ofSet O = .multi := by
  rw [ofSet, if_pos h]

theorem ofSet_eq_singleton (hne : O.Nonempty) (hnt : ¬ O.Nontrivial) :
    ofSet O = .singleton := by
  rw [ofSet, if_neg hnt, if_pos hne]

theorem ofSet_eq_empty (h : ¬ O.Nonempty) : ofSet O = .empty := by
  rw [ofSet, if_neg (fun hnt => h hnt.nonempty), if_neg h]

@[simp] theorem ofSet_singleton (s : State) : ofSet ({s} : Set State) = .singleton :=
  ofSet_eq_singleton ⟨s, rfl⟩ (by rw [Set.not_nontrivial_iff]; exact Set.subsingleton_singleton)

@[simp] theorem ofSet_empty : ofSet (∅ : Set State) = .empty :=
  ofSet_eq_empty (by simp)

end OutcomeCardinality

/-- The classes of dynamic transitive roots by what their outcome set encodes: the
potential-for-change class (60) and the classes with a lexically specified result or none
(61a–h). -/
inductive OutcomeClass where
  | potentialForChange
  | physicalProperty
  | transformation
  | movement
  | consumption
  | creation
  | degreeAchievement
  | impingement
  | noChange
  deriving DecidableEq, Repr

/-- The outcome tier of each class: multi-membered for potential-for-change roots,
singleton for every root with a lexically specified result, empty for roots unspecified
for change (62). -/
def OutcomeClass.tier : OutcomeClass → OutcomeCardinality
  | .potentialForChange => .multi
  | .noChange => .empty
  | _ => .singleton

/-- Potential-for-change roots are the only class whose outcome sets are multi-membered. -/
theorem tier_eq_multi_iff (c : OutcomeClass) :
    c.tier = .multi ↔ c = .potentialForChange := by
  cases c <;> decide

/-! ### States, boundaries, and roots -/

/-- An object's state over time: a lifespan point for each time (53). -/
abbrev StateFunction (Entity State Time : Type*) := Time → Entity → State

variable {Entity State Time : Type*} [LinearOrder Time]

/-- `res(e)(x)`, the object's state at the right boundary of `e` (64). -/
def resState (k : StateFunction Entity State Time) (e : Event Time) (x : Entity) : State :=
  k (Event.τ e).snd x

/-- `pre(e)(x)`, the object's state at the left boundary of `e` (65). -/
def preState (k : StateFunction Entity State Time) (e : Event Time) (x : Entity) : State :=
  k (Event.τ e).fst x

/-- A verb root as the prefixes see it: its base predicate with the lexical outcome set of
states at the right boundary and the contextual threshold set of states at the left
boundary ((56), (60)). -/
structure VerbOutcomes (Entity State Time : Type*) [LinearOrder Time] where
  /-- The base predicate `P(e)(x)`. -/
  verb : EventRel Time Entity
  /-- The outcome set `O`. -/
  outcomes : Set State
  /-- The threshold set `T`. -/
  thresholds : Set State

/-- The cardinality tier of a root's outcome set. -/
noncomputable def VerbOutcomes.cardinality (vro : VerbOutcomes Entity State Time) :
    OutcomeCardinality :=
  OutcomeCardinality.ofSet vro.outcomes

/-! ### The prefixes as result-state modifiers -/

/-- Reversative *un-* (66): a prior base event `e'` whose result is the state the *un-*
event starts from, a multi-membered outcome set, and the *un-* event returning the object
to the base event's initial state. The vacuous `∃ Q. Q(e)(x)` of the assertion is
dropped. -/
def unSem (k : StateFunction Entity State Time) (vro : VerbOutcomes Entity State Time)
    (e : Event Time) (x : Entity) : Prop :=
  ∃ e' : Event Time,
    vro.verb e' x ∧
    (Event.τ e').precedes (Event.τ e) ∧
    resState k e' x = preState k e x ∧
    vro.outcomes.Nontrivial ∧
    resState k e x = preState k e' x

/-- Restitutive *re-* ((68), (72)): a prior base event `e'` with the same result, whose
result state is an admissible start state — the base action does not leave the object where
its result cannot be restored — and the base predicate holding of the *re-* event. No
cardinality demand is placed on the outcome set. -/
def reSem (k : StateFunction Entity State Time) (vro : VerbOutcomes Entity State Time)
    (e : Event Time) (x : Entity) : Prop :=
  (∃ e' : Event Time,
    vro.verb e' x ∧
    (Event.τ e').precedes (Event.τ e) ∧
    resState k e x = resState k e' x ∧
    resState k e' x ∈ vro.thresholds) ∧
  vro.verb e x

/-- A root whose outcome set is not multi-membered cannot host *un-* (67). -/
theorem subsingleton_blocks_un (k : StateFunction Entity State Time)
    (vro : VerbOutcomes Entity State Time) (h : ¬ vro.outcomes.Nontrivial)
    (e : Event Time) (x : Entity) : ¬ unSem k vro e x :=
  fun ⟨_, _, _, _, hnt, _⟩ => h hnt

theorem singleton_blocks_un (k : StateFunction Entity State Time)
    (vro : VerbOutcomes Entity State Time) (s : State) (hs : vro.outcomes = {s})
    (e : Event Time) (x : Entity) : ¬ unSem k vro e x :=
  subsingleton_blocks_un k vro
    (by rw [Set.not_nontrivial_iff, hs]; exact Set.subsingleton_singleton) e x

theorem empty_blocks_un (k : StateFunction Entity State Time)
    (vro : VerbOutcomes Entity State Time) (hs : vro.outcomes = ∅)
    (e : Event Time) (x : Entity) : ¬ unSem k vro e x :=
  subsingleton_blocks_un k vro
    (by rw [Set.not_nontrivial_iff, hs]; exact Set.subsingleton_empty) e x

/-- Hosting *un-* forces a root's outcome set into the multi-membered tier. -/
theorem un_requires_multi (k : StateFunction Entity State Time)
    (vro : VerbOutcomes Entity State Time) (e : Event Time) (x : Entity)
    (h : unSem k vro e x) : vro.cardinality = .multi :=
  let ⟨_, _, _, _, hnt, _⟩ := h
  OutcomeCardinality.ofSet_eq_multi hnt

/-- A base action whose result is never an admissible start state blocks *re-* (72). -/
theorem not_reSem_of_outcome_not_threshold (k : StateFunction Entity State Time)
    (vro : VerbOutcomes Entity State Time) (x : Entity)
    (h : ∀ e', vro.verb e' x → resState k e' x ∉ vro.thresholds) (e : Event Time) :
    ¬ reSem k vro e x :=
  fun ⟨⟨e', hv, _, _, hT⟩, _⟩ => h e' hv hT

/-! ### Worked roots -/

section Examples

/-- The base event. -/
private def ev₁ : Event ℤ where
  runtime := ⟨⟨0, 5⟩, by omega⟩
  sort := .dynamic

/-- The prefixed event. -/
private def ev₂ : Event ℤ where
  runtime := ⟨⟨10, 15⟩, by omega⟩
  sort := .dynamic

private theorem ev₁_precedes_ev₂ : (Event.τ ev₁).precedes (Event.τ ev₂) := by
  show (5 : ℤ) < 10; omega

/-- The base predicate of every worked root: it holds of the scenario's two events. -/
private def acts : EventRel ℤ Unit := fun e _ => e = ev₁ ∨ e = ev₂

private theorem acts_ev₁ : acts ev₁ () := Or.inl rfl
private theorem acts_ev₂ : acts ev₂ () := Or.inr rfl

/-- A root whose action carries the object from `start` to `result` at the base event and
again at the prefixed event, both acting on the same object. -/
private def twice {State : Type*} (start result : State) : StateFunction Unit State ℤ :=
  fun t _ => if t ≤ 0 then start else result

/-- A root whose action carries the object from `start` to `result` at the base event and
back to `start` at the prefixed event. -/
private def andBack {State : Type*} (start result : State) : StateFunction Unit State ℤ :=
  fun t _ => if t ≤ 0 then start else if t ≤ 10 then result else start

/-- States of a parchment under folding (54). -/
inductive ParchmentState where
  | flat | slightlyCreased | folded | tightlyFolded
  deriving DecidableEq, Repr

/-- *fold*, a potential-for-change root (60): a multi-membered outcome set, and a folded
parchment can be folded again. -/
def foldVRO : VerbOutcomes Unit ParchmentState ℤ where
  verb := acts
  outcomes := {.slightlyCreased, .folded, .tightlyFolded}
  thresholds := {.flat, .slightlyCreased, .folded}

theorem fold_outcomes_multi : foldVRO.outcomes.Nontrivial :=
  ⟨.slightlyCreased, by simp [foldVRO], .folded, by simp [foldVRO], by decide⟩

/-- *Veena unfolded the parchment*: the worked derivation of (66). -/
theorem fold_un : unSem (andBack .flat .folded) foldVRO ev₂ () :=
  ⟨ev₁, acts_ev₁, ev₁_precedes_ev₂, rfl, fold_outcomes_multi, rfl⟩

/-- *refold*: *re-* attaches across the multi-membered tier as well. -/
theorem fold_re : reSem (twice .flat .folded) foldVRO ev₂ () :=
  ⟨⟨ev₁, acts_ev₁, ev₁_precedes_ev₂, rfl,
      by simp [foldVRO, resState, twice, ev₁, Event.τ]⟩, acts_ev₂⟩

inductive LimbState where
  | intact | broken
  deriving DecidableEq, Repr

/-- *break* applied to a limb (61a): a single result, and a broken limb admits another
breaking (73a). -/
def breakLimbVRO : VerbOutcomes Unit LimbState ℤ where
  verb := acts
  outcomes := {.broken}
  thresholds := {.intact, .broken}

/-- *break* applied to a sewer: the same single result, which a sewer cannot informatively
reach again (73a). -/
def breakSewerVRO : VerbOutcomes Unit LimbState ℤ where
  verb := acts
  outcomes := {.broken}
  thresholds := {.intact}

/-- *#unbreak a limb*: the singleton outcome set fails (67). -/
theorem breakLimb_not_un (k : StateFunction Unit LimbState ℤ) (e : Event ℤ) :
    ¬ unSem k breakLimbVRO e () :=
  singleton_blocks_un k breakLimbVRO .broken rfl e ()

/-- *rebreak a limb* (73a). -/
theorem breakLimb_re : reSem (twice .intact .broken) breakLimbVRO ev₂ () :=
  ⟨⟨ev₁, acts_ev₁, ev₁_precedes_ev₂, rfl,
      by simp [breakLimbVRO, resState, twice, ev₁, Event.τ]⟩, acts_ev₂⟩

/-- *#rebreak a sewer* (73a): the broken sewer is not an admissible start state. -/
theorem breakSewer_not_re (e : Event ℤ) : ¬ reSem (twice .intact .broken) breakSewerVRO e () :=
  not_reSem_of_outcome_not_threshold _ _ () (fun e' he' => by
    rcases he' with rfl | rfl <;> simp [breakSewerVRO, acts, resState, twice, ev₁, ev₂, Event.τ]) e

inductive SurfaceState where
  | unaltered | surfaceAltered
  deriving DecidableEq, Repr

/-- *hit*, an impingement-effecting root (61g): a single, irreversible surface alteration. -/
def hitVRO : VerbOutcomes Unit SurfaceState ℤ where
  verb := acts
  outcomes := {.surfaceAltered}
  thresholds := {.unaltered}

/-- *\*unhit* (25). -/
theorem hit_not_un (k : StateFunction Unit SurfaceState ℤ) (e : Event ℤ) :
    ¬ unSem k hitVRO e () :=
  singleton_blocks_un k hitVRO .surfaceAltered rfl e ()

/-- *\*rehit* (48): impingement leaves the surface altered, never again unaltered. -/
theorem hit_not_re (e : Event ℤ) : ¬ reSem (twice .unaltered .surfaceAltered) hitVRO e () :=
  not_reSem_of_outcome_not_threshold _ _ () (fun e' he' => by
    rcases he' with rfl | rfl <;> simp [hitVRO, acts, resState, twice, ev₁, ev₂, Event.τ]) e

inductive TruckState where
  | empty | full
  deriving DecidableEq, Repr

/-- *load*, a degree achievement (70): a single contextually salient result that does not
prevent loading again. -/
def loadVRO : VerbOutcomes Unit TruckState ℤ where
  verb := acts
  outcomes := {.full}
  thresholds := {.empty, .full}

/-- *Raj reloaded the truck* (69a). -/
theorem load_re : reSem (twice .empty .full) loadVRO ev₂ () :=
  ⟨⟨ev₁, acts_ev₁, ev₁_precedes_ev₂, rfl,
      by simp [loadVRO, resState, twice, ev₁, Event.τ]⟩, acts_ev₂⟩

inductive MirrorState where
  | intact | shattered
  deriving DecidableEq, Repr

/-- *shatter* (71): a single result that leaves the object outside every threshold. -/
def shatterVRO : VerbOutcomes Unit MirrorState ℤ where
  verb := acts
  outcomes := {.shattered}
  thresholds := {.intact}

/-- *#The children reshattered the mirror* (69b). -/
theorem shatter_not_re (e : Event ℤ) :
    ¬ reSem (twice .intact .shattered) shatterVRO e () :=
  not_reSem_of_outcome_not_threshold _ _ () (fun e' he' => by
    rcases he' with rfl | rfl <;> simp [shatterVRO, acts, resState, twice, ev₁, ev₂, Event.τ]) e

/-- *re-* is indifferent to outcome cardinality: it attaches to a singleton-outcome root. -/
theorem re_on_singleton :
    loadVRO.cardinality = .singleton ∧ reSem (twice .empty .full) loadVRO ev₂ () :=
  ⟨by simp [VerbOutcomes.cardinality, loadVRO], load_re⟩

end Examples

/-! ### The affectedness hierarchy -/

/-- Beavers's affectedness projection cannot separate potential-for-change roots from
impingement-effecting ones: a causally affected object with no entailed change and the
object of a surface-contact verb land on the same degree. Outcome structure separates
them — `foldVRO` is multi-membered where `hitVRO` is a singleton. -/
theorem affectedness_conflates_pfc_ie :
    profileToDegree { causallyAffected := true, stationary := true }
      = profileToDegree ArgumentStructure.contactObject :=
  rfl

end Bhadra2024
