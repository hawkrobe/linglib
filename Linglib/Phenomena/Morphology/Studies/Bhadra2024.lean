import Linglib.Theories.Morphology.ReversalRestitution
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Bhadra 2024: Verb roots encode outcomes

@cite{bhadra-2024}

Bhadra, D. (2024). Verb roots encode outcomes: argument structure and
lexical semantics of reversal and restitution. *Linguistics and Philosophy*
47: 557–610.

## Summary

The reversative prefix *un-* and the restitutive prefix *re-* are sensitive
to the **outcome set** of the base verb root. All verb roots come equipped
with sets of outcomes (possible states of the object after the action).
The cardinality of this set determines affix compatibility:

- PFC verbs (fold, wrap, coil): multi-membered outcomes → *un-* ✓, *re-* ✓
- IE verbs (hit, scrub, kick): singleton outcomes, surface only → *un-* ✗, *re-* ✗
- COS verbs (break, destroy, paint): singleton outcomes → *un-* ✗, *re-* partial

## Key formalizations

1. `ForceTransmissionClass` classifies verbs by impact type (§§2, 3, 4)
2. `BoundaryStates` formalizes `res`/`pre` operators for state equivalence (§5.2)
3. `LevinClass.forceTransmissionClass` bridges Levin classes to outcome classes
4. Per-verb *un-* and *re-* predictions verified against empirical data from (12), (45)
-/

namespace Phenomena.Morphology.Studies.Bhadra2024

open ForceTransmissionClass OutcomeCardinality

-- ════════════════════════════════════════════════════
-- § 1. Per-Class un- Compatibility (from paper's (12))
-- ════════════════════════════════════════════════════

/-! Only surface contact verbs (PFC class) allow *un-*:
    - (d) Surface contact: unpin, unwrap, untwist, unpack, unplug ✓
    - (a) Physical property: *unpaint, *unclean, *unfix, *unbreak ✗
    - (b) Transforms: *unturn, *uncarve ✗
    - (e) Creation: *unbuild, *unconstruct ✗
    - (f) Consumption: *undestroy, *uneat ✗
    - (g) Degree achievements: *unfill, *unwarm ✗
    - (h) No change: *unswim, *unwalk ✗ -/

/-- PFC classes allow un-. -/
theorem coil_un : (LevinClass.forceTransmissionClass .coil).unCompatible = true := rfl
theorem bend_un : (LevinClass.forceTransmissionClass .bend).unCompatible = true := rfl

/-- COS classes disallow un-. -/
theorem break_no_un : (LevinClass.forceTransmissionClass .break_).unCompatible = false := rfl
theorem color_no_un : (LevinClass.forceTransmissionClass .color).unCompatible = false := rfl
theorem build_no_un : (LevinClass.forceTransmissionClass .build).unCompatible = false := rfl
theorem destroy_no_un : (LevinClass.forceTransmissionClass .destroy).unCompatible = false := rfl
theorem eat_no_un : (LevinClass.forceTransmissionClass .eat).unCompatible = false := rfl
theorem calibratable_no_un :
    (LevinClass.forceTransmissionClass .calibratableCoS).unCompatible = false := rfl

/-- IE classes disallow un-. -/
theorem hit_no_un : (LevinClass.forceTransmissionClass .hit).unCompatible = false := rfl
theorem wipe_no_un : (LevinClass.forceTransmissionClass .wipe).unCompatible = false := rfl

/-- No-change classes disallow un-. -/
theorem swim_no_un :
    (LevinClass.forceTransmissionClass .mannerOfMotion).unCompatible = false := rfl

-- ════════════════════════════════════════════════════
-- § 2. Per-Class re- Compatibility (from paper's (45))
-- ════════════════════════════════════════════════════

/-! *re-* is more permissive than *un-*:
    - (a) Physical property: repaint ✓, reclean ✓, refix ✓, rebreak ✓
    - (d) Surface contact: repin ✓, rewrap ✓, retwist ✓
    - (e) Creation: rebuild ✓, reconstruct ✓, recreate ✓
    - (g) Degree achievements: refill ⊳, rewarm ⊳
    But *re-* is blocked when the object is eliminated:
    - (f) Consumption: *redestroy, *reeat ✗
    - (b) Transforms: *retransform ✗ (mostly)
    - IE: *rehit, *rescrub ✗
    - No change: *reswim, *rewalk ✗ -/

/-- PFC classes allow re-. -/
theorem coil_re : LevinClass.reCompatible .coil = true := rfl
theorem bend_re : LevinClass.reCompatible .bend = true := rfl

/-- Physical property and creation COS classes allow re-. -/
theorem break_re : LevinClass.reCompatible .break_ = true := rfl
theorem color_re : LevinClass.reCompatible .color = true := rfl
theorem build_re : LevinClass.reCompatible .build = true := rfl
theorem otherCoS_re : LevinClass.reCompatible .otherCoS = true := rfl
theorem cooking_re : LevinClass.reCompatible .cooking = true := rfl

/-- Consumption, destruction, killing COS classes block re-. -/
theorem destroy_no_re : LevinClass.reCompatible .destroy = false := rfl
theorem eat_no_re : LevinClass.reCompatible .eat = false := rfl
theorem murder_no_re : LevinClass.reCompatible .murder = false := rfl
theorem turn_no_re : LevinClass.reCompatible .turn = false := rfl

/-- IE classes block re-. -/
theorem hit_no_re : LevinClass.reCompatible .hit = false := rfl
theorem wipe_no_re : LevinClass.reCompatible .wipe = false := rfl

/-- No-change classes block re- (paper's (45h): *reswim, *rewalk). -/
theorem swim_no_re : LevinClass.reCompatible .mannerOfMotion = false := rfl

-- ════════════════════════════════════════════════════
-- § 3. Outcome Cardinality Verification
-- ════════════════════════════════════════════════════

/-- PFC verbs have multi-membered outcome sets. -/
theorem pfc_multi :
    (ForceTransmissionClass.outcomeCardinality .potentialForChange) = .multi := rfl

/-- IE verbs have singleton outcome sets (impingement only). -/
theorem ie_singleton :
    (ForceTransmissionClass.outcomeCardinality .impingementEffecting) = .singleton := rfl

/-- COS verbs have singleton outcome sets (specific result). -/
theorem cos_singleton :
    (ForceTransmissionClass.outcomeCardinality .integralChange) = .singleton := rfl

/-- No-change verbs have empty outcome sets. -/
theorem nochange_empty :
    (ForceTransmissionClass.outcomeCardinality .noForceTransmission) = .empty := rfl

-- ════════════════════════════════════════════════════
-- § 4. Worked Example: fold/unfold (@cite{bhadra-2024} §5.2, eqs. 74–75)
-- ════════════════════════════════════════════════════

/-- Possible states of a parchment under folding.
    Illustrates the multi-membered outcome set of a PFC verb:
    folding can yield any of these states depending on the
    force and manner of folding. -/
inductive ParchmentState where
  | flat | slightlyCreased | folded | tightlyFolded
  deriving DecidableEq, BEq, Repr

/-- fold(parchment): flat → folded -/
def foldBoundary : BoundaryStates ParchmentState := ⟨.flat, .folded⟩
/-- unfold(parchment): folded → flat (reverses fold) -/
def unfoldBoundary : BoundaryStates ParchmentState := ⟨.folded, .flat⟩

/-- Reversibility: fold and unfold satisfy the inverse equivalence condition.
    `res(fold) = pre(unfold)` and `res(unfold) = pre(fold)`. -/
theorem fold_unfold_reversible :
    reversible foldBoundary unfoldBoundary = true := rfl

/-- Restitution: refold achieves the same result as fold.
    `res(refold) = res(fold)`. -/
def refoldBoundary : BoundaryStates ParchmentState := ⟨.flat, .folded⟩
theorem fold_refold_restitutive :
    restitutive foldBoundary refoldBoundary = true := rfl

-- ════════════════════════════════════════════════════
-- § 5. Worked Example: paint/repaint (@cite{bhadra-2024} §5.2, eqs. 76–77)
-- ════════════════════════════════════════════════════

/-- States of a wall under painting. Singleton outcome set:
    painting deterministically yields the `painted` state. -/
inductive WallState where
  | unpainted | painted
  deriving DecidableEq, BEq, Repr

def paintBoundary : BoundaryStates WallState := ⟨.unpainted, .painted⟩
def repaintBoundary : BoundaryStates WallState := ⟨.unpainted, .painted⟩

/-- repaint satisfies restitution: `res(repaint) = res(paint)`. -/
theorem paint_repaint_restitutive :
    restitutive paintBoundary repaintBoundary = true := rfl

/-- *unpaint is blocked: color (24) is COS with singleton outcomes.
    un- requires multi-membered outcomes (PFC only). -/
theorem paint_un_blocked :
    (LevinClass.forceTransmissionClass .color).unCompatible = false := rfl

-- ════════════════════════════════════════════════════
-- § 6. Structural Results (Fig. 5)
-- ════════════════════════════════════════════════════

/-- PFC is the unique class compatible with BOTH *un-* and *re-*.
    This is the central distributional generalization of the paper. -/
theorem pfc_is_overlap_class :
    -- PFC: both ✓
    (ForceTransmissionClass.unCompatible .potentialForChange = true ∧
     ForceTransmissionClass.reCompatible .potentialForChange = true) ∧
    -- No other class has un-compatible = true
    ForceTransmissionClass.unCompatible .impingementEffecting = false ∧
    ForceTransmissionClass.unCompatible .integralChange = false ∧
    ForceTransmissionClass.unCompatible .noForceTransmission = false :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 7. Bridge: Bhadra Reclassifies Bend from COS to PFC
-- ════════════════════════════════════════════════════

/-- @cite{bhadra-2024} reclassifies the bend class (45.2) from COS to PFC.

    @cite{levin-1993}: bend has `changeOfState = true` (diagnosed by
    causative/inchoative alternation: "the paper folded" / "she folded the paper").

    @cite{bhadra-2024}: fold has multi-membered outcomes (slightly creased,
    halfway bent, tightly folded, etc.) → PFC, not COS. The change IS
    possible but not to a SPECIFIC fixed state.

    This is the paper's central theoretical move: outcome set structure is
    a finer-grained classification than the traditional COS label. -/
theorem bend_reclassification :
    -- COS per Levin (changeOfState = true in meaning components)
    (LevinClass.meaningComponents .bend).changeOfState = true ∧
    -- PFC per Bhadra (multi-membered outcome set)
    LevinClass.forceTransmissionClass .bend = .potentialForChange ∧
    -- Consequence: un- compatible
    (LevinClass.forceTransmissionClass .bend).unCompatible = true ∧
    -- Consequence: re- compatible
    LevinClass.reCompatible .bend = true :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 8. Bridge: motionContact Template = IE Verbs
-- ════════════════════════════════════════════════════

/-- @cite{rappaport-hovav-levin-2024}'s motionContact template corresponds
    exactly to @cite{bhadra-2024}'s IE class. The wipe class (10.4)
    has the motionContact template and is classified as IE. -/
theorem motionContact_is_ie :
    LevinClass.eventTemplate .wipe = .motionContact ∧
    LevinClass.forceTransmissionClass .wipe = .impingementEffecting := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 9. End-to-End: Fragment Verb → LevinClass → un-/re- Prediction
-- ════════════════════════════════════════════════════

open Fragments.English.Predicates.Verbal in
/-- End-to-end chain: the Fragment entry for "kick" (Levin 18.1 hit class)
    derives IE classification and correctly predicts both un- and re- blocking.
    kick.levinClass → .hit → .impingementEffecting → unCompatible=false, reCompatible=false -/
theorem kick_end_to_end :
    kick.toVerbCore.levinClass = some .hit ∧
    (LevinClass.forceTransmissionClass .hit) = .impingementEffecting ∧
    (LevinClass.forceTransmissionClass .hit).unCompatible = false ∧
    LevinClass.reCompatible .hit = false := ⟨rfl, rfl, rfl, rfl⟩

/-- End-to-end chain: the Fragment entry for "bend" (Levin 45.2)
    derives PFC classification and correctly predicts both un- and re- compatibility.
    bend.levinClass → .bend → .potentialForChange → unCompatible=true, reCompatible=true -/
theorem bend_end_to_end :
    Fragments.English.Predicates.Verbal.bend.toVerbCore.levinClass = some .bend ∧
    (LevinClass.forceTransmissionClass .bend) = .potentialForChange ∧
    (LevinClass.forceTransmissionClass .bend).unCompatible = true ∧
    LevinClass.reCompatible .bend = true := ⟨rfl, rfl, rfl, rfl⟩

open Fragments.English.Predicates.Verbal in
/-- End-to-end chain: the Fragment entry for "break" (Levin 45.1)
    derives COS classification → un- blocked, re- allowed.
    break.levinClass → .break_ → .integralChange → unCompatible=false, reCompatible=true -/
theorem break_end_to_end :
    break_.toVerbCore.levinClass = some .break_ ∧
    (LevinClass.forceTransmissionClass .break_) = .integralChange ∧
    (LevinClass.forceTransmissionClass .break_).unCompatible = false ∧
    LevinClass.reCompatible .break_ = true := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 10. Compositional VRO Worked Examples (@cite{bhadra-2024} §5)
-- ════════════════════════════════════════════════════

section CompositionalExamples

open Semantics.Events Core.Time

/-- VRO for "fold": PFC verb with multi-membered outcome set.
    The parchment can end up in any of several states after folding.
    Outcome set = {slightlyCreased, folded, tightlyFolded} (3 members).
    Threshold set = {flat, slightlyCreased} (contextual pre-states). -/
def foldVRO : VerbRootVRO Unit ParchmentState ℤ where
  verb := λ _ _ => True  -- simplified: fold always applies
  applies := λ _ _ => True
  outcomes := {.slightlyCreased, .folded, .tightlyFolded}
  thresholds := {.flat, .slightlyCreased}

/-- fold's outcome set is multi-membered: slightlyCreased ≠ folded. -/
theorem fold_outcomes_multi : foldVRO.outcomes.multiMembered :=
  ⟨.slightlyCreased, .folded,
   Or.inl rfl, Or.inr (Or.inl rfl),
   ParchmentState.noConfusion⟩

/-- VRO for "break": COS verb with singleton outcome set.
    Breaking yields exactly one lexically specified result: broken. -/
inductive LimbState where
  | intact | broken
  deriving DecidableEq, BEq, Repr

def breakVRO : VerbRootVRO Unit LimbState ℤ where
  verb := λ _ _ => True
  applies := λ _ _ => True
  outcomes := {.broken}  -- singleton: only one result state
  thresholds := {.intact}

/-- break's singleton outcome set blocks un-: *unbreak is predicted
    to fail because |O| = 1, so the multi-membered presupposition
    of un- (eq. 66) cannot be satisfied. -/
theorem break_blocks_un (stateAt : StateFunction Unit LimbState ℤ)
    (x : Unit) (e : Ev ℤ) :
    ¬ unSem stateAt breakVRO x e :=
  singleton_blocks_un stateAt breakVRO ⟨.broken, rfl⟩ x e

/-- VRO for "hit": IE verb with singleton outcome set (surface alteration).
    The object's surface is altered in exactly one way. -/
inductive SurfaceState where
  | unaltered | surfaceAltered
  deriving DecidableEq, BEq, Repr

def hitVRO : VerbRootVRO Unit SurfaceState ℤ where
  verb := λ _ _ => True
  applies := λ _ _ => True
  outcomes := {.surfaceAltered}  -- singleton: surface alteration only
  thresholds := {.unaltered}

/-- hit's singleton outcome set blocks un-: *unhit is predicted
    to fail for the same reason as *unbreak. -/
theorem hit_blocks_un (stateAt : StateFunction Unit SurfaceState ℤ)
    (x : Unit) (e : Ev ℤ) :
    ¬ unSem stateAt hitVRO x e :=
  singleton_blocks_un stateAt hitVRO ⟨.surfaceAltered, rfl⟩ x e

/-- VRO for "destroy": COS consumption verb with singleton outcome set.
    The outcome (ceased to exist) is also a blocking threshold for re-,
    since the object cannot be acted on again after being destroyed. -/
inductive ObjectExistence where
  | exists_ | ceasedToExist
  deriving DecidableEq, BEq, Repr

def destroyVRO : VerbRootVRO Unit ObjectExistence ℤ where
  verb := λ _ _ => True
  applies := λ _ _ => True
  outcomes := {.ceasedToExist}
  -- Threshold is the PRE-state: the object must exist before destruction
  thresholds := {.exists_}

/-- destroy blocks un- (singleton outcomes). -/
theorem destroy_blocks_un (stateAt : StateFunction Unit ObjectExistence ℤ)
    (x : Unit) (e : Ev ℤ) :
    ¬ unSem stateAt destroyVRO x e :=
  singleton_blocks_un stateAt destroyVRO ⟨.ceasedToExist, rfl⟩ x e

/-- The three-way distributional split is derived from outcome set structure:
    - PFC (fold): multi-membered → un- possible
    - COS (break): singleton → un- blocked
    - IE (hit): singleton → un- blocked -/
theorem distributional_split_derived :
    foldVRO.outcomes.multiMembered ∧
    (∃ s, breakVRO.outcomes = {s}) ∧
    (∃ s, hitVRO.outcomes = {s}) :=
  ⟨fold_outcomes_multi, ⟨.broken, rfl⟩, ⟨.surfaceAltered, rfl⟩⟩

end CompositionalExamples

-- ════════════════════════════════════════════════════
-- § 11. Stress Tests: Positive Existence Proofs
-- ════════════════════════════════════════════════════

/-! The theorems in § 10 prove that un- is BLOCKED for certain verb classes.
    But blocking theorems alone don't guarantee the compositional semantics
    is non-vacuous. We also need to show un- and re- are SATISFIABLE for the
    classes that should allow them. The following construct concrete event
    witnesses and state functions to demonstrate positive satisfiability. -/

section StressTests

open Semantics.Events Core.Time

/-- Event from t=0 to t=5 (the base event, e.g. folding). -/
private def ev₁ : Ev ℤ where
  runtime := ⟨0, 5, by omega⟩
  sort := .action

/-- Event from t=10 to t=15 (the reversal/restitution event, e.g. unfolding). -/
private def ev₂ : Ev ℤ where
  runtime := ⟨10, 15, by omega⟩
  sort := .action

/-- ev₁ temporally precedes ev₂: τ(ev₁).finish < τ(ev₂).start. -/
private theorem ev₁_precedes_ev₂ : (Ev.τ ev₁).precedes (Ev.τ ev₂) := by
  show (5 : ℤ) < 10; omega

/-- State function for fold/unfold: the parchment starts flat, is folded
    during ev₁, and returns to flat during ev₂.
    - t ≤ 0: flat (pre-state of fold)
    - 0 < t ≤ 5: folded (result of fold)
    - 5 < t ≤ 10: folded (between events)
    - 10 < t: flat (result of unfold) -/
private def foldUnfoldState : StateFunction Unit ParchmentState ℤ := λ t _ =>
  if t ≤ 0 then .flat
  else if t ≤ 10 then .folded
  else .flat

/-- Boundary state verification: pre(ev₁) = flat, res(ev₁) = folded,
    pre(ev₂) = folded, res(ev₂) = flat. -/
private theorem fold_unfold_boundaries :
    preState foldUnfoldState ev₁ () = .flat ∧
    resState foldUnfoldState ev₁ () = .folded ∧
    preState foldUnfoldState ev₂ () = .folded ∧
    resState foldUnfoldState ev₂ () = .flat := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Positive existence: un- IS satisfiable for PFC verbs.**
    Constructs a concrete witness showing `unSem` holds for fold. -/
theorem fold_un_satisfiable :
    ∃ (stateAt : StateFunction Unit ParchmentState ℤ) (x : Unit) (e : Ev ℤ),
    unSem stateAt foldVRO x e :=
  ⟨foldUnfoldState, (), ev₂, ev₁, trivial,
   ev₁_precedes_ev₂,
   -- resState ev₁ () = preState ev₂ ()  (folded = folded)
   rfl,
   fold_outcomes_multi,
   -- resState ev₂ () = preState ev₁ ()  (flat = flat)
   rfl⟩

/-- Event from t=20 to t=25 (the re-event, e.g. re-folding). -/
private def ev₃ : Ev ℤ where
  runtime := ⟨20, 25, by omega⟩
  sort := .action

/-- State function for fold/unfold/refold scenario:
    - t ≤ 0: flat (pre-state of first fold)
    - 0 < t ≤ 5: folded (result of first fold, ev₁)
    - 5 < t ≤ 15: flat (result of unfold, ev₂)
    - 15 < t: folded (result of refold, ev₃) -/
private def foldRefoldState : StateFunction Unit ParchmentState ℤ := λ t _ =>
  if t ≤ 0 then .flat
  else if t ≤ 5 then .folded
  else if t ≤ 20 then .flat
  else .folded

/-- ev₁ precedes ev₃. -/
private theorem ev₁_precedes_ev₃ : (Ev.τ ev₁).precedes (Ev.τ ev₃) := by
  show (5 : ℤ) < 20; omega

/-- **Positive existence: re- IS satisfiable for PFC verbs.**
    Three-event scenario: fold(ev₁), unfold(ev₂), refold(ev₃).
    The rePresupposition of ev₃ is witnessed by ev₁ (prior fold with
    matching result state). -/
theorem fold_re_satisfiable :
    ∃ (stateAt : StateFunction Unit ParchmentState ℤ) (x : Unit) (e : Ev ℤ),
    reSem stateAt foldVRO x e :=
  ⟨foldRefoldState, (), ev₃,
   -- rePresupposition: ∃ e', verb e' ∧ precedes ∧ resState match
   ⟨ev₁, trivial, ev₁_precedes_ev₃, rfl⟩,
   -- verb holds of the re-event
   trivial⟩

/-- State function for break/rebreak scenario:
    - t ≤ 0: intact (pre-state of first break)
    - 0 < t ≤ 5: broken (result of first break, ev₁)
    - 5 < t ≤ 15: intact (repaired between events)
    - 15 < t: broken (result of rebreak, ev₃) -/
private def breakRebreakState : StateFunction Unit LimbState ℤ := λ t _ =>
  if t ≤ 0 then .intact
  else if t ≤ 5 then .broken
  else if t ≤ 20 then .intact
  else .broken

/-- **Positive existence: re- IS satisfiable for COS verbs.**
    COS verbs (break) block un- but allow re-. This demonstrates
    that reSem is satisfiable for break despite singleton outcomes. -/
theorem break_re_satisfiable :
    ∃ (stateAt : StateFunction Unit LimbState ℤ) (x : Unit) (e : Ev ℤ),
    reSem stateAt breakVRO x e :=
  ⟨breakRebreakState, (), ev₃,
   ⟨ev₁, trivial, ev₁_precedes_ev₃, rfl⟩,
   trivial⟩

/-- **Cross-layer agreement: Boolean and compositional predictions align.**
    The Boolean layer (ForceTransmissionClass) and compositional layer (VRO)
    agree on the un- prediction for fold (both allow) and break (both block). -/
theorem cross_layer_un_agreement :
    -- Boolean layer: PFC allows un-, COS blocks un-
    (LevinClass.forceTransmissionClass .bend).unCompatible = true ∧
    (LevinClass.forceTransmissionClass .break_).unCompatible = false ∧
    -- Compositional layer: fold (PFC) un- is satisfiable
    (∃ (stateAt : StateFunction Unit ParchmentState ℤ) (x : Unit) (e : Ev ℤ),
      unSem stateAt foldVRO x e) ∧
    -- Compositional layer: break (COS) un- is blocked
    (∀ (stateAt : StateFunction Unit LimbState ℤ) (x : Unit) (e : Ev ℤ),
      ¬ unSem stateAt breakVRO x e) :=
  ⟨rfl, rfl,
   fold_un_satisfiable,
   λ stateAt x e => singleton_blocks_un stateAt breakVRO ⟨.broken, rfl⟩ x e⟩

end StressTests

end Phenomena.Morphology.Studies.Bhadra2024
