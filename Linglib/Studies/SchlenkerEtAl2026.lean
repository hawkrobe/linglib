import Linglib.Theories.Semantics.Iconic.Basic
import Linglib.Theories.Semantics.Reference.Monsters
import Linglib.Phenomena.Iconicity.Basic
import Linglib.Fragments.ASL.Classifiers
import Linglib.Core.Context.Shifts

/-!
# Schlenker, Lamberton & Lamberton (2026)
@cite{schlenker-lamberton-lamberton-2026}

Traveling Shots in Language: Towards an Analysis of Dynamic Viewpoints in ASL.
To appear in *Linguistic Inquiry*.

## Core Contribution

Extends Iconological Semantics (@cite{schlenker-lamberton-2024}) by showing that
viewpoint variables may denote **dynamic** (traveling) viewpoints — functions from
time-world pairs to static viewpoints — not just static observation points.

In ASL, a classifier denoting a static object (e.g., TREE-cl) can move in signing
space to represent the object's apparent motion from a moving character's
perspective. This is the linguistic analogue of a traveling camera shot in film.

## Two Analyses

1. **Analysis I** (§7): All viewpoint variables can be dynamic. Relative motion
   arises whenever a viewpoint variable takes a non-constant value.

2. **Analysis II** (§8): Only viewpoints introduced by Role Shift (as overt
   context shift) can be dynamic. Standard viewpoint variables denote static
   viewpoints. Under Role Shift, a distinguished variable π* reads the
   character's dynamic viewpoint from the shifted context.

The paper leaves both options open, pending a consensus on the definition
of Role Shift.

## Data

Paradigms were elicited from two Deaf native ASL signers. Acceptability
is on a 7-point scale (7 = best, 1 = worst). Classifier direction
(left vs. right) systematically determines the character's inferred path.
-/

open Phenomena.Iconicity

namespace SchlenkerEtAl2026

open Semantics.Iconic
open Semantics.Reference.Monsters (IsTowerMonster)
open Core.Context
open Fragments.ASL (SigningSpace)

-- ════════════════════════════════════════════════════════════════
-- § Analysis I: Dynamic Viewpoints (§7)
-- ════════════════════════════════════════════════════════════════

section AnalysisI

variable {W : Type*} {T : Type*} {P : Type*} {E : Type*}

/-- The static viewpoint analysis is a special case of the dynamic one.
    When a viewpoint is constant, dynamic projection reduces to
    time-invariant projection. The dynamic framework is a conservative
    extension. -/
theorem static_is_special_case
    (projects : E → StaticViewpoint P → Bool)
    (d : E) (sv : StaticViewpoint P) :
    ∀ (w : W) (t₁ t₂ : T),
    dynamicProjection projects d (DynamicViewpoint.static sv) w t₁ =
    dynamicProjection projects d (DynamicViewpoint.static sv) w t₂ :=
  fun _ _ _ => rfl

/-- The traveling shot condition: there exist two times at which the
    object's projection differs, producing apparent motion. This is
    only possible when the viewpoint is dynamic. -/
def travelingShotCondition {W : Type*} {T : Type*} {P : Type*} {E : Type*}
    (projects : E → StaticViewpoint P → Bool)
    (d : E) (vp : DynamicViewpoint W T P) (w : W) : Prop :=
  ∃ (t₁ t₂ : T),
    dynamicProjection projects d vp w t₁ ≠ dynamicProjection projects d vp w t₂

/-- A static viewpoint never produces a traveling shot: projection is
    constant across time, so no apparent motion is possible. -/
theorem no_travelingShot_static {W : Type*} (T : Type*) {P : Type*} {E : Type*}
    (projects : E → StaticViewpoint P → Bool)
    (d : E) (sv : StaticViewpoint P) (w : W) :
    ¬ travelingShotCondition (T := T) projects d (DynamicViewpoint.static sv) w := by
  intro h
  obtain ⟨_, _, h'⟩ := h
  exact absurd rfl h'

end AnalysisI

-- ════════════════════════════════════════════════════════════════
-- § Analysis II: Role Shift Introduces Dynamic Viewpoints (§8)
-- ════════════════════════════════════════════════════════════════

section AnalysisII

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*}

/-- A viewpoint assignment: maps viewpoint variable indices to dynamic
    viewpoints. The iconic analogue of an assignment function for
    pronouns. -/
def ViewpointAssignment (W : Type*) (T : Type*) (P : Type*) :=
  Nat → DynamicViewpoint W T P

/-- Resolve a viewpoint variable against a viewpoint assignment and
    an agent. Free variables read from the assignment; the context-bound
    variable π* reads the dynamic viewpoint associated with the agent.

    Under Role Shift (which changes the context's agent to the character),
    π* yields the character's dynamic viewpoint. -/
def resolveViewpoint
    (v : ViewpointVar)
    (assign : ViewpointAssignment W T P)
    (agentVP : E → DynamicViewpoint W T P)
    (agent : E) : DynamicViewpoint W T P :=
  match v with
  | .free i => assign i
  | .contextBound => agentVP agent

/-- Role Shift as context shift. Structurally identical to
    `attitudeShift` but labeled `.roleShift` — it changes the agent to
    the character (and the world to a Role-Shift-accessible world).

    The viewpoint consequence is indirect: since π* reads the agent's
    viewpoint via `resolveViewpoint`, changing the agent changes what
    π* denotes. -/
def roleShiftCtx (character : E) (rsWorld : W) :
    ContextShift (KContext W E P T) where
  apply := (attitudeShift (P := P) (T := T) character rsWorld).apply
  label := .roleShift

/-- Role Shift is a monster (non-identity context shift), connecting
    to the Kaplan/Schlenker monster debate in `Monsters.lean`. -/
theorem roleShift_is_monster
    (character : E) (rsWorld : W)
    (c : KContext W E P T)
    (hAgent : c.agent ≠ character) :
    IsTowerMonster (roleShiftCtx (P := P) (T := T) character rsWorld) := by
  refine ⟨c, fun h => ?_⟩
  have : ((roleShiftCtx character rsWorld).apply c).agent = c.agent :=
    congrArg KContext.agent h
  simp only [roleShiftCtx, attitudeShift] at this
  exact hAgent this.symm

/-- Under Role Shift, π* resolves to the character's viewpoint. -/
theorem contextBound_under_roleShift
    (assign : ViewpointAssignment W T P)
    (agentVP : E → DynamicViewpoint W T P)
    (character : E) :
    resolveViewpoint .contextBound assign agentVP character =
    agentVP character := rfl

/-- Free viewpoint variables are unaffected by who the agent is —
    they read from the assignment function regardless. -/
theorem free_unaffected_by_agent
    (assign : ViewpointAssignment W T P)
    (agentVP : E → DynamicViewpoint W T P)
    (agent₁ agent₂ : E) (i : Nat) :
    resolveViewpoint (.free i) assign agentVP agent₁ =
    resolveViewpoint (.free i) assign agentVP agent₂ := rfl

/-- The restrictive theory: free viewpoint variables always denote
    static viewpoints. Only context-bound π* (introduced by Role Shift)
    can be dynamic. -/
def RestrictiveTheory (assign : ViewpointAssignment W T P) : Prop :=
  ∀ (i : Nat), (assign i).isStatic

/-- Under the restrictive theory, traveling shots are impossible for
    classifiers with free viewpoint variables. -/
theorem restrictive_no_travelingShot
    (assign : ViewpointAssignment W T P)
    (agentVP : E → DynamicViewpoint W T P)
    (hRestr : RestrictiveTheory assign)
    (projects : E → StaticViewpoint P → Bool)
    (d : E) (i : Nat) (agent : E) (w : W) :
    ¬ travelingShotCondition (T := T) projects d
      (resolveViewpoint (.free i) assign agentVP agent) w := by
  intro ⟨t₁, t₂, h⟩
  exact h (congrArg (projects d) (hRestr i w w t₁ t₂))

end AnalysisII

-- ════════════════════════════════════════════════════════════════
-- § End-to-End: Role Shift → Dynamic Viewpoint → Traveling Shot
-- ════════════════════════════════════════════════════════════════

section EndToEnd

variable {W : Type*} {T : Type*}

/-- The complete argumentation chain:

    1. Role Shift changes the context's agent from signer to character
    2. π* reads the agent's viewpoint, so it now reads the character's
    3. The character's viewpoint is dynamic (they are moving)
    4. Dynamic viewpoint + static object → traveling shot is possible
    5. Static viewpoint would make traveling shot impossible

    This theorem captures steps 2-5: given that the character's viewpoint
    is genuinely dynamic (non-constant), the traveling shot condition is
    satisfiable — there exist times where projection differs. -/
theorem dynamicVP_enables_travelingShot
    (projects : Fragments.ASL.Entity → StaticViewpoint SigningSpace → Bool)
    (d : Fragments.ASL.Entity)
    (charVP : DynamicViewpoint W T SigningSpace)
    (w : W) (t₁ t₂ : T)
    (hDynamic : dynamicProjection projects d charVP w t₁ ≠
                dynamicProjection projects d charVP w t₂) :
    travelingShotCondition projects d charVP w :=
  ⟨t₁, t₂, hDynamic⟩

end EndToEnd

-- ════════════════════════════════════════════════════════════════
-- § Empirical Paradigms
-- ════════════════════════════════════════════════════════════════

/-- An acceptability judgment on a 7-point scale. -/
structure Judgment where
  score : Float
  numSessions : Nat
  deriving Repr

/-- A paradigm condition: classifier direction + Role Shift status. -/
structure Condition where
  classifierDirection : ClassifierDirection
  roleShiftStatus : RoleShiftStatus
  judgment : Judgment
  deriving Repr

/-- Paradigm (7): POLE-cl moving past signer. Ann driving drunk,
    nearly hits pole. Direction determines which side she nearly hits.
    No strict Role Shift (no body rotation). -/
def paradigm7 : List Condition :=
  [ { classifierDirection := .passingRight,
      roleShiftStatus := .broad,
      judgment := ⟨7, 3⟩ },
    { classifierDirection := .passingLeft,
      roleShiftStatus := .broad,
      judgment := ⟨7, 3⟩ } ]

/-- Paradigm (13): TREE-cl moving past signer. Ann runs past a tree.
    Direction determines which side the tree passes on.
    No strict Role Shift. -/
def paradigm13 : List Condition :=
  [ { classifierDirection := .passingLeft,
      roleShiftStatus := .broad,
      judgment := ⟨7, 3⟩ },
    { classifierDirection := .passingRight,
      roleShiftStatus := .broad,
      judgment := ⟨6.3, 3⟩ } ]

/-- Paradigm (19): Role-shifted version of (7). Strict Role Shift
    (body rotation). Same interpretive effect. -/
def paradigm19 : List Condition :=
  [ { classifierDirection := .passingRight,
      roleShiftStatus := .strict,
      judgment := ⟨7, 3⟩ },
    { classifierDirection := .passingLeft,
      roleShiftStatus := .strict,
      judgment := ⟨7, 3⟩ } ]

/-- Paradigm (7) instantiates the traveling shot: pole is static,
    classifier moves, motion type is relative. -/
def paradigm7_travelingShot : TravelingShotEffect where
  objectClass := "pole"
  classifierDirection := .passingRight
  motionType := .relative
  classifierDirection_isDynamic := rfl
  motionType_isRelative := rfl

/-- Paradigm (13) instantiates the traveling shot: tree is static,
    classifier moves, motion type is relative. -/
def paradigm13_travelingShot : TravelingShotEffect where
  objectClass := "tree"
  classifierDirection := .passingLeft
  motionType := .relative
  classifierDirection_isDynamic := rfl
  motionType_isRelative := rfl

/-- The traveling shot arises both with and without strict Role Shift. -/
theorem travelingShot_with_and_without_RS :
    (paradigm7.head?.map (·.roleShiftStatus)) = some .broad ∧
    (paradigm19.head?.map (·.roleShiftStatus)) = some .strict :=
  ⟨rfl, rfl⟩

/-- The classifier used in paradigm (7) is POLE-cl from the ASL fragment. -/
theorem paradigm7_uses_poleCl
    (proj : Fragments.ASL.Entity → StaticViewpoint SigningSpace → Bool) :
    (Fragments.ASL.poleCl proj).label = "POLE-cl" := rfl

/-- The classifier used in paradigm (13) is TREE-cl from the ASL fragment. -/
theorem paradigm13_uses_treeCl
    (proj : Fragments.ASL.Entity → StaticViewpoint SigningSpace → Bool) :
    (Fragments.ASL.treeCl proj).label = "TREE-cl" := rfl

end SchlenkerEtAl2026
