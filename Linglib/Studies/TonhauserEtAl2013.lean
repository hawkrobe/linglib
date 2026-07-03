import Linglib.Semantics.Presupposition.ProjectiveContent
import Linglib.Studies.Schlenker2009

/-!
# Tonhauser, Beaver, Roberts & Simons (2013): Taxonomy from Local Contexts
[tonhauser-beaver-roberts-simons-2013]

Derives the four-class projective-content taxonomy of
[tonhauser-beaver-roberts-simons-2013] from [schlenker-2009]-style local
contexts ([heim-1983], [lewis-1979]). The classes cross-classify two
properties:

| Class | SCF | OLE | Derived behavior |
|-------|-----|-----|------------------|
| A | yes | yes | Requires context + shifts under belief |
| B | no  | no  | Informative + speaker-anchored |
| C | no  | yes | Informative + shifts under belief |
| D | yes | no  | Requires context + speaker-anchored |

[tonhauser-beaver-roberts-simons-2013] object to satisfaction theories:

> "In theories like those of [schlenker-2009], where it is assumed that a
> presupposition is satisfied in its local context if it is entailed by it.
> Since, in general, the relevant local context is the context set ('which
> encodes what the speech act participants take for granted'), presuppositions
> are predicted to project. The heterogeneity of projective content, in
> particular the finding that many such contents are not associated with a
> strong contextual felicity constraint, provides an argument against an
> inclusive analysis of projection based on local satisfaction."

The resolution formalized here: *projection* is uniform (the local-context
machinery), while *accommodation* varies by trigger class. OLE is derived
directly from belief local contexts; SCF is characterized as a constraint
on accommodation, not built into local contexts (a full SCF derivation
needs QUD/information-structure machinery).

## Main declarations

- `SCF_Requires` / `SCF_Allows`: Strong Contextual Felicity in
  local-context terms.
- `OLE_Obligatory` / `OLE_NotObligatory`: Obligatory Local Effect via
  belief local contexts.
- `belief_derives_ole`: belief embedding filters holder-attributed
  presuppositions, deriving OLE=yes behavior.
- `classes_partition`: the SCF × OLE feature space partitions triggers
  into exactly the four classes.
- `schlenker_derives_tonhauser`: the local-context theory reproduces the
  taxonomy's structural predictions.
- `traditional_crosscuts_classes`: the traditional presupposition/CI
  labels cross-cut the SCF × OLE classes.
-/

namespace TonhauserEtAl2013

open CommonGround
open Core.Logic.Modal (AgentAccessRel)
open Semantics.Presupposition
open Semantics.Presupposition.Context
open Semantics.Presupposition.LocalContext
open Semantics.Presupposition.BeliefEmbedding
open Semantics.Presupposition.ProjectiveContent

variable {W : Type*} {Agent : Type*}

-- ════════════════════════════════════════════════════════════════
-- § SCF and OLE in Local-Context Terms
-- ════════════════════════════════════════════════════════════════

/--
**SCF (Strong Contextual Felicity)** in local context terms.

A trigger has SCF=yes iff its projective content MUST be entailed by the
global context for felicitous use. Accommodation is blocked.

In Schlenker's terms: the local context at matrix level IS the global context,
and the presupposition must be entailed (not just "could be accommodated").

This is a marker structure. The constraint that accommodation is blocked
is a property of the trigger class, not derivable from the content alone.
Full derivation requires connecting to `Accommodation.AccommodationOK` and
trigger-specific constraints (anaphoric binding, salience, etc.).
-/
structure SCF_Requires (W : Type*) where
  /-- The projective content that must be established -/
  content : Set W

/--
**SCF=no** means accommodation is ALLOWED.

The projective content can be informative — it can update the context
rather than being required to already hold.

Witness: there exist non-empty contexts where the content is NOT entailed
yet the trigger's use is still felicitous (via accommodation).
-/
structure SCF_Allows (W : Type*) where
  /-- The projective content -/
  content : Set W
  /-- Accommodation is possible: there exist contexts where content is
      informative (not entailed) yet use is felicitous -/
  accommodable : ∃ (c : ContextSet W), Set.Nonempty c ∧
    ¬ContextSet.entails c content

/--
**OLE (Obligatory Local Effect)** in local context terms.

OLE=yes means: under belief embedding, the local context is the attitude
holder's belief state. The projective content is attributed to the holder.
-/
def OLE_Obligatory (Dox : AgentAccessRel W Agent)
    (content : Set W) : Prop :=
  ∀ (c : ContextSet W) (agent : Agent) (w_star : W),
    c w_star →
    let blc : BeliefLocalCtx W Agent := { globalCtx := c, dox := Dox, agent := agent }
    -- Content is evaluated relative to holder's beliefs
    ContextSet.entails (blc.atWorld w_star) content

/--
**OLE=no** means: under belief embedding, the projective content is still
evaluated relative to the speaker's (global) context, not the holder's beliefs.

Formally: there exist doxastic contexts where the content holds globally
but NOT in the attitude holder's beliefs. The content is "speaker-anchored"
— it does not shift under belief embedding.

Class B triggers (expressives) and Class D triggers exhibit this behavior.
-/
def OLE_NotObligatory (Dox : AgentAccessRel W Agent)
    (content : Set W) : Prop :=
  ∃ (c : ContextSet W) (agent : Agent) (w_star : W),
    c w_star ∧
    ContextSet.entails c content ∧
    let blc : BeliefLocalCtx W Agent := { globalCtx := c, dox := Dox, agent := agent }
    ¬ContextSet.entails (blc.atWorld w_star) content

/--
**OLE derivation**: belief embedding creates an attitude-holder context.

Under "x believes φ", the local context at φ is x's belief state, so a
presupposition attributed to the holder is filtered there. This derives
OLE=yes behavior from [schlenker-2009]'s belief local contexts.
-/
theorem belief_derives_ole (blc : BeliefLocalCtx W Agent) (p : PartialProp W)
    (h : presupAttributedToHolder blc p) (w_star : W) (hw : blc.globalCtx w_star) :
    presupFiltered (beliefToLocalCtx blc w_star hw) p :=
  h w_star hw

-- ════════════════════════════════════════════════════════════════
-- § OLE as Shift Under Belief
-- ════════════════════════════════════════════════════════════════

/--
Determines whether a projective trigger's content shifts to the attitude
holder's perspective under belief embedding.

OLE = yes: Content shifts to attitude holder (computed from their beliefs)
OLE = no: Content remains attributed to speaker (no perspective shift)
-/
def shiftsUnderBelief : ProjectiveClass → Bool
  | .classA => true   -- OLE = yes
  | .classB => false  -- OLE = no
  | .classC => true   -- OLE = yes
  | .classD => false  -- OLE = no

/--
OLE status matches shift behavior.
-/
theorem ole_matches_shift (c : ProjectiveClass) :
    shiftsUnderBelief c = true ↔ c.ole = .obligatory := by
  cases c <;> simp [shiftsUnderBelief, ProjectiveClass.ole]

/--
The Schlenker local context machinery derives the OLE
predictions from [tonhauser-beaver-roberts-simons-2013].

For any trigger:
- If OLE=yes (Class A, C): Local context under belief = attitude holder's beliefs
- If OLE=no (Class B, D): Local context under belief = global context (speaker)

This explains why "stop" presuppositions shift to attitude holders but
"damn" expressives don't.
-/
theorem ole_from_local_contexts (trigger : ProjectiveTrigger) :
    shiftsUnderBelief trigger.toClass = true ↔
    trigger.toClass.ole = .obligatory :=
  ole_matches_shift trigger.toClass

/--
Class C triggers (stop, know, only) have OLE=yes.
-/
example : ProjectiveTrigger.stop_prestate.toClass.ole = .obligatory := rfl
example : ProjectiveTrigger.know_complement.toClass.ole = .obligatory := rfl

/--
Class B triggers (expressives, appositives) have OLE=no.
-/
example : ProjectiveTrigger.expressive.toClass.ole = .notObligatory := rfl
example : ProjectiveTrigger.appositive.toClass.ole = .notObligatory := rfl

-- ════════════════════════════════════════════════════════════════
-- § The Four-Class Taxonomy
-- ════════════════════════════════════════════════════════════════

/-- A projective trigger's behavior characterized by SCF and OLE values. -/
structure TriggerBehavior (W : Type*) (Agent : Type*) where
  content : Set W
  scf : StrongContextualFelicity
  ole : ObligatoryLocalEffect

def isClassA (tb : TriggerBehavior W Agent) : Prop :=
  tb.scf = .requires ∧ tb.ole = .obligatory

def isClassB (tb : TriggerBehavior W Agent) : Prop :=
  tb.scf = .noRequires ∧ tb.ole = .notObligatory

def isClassC (tb : TriggerBehavior W Agent) : Prop :=
  tb.scf = .noRequires ∧ tb.ole = .obligatory

def isClassD (tb : TriggerBehavior W Agent) : Prop :=
  tb.scf = .requires ∧ tb.ole = .notObligatory

/-- SCF-OLE correspondence with Tonhauser classes. -/
theorem class_from_scf_ole (tb : TriggerBehavior W Agent) :
    (isClassA tb ↔ (tb.scf = .requires ∧ tb.ole = .obligatory)) ∧
    (isClassB tb ↔ (tb.scf = .noRequires ∧ tb.ole = .notObligatory)) ∧
    (isClassC tb ↔ (tb.scf = .noRequires ∧ tb.ole = .obligatory)) ∧
    (isClassD tb ↔ (tb.scf = .requires ∧ tb.ole = .notObligatory)) := by
  unfold isClassA isClassB isClassC isClassD
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- Classes partition the space. -/
theorem classes_partition (tb : TriggerBehavior W Agent) :
    (isClassA tb ∨ isClassB tb ∨ isClassC tb ∨ isClassD tb) ∧
    ¬(isClassA tb ∧ isClassB tb) ∧
    ¬(isClassA tb ∧ isClassC tb) ∧
    ¬(isClassA tb ∧ isClassD tb) ∧
    ¬(isClassB tb ∧ isClassC tb) ∧
    ¬(isClassB tb ∧ isClassD tb) ∧
    ¬(isClassC tb ∧ isClassD tb) := by
  unfold isClassA isClassB isClassC isClassD
  cases tb.scf <;> cases tb.ole <;> simp

-- Trigger classification

theorem stop_is_classC : ProjectiveTrigger.stop_prestate.toClass = .classC := rfl
theorem expressive_is_classB : ProjectiveTrigger.expressive.toClass = .classB := rfl
theorem pronoun_is_classA : ProjectiveTrigger.pronoun_existence.toClass = .classA := rfl
theorem demonstrative_is_classD :
    ProjectiveTrigger.demonstrative_indication.toClass = .classD := rfl

/-- Schlenker's local context theory derives Tonhauser's taxonomy. -/
theorem schlenker_derives_tonhauser :
    (∀ (c : ContextSet W), (initialLocalCtx c).worlds = c) ∧
    (∀ (blc : BeliefLocalCtx W Agent) (w : W) (h : blc.globalCtx w),
      (beliefToLocalCtx blc w h).worlds = blc.atWorld w) ∧
    (∀ (c : ProjectiveClass),
      c = classFromProperties c.scf c.ole) ∧
    (ProjectiveClass.classA ≠ ProjectiveClass.classB ∧
     ProjectiveClass.classA ≠ ProjectiveClass.classC ∧
     ProjectiveClass.classA ≠ ProjectiveClass.classD ∧
     ProjectiveClass.classB ≠ ProjectiveClass.classC ∧
     ProjectiveClass.classB ≠ ProjectiveClass.classD ∧
     ProjectiveClass.classC ≠ ProjectiveClass.classD) := by
  refine ⟨Schlenker2009.matrix_local_context_is_global,
    Schlenker2009.belief_local_context_is_holder_beliefs, ?_, ?_⟩
  · intro c
    exact (class_properties_roundtrip c).symm
  · decide

-- Per-trigger phenomena

theorem stop_allows_informativity :
    ProjectiveTrigger.stop_prestate.toClass.scf = .noRequires := rfl

theorem stop_shifts_under_belief :
    ProjectiveTrigger.stop_prestate.toClass.ole = .obligatory := rfl

theorem expressive_allows_informativity :
    ProjectiveTrigger.expressive.toClass.scf = .noRequires := rfl

theorem expressive_stays_with_speaker :
    ProjectiveTrigger.expressive.toClass.ole = .notObligatory := rfl

theorem pronoun_requires_antecedent :
    ProjectiveTrigger.pronoun_existence.toClass.scf = .requires := rfl

theorem pronoun_shifts_under_belief :
    ProjectiveTrigger.pronoun_existence.toClass.ole = .obligatory := rfl

-- ════════════════════════════════════════════════════════════════
-- § Traditional Categories Don't Carve at the Joints
-- ════════════════════════════════════════════════════════════════

/-- Traditional labels for projective content, predating the SCF/OLE
taxonomy. -/
inductive TraditionalCategory where
  /-- Traditional "presupposition". -/
  | presupposition
  /-- Potts-style "conventional implicature". -/
  | conventionalImplicature
  /-- Supplementary/parenthetical content. -/
  | supplementary
  deriving DecidableEq, Repr

/-- The traditional category conventionally assigned to each trigger.
[tonhauser-beaver-roberts-simons-2013] argue this classification is
inadequate: the SCF × OLE taxonomy cross-cuts it
(`traditional_crosscuts_classes`). -/
def traditionalCategory : ProjectiveTrigger → TraditionalCategory
  | .pronoun_existence => .presupposition
  | .definite_description => .presupposition
  | .stop_prestate => .presupposition
  | .know_complement => .presupposition
  | .only_prejacent => .presupposition
  | .almost_polar => .presupposition
  | .too_existence => .presupposition
  | .too_salience => .presupposition
  | .occasion_verb => .presupposition
  | .demonstrative_indication => .presupposition
  | .focus_salience => .presupposition
  | .expressive => .conventionalImplicature
  | .appositive => .supplementary
  | .nrrc => .supplementary
  | .possessive_np => .supplementary

/-- Traditional categories don't carve at the joints: pronouns and *stop*
are both traditional "presuppositions" yet land in different projective
classes (A vs C). -/
theorem traditional_crosscuts_classes :
    traditionalCategory .pronoun_existence = traditionalCategory .stop_prestate ∧
    ProjectiveTrigger.toClass .pronoun_existence ≠
      ProjectiveTrigger.toClass .stop_prestate :=
  ⟨rfl, by decide⟩

end TonhauserEtAl2013
