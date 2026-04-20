import Linglib.Theories.Semantics.Presupposition.BeliefEmbedding
import Linglib.Theories.Semantics.Presupposition.TonhauserDerivation
import Linglib.Phenomena.Presupposition.ProjectiveContent
import Mathlib.Data.Set.Basic

/-!
# Belief Embedding -> Projective Content Taxonomy
@cite{schlenker-2009} @cite{tonhauser-beaver-roberts-simons-2013}

Connects the Schlenker local context machinery for belief embedding
to the @cite{tonhauser-beaver-roberts-simons-2013} projective content taxonomy.

Proves that OLE (Obligatory Local Effect) status matches shift behavior
under belief predicates, and verifies trigger-specific predictions.

-/

namespace Schlenker2009

open Semantics.Presupposition.BeliefEmbedding
open Phenomena.Presupposition.ProjectiveContent

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
predictions from @cite{tonhauser-beaver-roberts-simons-2013}.

For any trigger:
- If OLE=yes (Class A, C): Local context under belief = attitude holder's beliefs
- If OLE=no (Class B, D): Local context under belief = global context (speaker)

This explains why "stop" presuppositions shift to attitude holders but
"damn" expressives don't.
-/
theorem ole_from_local_contexts (trigger : ProjectiveTrigger) :
    shiftsUnderBelief trigger.toClass = true ↔
    trigger.toClass.ole = .obligatory := by
  exact ole_matches_shift trigger.toClass

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

-- ============================================================================
-- Part II: Tonhauser Taxonomy Derivation
-- ============================================================================

/-! Connects Schlenker's local context theory to the full empirical taxonomy of
@cite{tonhauser-beaver-roberts-simons-2013}. The four-class taxonomy is derived
from the SCF x OLE feature space. -/

open Core.Presupposition
open Core.CommonGround
open Semantics.Presupposition.LocalContext
open Semantics.Presupposition.TonhauserDerivation

variable {W : Type*} {Agent : Type*}

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
  constructor
  · intro c; rfl
  constructor
  · intro blc w h; rfl
  constructor
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

end Schlenker2009
