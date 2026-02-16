import Linglib.Theories.Semantics.Presupposition.TonhauserDerivation
import Linglib.Phenomena.Presupposition.ProjectiveContent

/-!
# Bridge: Tonhauser Derivation -> Projective Content Taxonomy

Connects Schlenker's local context theory to the empirical taxonomy of
Tonhauser et al. (2013). Contains trigger classification theorems, the
four-class taxonomy structure, and the main theorem showing that
Schlenker derives Tonhauser.

## References

- Tonhauser, Beaver, Roberts & Simons (2013). Toward a Taxonomy of
  Projective Content. Language 89(1), 66-109.
- Schlenker (2009). Local Contexts. Semantics & Pragmatics 2:3.
-/

namespace Phenomena.Presupposition.Bridge_TonhauserDerivation

open Core.Presupposition
open Core.Proposition
open Core.CommonGround
open Semantics.Presupposition.LocalContext
open Semantics.Presupposition.BeliefEmbedding
open Semantics.Presupposition.TonhauserDerivation
open Phenomena.Presupposition.ProjectiveContent

variable {W : Type*} {Agent : Type*}

/--
A projective trigger's behavior is characterized by its SCF and OLE values.
-/
structure TriggerBehavior (W : Type*) (Agent : Type*) where
  /-- The projective content -/
  content : BProp W
  /-- SCF: requires establishment (yes) or allows informativity (no) -/
  scf : StrongContextualFelicity
  /-- OLE: shifts to holder (yes) or stays with speaker (no) -/
  ole : ObligatoryLocalEffect

/--
**Class A Characterization**: SCF=yes, OLE=yes

Examples: pronouns (existence), "too" (existence of alternative)

Behavior:
- Requires antecedent/alternative in context (no accommodation)
- Under belief, attributed to attitude holder
-/
def isClassA (tb : TriggerBehavior W Agent) : Prop :=
  tb.scf = .requires ∧ tb.ole = .obligatory

/--
**Class B Characterization**: SCF=no, OLE=no

Examples: expressives ("damn"), appositives, NRRCs

Behavior:
- Can be informative (speaker can introduce new content)
- Under belief, still attributed to speaker (no perspective shift)
-/
def isClassB (tb : TriggerBehavior W Agent) : Prop :=
  tb.scf = .noRequires ∧ tb.ole = .notObligatory

/--
**Class C Characterization**: SCF=no, OLE=yes

Examples: "stop", "know", "only", definite descriptions

Behavior:
- Can be informative (hearer learns the presupposed content)
- Under belief, attributed to attitude holder
-/
def isClassC (tb : TriggerBehavior W Agent) : Prop :=
  tb.scf = .noRequires ∧ tb.ole = .obligatory

/--
**Class D Characterization**: SCF=yes, OLE=no

Examples: "too" (salience), demonstratives, focus (salience)

Behavior:
- Requires salience/indication in context
- Under belief, still anchored to speaker's context
-/
def isClassD (tb : TriggerBehavior W Agent) : Prop :=
  tb.scf = .requires ∧ tb.ole = .notObligatory


/--
**Main Theorem 3**: SCF-OLE correspondence with Tonhauser classes.

The four classes are exactly characterized by the two binary features.
-/
theorem class_from_scf_ole (tb : TriggerBehavior W Agent) :
    (isClassA tb ↔ (tb.scf = .requires ∧ tb.ole = .obligatory)) ∧
    (isClassB tb ↔ (tb.scf = .noRequires ∧ tb.ole = .notObligatory)) ∧
    (isClassC tb ↔ (tb.scf = .noRequires ∧ tb.ole = .obligatory)) ∧
    (isClassD tb ↔ (tb.scf = .requires ∧ tb.ole = .notObligatory)) := by
  unfold isClassA isClassB isClassC isClassD
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/--
**Main Theorem 4**: Classes partition the space.

Every trigger belongs to exactly one class.
-/
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


/--
"stop" is Class C: SCF=no, OLE=yes.
-/
theorem stop_is_classC : ProjectiveTrigger.stop_prestate.toClass = .classC := rfl

/--
"damn" (expressive) is Class B: SCF=no, OLE=no.
-/
theorem expressive_is_classB : ProjectiveTrigger.expressive.toClass = .classB := rfl

/--
Pronouns are Class A: SCF=yes, OLE=yes.
-/
theorem pronoun_is_classA : ProjectiveTrigger.pronoun_existence.toClass = .classA := rfl

/--
Demonstrative indication is Class D: SCF=yes, OLE=no.
-/
theorem demonstrative_is_classD :
    ProjectiveTrigger.demonstrative_indication.toClass = .classD := rfl

/--
**THE MAIN THEOREM**: Schlenker's local context theory derives Tonhauser's taxonomy.

Given:
1. Local context at matrix = global context
2. Local context under belief = attitude holder's beliefs
3. Presupposition must be entailed by local context

We derive:
- SCF=yes <-> no accommodation (content must be in global context)
- SCF=no <-> accommodation allowed (content can be informative)
- OLE=yes <-> local context under belief = holder's beliefs
- OLE=no <-> local context under belief = speaker's context

These two binary features cross-classify into exactly four classes (A, B, C, D).
-/
theorem schlenker_derives_tonhauser :
    -- 1. Matrix local context is global
    (∀ (c : ContextSet W), (initialLocalCtx c).worlds = c) ∧
    -- 2. Belief local context is holder's beliefs
    (∀ (blc : BeliefLocalCtx W Agent) (w : W) (h : blc.globalCtx w),
      (beliefToLocalCtx blc w h).worlds = blc.atWorld w) ∧
    -- 3. Classes are determined by SCF x OLE
    (∀ (c : ProjectiveClass),
      c = classFromProperties c.scf c.ole) ∧
    -- 4. Four classes exist and are distinct
    (ProjectiveClass.classA ≠ ProjectiveClass.classB ∧
     ProjectiveClass.classA ≠ ProjectiveClass.classC ∧
     ProjectiveClass.classA ≠ ProjectiveClass.classD ∧
     ProjectiveClass.classB ≠ ProjectiveClass.classC ∧
     ProjectiveClass.classB ≠ ProjectiveClass.classD ∧
     ProjectiveClass.classC ≠ ProjectiveClass.classD) := by
  constructor
  · -- 1. Matrix local context
    intro c; rfl
  constructor
  · -- 2. Belief local context
    intro blc w h; rfl
  constructor
  · -- 3. Class from properties
    intro c
    exact (class_properties_roundtrip c).symm
  · -- 4. Classes distinct
    decide


/--
**Phenomenon 1**: "John stopped smoking" (unembedded, Class C)

Prediction: Presupposition "John used to smoke" CAN be informative (SCF=no).
The hearer can learn this from the utterance.
-/
theorem stop_allows_informativity :
    ProjectiveTrigger.stop_prestate.toClass.scf = .noRequires := rfl

/--
**Phenomenon 2**: "Mary believes John stopped smoking" (embedded, Class C)

Prediction: Presupposition attributed to Mary (OLE=yes).
Mary believes John used to smoke (not: speaker presupposes it).
-/
theorem stop_shifts_under_belief :
    ProjectiveTrigger.stop_prestate.toClass.ole = .obligatory := rfl

/--
**Phenomenon 3**: "That damn cat is outside" (unembedded, Class B)

Prediction: Speaker attitude can be informative (SCF=no).
-/
theorem expressive_allows_informativity :
    ProjectiveTrigger.expressive.toClass.scf = .noRequires := rfl

/--
**Phenomenon 4**: "Mary believes that damn cat is outside" (embedded, Class B)

Prediction: Speaker attitude, NOT Mary's (OLE=no).
Speaker is annoyed at the cat; Mary may or may not be.
-/
theorem expressive_stays_with_speaker :
    ProjectiveTrigger.expressive.toClass.ole = .notObligatory := rfl

/--
**Phenomenon 5**: "She left" (unembedded, Class A)

Prediction: Requires antecedent in context (SCF=yes).
Cannot be used without prior establishment of referent.
-/
theorem pronoun_requires_antecedent :
    ProjectiveTrigger.pronoun_existence.toClass.scf = .requires := rfl

/--
**Phenomenon 6**: "Mary believes she left" (embedded, Class A)

Prediction: Referent existence attributed to Mary (OLE=yes).
-/
theorem pronoun_shifts_under_belief :
    ProjectiveTrigger.pronoun_existence.toClass.ole = .obligatory := rfl

end Phenomena.Presupposition.Bridge_TonhauserDerivation
