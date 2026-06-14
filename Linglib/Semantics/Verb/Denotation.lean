import Linglib.Semantics.Verb.Basic
import Linglib.Semantics.ArgumentStructure.Defs
import Linglib.Semantics.ArgumentStructure.Linking

/-!
# Verb denotation — what a verb *does*

A verb is, first of all, an **operation**: applied to its arguments it builds an
event predicate. This file is that operation — the DO layer of the Verb API —
parallel to how the φ substrate models person features as *operations*
(`oplus`/`act` building a partition) rather than predicates.

The verb's classificatory facets (`Verb.ArgStructure`, `Verb.Aspect`, …) are the
**parameters** of this operation: the per-argument `EntailmentProfile`s determine
the theta-grid (`subjectRole`/`objectRole`), and a `Model` supplies the thematic
frame and the lexical core. The denotation is then the neo-Davidsonian
composition `λe. ⟦√V⟧(e) ∧ θ(arg, e) …` — derived, not stipulated.

## Main definitions

* `ThetaRole.toRel` — the theta-role → frame-relation seam (the composer)
* `Verb.Model` — a theory hub: thematic frame + lexical core, over an entity/time
  domain
* `Verb.subjectRole` / `Verb.objectRole` — the theta-grid, derived from the
  effective `EntailmentProfile`s via `EntailmentProfile.toRole`
* `Verb.denote` — the operation: an `ArgFrame` ↦ event predicate

## Main results

* `Verb.denote_transitive` / `Verb.denote_intransitive` — the operation's truth
  conditions: lexical core conjoined with the thematic-role relations its
  theta-grid selects

## References

* [davidson-1967], [parsons-1990] (neo-Davidsonian composition)
* [kratzer-1996] (severed external argument)
* [dowty-1991] (the proto-role profiles that drive the theta-grid)
-/

namespace Semantics.ArgumentStructure

/-- Map a theta-role to the corresponding relation of a thematic frame: the seam
    that lets the verb's theta-grid compose with a model's role relations.
    (Removed in PR #378 as dead; restored here — `Verb.denote` is exactly the
    Verb→ThematicFrame composer it was the seam for.) -/
def ThetaRole.toRel {Entity Time : Type*} [LinearOrder Time]
    (θ : ThetaRole) (frame : ThematicFrame Entity Time) : ThematicRel Entity Time :=
  match θ with
  | .agent       => frame.agent
  | .patient     => frame.patient
  | .theme       => frame.theme
  | .experiencer => frame.experiencer
  | .goal        => frame.goal
  | .source      => frame.source
  | .instrument  => frame.instrument
  | .stimulus    => frame.stimulus

end Semantics.ArgumentStructure

open Semantics.ArgumentStructure
open Semantics.ArgumentStructure.EntailmentProfile (EntailmentProfile)

/-! ### The theory hub and the argument frame -/

/-- A model for verb denotation: the thematic frame (the role relations) and the
    lexical core (`⟦√V⟧ : Event → Prop` per verb). Parameterized by the semantic
    domain; instantiated by Studies. This is CLAUDE.md's "theory-hub denotation". -/
structure Verb.Model (Entity Time : Type*) [LinearOrder Time] where
  /-- The thematic frame: how each role relates entities to events. -/
  frame : ThematicFrame Entity Time
  /-- The lexical core of each verb: its bare event predicate `⟦√V⟧`. -/
  lex : Verb → Event Time → Prop

/-- An assignment of entities to a verb's argument slots. Phase-1 frame: an
    external argument and an optional internal argument. -/
structure ArgFrame (Entity : Type*) where
  /-- The entity in subject position. -/
  subject : Entity
  /-- The entity in object position, if any. -/
  object : Option Entity := none

/-! ### The theta-grid (derived from the proto-role profiles) -/

/-- The subject's theta-role, derived from its effective `EntailmentProfile`
    (verb override, else Levin-class profile) via `EntailmentProfile.toRole`. -/
def Verb.subjectRole (v : Verb) : Option ThetaRole :=
  v.effectiveSubjectEntailments.bind (·.toRole)

/-- The object's theta-role, derived from its effective `EntailmentProfile`. -/
def Verb.objectRole (v : Verb) : Option ThetaRole :=
  v.effectiveObjectEntailments.bind (·.toRole)

/-! ### The operation -/

/-- What a verb DOES: build an event predicate from an argument assignment, in a
    model. Neo-Davidsonian — the lexical core conjoined with one thematic-role
    relation per filled argument slot (vacuous where the theta-grid or the frame
    has no entry). The classificatory facets enter only through `subjectRole` /
    `objectRole`; nothing here is stipulated. -/
def Verb.denote {Entity Time : Type*} [LinearOrder Time]
    (M : Verb.Model Entity Time) (v : Verb) (args : ArgFrame Entity) :
    Event Time → Prop :=
  fun e =>
    M.lex v e
    ∧ (match v.subjectRole with
        | some θ => θ.toRel M.frame args.subject e
        | none => True)
    ∧ (match args.object, v.objectRole with
        | some x, some θ => θ.toRel M.frame x e
        | _, _ => True)

/-! ### The operation's truth conditions -/

/-- A transitive verb whose theta-grid is agent/patient denotes the lexical core
    conjoined with `Agent(subj)` and `Patient(obj)` — the standard
    neo-Davidsonian truth conditions, *derived* from the operation. -/
theorem Verb.denote_transitive {Entity Time : Type*} [LinearOrder Time]
    (M : Verb.Model Entity Time) (v : Verb) (s o : Entity) (e : Event Time)
    (hs : v.subjectRole = some .agent) (ho : v.objectRole = some .patient) :
    v.denote M ⟨s, some o⟩ e ↔
      M.lex v e ∧ M.frame.agent s e ∧ M.frame.patient o e := by
  simp only [Verb.denote, hs, ho, ThetaRole.toRel]

/-- An intransitive use (no object) drops the object conjunct entirely. -/
theorem Verb.denote_intransitive {Entity Time : Type*} [LinearOrder Time]
    (M : Verb.Model Entity Time) (v : Verb) (s : Entity) (e : Event Time)
    (hs : v.subjectRole = some .agent) :
    v.denote M ⟨s, none⟩ e ↔ M.lex v e ∧ M.frame.agent s e := by
  simp only [Verb.denote, hs, ThetaRole.toRel, and_true]

/-- When the theta-grid is empty (no profile data), the denotation is just the
    lexical core — graceful degradation, no spurious conjuncts. -/
theorem Verb.denote_bare {Entity Time : Type*} [LinearOrder Time]
    (M : Verb.Model Entity Time) (v : Verb) (s : Entity) (e : Event Time)
    (hs : v.subjectRole = none) :
    v.denote M ⟨s, none⟩ e ↔ M.lex v e := by
  simp only [Verb.denote, hs, and_true]
