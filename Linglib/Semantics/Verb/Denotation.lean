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

/-! ### Change-of-state decomposition ([beavers-koontz-garboden-2020] §1.3.2)

For a change-of-state verb the opaque lexical core unpacks into the
event-structural decomposition of [beavers-koontz-garboden-2020] (22)–(24): a
root denotes a *state* predicate `⟦√V⟧(x,s)`, and the verb's event predicate is
built by the templatic operators `become'` and `cause'`. The root's
`kinds` selects which operators apply — `.result` → `become`,
`.cause` → `cause`/`effector` — so the decomposition is the denotational payoff
of the root's kinds. -/

/-- The change-of-state model ([beavers-koontz-garboden-2020] (22)): the
    templatic primitives a COS verb's denotation is built from. `become`/`cause`/
    `effector` are model primitives here (BKG refine their truth conditions in
    their §1.6); a Study instantiates them. -/
structure Verb.CosModel (Entity State Time : Type*) [LinearOrder Time] where
  /-- `⟦√V⟧(x,s)` (BKG (22a)): a state `s` of the root's lexical property holds of
      `x` (e.g. `flat'(x,s)`). The root denotes a state predicate. -/
  rootState : Verb → Entity → State → Prop
  /-- `become'(s,e)` (BKG (22b)): event `e` gives rise to state `s`. -/
  become : State → Event Time → Prop
  /-- `cause'(v,e)` (BKG (22c)): event `v` causes event `e`. -/
  cause : Event Time → Event Time → Prop
  /-- `effector'(y,v)` (BKG (22c)): `y` is the effector of event `v`. -/
  effector : Entity → Event Time → Prop
  /-- The bare manner/activity core `⟦√V⟧(e)` of a pure-manner root (no change),
      e.g. `jog`/`run`'s action specification. -/
  manner : Verb → Event Time → Prop

namespace Verb.CosModel

variable {Entity State Time : Type*} [LinearOrder Time]

/-- The inchoative denotation ([beavers-koontz-garboden-2020] (23c)):
    `λxλe. ∃s. become'(s,e) ∧ ⟦√V⟧(x,s)` — an event of change giving rise to a
    state of the root's property holding of the patient `x`. -/
def inchoative (M : CosModel Entity State Time) (v : Verb) (x : Entity) :
    Event Time → Prop :=
  fun e => ∃ s, M.become s e ∧ M.rootState v x s

/-- The causative denotation ([beavers-koontz-garboden-2020] (24c)): the
    inchoative embedded under an effector and a causing event —
    `λyλxλw. ∃e. effector'(y,w) ∧ cause'(w,e) ∧ inchoative(x)(e)`. -/
def causative (M : CosModel Entity State Time) (v : Verb) (y x : Entity) :
    Event Time → Prop :=
  fun w => ∃ e, M.effector y w ∧ M.cause w e ∧ M.inchoative v x e

/-- BKG's first prediction ([beavers-koontz-garboden-2020] p. 16): the causative
    **entails** the inchoative — there is an event satisfying the inchoative,
    "by simple virtue of" the embedding (∃-projection over the caused event).
    Holds by construction, not stipulation. -/
theorem causative_entails_inchoative (M : CosModel Entity State Time)
    (v : Verb) (y x : Entity) (w : Event Time) (h : M.causative v y x w) :
    ∃ e, M.inchoative v x e := by
  obtain ⟨e, _, _, hinch⟩ := h
  exact ⟨e, hinch⟩

/-- The result-state entailment: the inchoative entails the patient reaches a
    state of the root's property — `∃s. become'(s,e) ∧ ⟦√V⟧(x,s)`. The
    non-cancelable result of a change-of-state root (the *break* vs *hit*
    contrast, [beavers-koontz-garboden-2020] (6)); definitional, hence immediate. -/
theorem inchoative_entails_resultState (M : CosModel Entity State Time)
    (v : Verb) (x : Entity) (e : Event Time) (h : M.inchoative v x e) :
    ∃ s, M.become s e ∧ M.rootState v x s := h

/-- Composing the two predictions: a caused change reaches the root state —
    the causative entails the full result-state condition. -/
theorem causative_entails_resultState (M : CosModel Entity State Time)
    (v : Verb) (y x : Entity) (w : Event Time) (h : M.causative v y x w) :
    ∃ e s, M.become s e ∧ M.rootState v x s := by
  obtain ⟨e, hinch⟩ := M.causative_entails_inchoative v y x w h
  exact ⟨e, hinch⟩

/-- The verb's change-of-state denotation, dispatched on its root's
    `kinds` (cf. [beavers-koontz-garboden-2020] (18)–(19)): `.cause` →
    causative, else `.result` → inchoative, else the bare manner core. The root's
    kinds *select the event template* — the denotational payoff of the signature. -/
def denote (M : CosModel Entity State Time) (v : Verb) (y x : Entity) :
    Event Time → Prop :=
  if LexKind.cause ∈ (v.root.map (·.kinds)).getD ∅ then M.causative v y x
  else if LexKind.result ∈ (v.root.map (·.kinds)).getD ∅ then M.inchoative v x
  else M.manner v

/-- The denotational payoff of a `.result` root: any verb whose root signature
    carries `result` has a denotation entailing the result state — whether the
    root is causative (`.cause`) or inchoative. The
    [beavers-koontz-garboden-2020] non-cancelable result, *derived from the
    signature* rather than stipulated (and absent for a pure-manner root, whose
    `denote` is the manner core). -/
theorem denote_result_entails_resultState (M : CosModel Entity State Time)
    (v : Verb) (y x : Entity) (e : Event Time)
    (hres : LexKind.result ∈ (v.root.map (·.kinds)).getD ∅)
    (h : M.denote v y x e) : ∃ e' s, M.become s e' ∧ M.rootState v x s := by
  unfold denote at h
  by_cases hc : LexKind.cause ∈ (v.root.map (·.kinds)).getD ∅
  · rw [if_pos hc] at h
    exact M.causative_entails_resultState v y x e h
  · rw [if_neg hc, if_pos hres] at h
    exact ⟨e, M.inchoative_entails_resultState v x e h⟩

end Verb.CosModel
