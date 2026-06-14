import Linglib.Semantics.Verb.Basic
import Linglib.Semantics.ArgumentStructure.Defs
import Linglib.Semantics.ArgumentStructure.Linking
import Linglib.Semantics.Lexical.EventStructure

/-!
# Verb denotation — what a verb *does*

A verb is, first of all, an **operation**: applied to its arguments it builds an
event predicate. This file is that operation — the DO layer of the Verb API —
parallel to how the φ substrate models person features as *operations* rather
than predicates.

For a change-of-state verb the operation is the [beavers-koontz-garboden-2020]
§1.3.2 decomposition (`Verb.CosModel`): a root denotes a state predicate and the
event predicate is built by `become'`/`cause'`, dispatched on the root's `kinds`.
The proto-role theta-grid (`Verb.subjectRole`/`objectRole`, derived from the
effective `EntailmentProfile`s via `EntailmentProfile.toRole`) supplies the
participant roles.

## Main definitions

* `Verb.subjectRole` / `Verb.objectRole` — the theta-grid from the proto-role
  profiles
* `Verb.CosModel` + `inchoative`/`causative`/`denote` — the change-of-state
  denotation, dispatched on the root's `kinds`
* `CosModel.again` + `againRestitutive`/`againRepetitiveBecome`/`againRepetitiveCause`
  — the sublexical *again* operator and its three attachment readings

## Main results

* `CosModel.causative_entails_inchoative`, `denote_result_entails_resultState` —
  the [beavers-koontz-garboden-2020] entailments, *derived* from the root signature
* `CosModel.againPresup_cause_entails_state`, `result_restitution_entails_change`
  — the [beavers-koontz-garboden-2020] (25) reading hierarchy and the result-root
  restitutive collapse, *derived* from the change-of-state entailments

## References

* [davidson-1967], [parsons-1990] (neo-Davidsonian composition)
* [beavers-koontz-garboden-2020] (the change-of-state decomposition; sublexical *again*)
* [von-stechow-1996] (the *again* presupposition analysis adopted in BKG (26))
* [dowty-1991] (the proto-role profiles that drive the theta-grid)
-/

open Semantics.ArgumentStructure
open Semantics.ArgumentStructure.EntailmentProfile (EntailmentProfile)

/-! ### The theta-grid (derived from the proto-role profiles) -/

/-- The subject's theta-role, derived from its effective `EntailmentProfile`
    (verb override, else Levin-class profile) via `EntailmentProfile.toRole`. -/
def Verb.subjectRole (v : Verb) : Option ThetaRole :=
  v.effectiveSubjectEntailments.bind (·.toRole)

/-- The object's theta-role, derived from its effective `EntailmentProfile`. -/
def Verb.objectRole (v : Verb) : Option ThetaRole :=
  v.effectiveObjectEntailments.bind (·.toRole)

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
  if LexKind.cause ∈ v.closedKinds then M.causative v y x
  else if LexKind.result ∈ v.closedKinds then M.inchoative v x
  else M.manner v

/-- The denotational payoff of a `.result` root: any verb whose root signature
    carries `result` has a denotation entailing the result state — whether the
    root is causative (`.cause`) or inchoative. The
    [beavers-koontz-garboden-2020] non-cancelable result, *derived from the
    signature* rather than stipulated (and absent for a pure-manner root, whose
    `denote` is the manner core). -/
theorem denote_result_entails_resultState (M : CosModel Entity State Time)
    (v : Verb) (y x : Entity) (e : Event Time)
    (hres : LexKind.result ∈ v.closedKinds)
    (h : M.denote v y x e) : ∃ e' s, M.become s e' ∧ M.rootState v x s := by
  unfold denote at h
  by_cases hc : LexKind.cause ∈ v.closedKinds
  · rw [if_pos hc] at h
    exact M.causative_entails_resultState v y x e h
  · rw [if_neg hc, if_pos hres] at h
    exact ⟨e, M.inchoative_entails_resultState v x e h⟩

/-- The denotational result entailment **is** the template diagnostic: a verb
    whose root's `EventStructure.Template` embeds a result state has a denotation
    entailing that result state — `denote_result_entails_resultState` and
    `Template.HasResultState` are one fact, through the closed kind signature
    ([beavers-koontz-garboden-2020]; [rappaport-hovav-levin-1998]). -/
theorem denote_result_from_template (M : CosModel Entity State Time)
    (v : Verb) (ht : v.root.template.HasResultState) (y x : Entity) (e : Event Time)
    (h : M.denote v y x e) : ∃ e' s, M.become s e' ∧ M.rootState v x s := by
  refine M.denote_result_entails_resultState v y x e ?_ h
  show LexKind.result ∈ v.root.closedKinds
  exact (Verb.Root.template_hasResultState_iff v.root).mp ht

/-! ### Sublexical *again* — the restitutive/repetitive hierarchy
    ([beavers-koontz-garboden-2020] §1.3.2, exs (25)–(27))

`again` is a presupposition trigger that can attach at three points in the
change-of-state structure — the root, `vbecome`, or `vcause` — yielding the three
readings of *Mary flattened the rug again* in BKG (25): restitutive ("it had been
flat", a prior **state**), repetitive over the change ("it had flattened", a prior
**become** event), and repetitive over the causation ("Mary had flattened it", a
prior **cause** event). BKG (26) (a simplified [von-stechow-1996]) defines
`⟦again⟧ = λPλe. P(e) ∧ ∂∃e′[e′ ≪ e ∧ P(e′)]`: `P` of the eventuality, plus the
presupposition (`∂`) of a strictly earlier `P`-eventuality (`e′ ≪ e`). The reading
hierarchy `(25c) ⊨ (25b) ⊨ (25a)` and the result-root collapse (§2.4, exs
(43)/(45): a result root's state entails its own change, so even root-scope
*again* is repetitive) fall out of the change-of-state entailments above. -/

/-- BKG (26): the sublexical modifier *again*. Given a precedence `≪` (`lt`) on an
    eventuality type `ι` and a predicate `P`, *again* asserts `P e` and presupposes
    a strictly earlier `e′ ≪ e` with `P e′`. Following BKG we do not analyse the
    `∂` operator further — the earlier-eventuality conjunct *is* the presupposition
    (`againPresup`). -/
def again {ι : Type*} (lt : ι → ι → Prop) (P : ι → Prop) (e : ι) : Prop :=
  P e ∧ ∃ e', lt e' e ∧ P e'

/-- The presupposition *again* contributes (BKG (26), the `∂`-marked conjunct):
    a strictly earlier eventuality also satisfying `P`. -/
def againPresup {ι : Type*} (lt : ι → ι → Prop) (P : ι → Prop) (e : ι) : Prop :=
  ∃ e', lt e' e ∧ P e'

theorem again_iff {ι : Type*} (lt : ι → ι → Prop) (P : ι → Prop) (e : ι) :
    again lt P e ↔ P e ∧ againPresup lt P e := Iff.rfl

/-- BKG (27a): *again* attached low, to the root `√V`. The asserted/presupposed
    predicate is the root **state**, so the presupposition is of a strictly
    earlier root-state of the patient — the restitutive reading. -/
def againRestitutive (M : CosModel Entity State Time)
    (ltS : State → State → Prop) (v : Verb) (x : Entity) (s : State) : Prop :=
  again ltS (M.rootState v x) s

/-- BKG (27b): *again* attached to `vbecomeP`. The predicate is the inchoative
    **change** event, so the presupposition is of a strictly earlier change —
    the repetitive-over-change reading. -/
def againRepetitiveBecome (M : CosModel Entity State Time)
    (ltE : Event Time → Event Time → Prop) (v : Verb) (x : Entity)
    (e : Event Time) : Prop :=
  again ltE (M.inchoative v x) e

/-- BKG (27c): *again* attached high, to `vcauseP`. The predicate is the
    causative **causing** event, so the presupposition is of a strictly earlier
    causation — the repetitive-over-causation reading. -/
def againRepetitiveCause (M : CosModel Entity State Time)
    (ltE : Event Time → Event Time → Prop) (v : Verb) (y x : Entity)
    (w : Event Time) : Prop :=
  again ltE (M.causative v y x) w

/-- BKG (25) hierarchy, upper step: the repetitive-causation presupposition (25c,
    "Mary had flattened it before") entails the repetitive-change presupposition
    (25b, "it had flattened before") — the earlier causing event *is* an earlier
    change, by `causative_entails_inchoative`. The `≪`-witness is carried through. -/
theorem againPresup_cause_entails_become (M : CosModel Entity State Time)
    (lt : Event Time → Event Time → Prop) (v : Verb) (y x : Entity)
    (w : Event Time) (h : againPresup lt (M.causative v y x) w) :
    ∃ w', lt w' w ∧ ∃ e, M.inchoative v x e := by
  obtain ⟨w', hlt, hcaus⟩ := h
  exact ⟨w', hlt, M.causative_entails_inchoative v y x w' hcaus⟩

/-- BKG (25) hierarchy, lower step: the repetitive-change presupposition (25b,
    "it had flattened before") entails the restitutive presupposition (25a, "it
    had been flat before") — the earlier change gives rise to an earlier root
    state, by `inchoative_entails_resultState`. -/
theorem againPresup_become_entails_state (M : CosModel Entity State Time)
    (lt : Event Time → Event Time → Prop) (v : Verb) (x : Entity)
    (e : Event Time) (h : againPresup lt (M.inchoative v x) e) :
    ∃ e', lt e' e ∧ ∃ s, M.become s e' ∧ M.rootState v x s := by
  obtain ⟨e', hlt, hinch⟩ := h
  exact ⟨e', hlt, M.inchoative_entails_resultState v x e' hinch⟩

/-- BKG (25) hierarchy, end to end: the repetitive-causation presupposition (25c)
    entails the restitutive presupposition (25a) — "Mary had flattened it before"
    ⊨ "it had been flat before". The two steps composed through the change-of-state
    decomposition (`causative_entails_resultState`). -/
theorem againPresup_cause_entails_state (M : CosModel Entity State Time)
    (lt : Event Time → Event Time → Prop) (v : Verb) (y x : Entity)
    (w : Event Time) (h : againPresup lt (M.causative v y x) w) :
    ∃ w', lt w' w ∧ ∃ e s, M.become s e ∧ M.rootState v x s := by
  obtain ⟨w', hlt, hcaus⟩ := h
  exact ⟨w', hlt, M.causative_entails_resultState v y x w' hcaus⟩

/-- BKG §2.4 (45): for a *result* root the root state itself entails a prior
    change (`∃ become`), so even the low/restitutive attachment of *again* over
    the root carries a change entailment — the restitutive reading collapses into
    the repetitive one ([beavers-koontz-garboden-2020]: "result roots never admit
    truly restitutive readings"). Formally, the restitutive presupposition (an earlier
    state) already delivers an earlier change. The premise `hres` is BKG (45a)'s
    meaning, realized by a root whose `closedKinds` contain `.result` (cf.
    `denote_result_entails_resultState`). -/
theorem result_restitution_entails_change (M : CosModel Entity State Time)
    (ltS : State → State → Prop) (v : Verb) (x : Entity) (s : State)
    (hres : ∀ s, M.rootState v x s → ∃ e, M.become s e)
    (h : againPresup ltS (M.rootState v x) s) :
    ∃ s', ltS s' s ∧ ∃ e, M.become s' e := by
  obtain ⟨s', hlt, hst⟩ := h
  obtain ⟨e, hbec⟩ := hres s' hst
  exact ⟨s', hlt, e, hbec⟩

end Verb.CosModel
