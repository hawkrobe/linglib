import Linglib.Semantics.ArgumentStructure.Thematic.Defs

/-!
# Argument Introduction by Functional Heads

[kratzer-1996] [pylkkanen-2008] [wood-marantz-2017]
[parsons-1990] [moltmann-2025] [hopperdietzel-2024]

Neo-Davidsonian substrate for argument-introducing heads (Voice, applicative,
Cause), built on the canonical `ThematicRel` (`Entity → Event T → Prop`,
[moltmann-2025]: "the preferred version of event semantics for
syntacticians"). A verb/VP denotation is a predicate of events
`Event T → Prop` (this is `Set (Event T)`; used predicatively).

The central new object is `VerbDenot`: a verb denotation classified by the
structure argument introduction is sensitive to (its valency; the finite
positional bookkeeping of who introduces which core position is the sibling
`Valency.lean`). [pylkkanen-2008]'s
high/low contrast is the `IntroMode` parameter — whether the introduced
participant is related to the *event* (high applicative / Voice, via Event
Identification) or to the verb's internal *theme* (low applicative, via a
transfer relation). The transitivity restriction then falls out of the
denotations' types rather than being stipulated, and [wood-marantz-2017]'s
contextually-interpreted single argument-introducer is its `IntroMode` reading.

## Main definitions

* `eventIdentification` — [kratzer-1996]'s Event Identification combinator
* `RolesExclusive` — thematic uniqueness (the principle behind eq. 103)
* `VerbDenot` — verb denotation classified by valence
* `IntroMode` / `IntroMode.Licenses` — high/low introduction and its licensing
* `applToEvent` / `applToTheme` — the high / low applicative denotations
* `causeBieventive` / `causeThetaRole` — the §3.2 Cause-is-not-a-θ-role contrast
-/

namespace ArgumentStructure

variable {Entity : Type*} {T : Type*} [LinearOrder T]

/-! ### Event Identification and thematic uniqueness -/

/-- Event Identification ([kratzer-1996]): combine an argument-introducer
`f` (a thematic relation, awaiting its participant) with a VP predicate `g`,
conjoining at the event. The result still awaits the introduced participant. -/
def eventIdentification (f : ThematicRel Entity T) (g : Event T → Prop) :
    ThematicRel Entity T :=
  fun x e => f x e ∧ g e

theorem eventIdentification_apply (f : ThematicRel Entity T)
    (g : Event T → Prop) (x : Entity) (e : Event T) :
    eventIdentification f g x e ↔ f x e ∧ g e := Iff.rfl

/-- Two thematic relations are role-exclusive when no participant bears both to
the same event (thematic uniqueness). This is the principle behind
[pylkkanen-2008]'s eq. 103: a participant cannot be both agent and theme. -/
def RolesExclusive (r₁ r₂ : ThematicRel Entity T) : Prop :=
  ∀ x e, r₁ x e → ¬ r₂ x e

/-! ### Verb denotations classified by valence -/

/-- A verb/VP denotation, classified by the structure argument introduction is
sensitive to. The valence distinction is a genuine *type* difference, which is
why [pylkkanen-2008]'s transitivity restriction is a fact about this type
rather than a stipulation.

* `unergative` — a saturated event predicate, no internal-argument slot
  (e.g. *run*). [Diagnostic 1 target]
* `transitive` — awaits its internal theme argument, carrying a theme relation
  (e.g. *send a letter*).
* `kimianStative` — a relation over individuals with *no* event argument
  (Kimian state, [moltmann-2025] §1.4.1; e.g. *own*, *owe*). [Diagnostic 2] -/
inductive VerbDenot (Entity : Type*) (T : Type*) [LinearOrder T] where
  | unergative (body : Event T → Prop)
  | transitive (theme : ThematicRel Entity T) (body : ThematicRel Entity T)
  | kimianStative (rel : Entity → Entity → Prop)

namespace VerbDenot

/-- Does this denotation supply an event-internal theme (Davidsonian transitive)?
`unergative` (no participant slot) and `kimianStative` (no event argument) lack
one, for two distinct structural reasons. -/
def IsTransitive : VerbDenot Entity T → Prop
  | .transitive _ _ => True
  | _ => False

instance : DecidablePred (IsTransitive (Entity := Entity) (T := T)) := fun vd =>
  match vd with
  | .transitive _ _ => .isTrue trivial
  | .unergative _ => .isFalse id
  | .kimianStative _ => .isFalse id

end VerbDenot

/-! ### Introduction mode and licensing -/

/-- The semantic mode of an argument introducer: whether it relates the
introduced participant to the *event* (high applicative / Voice, via Event
Identification) or to the verb's internal *theme* (low applicative, via a
transfer relation). This is [pylkkanen-2008]'s high/low contrast at the
denotational level, and [wood-marantz-2017]'s contextually-interpreted
single argument-introducer. -/
inductive IntroMode where
  | toEvent  -- high applicative / Voice
  | toTheme  -- low applicative
  deriving DecidableEq, Repr

/-- Which verb denotations an introducer of this mode can compose with, derived
from the denotation's valence: an event-relating introducer composes with
anything; a theme-relating one needs an event-internal theme. -/
def IntroMode.Licenses : IntroMode → VerbDenot Entity T → Prop
  | .toEvent, _  => True
  | .toTheme, vd => vd.IsTransitive

instance (m : IntroMode) :
    DecidablePred (IntroMode.Licenses m (Entity := Entity) (T := T)) := fun vd => by
  cases m <;> unfold IntroMode.Licenses <;> infer_instance

/-! ### Applicative denotations -/

/-- High applicative / Voice denotation: introduce a participant related to the
EVENT, via Event Identification. Total over any VP predicate — so it composes
with unergatives. -/
def applToEvent (rel : ThematicRel Entity T) (vp : Event T → Prop) :
    ThematicRel Entity T :=
  eventIdentification rel vp

/-- Low applicative denotation: relate the applied argument to the THEME of a
transitive verb via a transfer relation. Requires the verb's internal theme
function `ThematicRel Entity T` (type ⟨e,⟨s,t⟩⟩) — an unergative or Kimian
state cannot supply it. -/
def applToTheme (themeRel : ThematicRel Entity T)
    (transfer : Entity → Entity → Prop) (verb : ThematicRel Entity T)
    (theme applied : Entity) : Event T → Prop :=
  fun e => verb theme e ∧ themeRel theme e ∧ transfer theme applied

/-- Any low-applicative denotation entails the theme bears the theme relation —
the theme conjunct is present by construction. -/
theorem applToTheme_entails_theme (themeRel : ThematicRel Entity T)
    (transfer : Entity → Entity → Prop) (verb : ThematicRel Entity T)
    (theme applied : Entity) (e : Event T)
    (h : applToTheme themeRel transfer verb theme applied e) : themeRel theme e :=
  h.2.1

/-! ### The transitivity restriction, derived -/

/-- High introduction licenses any verb, including unergatives (Luganda/Venda/
Albanian high applicatives over unergatives, [pylkkanen-2008] §2.1.2). -/
theorem toEvent_licenses_all (vd : VerbDenot Entity T) :
    IntroMode.toEvent.Licenses vd := trivial

/-- Diagnostic 1: low (theme-relating) introduction is blocked over an
unergative — it has no event-internal theme. Derived from the valence type,
not stipulated. -/
theorem toTheme_blocks_unergative (body : Event T → Prop) :
    ¬ IntroMode.toTheme.Licenses (VerbDenot.unergative (Entity := Entity) body) :=
  id

/-- Diagnostic 2: low introduction is blocked over a Kimian stative — distinct
reason from Diagnostic 1: no event argument at all ([moltmann-2025]). -/
theorem toTheme_blocks_kimian (rel : Entity → Entity → Prop) :
    ¬ IntroMode.toTheme.Licenses (VerbDenot.kimianStative (T := T) rel) :=
  id

/-- Low introduction is licensed over a Davidsonian transitive (English DOC,
Hebrew possessor datives). -/
theorem toTheme_licenses_transitive (themeRel body : ThematicRel Entity T) :
    IntroMode.toTheme.Licenses (VerbDenot.transitive themeRel body) := trivial

/-- [pylkkanen-2008]'s eq. 103, as a theorem about the denotations:
forcing a low (theme-relating) applicative onto an unergative binds the applied
argument's theme relation to the external argument, yielding `agentRel x e ∧
themeRel x e` for one participant — contradictory under thematic uniqueness.
The transitivity restriction is thus *derived*, not stipulated. -/
theorem low_external_arg_clash
    (agentRel themeRel : ThematicRel Entity T)
    (excl : RolesExclusive agentRel themeRel)
    (x : Entity) (e : Event T)
    (hAgent : agentRel x e) (hTheme : themeRel x e) : False :=
  excl x e hAgent hTheme

/-! ### Cause is not a θ-role ([pylkkanen-2008] Ch. 3 §3.2) -/

/-- Bieventive Cause: the causative head relates the described event to a
causing event, introducing NO individual. `λf.λe. ∃e'. f e' ∧ cause e e'`. -/
def causeBieventive (cause : Event T → Event T → Prop) (caused : Event T → Prop) :
    Event T → Prop :=
  fun e => ∃ e', caused e' ∧ cause e e'

/-- The θ-role analysis [pylkkanen-2008] argues against: Cause introduces a
causer individual. `λx.λe. causer x e ∧ ∃e'. f e' ∧ cause e e'`. -/
def causeThetaRole (cause : Event T → Event T → Prop)
    (causer : ThematicRel Entity T) (caused : Event T → Prop) :
    ThematicRel Entity T :=
  fun x e => causer x e ∧ ∃ e', caused e' ∧ cause e e'

/-- The θ-role analysis forces an external (causer) participant: its denotation
entails `causer x e`. -/
theorem causeThetaRole_forces_causer (cause : Event T → Event T → Prop)
    (causer : ThematicRel Entity T) (caused : Event T → Prop)
    (x : Entity) (e : Event T)
    (h : causeThetaRole cause causer caused x e) : causer x e :=
  h.1

/-- The bieventive analysis admits a causative event with NO external
participant: given only a causing relation to some caused event,
`causeBieventive` holds without any causer. This is the Japanese adversity
causative ([pylkkanen-2008] §3.2.2) the θ-role analysis cannot model. -/
theorem causeBieventive_no_external_arg
    (cause : Event T → Event T → Prop) (caused : Event T → Prop)
    (e e' : Event T) (hc : caused e') (hcause : cause e e') :
    causeBieventive cause caused e :=
  ⟨e', hc, hcause⟩

end ArgumentStructure
