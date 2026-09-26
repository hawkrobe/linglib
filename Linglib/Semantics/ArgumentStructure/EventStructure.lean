module

public import Linglib.Semantics.Root.Defs

/-!
# Event structure templates

An event structure template is a term over a small set of primitive predicates: a state, an
action `ACT`, a change `BECOME` and causation `CAUSE`, where `BECOME` and `CAUSE` take templates
as arguments and so build larger templates out of smaller ones ([rappaport-hovav-levin-1998];
[beavers-koontz-garboden-2020]). A verb's meaning pairs a template, which fixes its class, with a
root, which tells it apart from the other members of the class. The basic inventory of
[rappaport-hovav-levin-1998] is the state `[x ⟨STATE⟩]`, the activity `[x ACT⟨MANNER⟩]`, the
achievement `[BECOME [x ⟨STATE⟩]]` and the accomplishment
`[[x ACT⟨MANNER⟩] CAUSE [BECOME [y ⟨STATE⟩]]]`.

The primitives are the four kinds of entailment of the root typology of
[beavers-koontz-garboden-2020], whose collocational restrictions mirror the conditions on
possible templates, so `Template.kinds` reads a template's primitives as a root signature. The
diagnostics `HasCause` and `HasResultState` are membership in it, and a root's template is the
canonical template of its signature.

## Main definitions

* `Template`: the terms, with `Template.achievement` and `Template.accomplishment`
* `Template.kinds`: the kinds of entailment a template's primitives contribute
* `Template.HasCause`, `Template.HasResultState`: the template has `CAUSE`, or `BECOME`
* `Template.causing`, `Template.caused`: the two subevents of a causative template
* `Template.ofKinds`, `Semantics.Root.template`: the canonical template of a signature, and of a
  root

## Implementation notes

`CAUSE` relates a causing subevent to a caused one. The inventory's second accomplishment,
`[x CAUSE [BECOME [y ⟨STATE⟩]]]`, has an individual causer, and is read here as the first, with
an action by the causer as the causing subevent. Participants are not represented: a template is
the shape of an event structure, and the interpretation of its primitives is
`EventStructure.Interpretation`.

## References

* [rappaport-hovav-levin-1998]
* [beavers-koontz-garboden-2020]
-/

@[expose] public section

namespace ArgumentStructure.EventStructure

open Semantics

/-- An event structure template, a term over the primitive predicates. -/
inductive Template where
  /-- `[x ⟨STATE⟩]`. -/
  | state
  /-- `[x ACT⟨MANNER⟩]`, the activity. -/
  | act
  /-- `[BECOME t]`. -/
  | become (t : Template)
  /-- `[causing CAUSE caused]`. -/
  | cause (causing caused : Template)
  deriving DecidableEq, Repr

namespace Template

/-- The achievement `[BECOME [x ⟨STATE⟩]]`. -/
def achievement : Template := become state

/-- The accomplishment `[[x ACT⟨MANNER⟩] CAUSE [BECOME [y ⟨STATE⟩]]]`. -/
def accomplishment : Template := cause act achievement

/-- The kinds of entailment a template's primitives contribute: a state, the manner of an
action, the change of `BECOME` and the causation of `CAUSE`. -/
def kinds : Template → Root.Kinds
  | state => {.state}
  | act => {.manner}
  | become t => insert .result t.kinds
  | cause c e => insert .cause (c.kinds ∪ e.kinds)

/-- The template has `CAUSE`. -/
def HasCause (t : Template) : Prop := Root.Kind.cause ∈ t.kinds

/-- The template has `BECOME`, and so a result state. -/
def HasResultState (t : Template) : Prop := Root.Kind.result ∈ t.kinds

instance (t : Template) : Decidable t.HasCause := inferInstanceAs (Decidable (_ ∈ _))

instance (t : Template) : Decidable t.HasResultState := inferInstanceAs (Decidable (_ ∈ _))

/-- The causing subevent of a causative template. -/
def causing : Template → Option Template
  | cause c _ => some c
  | _ => none

/-- The caused subevent of a causative template. -/
def caused : Template → Option Template
  | cause _ e => some e
  | _ => none

/-! ### The canonical template of a root -/

/-- The canonical template of a kind signature: an accomplishment for a caused change, an
achievement for a change, an activity for a manner, and otherwise a state. -/
def ofKinds (σ : Root.Kinds) : Template :=
  if Root.Kind.cause ∈ σ then accomplishment
  else if Root.Kind.result ∈ σ then achievement
  else if Root.Kind.manner ∈ σ then act
  else state

theorem ofKinds_hasCause_iff (σ : Root.Kinds) : (ofKinds σ).HasCause ↔ Root.Kind.cause ∈ σ := by
  unfold ofKinds
  split_ifs <;> simp_all [HasCause, kinds, accomplishment, achievement]

/-- On a well-formed signature, whose `cause` brings its `result`, the canonical template has a
result state iff the signature has a change. -/
theorem ofKinds_hasResultState_iff {σ : Root.Kinds} (h : σ.WellFormed) :
    (ofKinds σ).HasResultState ↔ Root.Kind.result ∈ σ := by
  have hcr : Root.Kind.cause ∈ σ → Root.Kind.result ∈ σ := h Root.Kind.LE.result_cause
  unfold ofKinds
  split_ifs <;> simp_all [HasResultState, kinds, accomplishment, achievement]

end Template

/-- A root's template, the canonical template of its collocational closure. -/
def _root_.Semantics.Root.template (r : Root) : Template :=
  Template.ofKinds r.closedKinds

/-- A root's template has a result state iff the root entails a change
([beavers-koontz-garboden-2020]'s result entailment). -/
theorem _root_.Semantics.Root.template_hasResultState_iff (r : Root) :
    r.template.HasResultState ↔ Root.Kind.result ∈ r.closedKinds :=
  Template.ofKinds_hasResultState_iff r.closedKinds_wellFormed

end ArgumentStructure.EventStructure
