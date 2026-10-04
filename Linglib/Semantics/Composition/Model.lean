module

public import Linglib.Semantics.Composition.Tree
public import Mathlib.ModelTheory.Basic

/-!
# Model-theoretic semantics for type-driven composition

A composition model is a mathlib first-order structure on one entity domain at each world of a
world set. Content words name relation symbols of a signature, and their denotations are read off
the structure through `Structure.RelMap`, as DRT reads off the truth of atomic conditions
(`Semantics/Dynamic/DRS/`). Quantifiers, type shifts and world dependence stay in Lean and in the
`.intens` types, so `Tree.interp`, the engine for Heim and Kratzer's type-driven composition,
composes a lexicon read off a model without change.

## Main definitions

* `Model`: an entity domain `E`, worlds `W`, and a structure `interp w` at each world.
* `Model.pred₁`, `Model.pred₂`: the intensional denotations of unary and binary symbols, with
  `Model.const`, `Model.pred₁ext` and `Model.pred₂ext` the extensions at a world.
* `LexNaming`, `Model.lexiconAt`: naming maps into the signature and the lexicon they induce.

## Main results

* `interp_lexiconAt_predication`: over `Model.lexiconAt`, `Tree.interp` composes a name–verb
  predication to the truth value `RelMap` gives.

## Implementation notes

`interp : W → L.Structure E` carries structures as terms rather than instances, since a
world-indexed family of structures on one carrier cannot be instance-based. Instance-based
mathlib API such as `Formula.Realize` then needs `letI := m.interp w`. The concrete model in
`Semantics/Composition/Toy.lean` follows mathlib's concrete-language idiom.

## References

* [heim-kratzer-1998]
-/

@[expose] public section

open FirstOrder Language
open Semantics.Composition
open Semantics.Composition.Tree
open Syntax (Tree)

namespace Semantics.Composition

universe u v

/-- A composition model has a constant entity domain `E`, a world set `W`, and at each world a
first-order `L`-structure interpreting the content signature. -/
structure Model (L : Language.{u, v}) where
  /-- The entity domain is shared by all worlds. -/
  E : Type
  /-- The worlds index the interpretations. -/
  W : Type
  /-- At each world a structure interprets the signature. -/
  interp : W → L.Structure E

variable {L : Language.{u, v}}

/-- The intensional denotation `e ⇒ ⟨s,t⟩` of a unary symbol holds of an entity at a world where
the structure there relates it by the symbol. -/
def Model.pred₁ (m : Model L) (R : L.Relations 1) : Ty.Domain m.E m.W (.e ⇒ .intens .t) :=
  fun x w ↦ (m.interp w).RelMap R (fun _ ↦ x)

/-- The intensional denotation `e ⇒ e ⇒ ⟨s,t⟩` of a binary symbol takes the object first and
the subject second, as transitive verbs do. -/
def Model.pred₂ (m : Model L) (R : L.Relations 2) :
    Ty.Domain m.E m.W (.e ⇒ .e ⇒ .intens .t) :=
  fun y x w ↦ (m.interp w).RelMap R (fun i ↦ if i = 0 then x else y)

/-- The interpretation of a constant at world `w` is the entity the structure there assigns
it. -/
def Model.const (m : Model L) (c : L.Constants) (w : m.W) : Ty.Domain m.E m.W .e :=
  (m.interp w).funMap c default

/-- The extensional denotation `e ⇒ t` of a unary symbol at world `w` is the extension of
`Model.pred₁` there. -/
def Model.pred₁ext (m : Model L) (R : L.Relations 1) (w : m.W) :
    Ty.Domain m.E m.W (.e ⇒ .t) :=
  fun x ↦ (m.interp w).RelMap R (fun _ ↦ x)

/-- The extensional denotation `e ⇒ e ⇒ t` of a binary symbol at world `w` is the extension
of `Model.pred₂` there, object first. -/
def Model.pred₂ext (m : Model L) (R : L.Relations 2) (w : m.W) :
    Ty.Domain m.E m.W (.e ⇒ .e ⇒ .t) :=
  fun y x ↦ (m.interp w).RelMap R (fun i ↦ if i = 0 then x else y)

@[simp] theorem Model.pred₁_apply (m : Model L) (R : L.Relations 1) (x : m.E) (w : m.W) :
    m.pred₁ R x w = m.pred₁ext R w x := rfl

@[simp] theorem Model.pred₂_apply (m : Model L) (R : L.Relations 2) (y x : m.E) (w : m.W) :
    m.pred₂ R y x w = m.pred₂ext R w y x := rfl

/-! ### Lexicon from signature

A fragment supplies naming maps from word forms into the signature, and the model induces the
lexicon, so the denotations are read off `funMap` and `RelMap` rather than stored with the
words. -/

/-- Naming maps send proper names to constants and content words to relation symbols of a
signature. -/
structure LexNaming (L : Language.{u, v}) where
  /-- Proper names denote constants. -/
  names : String → Option L.Constants := fun _ ↦ none
  /-- Common nouns and intransitive verbs denote unary relation symbols. -/
  preds₁ : String → Option (L.Relations 1) := fun _ ↦ none
  /-- Transitive verbs denote binary relation symbols. -/
  preds₂ : String → Option (L.Relations 2) := fun _ ↦ none

/-- The extensional lexicon that naming maps induce at world `w` gives names the
interpretations of their constants at type `e`, unary symbols their extensions at `e ⇒ t`, and
binary symbols their extensions at `e ⇒ e ⇒ t`. -/
def Model.lexiconAt (m : Model L) (nm : LexNaming L) (w : m.W) : Lexicon m.E m.W :=
  fun s ↦
    (nm.names s).map (fun c ↦ ⟨.e, m.const c w⟩) <|>
    (nm.preds₁ s).map (fun R ↦ ⟨.e ⇒ .t, m.pred₁ext R w⟩) <|>
    (nm.preds₂ s).map (fun R ↦ ⟨.e ⇒ .e ⇒ .t, m.pred₂ext R w⟩)

/-- A naming-map lexicon has entries of the three extensional lexical types only. -/
theorem Model.lexiconAt_fst {m : Model L} {nm : LexNaming L} {w : m.W} {s : String}
    {d : Denotation m.E m.W} (h : m.lexiconAt nm w s = some d) :
    d.1 = .e ∨ d.1 = (.e ⇒ .t) ∨ d.1 = (.e ⇒ .e ⇒ .t) := by
  simp only [Model.lexiconAt, Option.orElse_eq_orElse, Option.orElse_eq_or, Option.or_eq_some_iff,
    Option.map_eq_some_iff] at h
  rcases h with ⟨_, -, rfl⟩ | ⟨-, ⟨_, -, rfl⟩ | ⟨-, _, -, rfl⟩⟩ <;> simp

/-! ### Engine integration -/

/-- Over the lexicon of `Model.lexiconAt`, a name–verb predication composes by backward
functional application to the truth value `RelMap` gives at the lexicon's world. -/
theorem interp_lexiconAt_predication (m : Model L) (nm : LexNaming L) (w : m.W)
    (g : Assignment m.E) {s v : String} {c : L.Constants} {R : L.Relations 1}
    (hs : nm.names s = some c) (hv : nm.names v = none) (hv₁ : nm.preds₁ v = some R) :
    interp (m.lexiconAt nm w) g
      (.node () [.terminal () s, .terminal () v] : Tree Unit String)
      = some ⟨.t, (m.interp w).RelMap R (fun _ ↦ m.const c w)⟩ := by
  simp only [interp_node_binary, interp_terminal, Model.lexiconAt, hs, hv, hv₁]
  rfl

end Semantics.Composition
