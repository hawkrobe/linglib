import Linglib.Theories.Semantics.TypeTheoretic.Core

/-!
# Chatzikyriakidis & Luo (2020): MTT subsumptive subtyping for typed composition
@cite{chatzikyriakidis-luo-2020}

Modern Type Theory (MTT) analysis where common nouns denote *types*
rather than predicates, and selectional restrictions are enforced
through *subsumptive subtyping*. Verb meanings are partial functions
restricted to argument types; composition through `restrict` succeeds
only when a `SubtypeOf` instance is in scope; without one, the
composition fails to typecheck (the formal counterpart of a category
mistake).

## Main definitions

* Toy ontology with `Human ⊑ Animate ⊑ Entity`, `Animal ⊑ Animate`,
  `PhysObj ⊑ Entity`, `Info ⊑ Entity` and their composite-subsumption
  derivations.
* `restrict`: typed-composition operator (apply `P : Ppty B` to an
  `a : A` via `SubtypeOf A B`).
* Witness theorems exercising each `SubtypeOf` instance — removing any
  instance breaks the corresponding theorem at the type level.

## References

* @cite{chatzikyriakidis-luo-2020} ch. 2–4 (MTT subsumptive subtyping;
  common nouns as types; typed selectional restrictions).
-/

namespace ChatzikyriakidisLuo2020

open Semantics.TypeTheoretic (Ppty Quant IsTrue IsFalse SubtypeOf
  subtypeTrans semPropName semIndefArt ExistWitness)

/-! ### Toy ontology

Human ⊑ Animate ⊑ Entity, Animal ⊑ Animate, PhysObj ⊑ Entity,
Info ⊑ Entity. -/

inductive Human where | john | mary
  deriving DecidableEq, Repr

inductive Animal where | fido
  deriving DecidableEq, Repr

inductive Animate where
  | human : Human → Animate
  | animal : Animal → Animate
  deriving DecidableEq, Repr

inductive PhysObj where | table | book
  deriving DecidableEq, Repr

inductive Info where | hamletInfo
  deriving DecidableEq, Repr

inductive Entity where
  | animate : Animate → Entity
  | physObj : PhysObj → Entity
  | info : Info → Entity
  deriving DecidableEq, Repr

instance instHumanAnimate : SubtypeOf Human Animate where up := .human
instance instAnimalAnimate : SubtypeOf Animal Animate where up := .animal
instance instAnimateEntity : SubtypeOf Animate Entity where up := .animate
instance instPhysObjEntity : SubtypeOf PhysObj Entity where up := .physObj
instance instInfoEntity : SubtypeOf Info Entity where up := .info

/-- Composite: Human ⊑ Entity via Human ⊑ Animate ⊑ Entity. -/
instance instHumanEntity : SubtypeOf Human Entity :=
  subtypeTrans (T₂ := Animate)

/-- Composite: Animal ⊑ Entity. -/
instance instAnimalEntity : SubtypeOf Animal Entity :=
  subtypeTrans (T₂ := Animate)

/-! ### Typed-composition operator -/

/-- `restrict P` coerces an `a : A` to `B` (via `SubtypeOf A B`) and
    applies `P : Ppty B`. The semantic counterpart of typed function
    application under subsumptive subtyping. If no `SubtypeOf` instance
    exists, the composition fails at the type level — a category
    mistake, not a truth-value failure. -/
def restrict {A B : Type} [h : SubtypeOf A B] (P : Ppty B) : Ppty A :=
  fun a => P (h.up a)

/-! ### Selectional restrictions as types -/

/-- "laugh" selects for `Animate`. -/
def laughs : Ppty Animate
  | .human .john => Unit
  | .human .mary => Empty
  | .animal .fido => Unit

/-- "think" selects for `Human`. -/
def thinks : Ppty Human
  | .john => Unit
  | .mary => Unit

/-- "fall" accepts any `Entity`. -/
def falls : Ppty Entity
  | .animate (.human .john) => Unit
  | .animate (.human .mary) => Empty
  | .animate (.animal .fido) => Unit
  | .physObj _ => Unit
  | .info _ => Empty

theorem john_laughs : IsTrue ((restrict laughs : Ppty Human) .john) := ⟨()⟩
theorem mary_doesnt_laugh : IsFalse ((restrict laughs : Ppty Human) .mary) := ⟨nofun⟩
theorem fido_laughs : IsTrue ((restrict laughs : Ppty Animal) .fido) := ⟨()⟩
theorem john_falls : IsTrue ((restrict falls : Ppty Human) .john) := ⟨()⟩
theorem table_falls : IsTrue ((restrict falls : Ppty PhysObj) .table) := ⟨()⟩
theorem info_doesnt_fall :
    IsFalse ((restrict falls : Ppty Info) .hamletInfo) := ⟨nofun⟩

/- No `SubtypeOf PhysObj Animate`: `restrict laughs : Ppty PhysObj` fails
   to synthesize. No `SubtypeOf Animal Human`: `restrict thinks : Ppty Animal`
   fails. The absence of the instance IS the selectional restriction. -/

/-! ### Compositional derivations with typed NPs -/

def johnQ : Quant Human := semPropName .john
def fidoQ : Quant Animal := semPropName .fido
def aHumanWhoThinks : Quant Human := semIndefArt thinks

/-- "John laughs" composes via `instHumanAnimate`. -/
def johnLaughsDeriv : Type := johnQ (restrict laughs)
theorem john_laughs_deriv : IsTrue johnLaughsDeriv := ⟨()⟩

/-- "Fido laughs" composes via `instAnimalAnimate`. -/
def fidoLaughsDeriv : Type := fidoQ (restrict laughs)
theorem fido_laughs_deriv : IsTrue fidoLaughsDeriv := ⟨()⟩

/-- "A human who thinks laughs": the indefinite quantifier requires a
    Human who both thinks (restrictor) and laughs (scope, via
    coercion through `instHumanAnimate`). -/
def aThinkingHumanLaughs : Type := aHumanWhoThinks (restrict laughs)
theorem a_thinking_human_laughs : IsTrue aThinkingHumanLaughs :=
  ⟨⟨.john, (), ()⟩⟩

/-- Coercion coherence: direct Human ⊑ Entity and chained Human ⊑
    Animate ⊑ Entity produce the same result (subsumption commutes). -/
theorem coercion_coherence (P : Ppty Entity) (h : Human) :
    restrict P h = restrict (restrict P : Ppty Animate) h := rfl

end ChatzikyriakidisLuo2020
