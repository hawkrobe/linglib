import Linglib.Theories.Semantics.TypeTheoretic.Core

/-!
# Selectional Restrictions via Subtyping @cite{sutton-2024}

Makes `SubtypeOf` from `Core.lean` load-bearing by wiring it into
typed composition. Verbs declare the ontological sort they require;
composition through `restrict` succeeds only when `SubtypeOf A B` is
available. Removing a `SubtypeOf` instance breaks the downstream
derivation — that is the "load" the instance bears.

## Key definition

`restrict P : Ppty A` takes a property `P : Ppty B` and a proof
`[SubtypeOf A B]`, returning the property composed with coercion.
This is **typed function application** (Luo 2012, Chatzikyriakidis
& Luo 2020): the argument type must be a subtype of the parameter
type for composition to proceed.

## Complement coercion

When no `SubtypeOf` instance exists but composition should still
succeed, a `ComplementCoercion` provides a *meaning-changing* type
shift. "John enjoyed the book" coerces `PhysObj` to `Event` via
the telic quale (Pustejovsky 1995). Unlike `SubtypeOf`, this
changes what entity is being talked about.

## Connection to SelectionalPreferences.lean

`SelectionalPreferences.lean` implements the *soft* (probabilistic)
tradition of Resnik/Erk: selectional constraints are weighted
preferences over `SemClass`. This file implements the *hard*
(type-theoretic) tradition of Luo/MTT: selectional constraints are
type requirements enforced by the type checker. The bridge between
them: when subtyping succeeds, the soft preference is high; when it
fails, the soft preference is at `selectionalEpsilon` (the coercion/
metaphor residual).

## References

- Luo, Z. (2012). Common Nouns as Types. LACL 2012, LNCS 7351.
- Chatzikyriakidis, S. & Luo, Z. (2020). Formal Semantics in
  Modern Type Theories. Wiley/ISTE.
- Pustejovsky, J. (1995). The Generative Lexicon. MIT Press.
- Sutton, P. (2024). Types and Type Theories. Annual Review of
  Linguistics 10: 347–370.
- Cooper, R. (2023). From Perception to Communication. OUP.
-/

namespace Semantics.TypeTheoretic.Selectional

open Semantics.TypeTheoretic (SubtypeOf subtypeTrans Ppty Quant
  semPropName semIndefArt ExistWitness IsTrue IsFalse propT)

-- ════════════════════════════════════════════════════════════════
-- § 1. Ontological Sorts
-- ════════════════════════════════════════════════════════════════

inductive Human where | john | mary
  deriving DecidableEq, Repr

inductive Animal where | fido
  deriving DecidableEq, Repr

/-- Animate: the union of Human and Animal. Domain of "laugh", "sleep". -/
inductive Animate where
  | human : Human → Animate
  | animal : Animal → Animate
  deriving DecidableEq, Repr

inductive PhysObj where | table | book_phys
  deriving DecidableEq, Repr

inductive Info where | hamlet_info
  deriving DecidableEq, Repr

/-- Top-level entity sort. Everything coerces here. -/
inductive Entity where
  | animate : Animate → Entity
  | physObj : PhysObj → Entity
  | info : Info → Entity
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 2. Subtype Hierarchy
-- ════════════════════════════════════════════════════════════════

/-! Each instance is load-bearing: removing it breaks a named
theorem in §5. The hierarchy:

    Human ⊑ Animate ⊑ Entity
    Animal ⊑ Animate
    PhysObj ⊑ Entity
    Info ⊑ Entity
-/

instance instHumanAnimate : SubtypeOf Human Animate where
  up := .human

instance instAnimalAnimate : SubtypeOf Animal Animate where
  up := .animal

instance instAnimateEntity : SubtypeOf Animate Entity where
  up := .animate

instance instPhysObjEntity : SubtypeOf PhysObj Entity where
  up := .physObj

instance instInfoEntity : SubtypeOf Info Entity where
  up := .info

/-- Composite: Human ⊑ Entity via Human ⊑ Animate ⊑ Entity. -/
instance instHumanEntity : SubtypeOf Human Entity :=
  subtypeTrans (T₂ := Animate)

/-- Composite: Animal ⊑ Entity. -/
instance instAnimalEntity : SubtypeOf Animal Entity :=
  subtypeTrans (T₂ := Animate)

-- ════════════════════════════════════════════════════════════════
-- § 3. Typed Composition
-- ════════════════════════════════════════════════════════════════

/-- Restrict a property to a subtype domain.
Given `P : Ppty B` and `[SubtypeOf A B]`, produce `Ppty A` by coercing
the argument up before applying `P`.

This is **typed function application** (Luo 2012): the semantic
analogue of checking that the argument type is a subtype of the
parameter type. If no `SubtypeOf` instance exists, composition fails
at the Lean type level — a category mistake, not a truth-value failure. -/
def restrict {A B : Type} [h : SubtypeOf A B] (P : Ppty B) : Ppty A :=
  λ a => P (h.up a)

-- ════════════════════════════════════════════════════════════════
-- § 4. Typed Verbs
-- ════════════════════════════════════════════════════════════════

/-- "laugh" selects for Animate. -/
def laughs : Ppty Animate
  | .human .john => Unit
  | .human .mary => Empty
  | .animal .fido => Unit

/-- "think" selects for Human. -/
def thinks : Ppty Human
  | .john => Unit
  | .mary => Unit

/-- "fall" accepts any Entity. -/
def falls : Ppty Entity
  | .animate (.human .john) => Unit
  | .animate (.human .mary) => Empty
  | .animate (.animal .fido) => Unit
  | .physObj _ => Unit
  | .info _ => Empty

-- ════════════════════════════════════════════════════════════════
-- § 5. Per-Instance Verification
-- ════════════════════════════════════════════════════════════════

/-! Each theorem exercises a specific `SubtypeOf` instance. Removing
the instance makes the theorem fail to typecheck — the instance
literally bears the load of the derivation. -/

-- instHumanAnimate: Human can laugh
theorem john_laughs : IsTrue ((restrict laughs : Ppty Human) .john) := ⟨()⟩
theorem mary_doesnt_laugh : IsFalse ((restrict laughs : Ppty Human) .mary) := ⟨nofun⟩

-- instAnimalAnimate: Animal can laugh
theorem fido_laughs : IsTrue ((restrict laughs : Ppty Animal) .fido) := ⟨()⟩

-- instHumanEntity: Human can fall (composite coercion)
theorem john_falls : IsTrue ((restrict falls : Ppty Human) .john) := ⟨()⟩

-- instPhysObjEntity: PhysObj can fall
theorem table_falls : IsTrue ((restrict falls : Ppty PhysObj) .table) := ⟨()⟩

-- instInfoEntity: Info can fall (it can't — empty, but typechecks)
theorem info_doesnt_fall : IsFalse ((restrict falls : Ppty Info) .hamlet_info) := ⟨nofun⟩

-- No SubtypeOf PhysObj Animate: a table cannot laugh.
-- Uncomment to verify the type error:
--   #check (restrict laughs : Ppty PhysObj)
--   → failed to synthesize SubtypeOf PhysObj Animate

-- No SubtypeOf Animal Human: an animal cannot think.
--   #check (restrict thinks : Ppty Animal)
--   → failed to synthesize SubtypeOf Animal Human

-- ════════════════════════════════════════════════════════════════
-- § 6. Compositional Derivations with Typed NPs
-- ════════════════════════════════════════════════════════════════

/-- "john" as a typed quantifier over Human. -/
def johnQ : Quant Human := semPropName .john

/-- "fido" as a typed quantifier over Animal. -/
def fidoQ : Quant Animal := semPropName .fido

/-- "a human who thinks" = typed indefinite with Human restrictor. -/
def aHumanWhoThinks : Quant Human := semIndefArt thinks

/-- "john laughs" = ⟦john⟧(restrict ⟦laugh⟧)
Uses instHumanAnimate to compose Human quantifier with Animate VP. -/
def johnLaughsDeriv : Type := johnQ (restrict laughs)

theorem john_laughs_deriv_true : IsTrue johnLaughsDeriv := ⟨()⟩

/-- "fido laughs" = ⟦fido⟧(restrict ⟦laugh⟧)
Uses instAnimalAnimate. -/
def fidoLaughsDeriv : Type := fidoQ (restrict laughs)

theorem fido_laughs_deriv_true : IsTrue fidoLaughsDeriv := ⟨()⟩

/-- "a human who thinks laughs" = ⟦a human who thinks⟧(restrict ⟦laugh⟧)
Uses instHumanAnimate. The ExistWitness requires a Human who both
thinks (restrictor) and laughs (scope, via coercion). -/
def aThinkingHumanLaughs : Type := aHumanWhoThinks (restrict laughs)

theorem a_thinking_human_laughs : IsTrue aThinkingHumanLaughs :=
  ⟨⟨.john, (), ()⟩⟩

-- ════════════════════════════════════════════════════════════════
-- § 7. Coercion Chain Coherence
-- ════════════════════════════════════════════════════════════════

/-- Direct Human ⊑ Entity and chained Human ⊑ Animate ⊑ Entity
produce the same result. This is the content of the coherence
requirement on subtyping: the diagram commutes. -/
theorem coercion_coherence (P : Ppty Entity) (h : Human) :
    restrict P h = restrict (restrict P : Ppty Animate) h := rfl

-- ════════════════════════════════════════════════════════════════
-- § 8. Complement Coercion
-- ════════════════════════════════════════════════════════════════

/-! Unlike `SubtypeOf` (identity-preserving: a human IS an animate
entity), complement coercion is *meaning-changing*: the coerced entity
is a DIFFERENT thing. "John enjoyed the book" doesn't mean John enjoyed
a physical object — it means he enjoyed *reading* it. The book is
coerced to an event via the telic quale (Pustejovsky 1995).

This is a distinct mechanism from subtyping, and conflating them would
lose the meaning change. -/

inductive Activity where
  | reading : PhysObj → Activity
  | building : PhysObj → Activity
  deriving DecidableEq, Repr

/-- Complement coercion: a meaning-changing type shift triggered by
type mismatch. The `coerce` function produces a new entity in the
target type, not a view of the old one. -/
class ComplementCoercion (A B : Type) where
  coerce : A → B

/-- Telic quale: books coerce to reading events. -/
instance : ComplementCoercion PhysObj Activity where
  coerce := .reading

/-- "enjoy" selects for Activity. -/
def enjoy : Ppty Activity
  | .reading _ => Unit
  | .building _ => Unit

/-- Compose through complement coercion. Structurally parallel to
`restrict` but semantically different: the argument changes identity. -/
def coerceApply {A B : Type} [ComplementCoercion A B]
    (P : Ppty B) : Ppty A :=
  λ a => P (ComplementCoercion.coerce a)

/-- "enjoy the book" via complement coercion. -/
theorem enjoy_book : IsTrue ((coerceApply enjoy : Ppty PhysObj) .book_phys) := ⟨()⟩
theorem enjoy_table : IsTrue ((coerceApply enjoy : Ppty PhysObj) .table) := ⟨()⟩

-- ════════════════════════════════════════════════════════════════
-- § 9. restrict ≠ coerceApply
-- ════════════════════════════════════════════════════════════════

/-! The structural distinction: `restrict` composes with `SubtypeOf.up`
(the argument IS-A member of the supertype), while `coerceApply`
composes with `ComplementCoercion.coerce` (the argument is MAPPED TO
a different entity). Both produce `Ppty A` from `Ppty B`, but the
semantic relationship is different.

Consequence: "John fell" (restrict: John is an entity) and "John
enjoyed the book" (coerceApply: the book became a reading event) are
composed by different mechanisms, and the type system keeps them apart. -/

/-- restrict preserves identity: coercion is a subsumption. -/
theorem restrict_is_subsumption {A B : Type} [h : SubtypeOf A B]
    (P : Ppty B) (a : A) : restrict P a = P (h.up a) := rfl

/-- coerceApply changes identity: coercion is a type-shift. -/
theorem coerceApply_is_shift {A B : Type} [h : ComplementCoercion A B]
    (P : Ppty B) (a : A) : coerceApply P a = P (h.coerce a) := rfl

end Semantics.TypeTheoretic.Selectional
