import Linglib.Theories.Semantics.TypeTheoretic.Core

/-!
# Sutton (2024) — Common Nouns as Predicates vs. Types
@cite{sutton-2024}
@cite{chatzikyriakidis-luo-2020} @cite{cooper-2023} @cite{luo-2012}
@cite{pustejovsky-1995}

@cite{sutton-2024} surveys the choice between Montagovian
predicate denotations (`man : Entity → Bool`) and TTR/MTT type
denotations (`Man : Type`, with `a : Man` witnessing manhood). The
choice is not a notational variant: it determines whether selectional
restriction violations are *type errors* or merely *false*, and
whether co-extensional predicates can be intensionally distinguished.

This study file owns both halves of the argument:

- **§1. Bridge** — formal equivalence where Montague and TTR coincide
  (basic extensional predication), via `predToPtype`/`ptypeToPred`.
- **§2. Selectional restrictions as type errors** — Sutton's §4
  argument, demonstrated on a small Animate/Inanimate ontology.
- **§3. Hyperintensionality** — Sutton's §3.1 argument: TTR's `IType`
  preserves intensional distinctions Montague's predicate equality
  collapses (groundhog ≠ woodchuck).
- **§4. Equivalence boundary** — the exact extent of the equivalence.
- **§5. SubtypeOf-bearing typed composition** — Sutton's §4 / Luo's
  MTT direction: subtyping makes `restrict` work, removing instances
  breaks named theorems.
- **§6. Complement coercion** — meaning-changing type shifts
  (telic quale: "enjoy the book" → "enjoy reading the book"),
  contrasted structurally with `restrict`.

This file consolidates the former `TypeTheoretic/CNsAsTypes.lean`
(§§1–4) and `TypeTheoretic/Selectional.lean` (§§5–6), absorbed here
under their shared Sutton-2024 anchor. Neither had any external
consumer beyond this study's argument.

-/

namespace Phenomena.Polysemy.Studies.Sutton2024

open Semantics.TypeTheoretic (PredType Ppty Quant IsTrue IsFalse propT
  SubtypeOf subtypeTrans propExtension IType
  semPropName semIndefArt ExistWitness)

-- ════════════════════════════════════════════════════════════════
-- § 1. The Bridge: Montague predicates ↔ TTR ptypes
-- ════════════════════════════════════════════════════════════════

/-- Lift a Montague predicate `E → Bool` to a TTR ptype `E → Type`.
The resulting type family is inhabited at `e` iff `p e = true`. -/
def predToPtype {E : Type} (p : E → Bool) : PredType E :=
  λ e => propT (p e = true)

/-- Inhabitation of `predToPtype p e` is decidable (since `p e = true` is). -/
instance predToPtype_decidable {E : Type} (p : E → Bool) (e : E) :
    Decidable (Nonempty (predToPtype p e)) :=
  if h : p e = true then isTrue ⟨PLift.up h⟩
  else isFalse (λ ⟨⟨h'⟩⟩ => h h')

/-- Project a TTR ptype back to a Montague predicate.
Requires decidable inhabitation (satisfied by any finite ptype). -/
def ptypeToPred {E : Type} (P : PredType E) [∀ e, Decidable (Nonempty (P e))] :
    E → Bool :=
  λ e => decide (Nonempty (P e))

/-- **Bridge theorem**: Montague predication and TTR type inhabitation
agree when connected by `predToPtype`.

`p e = true ↔ Nonempty (predToPtype p e)` — the predicate holds of `e`
iff the corresponding ptype is inhabited (has a witness). -/
theorem montague_ttr_equiv {E : Type} (p : E → Bool) (e : E) :
    p e = true ↔ Nonempty (predToPtype p e) :=
  ⟨λ h => ⟨PLift.up h⟩, λ ⟨⟨h⟩⟩ => h⟩

/-- The round-trip `ptypeToPred ∘ predToPtype` recovers the original predicate. -/
theorem roundtrip_pred {E : Type} (p : E → Bool) (e : E) :
    @ptypeToPred E (predToPtype p) (λ x => predToPtype_decidable p x) e = p e := by
  unfold ptypeToPred
  cases hp : p e
  · -- p e = false: the ptype is empty
    have : ¬ Nonempty (predToPtype p e) := λ ⟨⟨h⟩⟩ => by rw [hp] at h; exact nomatch h
    exact decide_eq_false this
  · -- p e = true: the ptype is inhabited
    have : Nonempty (predToPtype p e) := ⟨PLift.up hp⟩
    exact decide_eq_true this

/-- TTR `propExtension` coincides with our bridge on lifted predicates. -/
theorem propExtension_agrees {E : Type} (p : E → Bool) (e : E) :
    propExtension (predToPtype p) e ↔ (p e = true) :=
  ⟨λ ⟨⟨h⟩⟩ => h, λ h => ⟨PLift.up h⟩⟩

-- ════════════════════════════════════════════════════════════════
-- § 2. Separation: Selectional Restrictions
-- ════════════════════════════════════════════════════════════════

/-! In Montague's STT, every entity has the same type `e`. A verb like
"laugh" takes any entity and returns `true` or `false`. There is no
structural distinction between a *category mistake* ("the chair laughed")
and *contingent falsity* ("Mary didn't laugh").

In TTR/MTT, verbs can require arguments of specific *types*. "Laugh"
takes `Animate`, not `Entity`. A chair is not `Animate`, so the
predication doesn't compose — it's not false, it's *ill-typed*.

@cite{sutton-2024} §4: "In MTT [...] common nouns are interpreted as types
[...] selectional restrictions are *type* requirements." -/

namespace SelectionalDemo

/-- Ontological sorts (TTR types for entity subclasses). -/
inductive Animate where | john | mary
inductive Inanimate where | chair | rock

/-- In Montague, everything is an Entity. Chairs and people cohabit. -/
inductive FlatEntity where
  | john | mary | chair | rock
  deriving DecidableEq

/-- Montague predicate: laughs is defined on ALL entities. -/
def laughs_montague : FlatEntity → Bool
  | .john => true
  | .mary => false
  | .chair => false
  | .rock => false

/-- In Montague, "the chair laughed" *composes and evaluates to false*.
It's the same kind of thing as "Mary didn't laugh" — both are `false`. -/
theorem montague_chair_laughed : laughs_montague .chair = false := rfl
theorem montague_mary_didnt_laugh : laughs_montague .mary = false := rfl

/-- There's no structural way to distinguish category mistakes from
contingent falsity — both are just `false`. -/
theorem montague_conflates_mistakes :
    laughs_montague .chair = false ∧ laughs_montague .mary = false :=
  ⟨rfl, rfl⟩

/-- TTR predicate: laughs is typed to require `Animate` arguments.
"The chair laughed" doesn't evaluate to false — it doesn't *typecheck*. -/
def laughs_ttr : Animate → Bool
  | .john => true
  | .mary => false

-- In TTR, a chair cannot even be *given* to `laughs_ttr`.
-- The following would be a Lean type error:
--   `#check laughs_ttr Inanimate.chair`
--   — expected `Animate`, got `Inanimate`
-- The types `Animate` and `Inanimate` are disjoint.

/-- In TTR, contingent falsity (Mary doesn't laugh) is well-typed but false.
Category mistakes (chair laughs) don't typecheck at all. The selectional
restriction *prevents composition*, rather than evaluating to `false`. -/
theorem ttr_distinguishes_sorts :
    -- laughs_ttr is defined on a strict subtype of FlatEntity
    -- (2 constructors vs 4) — this IS the selectional restriction
    (∀ a : Animate, ∃ b : Bool, laughs_ttr a = b) ∧
    -- There is no analogous totality statement for Inanimate
    -- (laughs_ttr is not defined on Inanimate at all)
    (∀ e : FlatEntity, ∃ b : Bool, laughs_montague e = b) :=
  ⟨λ _ => ⟨_, rfl⟩, λ _ => ⟨_, rfl⟩⟩

end SelectionalDemo

-- ════════════════════════════════════════════════════════════════
-- § 3. Separation: Hyperintensionality
-- ════════════════════════════════════════════════════════════════

/-! Montague predicates are functions `E → Bool`. Two predicates with
the same extension are *definitionally equal* by `funext`. TTR types
carry intensional identity — two types can have the same witnesses
yet remain distinct.

@cite{sutton-2024} §3.1: "there is nothing which prevents two types from
being associated with exactly the same set of objects." -/

namespace HyperDemo

open SelectionalDemo (FlatEntity)

/-- Two Montague predicates with the same extension are equal. -/
theorem montague_extensional {E : Type} (p q : E → Bool) (h : ∀ e, p e = q e) :
    p = q :=
  funext h

/-- Co-extensional ITypes can be distinct (from TypeTheoretic/Core.lean). -/
example : ∃ T₁ T₂ : IType, T₁.extEquiv T₂ ∧ ¬ T₁.intEq T₂ :=
  ⟨⟨Unit, "groundhog"⟩, ⟨Unit, "woodchuck"⟩,
   ⟨Equiv.refl Unit⟩, by simp [IType.intEq]⟩

/-- The consequence for attitude reports: Montague cannot distinguish
"John believes a groundhog is outside" from "John believes a woodchuck
is outside" — the belief content is the same function. TTR can. -/
theorem montague_collapses_attitudes :
    -- If groundhog and woodchuck have the same extension...
    ∀ (p_groundhog p_woodchuck : FlatEntity → Bool),
      (∀ e, p_groundhog e = p_woodchuck e) →
      -- ...then there is NO attitude verb that distinguishes them
      -- (the predicates are literally equal)
      p_groundhog = p_woodchuck :=
  λ _ _ h => funext h

/-- TTR preserves the distinction: groundhog ≠ woodchuck as ITypes,
even when co-extensional. Attitude verbs can be sensitive to this. -/
theorem ttr_preserves_attitudes :
    let groundhog : IType := ⟨Unit, "groundhog"⟩
    let woodchuck : IType := ⟨Unit, "woodchuck"⟩
    groundhog.extEquiv woodchuck ∧ ¬ groundhog.intEq woodchuck :=
  ⟨⟨Equiv.refl Unit⟩, by simp [IType.intEq]⟩

end HyperDemo

-- ════════════════════════════════════════════════════════════════
-- § 4. When the Two Approaches Coincide
-- ════════════════════════════════════════════════════════════════

/-! For basic extensional predication over a fixed domain without
selectional restrictions or attitude contexts, Montague predicates
and TTR ptypes are interchangeable. The bridge is `predToPtype`/
`ptypeToPred`, and the equivalence is `montague_ttr_equiv`.

The approaches diverge exactly when:
1. Selectional restrictions matter (§2)
2. Hyperintensional contexts arise (§3)
3. Copredication requires dot types (see `Studies/Gotham2017.lean`)

These are precisely @cite{sutton-2024}'s arguments for rich type theories. -/

/-- Summary: the predicate/type duality is an equivalence modulo three
phenomena. We can state the exact boundary. -/
theorem equivalence_boundary {E : Type} (p : E → Bool) :
    -- (1) Basic predication: full equivalence
    (∀ e, p e = true ↔ Nonempty (predToPtype p e)) ∧
    -- (2) Round-trip: lossless for predicates
    (∀ e, @ptypeToPred E (predToPtype p) (λ x => predToPtype_decidable p x) e = p e) :=
  ⟨λ e => montague_ttr_equiv p e, λ e => roundtrip_pred p e⟩

-- ════════════════════════════════════════════════════════════════
-- § 5. SubtypeOf-Bearing Typed Composition
-- ════════════════════════════════════════════════════════════════

/-! Makes `SubtypeOf` from `TypeTheoretic/Core.lean` load-bearing by
wiring it into typed composition. Verbs declare the ontological sort
they require; composition through `restrict` succeeds only when
`SubtypeOf A B` is available. Removing a `SubtypeOf` instance breaks
the downstream derivation — that is the "load" the instance bears. -/

namespace SubtypeDemo

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

/-! Each instance is load-bearing: removing it breaks a named
theorem below. The hierarchy:

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

/-- Restrict a property to a subtype domain.
Given `P : Ppty B` and `[SubtypeOf A B]`, produce `Ppty A` by coercing
the argument up before applying `P`.

This is **typed function application**: the semantic
analogue of checking that the argument type is a subtype of the
parameter type. If no `SubtypeOf` instance exists, composition fails
at the Lean type level — a category mistake, not a truth-value failure. -/
def restrict {A B : Type} [h : SubtypeOf A B] (P : Ppty B) : Ppty A :=
  λ a => P (h.up a)

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

/-! ## Compositional derivations with typed NPs -/

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

/-- Direct Human ⊑ Entity and chained Human ⊑ Animate ⊑ Entity
produce the same result. This is the content of the coherence
requirement on subtyping: the diagram commutes. -/
theorem coercion_coherence (P : Ppty Entity) (h : Human) :
    restrict P h = restrict (restrict P : Ppty Animate) h := rfl

end SubtypeDemo

-- ════════════════════════════════════════════════════════════════
-- § 6. Complement Coercion
-- ════════════════════════════════════════════════════════════════

/-! Unlike `SubtypeOf` (identity-preserving: a human IS an animate
entity), complement coercion is *meaning-changing*: the coerced entity
is a DIFFERENT thing. "John enjoyed the book" doesn't mean John enjoyed
a physical object — it means he enjoyed *reading* it. The book is
coerced to an event via the telic quale.

This is a distinct mechanism from subtyping, and conflating them would
lose the meaning change. -/

namespace ComplementDemo

open SubtypeDemo (PhysObj)

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

/-! ## restrict ≠ coerceApply

The structural distinction: `restrict` composes with `SubtypeOf.up`
(the argument IS-A member of the supertype), while `coerceApply`
composes with `ComplementCoercion.coerce` (the argument is MAPPED TO
a different entity). Both produce `Ppty A` from `Ppty B`, but the
semantic relationship is different.

Consequence: "John fell" (restrict: John is an entity) and "John
enjoyed the book" (coerceApply: the book became a reading event) are
composed by different mechanisms, and the type system keeps them apart. -/

/-- restrict preserves identity: coercion is a subsumption. -/
theorem restrict_is_subsumption {A B : Type} [h : SubtypeOf A B]
    (P : Ppty B) (a : A) : SubtypeDemo.restrict P a = P (h.up a) := rfl

/-- coerceApply changes identity: coercion is a type-shift. -/
theorem coerceApply_is_shift {A B : Type} [h : ComplementCoercion A B]
    (P : Ppty B) (a : A) : coerceApply P a = P (h.coerce a) := rfl

end ComplementDemo

end Phenomena.Polysemy.Studies.Sutton2024
