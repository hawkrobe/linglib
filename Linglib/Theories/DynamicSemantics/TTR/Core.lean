import Linglib.Core.Proposition
import Linglib.Core.Intension
import Linglib.Core.CommonGround
import Linglib.Core.Basic
import Linglib.Core.Presupposition
import Linglib.Core.ModalLogic

/-!
# Type Theory with Records — Core Foundations

Type-theoretic foundations for TTR (Cooper 2023), organized by conceptual role:

**Types & Judgments**: IType, PredType/Ppty, records (DepRecordType, SituationRec),
  SubtypeOf, IsTrue/IsFalse.

**Type Operations**: MeetType = Prod, JoinType = Sum (native Lean),
  Restriction = Subtype (A11.7), record merges (symmetric = Prod, asymmetric; A11.3),
  StringType, TypeAct.

**Modal Type Systems**: ModalTypeSystem (Bool-valued, Ch1 Def 54), bridge to BProp.

**Grammar**: Cat, GSign, PSRule, phrase structure rules, lexical signs.

**Compositional Semantics**: Ppty, Quant, semCommonNoun, semPropName,
  ExistWitness, semIndefArt, semBe, propExtension, existPQ.

TTR replaces possible worlds with *types* as the bearers of propositional content.
A type is "true" when it has a witness (is inhabited) and "false" when empty.
Unlike sets, types are *intensional*: two types can have the same witnesses yet
remain distinct (`groundhog` ≠ `woodchuck` even if co-extensional).

## Native Lean type usage

| TTR Concept | Lean Encoding |
|---|---|
| `a : T` judgment | Native typing |
| Predicate types | `E → Type` (`PredType`/`Ppty`) |
| Meet types | `T₁ × T₂` (`Prod`) |
| Join types | `Sum T₁ T₂` |
| Restriction (A11.7) | `{ x : T // P x }` (`Subtype`) |
| Symmetric merge (A11.3) | `T₁ × T₂` (`Prod`) |
| Dependent records | `structure` |
| Fixed-point types | `(x : E) × P x` (`Sigma`) |
| IsTrue/IsFalse | `Nonempty T`/`IsEmpty T` |

## References

- Cooper (2023). From Perception to Communication. OUP. Ch 1, 3.
- Martin-Löf (1984). Intuitionistic Type Theory.
- Barwise & Perry (1983). Situations and Attitudes.
- Montague (1973). The Proper Treatment of Quantification.
-/

namespace Theories.DynamicSemantics.TTR

-- ============================================================================
-- Types, Records, Judgments
-- ============================================================================

/-! ## § 1.2 Perception as type assignment

Perceiving an object involves classifying it as being of a type.
In symbols: `a : T` — a judgement that `a` is of type `T`.
This is Lean's native typing judgement, so no new definition is needed.

The key philosophical point: you cannot perceive something without
ascribing *some* type to it, even if very general (Thing, Entity). -/

/-! ## § 1.3 System of basic types (Cooper Def 1)

A system of basic types TYPE_B = ⟨Type, A⟩ where:
- **Type** is a non-empty set of types
- **A** assigns to each type its set of witnesses
- Types are *intensional*: distinct types may share all witnesses

In Lean, `Type u` already provides the universe of types, and each type
`T : Type u` has its collection of terms. The key TTR feature that Lean
*does* capture is intensionality at the `Prop` level: `propext` identifies
logically equivalent propositions, but at `Type` two types can be
equivalent (`T ≃ S`) yet not definitionally equal.

For the purposes of connecting to linguistic theory, we introduce a
lightweight wrapper that makes TTR's intensional type identity explicit. -/

/-- An intensional type: a named type that carries identity beyond its extension.
Cooper (2023) §1.3: "there is nothing which prevents two types from being
associated with exactly the same set of objects" — types are intensional.

The `name` field distinguishes types even when they have the same carrier.
This models the `groundhog`/`woodchuck` distinction: same animals, different types. -/
structure IType where
  /-- The underlying Lean type (extension carrier) -/
  carrier : Type
  /-- Intensional identity tag (e.g., a predicate name) -/
  name : String
  deriving Repr

/-- Two ITypes are extensionally equivalent when their carriers are equivalent. -/
def IType.extEquiv (T₁ T₂ : IType) : Prop := Nonempty (T₁.carrier ≃ T₂.carrier)

/-- Two ITypes are intensionally identical when both name and carrier match. -/
def IType.intEq (T₁ T₂ : IType) : Prop := T₁ = T₂

/-- Core TTR thesis: extensional equivalence does not entail intensional identity.
This is the formal content of Cooper's claim that types are not sets. -/
theorem ext_equiv_not_implies_int_eq :
    ¬ (∀ T₁ T₂ : IType, T₁.extEquiv T₂ → T₁.intEq T₂) := by
  intro h
  -- groundhog and woodchuck: same carrier (Bool as stand-in), different names
  have := h ⟨Bool, "groundhog"⟩ ⟨Bool, "woodchuck"⟩ ⟨Equiv.refl Bool⟩
  simp [IType.intEq] at this

/-! ## § 1.4.1 Predicate types (ptypes)

A ptype `P(a₁,...,aₙ)` is a type constructed from a predicate and arguments.
Witnesses are situations/events in which the predicate holds of the arguments.

In Lean, this is naturally modeled as dependent function application:
given `P : α → Type` (a one-place predicate-as-type-constructor),
`P a` is the ptype whose witnesses are proofs/situations of `P a`. -/

/-- A predicate type constructor: maps entities to types (of situations).
`PredType E` is a one-place predicate over entities of type `E`.
The resulting type `p e` is the type of situations witnessing `p` of `e`. -/
abbrev PredType (E : Type) := E → Type

/-- A two-place predicate type constructor (relations). -/
abbrev PredType2 (E : Type) := E → E → Type

/-- A ptype: the type of situations where predicate `P` holds of argument `a`.
Cooper (2023) §1.4.1, Def 7: if `Arity(P) = ⟨T₁,...,Tₙ⟩` and `aᵢ : Tᵢ`,
then `P(a₁,...,aₙ) ∈ PType`. -/
abbrev ptype {E : Type} (P : PredType E) (a : E) := P a

/-- A relational ptype: `P(a,b)` for a two-place predicate. -/
abbrev ptype2 {E : Type} (P : PredType2 E) (a b : E) := P a b

/-- The relationship between basic types and predicates (Cooper §1.4.1, ex 10):
`a : Dog` iff there exists a situation `e` witnessing `dog(a)`.
This connects basic types (like `Dog`) to predicate types. -/
def typeFromPred {E : Type} (P : PredType E) (a : E) : Prop := Nonempty (P a)

/-! ## § 1.4.3 Record types

A record type is a collection of labelled fields where each field specifies
a type. Fields may be *dependent*: the type of a later field can depend on
the values in earlier fields.

Records (witnesses of record types) are labelled sets of values matching
the field types.

In Lean, `structure` declarations *are* record types. We don't re-implement
the infrastructure — we identify Lean structures with TTR records and prove
the key properties Cooper establishes. -/

/-- A simple (non-dependent) record type with two fields.
Models Cooper (2023) §1.4.3, ex (18a):
  [ x : Ind, y : Ind, e : hug(x,y) ]
but without dependency (the hug field's type doesn't reference x,y). -/
structure SimpleRecordType2 (T₁ T₂ : Type) where
  fst : T₁
  snd : T₂

/-- A dependent record type: the second field's type depends on the first.
This captures Cooper's dependent fields (§1.4.3.1, ex 25):
  [ x : Ind, c₁ : boy(x) ]
where the type of c₁ depends on which individual x is. -/
structure DepRecordType (T₁ : Type) (T₂ : T₁ → Type) where
  fst : T₁
  snd : T₂ fst

/-- A situation record: the canonical TTR record type for event semantics.
Models Cooper (2023) §1.4.3, ex (18a):
  [ x : Ind, y : Ind, e : hug(x,y) ] -/
structure SituationRec (E : Type) (R : E → E → Type) where
  x : E
  y : E
  evt : R x y

/-! ## § 1.4.3.5 Subtyping

Record type T₁ is a subtype of T₂ (T₁ ⊑ T₂) iff every witness of T₁
is also a witness of T₂, *regardless of what is assigned to the basic types
and ptypes* (Cooper Def 55 — this is a modal/universal notion).

For record types specifically, T₁ ⊑ T₂ when T₁ has all the fields of T₂
(plus possibly more). More fields = more specific = subtype.

This is the reverse of what you might expect from set inclusion:
the type with MORE constraints has FEWER witnesses. -/

/-- Subtyping: `T₁` is a subtype of `T₂` when every witness of `T₁`
is also a witness of `T₂`. Cooper (2023) §1.4.3.5, Def 55. -/
class SubtypeOf (T₁ T₂ : Type) where
  /-- The coercion witnessing the subtype relation -/
  up : T₁ → T₂

infixl:50 " ⊑ " => SubtypeOf

/-- Record type with more fields is a subtype of one with fewer fields.
Cooper (2023) ex (53): [ x:Ind, c₁:boy(x), y:Ind, c₂:dog(y), e:hug(x,y) ]
is a subtype of [ x:Ind, c₁:boy(x), y:Ind, c₂:dog(y) ].

We demonstrate this with Lean's structure inheritance: -/
structure BoyAndDog (E : Type) (Boy Dog : E → Prop) where
  x : E
  c₁ : Boy x
  y : E
  c₂ : Dog y

structure BoyHugsDog (E : Type) (Boy Dog : E → Prop) (Hug : E → E → Prop)
    extends BoyAndDog E Boy Dog where
  evt : Hug x y

/-- The subtype relation: BoyHugsDog ⊑ BoyAndDog (more fields → subtype). -/
instance (E : Type) (Boy Dog : E → Prop) (Hug : E → E → Prop) :
    SubtypeOf (BoyHugsDog E Boy Dog Hug) (BoyAndDog E Boy Dog) where
  up := BoyHugsDog.toBoyAndDog

/-- Subtyping is reflexive. -/
instance subtypeRefl (T : Type) : SubtypeOf T T where
  up := id

/-- Subtyping is transitive. -/
def subtypeTrans {T₁ T₂ T₃ : Type} [h₁₂ : SubtypeOf T₁ T₂] [h₂₃ : SubtypeOf T₂ T₃] :
    SubtypeOf T₁ T₃ where
  up := h₂₃.up ∘ h₁₂.up

/-! ## § 1.5 Propositions as types

The central semantic thesis of TTR: types play the role of propositions.
- A type is **true** when it is inhabited (has a witness).
- A type is **false** when it is empty (has no witness).
- `hug(a,b)` is true iff there exists a situation of that type.

This connects to Martin-Löf's (1984) propositions-as-types and to
constructive mathematics' proof-by-witness. -/

/-- A TTR type is "true" (inhabited). Cooper (2023) §1.5. -/
abbrev IsTrue (T : Type) : Prop := Nonempty T

/-- A TTR type is "false" (empty). -/
abbrev IsFalse (T : Type) : Prop := IsEmpty T

/-- Truth and falsity are exclusive. -/
theorem true_false_exclusive (T : Type) : ¬ (IsTrue T ∧ IsFalse T) := by
  intro ⟨⟨t⟩, hE⟩
  exact hE.false t

/-- Subtypes preserve truth: if T₁ ⊑ T₂ and T₁ is true, then T₂ is true. -/
theorem subtype_preserves_truth {T₁ T₂ : Type} [h : SubtypeOf T₁ T₂]
    (hT : IsTrue T₁) : IsTrue T₂ :=
  ⟨h.up hT.some⟩

/-- Supertypes preserve falsity: if T₁ ⊑ T₂ and T₂ is false, then T₁ is false. -/
theorem supertype_preserves_falsity {T₁ T₂ : Type} [h : SubtypeOf T₁ T₂]
    (hF : IsFalse T₂) : IsFalse T₁ :=
  ⟨λ t => hF.false (h.up t)⟩

/-! ## PLift helper

`propT p` is a readable alias for `PLift p`, used throughout TTR when
embedding a `Prop` into `Type` (e.g., `propT (x = y)` instead of `PLift (x = y)`). -/

/-- Lift a proposition to a type. Alias for `PLift`. -/
abbrev propT (p : Prop) : Type := PLift p

/-! ## Bridge to Core.Proposition

Cooper's world-indexed propositions: at each world `w`, a proposition
corresponds to a type that may or may not be inhabited. This is exactly
`Prop' W = W → Prop` — at each world, we get a `Prop`, which in CIC
*is* a type (in `Sort 0`).

The bridge: `Prop' W` is a family of TTR types indexed by "possibilities"
(worlds). The proposition is true at `w` iff the type `p w` is inhabited. -/

/-- A `Prop' W` proposition is TTR-true at world `w` iff the Prop is inhabited. -/
theorem prop'_true_iff_inhabited {W : Type*} (p : Core.Proposition.Prop' W) (w : W) :
    p w ↔ Nonempty (propT (p w)) :=
  ⟨λ h => ⟨PLift.up h⟩, λ ⟨⟨h⟩⟩ => h⟩

/-! ## Bridge to Core.Intension

An `Intension W τ` is a function from worlds to extensions. In TTR terms,
this is a type family indexed by possibilities in a modal type system
(Cooper Def 54). When `τ = Prop`, an intension is exactly a world-indexed
TTR proposition. -/

/-- An intension of Prop is a world-indexed family of TTR propositions. -/
theorem intension_prop_is_ttr_prop (W : Type*) :
    Core.Intension.Intension W Prop = Core.Proposition.Prop' W := rfl

/-! ## Modal type systems (Cooper Def 54)

A modal system of complex types TYPE_MC is a family of type systems
indexed by "possibilities" M ∈ M. Basic types and predicates are
shared across possibilities, but witness assignments vary.

This is structurally a Kripke model: each possibility assigns
extensions to predicates, just as each world assigns truth values.

We formalize the connection: a modal type system over `W` possibilities
with Bool-valued predicates is exactly a `BProp W`. -/

/-- A modal type system: for each possibility and predicate, whether the
predicate has witnesses. Cooper (2023) §1.4.3.5, Def 54. -/
abbrev ModalTypeSystem (W : Type) (Pred : Type) := W → Pred → Bool

/-- A predicate in a modal type system yields a BProp. -/
def ModalTypeSystem.toBProp {W Pred : Type} (mts : ModalTypeSystem W Pred)
    (P : Pred) : Core.Proposition.BProp W :=
  λ w => mts w P

/-- Subtyping in a modal type system: T₁ ⊑ T₂ iff at every possibility
where T₁ has witnesses, T₂ also has witnesses. This is exactly
propositional entailment. Cooper (2023) Def 55. -/
def ModalTypeSystem.subtypeBProp {W Pred : Type} (mts : ModalTypeSystem W Pred)
    (P₁ P₂ : Pred) : Prop :=
  ∀ w, mts w P₁ = true → mts w P₂ = true

/-- Modal subtyping = propositional entailment (the bridge theorem). -/
theorem modal_subtype_eq_entailment {W Pred : Type}
    (mts : ModalTypeSystem W Pred) (P₁ P₂ : Pred) :
    mts.subtypeBProp P₁ P₂ ↔
    Core.Proposition.Classical.entails W
      (↑(mts.toBProp P₁) : Core.Proposition.Prop' W)
      (↑(mts.toBProp P₂)) := by
  rfl

/-! ## Bridge: IType + ModalTypeSystem → Core.Intension

An IType, viewed through a Bool-valued modal type system (Def 54),
induces an intension (W → Bool). Whether this intension is rigid
(constant across all possibilities) corresponds exactly to
Core.Intension.IsRigid — connecting Cooper's Ch1 intensional types
to the framework-agnostic intension machinery. -/

/-- An IType in a modal type system induces an intension.
    At each possibility w, the type either has witnesses (true) or not (false).
    Cooper (2023) Def 54: possibilities index witness assignments. -/
def IType.toIntension {W : Type} (mts : ModalTypeSystem W String)
    (T : IType) : Core.Intension.Intension W Bool :=
  mts.toBProp T.name

/-- An IType's intension is rigid iff it has constant witness status
    across all possibilities. Bridges Ch1 intensional types to IsRigid. -/
theorem IType.rigid_iff_isRigid {W : Type} (mts : ModalTypeSystem W String)
    (T : IType) :
    Core.Intension.IsRigid (T.toIntension mts) ↔
    ∀ w₁ w₂ : W, mts w₁ T.name = mts w₂ T.name :=
  Iff.rfl

/-- Intensionally distinct ITypes can have co-extensional intensions:
    the groundhog/woodchuck phenomenon at the modal level. -/
theorem IType.coext_not_intEq {W : Type}
    (mts : ModalTypeSystem W String) (T₁ T₂ : IType)
    (_hCoExt : Core.Intension.CoExtensional (T₁.toIntension mts)
                                             (T₂.toIntension mts))
    (hNames : T₁.name ≠ T₂.name) :
    ¬ T₁.intEq T₂ :=
  λ heq => hNames (congrArg IType.name heq)

-- ============================================================================
-- Type Operations (Meet, Join, Restriction, Merge)
-- ============================================================================

/-! ## § 2.2 String theory of events

Events have temporal extent and can be decomposed into strings (sequences)
of sub-events. A game of fetch decomposes into: pick_up ⌢ throw ⌢ run_after ⌢ ...
In TTR, a string type `T⁺` is the type of non-empty strings of events of type T.
We model this with lists, which Lean handles natively. -/

/-- A string type: a non-empty sequence of typed events.
Cooper (2023) §2.2: events decompose into strings of sub-events.
The field `ne` ensures non-emptiness (TTR uses T⁺, not T*). -/
structure StringType (T : Type) where
  events : List T
  ne : events ≠ []

/-- String concatenation: combining two event strings.
Cooper (2023) §2.2, string concatenation `s₁ ⌢ s₂`. -/
def StringType.concat {T : Type} (s₁ s₂ : StringType T) : StringType T where
  events := s₁.events ++ s₂.events
  ne := by
    intro h
    cases hs : s₁.events with
    | nil => exact s₁.ne hs
    | cons a as => simp [hs, List.cons_append] at h

infixl:65 " ⌢ " => StringType.concat

/-- Concatenation is associative (strings form a semigroup). -/
theorem StringType.concat_assoc {T : Type} (s₁ s₂ s₃ : StringType T) :
    (s₁ ⌢ s₂ ⌢ s₃).events = (s₁ ⌢ (s₂ ⌢ s₃)).events := by
  simp only [StringType.concat, List.append_assoc]

/-- A single-element string (singleton event). -/
def StringType.singleton {T : Type} (t : T) : StringType T where
  events := [t]
  ne := by simp

/-! ## § 2.3.1 Type acts

Agents interact with types through three fundamental acts:
- **Judge**: classify an observed object as being of a type (`a : T`)
- **Query**: ask whether an object is of a type (`a : T?`)
- **Create**: bring into existence a witness of a type

These correspond to the three basic speech acts: assertion, question, command.
Cooper (2023) §2.3.1, ex (30–32). -/

/-- The three fundamental type acts. Cooper (2023) §2.3.1. -/
inductive TypeAct where
  | judge   -- classify an object as being of a type
  | query   -- ask whether an object is of a type
  | create  -- bring a witness into existence
  deriving Repr, DecidableEq

/-! ## § 2.3.3 Meet and join types (Cooper ex 42, 47)

Meet types (T₁ ∧ T₂): a witness must be of BOTH types simultaneously.
Join types (T₁ ∨ T₂): a witness is of EITHER type.

These are the type-theoretic analogues of conjunction and disjunction,
and they correspond exactly to Lean's `Prod` and `Sum`. -/

/-- Meet type: `a : T₁ ∧ T₂` iff `a : T₁` and `a : T₂`.
Cooper (2023) §2.6, Def 97. In Lean, this is `T₁ × T₂`.
We introduce an alias to make the TTR connection explicit. -/
abbrev MeetType (T₁ T₂ : Type) := T₁ × T₂

/-- Join type: `a : T₁ ∨ T₂` iff `a : T₁` or `a : T₂`.
Cooper (2023) §2.3.3, ex (47). In Lean, this is `Sum T₁ T₂`. -/
abbrev JoinType (T₁ T₂ : Type) := Sum T₁ T₂

/-- Meet of inhabited types is inhabited. -/
theorem meet_true_of_both {T₁ T₂ : Type} (h₁ : IsTrue T₁) (h₂ : IsTrue T₂) :
    IsTrue (MeetType T₁ T₂) :=
  ⟨(h₁.some, h₂.some)⟩

/-- Join is inhabited if either component is. -/
theorem join_true_of_left {T₁ T₂ : Type} (h : IsTrue T₁) :
    IsTrue (JoinType T₁ T₂) :=
  ⟨Sum.inl h.some⟩

theorem join_true_of_right {T₁ T₂ : Type} (h : IsTrue T₂) :
    IsTrue (JoinType T₁ T₂) :=
  ⟨Sum.inr h.some⟩

/-- Meet type is a subtype of each component (projection).
Cooper (2023) ex (98c,d). -/
instance meetSubtypeLeft (T₁ T₂ : Type) : SubtypeOf (MeetType T₁ T₂) T₁ where
  up := Prod.fst

instance meetSubtypeRight (T₁ T₂ : Type) : SubtypeOf (MeetType T₁ T₂) T₂ where
  up := Prod.snd

/-- Each component is a subtype of the join type (injection).
Cooper (2023) §2.3.3. -/
instance joinSubtypeLeft (T₁ T₂ : Type) : SubtypeOf T₁ (JoinType T₁ T₂) where
  up := Sum.inl

instance joinSubtypeRight (T₁ T₂ : Type) : SubtypeOf T₂ (JoinType T₁ T₂) where
  up := Sum.inr

/-- Meet preserves truth in both directions (iff).
The type-theoretic analogue of conjunction introduction + elimination. -/
theorem meet_true_iff {T₁ T₂ : Type} :
    IsTrue (MeetType T₁ T₂) ↔ IsTrue T₁ ∧ IsTrue T₂ :=
  ⟨λ ⟨(a, b)⟩ => ⟨⟨a⟩, ⟨b⟩⟩, λ ⟨h₁, h₂⟩ => meet_true_of_both h₁ h₂⟩

/-- Join preserves truth in both directions (iff).
The type-theoretic analogue of disjunction introduction + elimination. -/
theorem join_true_iff {T₁ T₂ : Type} :
    IsTrue (JoinType T₁ T₂) ↔ IsTrue T₁ ∨ IsTrue T₂ :=
  ⟨λ ⟨s⟩ => match s with | .inl a => Or.inl ⟨a⟩ | .inr b => Or.inr ⟨b⟩,
   λ h => h.elim join_true_of_left join_true_of_right⟩

/-! ## Appendix A11.7: Restriction (T ∥ r)

Cooper (2023) Appendix A11.7: a *restriction* of type T by predicate r
is the type of objects of T satisfying r. This is exactly Lean's native
`Subtype` (refinement type): `{ x : T // P x }`.

Using Lean's `Subtype` directly gives us the full API for free:
`.val` projects the underlying value, `.property` gives the proof. -/

/-- Cooper's restriction T ∥ r = Lean's `Subtype`:
the type of elements of `T` satisfying predicate `P`.
Cooper (2023) Appendix A11.7. -/
abbrev Restriction (T : Type) (P : T → Prop) := { x : T // P x }

/-- Restriction preserves the subtype relation: (T ∥ P) ⊑ T.
Every restricted element is an element of the base type. -/
instance restrictionSubtypeOf (T : Type) (P : T → Prop) :
    SubtypeOf (Restriction T P) T where
  up := Subtype.val

/-- Truth of a restriction requires both: an element AND the predicate. -/
theorem restriction_true_iff {T : Type} {P : T → Prop} :
    IsTrue (Restriction T P) ↔ ∃ x : T, P x :=
  ⟨λ ⟨⟨x, h⟩⟩ => ⟨x, h⟩, λ ⟨x, h⟩ => ⟨⟨x, h⟩⟩⟩

/-- Restriction strengthens: if T is restricted, the base type is also true. -/
theorem restriction_implies_base {T : Type} {P : T → Prop}
    (h : IsTrue (Restriction T P)) : IsTrue T :=
  subtype_preserves_truth h

/-! ## Appendix A11.3: Record merges

Cooper (2023) Appendix A11.3 defines two kinds of record merge:
- **Symmetric merge** μ(T₁, T₂): the type with fields from both records.
  This is `MeetType T₁ T₂ = T₁ × T₂` (Lean's `Prod`).
- **Asymmetric merge** μ_asym(T₁, T₂): T₂ fields override T₁ fields.
  Modeled as a base-override pair. -/

/-- Symmetric merge is meet (product type).
Cooper (2023) A11.3: μ(T₁, T₂) combines all fields of both records. -/
theorem symmetric_merge_is_meet (T₁ T₂ : Type) :
    MeetType T₁ T₂ = (T₁ × T₂) := rfl

/-- Symmetric merge is commutative (up to equivalence). -/
def symmetric_merge_comm (T₁ T₂ : Type) : MeetType T₁ T₂ ≃ MeetType T₂ T₁ where
  toFun := λ ⟨a, b⟩ => ⟨b, a⟩
  invFun := λ ⟨b, a⟩ => ⟨a, b⟩
  left_inv := λ ⟨_, _⟩ => rfl
  right_inv := λ ⟨_, _⟩ => rfl

/-- Merging with Unit is identity (up to equivalence).
Cooper (2023) A11.3: the empty record type acts as a merge identity. -/
def merge_unit_right (T : Type) : MeetType T Unit ≃ T where
  toFun := Prod.fst
  invFun := λ t => ⟨t, ()⟩
  left_inv := λ ⟨_, ()⟩ => rfl
  right_inv := λ _ => rfl

/-- Asymmetric merge: T₂ fields override T₁ fields.
Cooper (2023) A11.3: μ_asym(T₁, T₂) takes T₁ as base and T₂ as override.
Accessors prefer override fields when both provide the same label. -/
structure AsymMerge (T₁ T₂ : Type) where
  /-- The base record -/
  base : T₁
  /-- The override record (its fields take priority) -/
  override : T₂

/-- Asymmetric merge with Unit override is equivalent to the base. -/
def asymMerge_unit_override (T : Type) : AsymMerge T Unit ≃ T where
  toFun := AsymMerge.base
  invFun := λ t => ⟨t, ()⟩
  left_inv := λ ⟨_, ()⟩ => rfl
  right_inv := λ _ => rfl

-- ============================================================================
-- Signs (basic, before grammar)
-- ============================================================================

/-! ## § 2.5 Signs (Cooper ex 70)

A sign pairs a speech event with its content. -/

/-- A TTR sign: a pairing of speech event type and content type.
Cooper (2023) §2.5, ex (70). -/
structure TTRSign (Phon Cont : Type) where
  sEvent : Phon
  cont : Cont

-- ============================================================================
-- Intensionality Phenomena
-- ============================================================================

section CorePhenomena

/-- `groundhog` and `woodchuck` as intensional types: same carrier, different names.
Cooper (2023) §1.3: types are not sets; two types can share all witnesses
yet remain distinct. -/
def groundhog : IType := ⟨Unit, "groundhog"⟩
def woodchuck : IType := ⟨Unit, "woodchuck"⟩

/-- They are extensionally equivalent (same carrier). -/
theorem groundhog_woodchuck_ext_equiv : groundhog.extEquiv woodchuck :=
  ⟨Equiv.refl Unit⟩

/-- But they are intensionally distinct (different names).
This is Cooper's key point: groundhog ≠ woodchuck in TTR,
whereas in extensional set theory {marmota} = {marmota}. -/
theorem groundhog_ne_woodchuck : ¬ groundhog.intEq woodchuck := by
  simp [IType.intEq, groundhog, woodchuck]

/-- `round_square` and `even_prime_gt_2` are both empty but distinct.
Cooper (2023) §1.3: possible worlds cannot distinguish these since both
have empty extension at every world. TTR can: they are different types. -/
def roundSquare : IType := ⟨Empty, "round_square"⟩
def evenPrimeGt2 : IType := ⟨Empty, "even_prime_gt_2"⟩

theorem round_square_empty : IsFalse roundSquare.carrier :=
  show IsEmpty Empty from inferInstance
theorem even_prime_gt2_empty : IsFalse evenPrimeGt2.carrier :=
  show IsEmpty Empty from inferInstance
theorem empty_types_distinct : ¬ roundSquare.intEq evenPrimeGt2 := by
  simp [IType.intEq, roundSquare, evenPrimeGt2]

/-- Subtyping example from Cooper (2023) ex (53):
A situation with a boy hugging a dog is a subtype of a situation with
a boy and a dog (regardless of what is going on between them). -/
example (E : Type) (Boy Dog : E → Prop) (Hug : E → E → Prop)
    (sit : BoyHugsDog E Boy Dog Hug) :
    BoyAndDog E Boy Dog :=
  SubtypeOf.up sit

end CorePhenomena

-- ============================================================================
-- Grammar (Cat, GSign, PSRule)
-- ============================================================================

/-! ## § 3.2 Hierarchical constituent structure

Events have hierarchical structure beyond flat string types. -/

section HierarchicalEvents

/-- Events in a bus trip. Cooper (2023) §3.2, ex (1–2). -/
inductive BusEvent where
  | waitAtBusstop | busArrive | getOnBus
  | travelOnBus | getOffBus
  deriving Repr, DecidableEq

/-- GetBus = WaitAtBusstop ⌢ BusArrive ⌢ GetOnBus. Cooper §3.2, ex (2). -/
def getBus : StringType BusEvent where
  events := [.waitAtBusstop, .busArrive, .getOnBus]
  ne := by simp

/-- BusTrip decomposes as GetBus ⌢ TravelOnBus ⌢ GetOffBus. Cooper §3.2, ex (1). -/
theorem busTripDecomp :
    [BusEvent.waitAtBusstop, .busArrive, .getOnBus, .travelOnBus, .getOffBus] =
    (getBus ⌢ StringType.singleton .travelOnBus ⌢ StringType.singleton .getOffBus).events := rfl

end HierarchicalEvents

/-! ## § 3.3 Syntactic categories

Cooper (2023) §3.3, ex (12): Cat is a basic type with witnesses
s, np, det, n, v, vp — the categories needed for the English fragment. -/

/-- Syntactic categories for Cooper's English fragment.
Cooper (2023) §3.3, ex (12). -/
inductive Cat where
  | s   -- sentence
  | np  -- noun phrase
  | det -- determiner
  | n   -- common noun
  | v   -- verb
  | vp  -- verb phrase
  deriving Repr, DecidableEq, BEq

/-- Whether a category is lexical (word-level) vs phrasal. -/
def Cat.isLexical : Cat → Bool
  | .n | .v | .det => true
  | .s | .np | .vp => false

/-- Bridge: TTR Cat → UD UPOS for lexical categories. -/
def Cat.toUPOS? : Cat → Option UD.UPOS
  | .n => some .NOUN
  | .v => some .VERB
  | .det => some .DET
  | .s | .np | .vp => none

/-- Lexical categories always have a UPOS mapping. -/
theorem cat_lexical_has_upos (c : Cat) (h : c.isLexical = true) :
    c.toUPOS?.isSome = true := by
  cases c <;> simp [Cat.isLexical] at h <;> simp [Cat.toUPOS?]

/-- A grammatical sign with syntactic structure.
Cooper (2023) §3.3, ex (11). -/
inductive GSign (Phon Cont : Type) where
  | mk (sEvent : Phon) (cat : Cat)
       (daughters : List (GSign Phon Cont)) (cont : Cont)

namespace GSign
variable {Phon Cont : Type}

def sEvent : GSign Phon Cont → Phon
  | .mk e _ _ _ => e

def cat : GSign Phon Cont → Cat
  | .mk _ c _ _ => c

def daughters : GSign Phon Cont → List (GSign Phon Cont)
  | .mk _ _ ds _ => ds

def cont : GSign Phon Cont → Cont
  | .mk _ _ _ c => c

/-- Whether a sign is lexical (NoDaughters = empty daughter string). -/
def isLexical (s : GSign Phon Cont) : Bool :=
  s.daughters.isEmpty

/-- Project out the Ch2 sign (dropping syntactic structure). -/
def toTTRSign (s : GSign Phon Cont) : TTRSign Phon Cont where
  sEvent := s.sEvent
  cont := s.cont

end GSign

/-- Create a lexical sign (no daughters).
Cooper (2023) §3.3, ex (18). -/
def lexSign {Phon Cont : Type} (phon : Phon) (c : Cat) (cont : Cont) :
    GSign Phon Cont :=
  .mk phon c [] cont

/-- Lexical signs have no daughters by construction. -/
theorem lexSign_isLexical {Phon Cont : Type}
    (phon : Phon) (c : Cat) (cont : Cont) :
    (lexSign phon c cont : GSign Phon Cont).isLexical = true := rfl

/-! ## § 3.3 Phrase structure rules -/

/-- A phrase structure rule: mother category and ordered daughter categories.
Cooper (2023) §3.3, ex (27). -/
structure PSRule where
  mother : Cat
  daughters : List Cat
  deriving Repr, DecidableEq

/-- S → NP VP. Cooper (2023) §3.3, ex (29). -/
def rule_S_NP_VP : PSRule := ⟨.s, [.np, .vp]⟩
/-- NP → Det N. -/
def rule_NP_Det_N : PSRule := ⟨.np, [.det, .n]⟩
/-- VP → V NP. -/
def rule_VP_V_NP : PSRule := ⟨.vp, [.v, .np]⟩

/-- The complete set of phrase structure rules for Cooper's fragment. -/
def fragmentRules : List PSRule :=
  [rule_S_NP_VP, rule_NP_Det_N, rule_VP_V_NP]

/-- All fragment rules are binary (two daughters). -/
theorem fragment_rules_binary :
    ∀ r ∈ fragmentRules, r.daughters.length = 2 := by
  intro r hr
  simp [fragmentRules] at hr
  rcases hr with rfl | rfl | rfl <;> rfl

/-- Build a phrasal sign from a rule and daughters. -/
def ruleDaughters {Phon Cont : Type}
    (rule : PSRule) (phon : Phon) (cont : Cont)
    (daus : List (GSign Phon Cont)) : GSign Phon Cont :=
  .mk phon rule.mother daus cont

/-- Phrasal signs (with at least one daughter) are not lexical. -/
theorem ruleDaughters_not_lexical {Phon Cont : Type}
    (rule : PSRule) (phon : Phon) (cont : Cont)
    (d : GSign Phon Cont) (ds : List (GSign Phon Cont)) :
    (ruleDaughters rule phon cont (d :: ds)).isLexical = false := rfl

-- ============================================================================
-- Compositional Semantics (Ppty, Quant, semCommonNoun, etc.)
-- ============================================================================

/-! ## § 3.4 Property and quantifier types

Cooper (2023) §3.4 introduces the semantic type hierarchy:
- **Ppty** = [x:Ind] → RecType: maps individuals to situation types (properties)
- **Quant** = Ppty → RecType: maps properties to types (quantifiers)

These are the TTR analogues of Montague's ⟨e,t⟩ and ⟨⟨e,t⟩,t⟩. -/

/-- A property type: maps an individual to a type of situations.
Cooper (2023) §3.4, ex (30): Ppty = [x:Ind] → RecType.
Alias for `PredType E`. Montague type: ⟨e,t⟩. -/
abbrev Ppty (E : Type) := PredType E

/-- A quantifier type: maps a property to a type.
Cooper (2023) §3.4: Quant = Ppty → RecType.
Montague type: ⟨⟨e,t⟩,t⟩ — a generalized quantifier. -/
abbrev Quant (E : Type) := Ppty E → Type

/-- Bridge: TTR Ppty is structurally identical to PredType from §1.4.1. -/
theorem ppty_eq_predType (E : Type) : Ppty E = PredType E := rfl

/-! ## § 3.4 Compositional semantics functions -/

/-- Common noun content: wrap a predicate as a property.
Cooper (2023) §3.4, ex (30). -/
def semCommonNoun {E : Type} (p : E → Type) : Ppty E := p

/-- Proper name content as a generalized quantifier (Montague 1973).
Cooper (2023) §3.4, ex (33): SemPropName(a) = λP:Ppty . P([x=a]). -/
def semPropName {E : Type} (a : E) : Quant E := λ P => P a

/-- The existential witness record type.
Cooper (2023) §3.4, ex (37). -/
structure ExistWitness (E : Type) (restr scope : Ppty E) where
  individual : E
  restrWit : restr individual
  scopeWit : scope individual

/-- Indefinite article content: maps a restrictor property to a quantifier.
Cooper (2023) §3.4, ex (37). -/
def semIndefArt {E : Type} (restr : Ppty E) : Quant E :=
  λ scope => ExistWitness E restr scope

/-- Copula "be" for predicate nominal constructions.
Cooper (2023) §3.4, ex (78). -/
def semBe {E : Type} (Q : Quant E) : Ppty E :=
  λ x => Q (λ y => propT (x = y))

/-! ## § 3.4 Property extension and existential quantification -/

/-- Property extension: whether an individual has property P.
Cooper (2023) §3.4, ex (46). -/
def propExtension {E : Type} (P : Ppty E) (a : E) : Prop := Nonempty (P a)

/-- Existential quantification as property-extension overlap.
Cooper (2023) §3.4, ex (55). -/
def existPQ {E : Type} (P Q : Ppty E) : Prop :=
  ∃ a : E, Nonempty (P a) ∧ Nonempty (Q a)

/-- existPQ is equivalent to inhabitation of ExistWitness. -/
theorem existPQ_iff_witness {E : Type} (P Q : Ppty E) :
    existPQ P Q ↔ Nonempty (ExistWitness E P Q) := by
  constructor
  · rintro ⟨a, ⟨hp⟩, ⟨hq⟩⟩; exact ⟨⟨a, hp, hq⟩⟩
  · rintro ⟨⟨a, hp, hq⟩⟩; exact ⟨a, ⟨hp⟩, ⟨hq⟩⟩

/-- Bridge: TTR existPQ reduces to classical ∃ when properties are Prop-valued. -/
theorem existPQ_eq_exists {E : Type} (P Q : E → Prop) :
    existPQ (λ e => propT (P e)) (λ e => propT (Q e)) ↔ ∃ a, P a ∧ Q a := by
  simp [existPQ]

-- ============================================================================
-- Compositional Derivation Phenomena
-- ============================================================================

section DerivationPhenomena

/-- Individuals in Cooper's fragment: Dudamel and Beethoven. -/
inductive Ind where
  | dudamel | beethoven
  deriving Repr, DecidableEq

/-- Predicate "conductor": Dudamel is a conductor. -/
inductive Conductor : Ind → Type where
  | mk : Conductor .dudamel

/-- Predicate "composer": Beethoven is a composer. -/
inductive Composer : Ind → Type where
  | mk : Composer .beethoven

/-- "conductor" content: Ppty Ind. -/
def conductorPpty : Ppty Ind := semCommonNoun Conductor

/-- "composer" content: Ppty Ind. -/
def composerPpty : Ppty Ind := semCommonNoun Composer

/-- "Dudamel" content: Quant Ind (GQ). -/
def dudamelQuant : Quant Ind := semPropName .dudamel

/-- "Beethoven" content: Quant Ind (GQ). -/
def beethovenQuant : Quant Ind := semPropName .beethoven

/-- Step 3: "a conductor" — existential quantifier over conductors. -/
abbrev aConductor : Quant Ind := semIndefArt conductorPpty

/-- Step 5: "is a conductor" — property of being a conductor. -/
abbrev isAConductor : Ppty Ind := semBe aConductor

/-- Step 7: "Dudamel is a conductor" — a proposition (type). -/
abbrev dudamelIsAConductor : Type := dudamelQuant isAConductor

/-- "Dudamel is a conductor" is TRUE (the proposition type is inhabited). -/
def dudamelIsAConductorTrue : dudamelIsAConductor :=
  ⟨.dudamel, Conductor.mk, PLift.up rfl⟩

/-- The analogous sentence with Beethoven. -/
abbrev beethovenIsAConductor : Type := beethovenQuant isAConductor

/-- "Beethoven is a conductor" is FALSE (the proposition type is empty). -/
instance : IsFalse beethovenIsAConductor :=
  ⟨fun | ⟨.dudamel, _, ⟨heq⟩⟩ => nomatch heq
       | ⟨.beethoven, hc, _⟩ => nomatch hc⟩

/-- "Beethoven is a composer" — TRUE. -/
abbrev aComposer : Quant Ind := semIndefArt composerPpty
abbrev isAComposer : Ppty Ind := semBe aComposer
abbrev beethovenIsAComposer : Type := beethovenQuant isAComposer

def beethovenIsAComposerTrue : beethovenIsAComposer :=
  ⟨.beethoven, Composer.mk, PLift.up rfl⟩

/-- "a conductor" unfolds to semIndefArt applied to conductor property. -/
theorem aConductor_unfold :
    aConductor = semIndefArt conductorPpty := rfl

/-- "is a conductor" unfolds to semBe applied to the quantifier. -/
theorem isAConductor_unfold :
    isAConductor = semBe (semIndefArt conductorPpty) := rfl

/-- The full derivation: semPropName applied to the VP property. -/
theorem dudamelSentence_unfold :
    dudamelIsAConductor =
    semPropName .dudamel (semBe (semIndefArt conductorPpty)) := rfl

/-- The sentence type is exactly ExistWitness with identity scope. -/
theorem dudamelSentence_is_existWitness :
    dudamelIsAConductor =
    ExistWitness Ind Conductor (λ y => propT (Ind.dudamel = y)) := rfl

end DerivationPhenomena

end Theories.DynamicSemantics.TTR
