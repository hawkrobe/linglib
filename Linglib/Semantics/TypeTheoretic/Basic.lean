import Mathlib.Data.Set.Basic
import Linglib.Core.Logic.Intensional.Rigidity
import Linglib.Discourse.CommonGround
import Linglib.Semantics.Presupposition.Basic
import Linglib.Data.UD.Basic

/-!
# Type Theory with Records — Core Foundations
[barwise-perry-1983] [cooper-2023] [martin-lf-1984] [montague-1973]

Type-theoretic foundations for TTR, organized by conceptual role:

**Types & Judgments**: IType, PredType/Ppty, records (DepRecordType, SituationRec),
  IsTrue/IsFalse. Subtyping uses Lean's built-in `Coe` typeclass.

**Type Operations**: MeetType = Prod, JoinType = Sum (native Lean),
  Restriction = Subtype (A11.7), record merges (symmetric = Prod, asymmetric; A11.3),
  StringType, TypeAct.

**Modal Type Systems**: ModalTypeSystem (Bool-valued, Ch1 Def 54), bridge to `W → Bool`.

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

-/

namespace Semantics.TypeTheoretic

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
§1.3: "there is nothing which prevents two types from being
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

/-- Meet of intensional types: compose carriers and names.
Intensional identity is preserved through meet, so compositional
expressions built from distinct atomic types remain distinct. -/
def IType.meet (T₁ T₂ : IType) : IType where
  carrier := T₁.carrier × T₂.carrier
  name := T₁.name ++ " ∧ " ++ T₂.name

/-- Join of intensional types: sum carriers and compose names. -/
def IType.join (T₁ T₂ : IType) : IType where
  carrier := Sum T₁.carrier T₂.carrier
  name := T₁.name ++ " ∨ " ++ T₂.name

/-- Core TTR thesis: extensional equivalence does not entail intensional identity.
This is the formal content of Cooper's claim that types are not sets. -/
theorem ext_equiv_not_implies_int_eq :
    ¬ (∀ T₁ T₂ : IType, T₁.extEquiv T₂ → T₁.intEq T₂) := by
  intro h
  -- groundhog and woodchuck: same carrier (Bool as stand-in), different names
  have := h ⟨Bool, "groundhog"⟩ ⟨Bool, "woodchuck"⟩ ⟨Equiv.refl Bool⟩
  simp only [IType.intEq, IType.mk.injEq] at this
  exact absurd this.2 (by decide)

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
§1.4.1, Def 7: if `Arity(P) = ⟨T₁,...,Tₙ⟩` and `aᵢ : Tᵢ`,
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
Models §1.4.3, ex (18a):
  [ x : Ind, y : Ind, e : hug(x,y)]
but without dependency (the hug field's type doesn't reference x,y). -/
structure SimpleRecordType2 (T₁ T₂ : Type) where
  fst : T₁
  snd : T₂

/-- A dependent record type: the second field's type depends on the first.
This captures Cooper's dependent fields (§1.4.3.1, ex 25):
  [ x : Ind, c₁ : boy(x)]
where the type of c₁ depends on which individual x is. -/
structure DepRecordType (T₁ : Type) (T₂ : T₁ → Type) where
  fst : T₁
  snd : T₂ fst

/-- A situation record: the canonical TTR record type for event semantics.
Models §1.4.3, ex (18a):
  [ x : Ind, y : Ind, e : hug(x,y)] -/
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

/-! ### Subtyping via Lean's `Coe`

Subtyping `T₁ ⊑ T₂` (§1.4.3.5, Def 55) is Lean's `Coe T₁ T₂` — a
coercive subtyping mechanism with implicit elaboration insertion.
This matches [chatzikyriakidis-luo-2020]'s preferred coercive
subtyping (paper §2.4, p. 39: subsumptive subtyping "cannot be
employed for an MTT"; coercive subtyping is the suitable mechanism).
Composition through Coe chains via Lean's `CoeHTCT`; no explicit
`Trans` registration needed. -/

/-- Record type with more fields is a subtype of one with fewer
fields. ex (53): `[x:Ind, c₁:boy(x), y:Ind, c₂:dog(y), e:hug(x,y)]`
is a subtype of `[x:Ind, c₁:boy(x), y:Ind, c₂:dog(y)]`. -/
structure BoyAndDog (E : Type) (Boy Dog : E → Prop) where
  x : E
  c₁ : Boy x
  y : E
  c₂ : Dog y

structure BoyHugsDog (E : Type) (Boy Dog : E → Prop) (Hug : E → E → Prop)
    extends BoyAndDog E Boy Dog where
  evt : Hug x y

/-! `BoyHugsDog ⊑ BoyAndDog` (more fields → subtype). The projection
is `BoyHugsDog.toBoyAndDog`, automatically generated by Lean's
`extends`. We do not register this as a `Coe` instance — the extra
parameter `Hug` is in the source but not the target, so the
elaborator cannot synthesize the instance from a `BoyAndDog`-typed
context. Consumers project explicitly via `.toBoyAndDog`. -/

/-! ## § 1.5 Propositions as types

The central semantic thesis of TTR: types play the role of propositions.
- A type is **true** when it is inhabited (has a witness).
- A type is **false** when it is empty (has no witness).
- `hug(a,b)` is true iff there exists a situation of that type.

This connects to [martin-lf-1984]'s propositions-as-types and to
constructive mathematics' proof-by-witness. -/

/-- A TTR type is "true" (inhabited). §1.5. -/
abbrev IsTrue (T : Type) : Prop := Nonempty T

/-- A TTR type is "false" (empty). -/
abbrev IsFalse (T : Type) : Prop := IsEmpty T

/-- Truth and falsity are exclusive. -/
theorem true_false_exclusive (T : Type) : ¬ (IsTrue T ∧ IsFalse T) := by
  intro ⟨⟨t⟩, hE⟩
  exact hE.false t

/-- IType.meet truth = conjunction of component truth. -/
theorem IType.meet_true_iff (T₁ T₂ : IType) :
    IsTrue (T₁.meet T₂).carrier ↔ IsTrue T₁.carrier ∧ IsTrue T₂.carrier :=
  ⟨λ ⟨(a, b)⟩ => ⟨⟨a⟩, ⟨b⟩⟩, λ ⟨⟨a⟩, ⟨b⟩⟩ => ⟨(a, b)⟩⟩

/-- IType.join truth = disjunction of component truth. -/
theorem IType.join_true_iff (T₁ T₂ : IType) :
    IsTrue (T₁.join T₂).carrier ↔ IsTrue T₁.carrier ∨ IsTrue T₂.carrier :=
  ⟨λ ⟨s⟩ => match s with | .inl a => Or.inl ⟨a⟩ | .inr b => Or.inr ⟨b⟩,
   λ h => h.elim (λ ⟨a⟩ => ⟨Sum.inl a⟩) (λ ⟨b⟩ => ⟨Sum.inr b⟩)⟩

/-- Subtypes preserve truth: if `T₁ ⊑ T₂` (`Coe T₁ T₂`) and `T₁`
    is true, then `T₂` is true. -/
theorem subtype_preserves_truth {T₁ T₂ : Type} [Coe T₁ T₂]
    (hT : IsTrue T₁) : IsTrue T₂ :=
  ⟨Coe.coe hT.some⟩

/-- Supertypes preserve falsity: if `T₁ ⊑ T₂` (`Coe T₁ T₂`) and
    `T₂` is false, then `T₁` is false. -/
theorem supertype_preserves_falsity {T₁ T₂ : Type} [Coe T₁ T₂]
    (hF : IsFalse T₂) : IsFalse T₁ :=
  ⟨λ t => hF.false (Coe.coe t)⟩

/-! ## PLift helper

`propT p` is a readable alias for `PLift p`, used throughout TTR when
embedding a `Prop` into `Type` (e.g., `propT (x = y)` instead of `PLift (x = y)`). -/

/-- Lift a proposition to a type. Alias for `PLift`. -/
abbrev propT (p : Prop) : Type := PLift p

/-! ## Bridge to Set

Cooper's world-indexed propositions: at each world `w`, a proposition
corresponds to a type that may or may not be inhabited. This is exactly
`Set W = W → Prop` — at each world, we get a `Prop`, which in CIC
*is* a type (in `Sort 0`).

The bridge: `Set W` is a family of TTR types indexed by "possibilities"
(worlds). The proposition is true at `w` iff the type `p w` is inhabited. -/

/-- A `Set W` proposition is TTR-true at world `w` iff the Prop is inhabited. -/
theorem prop'_true_iff_inhabited {W : Type*} (p : Set W) (w : W) :
    p w ↔ Nonempty (propT (p w)) :=
  ⟨λ h => ⟨PLift.up h⟩, λ ⟨⟨h⟩⟩ => h⟩

/-! ## Bridge to Core.Intension

An `Intension W τ` is a function from worlds to extensions. In TTR terms,
this is a type family indexed by possibilities in a modal type system
(Cooper Def 54). When `τ = Prop`, an intension is exactly a world-indexed
TTR proposition. -/

/-- An intension of Prop is a world-indexed family of TTR propositions. -/
theorem intension_prop_is_ttr_prop (W : Type*) :
    Core.Intension W Prop = Set W := rfl

/-! ## Modal type systems (Cooper Def 54)

A modal system of complex types TYPE_MC is a family of type systems
indexed by "possibilities" M ∈ M. Basic types and predicates are
shared across possibilities, but witness assignments vary.

This is structurally a Kripke model: each possibility assigns
extensions to predicates, just as each world assigns truth values.

We formalize the connection: a modal type system over `W` possibilities
with Bool-valued predicates is exactly a `(W → Bool)`. -/

/-- A modal type system: for each possibility and predicate, whether the
predicate has witnesses. §1.4.3.5, Def 54. -/
abbrev ModalTypeSystem (W : Type) (Pred : Type) := W → Pred → Bool

/-- A predicate in a modal type system yields a `W → Bool`. -/
def ModalTypeSystem.toBProp {W Pred : Type} (mts : ModalTypeSystem W Pred)
    (P : Pred) : (W → Bool) :=
  λ w => mts w P

/-- Subtyping in a modal type system: T₁ ⊑ T₂ iff at every possibility
where T₁ has witnesses, T₂ also has witnesses. This is exactly
propositional entailment. Def 55. -/
def ModalTypeSystem.subtypeBProp {W Pred : Type} (mts : ModalTypeSystem W Pred)
    (P₁ P₂ : Pred) : Prop :=
  ∀ w, mts w P₁ = true → mts w P₂ = true

/-- Modal subtyping = propositional entailment (the bridge theorem). -/
theorem modal_subtype_eq_entailment {W Pred : Type}
    (mts : ModalTypeSystem W Pred) (P₁ P₂ : Pred) :
    mts.subtypeBProp P₁ P₂ ↔
    ({w | mts.toBProp P₁ w = true} : Set W) ⊆
      {w | mts.toBProp P₂ w = true} := by
  rfl

/-! ## Bridge: IType + ModalTypeSystem → Core.Intension

An IType, viewed through a Bool-valued modal type system (Def 54),
induces an intension (W → Bool). Whether this intension is rigid
(constant across all possibilities) corresponds exactly to
Core.Intension.IsRigid — connecting Cooper's Ch1 intensional types
to the framework-agnostic intension machinery. -/

/-- An IType in a modal type system induces an intension.
    At each possibility w, the type either has witnesses (true) or not (false).
    Def 54: possibilities index witness assignments. -/
def IType.toIntension {W : Type} (mts : ModalTypeSystem W String)
    (T : IType) : Core.Intension W Bool :=
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
of sub-events. A game of fetch decomposes into: pick_up ⌢ throw ⌢ run_after ⌢...
In TTR, a string type `T⁺` is the type of non-empty strings of events of type T.
We model this with lists, which Lean handles natively. -/

/-- A string type: a non-empty sequence of typed events.
§2.2: events decompose into strings of sub-events.
The field `ne` ensures non-emptiness (TTR uses T⁺, not T*). -/
structure StringType (T : Type) where
  events : List T
  ne : events ≠ []

/-- String concatenation: combining two event strings.
§2.2, string concatenation `s₁ ⌢ s₂`. -/
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
§2.3.1, ex (30–32). -/

/-- The three fundamental type acts. §2.3.1. -/
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
§2.6, Def 97. In Lean, this is `T₁ × T₂`.
We introduce an alias to make the TTR connection explicit. -/
abbrev MeetType (T₁ T₂ : Type) := T₁ × T₂

/-- Join type: `a : T₁ ∨ T₂` iff `a : T₁` or `a : T₂`.
§2.3.3, ex (47). In Lean, this is `Sum T₁ T₂`. -/
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

/-! Meet/Join subtyping (ex 98c,d and §2.3.3) is captured by Lean's
native `Prod.fst`/`Prod.snd` (projection out of meet) and
`Sum.inl`/`Sum.inr` (injection into join). Per mathlib idiom we do
not register these as `Coe` instances — the `(MeetType T₁ T₂) ⊑ T₁`
shape leaves the other component (`T₂`) unrecoverable from the
target type alone, so the elaborator cannot synthesize the instance.
Consumers use the projections/injections explicitly. -/

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

Appendix A11.7: a *restriction* of type T by predicate r
is the type of objects of T satisfying r. This is exactly Lean's native
`Subtype` (refinement type): `{ x : T // P x }`.

Using Lean's `Subtype` directly gives us the full API for free:
`.val` projects the underlying value, `.property` gives the proof. -/

/-- Cooper's restriction T ∥ r = Lean's `Subtype`:
the type of elements of `T` satisfying predicate `P`.
Appendix A11.7. -/
abbrev Restriction (T : Type) (P : T → Prop) := { x : T // P x }

/-! Restriction `(T ∥ P) ⊑ T`: every restricted element projects to
the base type via `Subtype.val`. Per mathlib idiom we do not
register this as a generic `Coe (Restriction T P) T` instance
because Lean cannot infer `P` from the target `T` alone; consumers
use `.val` explicitly. -/

/-- Truth of a restriction requires both: an element AND the predicate. -/
theorem restriction_true_iff {T : Type} {P : T → Prop} :
    IsTrue (Restriction T P) ↔ ∃ x : T, P x :=
  ⟨λ ⟨⟨x, h⟩⟩ => ⟨x, h⟩, λ ⟨x, h⟩ => ⟨⟨x, h⟩⟩⟩

/-- Restriction strengthens: if `T ∥ P` is true, the base type `T`
    is also true (via `.val` projection). -/
theorem restriction_implies_base {T : Type} {P : T → Prop}
    (h : IsTrue (Restriction T P)) : IsTrue T :=
  ⟨h.some.val⟩

/-! ## Appendix A11.3: Record merges

Appendix A11.3 defines two kinds of record merge:
- **Symmetric merge** μ(T₁, T₂): the type with fields from both records.
  This is `MeetType T₁ T₂ = T₁ × T₂` (Lean's `Prod`).
- **Asymmetric merge** μ_asym(T₁, T₂): T₂ fields override T₁ fields.
  Modeled as a base-override pair. -/

/-- Symmetric merge is meet (product type).
A11.3: μ(T₁, T₂) combines all fields of both records. -/
theorem symmetric_merge_is_meet (T₁ T₂ : Type) :
    MeetType T₁ T₂ = (T₁ × T₂) := rfl

/-- Symmetric merge is commutative (up to equivalence). -/
def symmetric_merge_comm (T₁ T₂ : Type) : MeetType T₁ T₂ ≃ MeetType T₂ T₁ where
  toFun := λ ⟨a, b⟩ => ⟨b, a⟩
  invFun := λ ⟨b, a⟩ => ⟨a, b⟩
  left_inv := λ ⟨_, _⟩ => rfl
  right_inv := λ ⟨_, _⟩ => rfl

/-- Merging with Unit is identity (up to equivalence).
A11.3: the empty record type acts as a merge identity. -/
def merge_unit_right (T : Type) : MeetType T Unit ≃ T where
  toFun := Prod.fst
  invFun := λ t => ⟨t, ()⟩
  left_inv := λ ⟨_, ()⟩ => rfl
  right_inv := λ _ => rfl

/-- Asymmetric merge: T₂ fields override T₁ fields.
A11.3: μ_asym(T₁, T₂) takes T₁ as base and T₂ as override.
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
§2.5, ex (70). The phonological-form field is named `phon`
(broader linguistic terminology; Cooper writes "s-event" interchangeably). -/
structure TTRSign (Phon Cont : Type) where
  phon : Phon
  cont : Cont
  deriving Repr, DecidableEq

namespace TTRSign

variable {Phon Cont Phon' Cont' : Type}

/-- Extensionality for TTR signs. -/
@[ext] theorem ext {s t : TTRSign Phon Cont}
    (hphon : s.phon = t.phon) (hcont : s.cont = t.cont) : s = t := by
  cases s; cases t; congr

/-- Map both fields of a TTR sign — the `Bifunctor.bimap` analogue. -/
def map (f : Phon → Phon') (g : Cont → Cont') (s : TTRSign Phon Cont) :
    TTRSign Phon' Cont' :=
  ⟨f s.phon, g s.cont⟩

@[simp] theorem map_phon (f : Phon → Phon') (g : Cont → Cont') (s : TTRSign Phon Cont) :
    (s.map f g).phon = f s.phon := rfl

@[simp] theorem map_cont (f : Phon → Phon') (g : Cont → Cont') (s : TTRSign Phon Cont) :
    (s.map f g).cont = g s.cont := rfl

@[simp] theorem map_id (s : TTRSign Phon Cont) : s.map id id = s := rfl

end TTRSign

-- (Cooper §1.3 intensional examples — `groundhog`/`woodchuck`,
--  `roundSquare`/`evenPrimeGt2`, `BoyHugsDog` subtyping demo —
--  moved to `Studies/Cooper2023.lean` §7.)

-- ============================================================================
-- Grammar (Cat, GSign, PSRule)
-- ============================================================================

/-! ## § 3.2 Hierarchical constituent structure

Events have hierarchical structure beyond flat string types. -/

section HierarchicalEvents

/-- Events in a bus trip. §3.2, ex (1–2). -/
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

§3.3, ex (12): Cat is a basic type with witnesses
s, np, det, n, v, vp — the categories needed for the English fragment. -/

/-- Syntactic categories for Cooper's English fragment.
§3.3, ex (12). -/
inductive Cat where
  | s   -- sentence
  | np  -- noun phrase
  | det -- determiner
  | n   -- common noun
  | v   -- verb
  | vp  -- verb phrase
  deriving Repr, DecidableEq

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
§3.3, ex (11). -/
inductive GSign (Phon Cont : Type) where
  | mk (phon : Phon) (cat : Cat)
       (daughters : List (GSign Phon Cont)) (cont : Cont)

namespace GSign
variable {Phon Cont : Type}

def phon : GSign Phon Cont → Phon
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
  phon := s.phon
  cont := s.cont

end GSign

/-- Create a lexical sign (no daughters).
§3.3, ex (18). -/
def lexSign {Phon Cont : Type} (phon : Phon) (c : Cat) (cont : Cont) :
    GSign Phon Cont :=
  .mk phon c [] cont

/-- Lexical signs have no daughters by construction. -/
theorem lexSign_isLexical {Phon Cont : Type}
    (phon : Phon) (c : Cat) (cont : Cont) :
    (lexSign phon c cont : GSign Phon Cont).isLexical = true := rfl

/-! ## § 3.3 Phrase structure rules -/

/-- A phrase structure rule: mother category and ordered daughter categories.
§3.3, ex (27). -/
structure PSRule where
  mother : Cat
  daughters : List Cat
  deriving Repr, DecidableEq

/-- S → NP VP. §3.3, ex (29). -/
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

§3.4 introduces the semantic type hierarchy:
- **Ppty** = [x:Ind] → RecType: maps individuals to situation types (properties)
- **Quant** = Ppty → RecType: maps properties to types (quantifiers)

These are the TTR analogues of Montague's ⟨e,t⟩ and ⟨⟨e,t⟩,t⟩. -/

/-- A property type: maps an individual to a type of situations.
§3.4, ex (30): Ppty = [x:Ind] → RecType.
Alias for `PredType E`. Montague type: ⟨e,t⟩. -/
abbrev Ppty (E : Type) := PredType E

/-- A quantifier type: maps a property to a type.
§3.4: Quant = Ppty → RecType.
Montague type: ⟨⟨e,t⟩,t⟩ — a generalized quantifier. -/
abbrev Quant (E : Type) := Ppty E → Type

/-- Bridge: TTR Ppty is structurally identical to PredType from §1.4.1. -/
theorem ppty_eq_predType (E : Type) : Ppty E = PredType E := rfl

/-! ## § 3.4 Compositional semantics functions -/

/-- Common noun content: wrap a predicate as a property.
§3.4, ex (30). -/
def semCommonNoun {E : Type} (p : E → Type) : Ppty E := p

/-- Proper name content as a generalized quantifier.
§3.4, ex (33): SemPropName(a) = λP:Ppty. P([x=a]). -/
def semPropName {E : Type} (a : E) : Quant E := λ P => P a

/-- The existential witness record type.
§3.4, ex (37). -/
structure ExistWitness (E : Type) (restr scope : Ppty E) where
  individual : E
  restrWit : restr individual
  scopeWit : scope individual

/-- Indefinite article content: maps a restrictor property to a quantifier.
§3.4, ex (37). -/
def semIndefArt {E : Type} (restr : Ppty E) : Quant E :=
  λ scope => ExistWitness E restr scope

/-- Copula "be" for predicate nominal constructions.
§3.4, ex (78). -/
def semBe {E : Type} (Q : Quant E) : Ppty E :=
  λ x => Q (λ y => propT (x = y))

/-! ## § 3.4 Property extension and existential quantification -/

/-- Property extension: whether an individual has property P.
§3.4, ex (46). -/
def propExtension {E : Type} (P : Ppty E) (a : E) : Prop := Nonempty (P a)

/-- Existential quantification as property-extension overlap.
§3.4, ex (55). -/
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
  -- bare `simp` retained: `existPQ` unfolds to `∃ a, Nonempty (PLift _) ∧ Nonempty (PLift _)`
  -- and the trip through `PLift`/`Nonempty` involves multiple non-`@[simp]` rewrites
  simp [existPQ]

-- (Cooper §3.4 derivation examples — `Conductor`/`Composer`/`Dudamel`/
--  `Beethoven`, `cnstrIsA`, `aConductorIsDudamel` reversal demo —
--  moved to `Studies/Cooper2023.lean` §8.)


-- ============================================================================
-- Proposition Granularity Hierarchy
-- ============================================================================

/-! ## Proposition granularity: Set W vs TTR types

[chatzikyriakidis-etal-2025] §2 argue that the choice of proposition
type determines what distinctions a semantic theory can make. We formalize
the granularity hierarchy:

  `IType` (finest) > `Type` (medium) > `Set W` (coarsest)

- `Set W` identifies all propositions with the same truth conditions
- TTR types distinguish propositions that are merely co-extensional
- `IType` adds intensional identity (name-based distinction)

The key consequence: attitude verbs that need to distinguish Hesperus-beliefs
from Phosphorus-beliefs cannot use `Set W` — they need `IType`. -/

/-- Possible-worlds propositions collapse TTR distinctions:
two ITypes with different names but same carrier map to the same Prop.
This is why Set W is too coarse for attitude reports. -/
theorem prop_collapses_intensional_distinctions (W : Type*) :
    ∃ T₁ T₂ : IType,
      -- Intensionally distinct in TTR
      ¬ T₁.intEq T₂ ∧
      -- But indistinguishable as Set W propositions
      -- (both map to the same truth value at every world)
      (∀ (embed : IType → Set W),
        (∀ T w, embed T w ↔ Nonempty T.carrier) →
        ∀ w, embed T₁ w ↔ embed T₂ w) := by
  refine ⟨⟨Unit, "hesperus_rises"⟩, ⟨Unit, "phosphorus_rises"⟩,
    by simp [IType.intEq], λ embed hembed w => ?_⟩
  -- Both carriers are Unit, so Nonempty T₁.carrier ↔ Nonempty T₂.carrier
  constructor
  · intro h; exact (hembed ⟨Unit, "phosphorus_rises"⟩ w).mpr
      ((hembed ⟨Unit, "hesperus_rises"⟩ w).mp h)
  · intro h; exact (hembed ⟨Unit, "hesperus_rises"⟩ w).mpr
      ((hembed ⟨Unit, "phosphorus_rises"⟩ w).mp h)

/-- TTR types are strictly finer than Set W:
there exist types that TTR distinguishes but Set W cannot.
(This is `ext_equiv_not_implies_int_eq` restated in terms of the
granularity hierarchy.) -/
theorem ttr_strictly_finer_than_worlds :
    -- TTR can distinguish types that are co-extensional
    (∃ T₁ T₂ : IType, T₁.extEquiv T₂ ∧ ¬ T₁.intEq T₂) ∧
    -- But Set identifies co-extensional propositions
    (∀ (W : Type) (p q : Set W),
      p = q → ∀ w, p w ↔ q w) :=
  ⟨⟨⟨Unit, "groundhog"⟩, ⟨Unit, "woodchuck"⟩,
    ⟨Equiv.refl Unit⟩, by simp [IType.intEq]⟩,
   λ _ _ _ heq w => by rw [heq]⟩

end Semantics.TypeTheoretic
