module

public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Sublattice
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Data.Fintype.Defs

/-!
# Generalized quantifiers

This file defines generalized quantifier denotations and the properties of them that the
theory of determiners studies. A generalized quantifier on a type `α` is a relation between two
predicates on `α`, the restrictor and the scope, so `GQ α` is `(α → Prop) → (α → Prop) → Prop`
and inherits the Boolean algebra of the Pi type. The properties are Barwise and Cooper's
conservativity, monotonicity, symmetry and strength, Peters and Westerståhl's left monotonicity,
smoothness and anti-additivity, van Benthem's relational properties and quantity invariance in
the sense of Mostowski. The operations are the negations and the dual, the Boolean operations
named for determiner conjunction and disjunction, and restriction by an adjective. The concrete
denotations are in `Quantification/Basic.lean` and the type ⟨1⟩ quantifiers in
`Quantification/NP.lean`.

## Main definitions

* `GQ`, `GQ.Family`, `NP`: quantifier denotations on a type, on every finite type, and of
  type ⟨1⟩.
* `GQ.Conservative`, `GQ.ScopeUpwardMono`, `GQ.RestrictorUpwardMono`, `GQ.QSymmetric`,
  `GQ.PositiveStrong`: the properties of Barwise and Cooper.
* `GQ.UpSEMon`, `GQ.Smooth`, `GQ.LeftAntiAdditive`: the left monotonicities of Peters and
  Westerståhl.
* `GQ.QuasiReflexive`, `GQ.Filtrating`, `GQ.QuantityInvariant`: van Benthem's relational
  properties and quantity invariance.
* `GQ.outerNeg`, `GQ.innerNeg`, `GQ.dualQ`, `GQ.adjRestrict`: the operations.
* `NP.individual`, `NP.LivesOn`: the Montague lift and the live-on property.

## Implementation notes

Extension, the independence of a quantifier from the ambient universe, holds by construction,
since a denotation is given on one type. Decidability of the concrete denotations is recovered
pointwise from `[Fintype α]` and decidable restrictor and scope.

## References

* [barwise-cooper-1981]
* [keenan-stavi-1986]
* [mostowski-1957]
* [partee-1987]
* [peters-westerstahl-2006]
* [van-benthem-1984]
-/

@[expose] public section

namespace Quantifier

/-- A generalized quantifier denotation maps a restrictor and a scope to a proposition. Under
the pointwise ordering of `α → Prop` it is a binary relation between predicates. -/
abbrev GQ (α : Type*) := (α → Prop) → (α → Prop) → Prop

universe u

/-- A determiner denotation given on every finite domain, the object from which a lexicon
entry's available readings are drawn. -/
abbrev GQ.Family : Type (u + 1) := ∀ (α : Type u) [Fintype α], GQ α

/-- A type ⟨1⟩ quantifier, the denotation of a noun phrase, is a property of properties, a
quantifier proper in Barwise and Cooper's sense. It is definitionally `Cont Prop α`, the
scope-taking continuation. -/
abbrev NP (α : Type*) := (α → Prop) → Prop

variable {α : Type*}

namespace GQ

/-! ### Conservativity and monotonicity -/

/-- A quantifier is conservative when `Q(A, B) ↔ Q(A, A ∩ B)`, so that only the elements of the
scope that are in the restrictor matter. Barwise and Cooper's universal says that every simple
determiner denotes a conservative quantifier. -/
def Conservative (q : GQ α) : Prop :=
  ∀ (R S : α → Prop), q R S ↔ q R (fun x => R x ∧ S x)

/-- A quantifier is scope-upward monotone when `B ⊆ B'` and `Q(A, B)` give `Q(A, B')`, which is
`∀ R, Monotone (q R)` under the pointwise ordering. -/
def ScopeUpwardMono (q : GQ α) : Prop :=
  ∀ (R S S' : α → Prop), (∀ x, S x → S' x) → q R S → q R S'

/-- A quantifier is scope-downward monotone when `B ⊆ B'` and `Q(A, B')` give `Q(A, B)`, which is
`∀ R, Antitone (q R)`. -/
def ScopeDownwardMono (q : GQ α) : Prop :=
  ∀ (R S S' : α → Prop), (∀ x, S x → S' x) → q R S' → q R S

/-- A quantifier satisfies the intersection condition when `Q(A, B)` depends only on `A ∩ B`. -/
def IntersectionCondition (q : GQ α) : Prop :=
  ∀ (R S R' S' : α → Prop),
    (∀ x, (R x ∧ S x) ↔ (R' x ∧ S' x)) →
    (q R S ↔ q R' S')

/-- A quantifier is symmetric when `Q(A, B) ↔ Q(B, A)`. Under conservativity this is the
intersection condition. -/
def QSymmetric (q : GQ α) : Prop :=
  ∀ (R S : α → Prop), q R S ↔ q S R

/-- A quantifier is restrictor-upward monotone, or persistent, when `A ⊆ A'` and `Q(A, B)` give
`Q(A', B)`. -/
def RestrictorUpwardMono (q : GQ α) : Prop :=
  ∀ (R R' S : α → Prop), (∀ x, R x → R' x) → q R S → q R' S

/-- A quantifier is restrictor-downward monotone, or anti-persistent, when `A ⊆ A'` and
`Q(A', B)` give `Q(A, B)`. -/
def RestrictorDownwardMono (q : GQ α) : Prop :=
  ∀ (R R' S : α → Prop), (∀ x, R x → R' x) → q R' S → q R S

/-! ### Strength -/

/-- A quantifier is positive strong when `Q(A, A)` holds for every `A`, as for *every*. -/
def PositiveStrong (q : GQ α) : Prop :=
  ∀ (R : α → Prop), q R R

/-- A quantifier is negative strong when `Q(A, A)` fails for every `A`, as for *neither*. -/
def NegativeStrong (q : GQ α) : Prop :=
  ∀ (R : α → Prop), ¬ q R R

/-- A quantifier has the existential property when `Q(A, B) ↔ Q(A ∩ B, ⊤)`, the property of the
determiners felicitous in *there*-sentences. -/
def Existential (q : GQ α) : Prop :=
  ∀ (R S : α → Prop), q R S ↔ q (fun x => R x ∧ S x) (fun _ => True)

/-! ### Left monotonicity and smoothness

Peters and Westerståhl's four left monotonicities enlarge or shrink the restrictor by elements
inside or outside the scope. On the number triangle, with `k = |A ∖ B|` and `m = |A ∩ B|`,
`UpSEMon` moves `(k, m)` to `(k, m + 1)`, `UpSWMon` to `(k + 1, m)`, `DownNWMon` moves
`(k, m + 1)` to `(k, m)` and `DownNEMon` moves `(k + 1, m)` to `(k, m)`. -/

/-- A quantifier is ↑SE monotone when enlarging the restrictor by elements of the scope
preserves it, so that `A ⊆ A'`, `A ∖ B = A' ∖ B` and `Q(A, B)` give `Q(A', B)`. -/
def UpSEMon (q : GQ α) : Prop :=
  ∀ (R S R' : α → Prop),
    (∀ x, R x → R' x) →
    (∀ x, R' x → ¬ S x → R x) →
    q R S → q R' S

/-- A quantifier is ↑SW monotone when enlarging the restrictor by elements outside the scope
preserves it, so that `A ⊆ A'`, `A ∩ B = A' ∩ B` and `Q(A, B)` give `Q(A', B)`. -/
def UpSWMon (q : GQ α) : Prop :=
  ∀ (R S R' : α → Prop),
    (∀ x, R x → R' x) →
    (∀ x, R' x → S x → R x) →
    q R S → q R' S

/-- A quantifier is ↓NW monotone when shrinking the restrictor by elements of the scope
preserves it, so that `A' ⊆ A`, `A ∖ B = A' ∖ B` and `Q(A, B)` give `Q(A', B)`. -/
def DownNWMon (q : GQ α) : Prop :=
  ∀ (R S R' : α → Prop),
    (∀ x, R' x → R x) →
    (∀ x, R x → ¬ S x → R' x) →
    q R S → q R' S

/-- A quantifier is ↓NE monotone when shrinking the restrictor by elements outside the scope
preserves it, so that `A' ⊆ A`, `A ∩ B = A' ∩ B` and `Q(A, B)` give `Q(A', B)`. -/
def DownNEMon (q : GQ α) : Prop :=
  ∀ (R S R' : α → Prop),
    (∀ x, R' x → R x) →
    (∀ x, R x → S x → R' x) →
    q R S → q R' S

/-- A quantifier is smooth when it is ↓NE and ↑SE monotone; smooth quantifiers are scope-upward
monotone. -/
def Smooth (q : GQ α) : Prop := DownNEMon q ∧ UpSEMon q

/-- A quantifier is co-smooth when its inner negation is smooth, that is, when it is ↓NW and ↑SW
monotone. -/
def CoSmooth (q : GQ α) : Prop := DownNWMon q ∧ UpSWMon q

/-- A quantifier is left anti-additive when `Q(A ∪ B, C) ↔ Q(A, C) ∧ Q(B, C)`. -/
def LeftAntiAdditive (q : GQ α) : Prop :=
  ∀ (R R' S : α → Prop),
    q (fun x => R x ∨ R' x) S ↔ (q R S ∧ q R' S)

/-- A quantifier is right anti-additive when `Q(A, B ∪ C) ↔ Q(A, B) ∧ Q(A, C)`. -/
def RightAntiAdditive (q : GQ α) : Prop :=
  ∀ (R S S' : α → Prop),
    q R (fun x => S x ∨ S' x) ↔ (q R S ∧ q R S')

/-! ### Relational properties

Van Benthem reads a quantifier as a relation between predicates and asks which relational
properties it has; *all* is the transitive antisymmetric one and *not all* the linear one. -/

/-- A quantifier is transitive when `Q(A, B)` and `Q(B, C)` give `Q(A, C)`. -/
def QTransitive (q : GQ α) : Prop :=
  ∀ (A B C : α → Prop), q A B → q B C → q A C

/-- A quantifier is antisymmetric when `Q(A, B)` and `Q(B, A)` give `A = B`. -/
def QAntisymmetric (q : GQ α) : Prop :=
  ∀ (A B : α → Prop), q A B → q B A → A = B

/-- A quantifier is linear when any two predicates are equal or related in one direction. -/
def QLinear (q : GQ α) : Prop :=
  ∀ (A B : α → Prop), A = B ∨ q A B ∨ q B A

/-- A quantifier is quasi-reflexive when `Q(A, B)` gives `Q(A, A)`, as for *some*. -/
def QuasiReflexive (q : GQ α) : Prop :=
  ∀ (A B : α → Prop), q A B → q A A

/-- A quantifier is quasi-universal when `Q(A, A)` gives `Q(A, B)` for every `B`, as for *no*. -/
def QuasiUniversal (q : GQ α) : Prop :=
  ∀ (A B : α → Prop), q A A → q A B

/-- A quantifier is almost connected when `Q(A, B)` gives `Q(A, C)` or `Q(C, B)` for every `C`,
which is the transitivity of its complement. -/
def AlmostConnected (q : GQ α) : Prop :=
  ∀ (A B C : α → Prop), q A B → q A C ∨ q C B

/-- A quantifier is asymmetric when `Q(A, B)` excludes `Q(B, A)`. -/
def QAsymmetric (q : GQ α) : Prop :=
  ∀ (A B : α → Prop), q A B → ¬ q B A

/-- A quantifier is circular when `Q(A, B)` and `Q(B, C)` give `Q(C, A)`. -/
def QCircular (q : GQ α) : Prop :=
  ∀ (A B C : α → Prop), q A B → q B C → q C A

/-- A quantifier is right continuous when `Q(A, B₁)`, `Q(A, B₂)` and `B₁ ⊆ B ⊆ B₂` give
`Q(A, B)`; every scope-monotone quantifier is right continuous. -/
def RightContinuous (q : GQ α) : Prop :=
  ∀ (A B B₁ B₂ : α → Prop),
    (∀ x, B₁ x → B x) →
    (∀ x, B x → B₂ x) →
    q A B₁ → q A B₂ → q A B

/-- A quantifier is scope-intersective when `Q(A, B)` and `Q(A, C)` give `Q(A, B ∩ C)`. -/
def ScopeIntersective (q : GQ α) : Prop :=
  ∀ (A B C : α → Prop),
    q A B → q A C → q A (fun x => B x ∧ C x)

/-- A quantifier is filtrating when it is scope-upward monotone and scope-intersective, so that
its scopes at a fixed restrictor form a filter. -/
def Filtrating (q : GQ α) : Prop := ScopeUpwardMono q ∧ ScopeIntersective q

/-! ### Invariance -/

/-- A quantifier is quantity invariant when it is invariant under permutations of the domain,
so that `Q(A, B)` depends only on the pattern of the two predicates and not on which elements
satisfy them. This is Mostowski's permutation invariance for type ⟨1, 1⟩ quantifiers. -/
def QuantityInvariant (q : GQ α) : Prop :=
  ∀ (A B A' B' : α → Prop) (f : α → α),
    Function.Bijective f →
    (∀ x, A (f x) ↔ A' x) → (∀ x, B (f x) ↔ B' x) →
    (q A B ↔ q A' B')

/-! ### Negations and the dual -/

/-- The outer negation of a quantifier, `(~Q)(A, B) = ¬ Q(A, B)`, is its Boolean complement,
named for the duality square it forms with the inner negation and the dual. -/
abbrev outerNeg (q : GQ α) : GQ α := qᶜ

@[simp] theorem outerNeg_apply (q : GQ α) (R S : α → Prop) : outerNeg q R S = ¬ q R S := rfl

/-- The inner negation of a quantifier, `(Q~)(A, B) = Q(A, ¬ B)`. -/
def innerNeg (q : GQ α) : GQ α :=
  fun R S => q R (fun x => ¬ S x)

/-- The dual of a quantifier, `Q̌ = ~(Q~)`, so that the dual of *every* is *some*. -/
def dualQ (q : GQ α) : GQ α :=
  outerNeg (innerNeg q)

/-! ### Boolean operations and restriction -/

/-- The meet of two quantifiers is determiner conjunction, the meet `⊓` of the Boolean algebra
`GQ α` under the name of the linguistic operation. -/
abbrev gqMeet (f g : GQ α) : GQ α := f ⊓ g

@[simp] theorem gqMeet_apply (f g : GQ α) (R S : α → Prop) :
    gqMeet f g R S = (f R S ∧ g R S) := rfl

/-- The join of two quantifiers is determiner disjunction, the join `⊔` of the Boolean algebra
`GQ α`. -/
abbrev gqJoin (f g : GQ α) : GQ α := f ⊔ g

@[simp] theorem gqJoin_apply (f g : GQ α) (R S : α → Prop) :
    gqJoin f g R S = (f R S ∨ g R S) := rfl

/-- The restriction of a quantifier by an adjective or relative clause narrows the restrictor,
so that *tall student* is *student* and *tall*. -/
def adjRestrict (q : GQ α) (adj : α → Prop) : GQ α :=
  fun R S => q (fun x => R x ∧ adj x) S

/-- The type ⟨1⟩ quantifier a determiner and a restrictor denote, `restrict Q A B = Q A B`. -/
def restrict (q : GQ α) (A : α → Prop) : NP α := q A

/-! ### The monotonicity properties as `Monotone` and `Antitone` -/

/-- Scope-upward monotonicity is `Monotone` of every section, under the pointwise ordering. -/
theorem scopeUpMono_iff_monotone (q : GQ α) : ScopeUpwardMono q ↔ ∀ R, Monotone (q R) :=
  Iff.rfl

/-- Scope-downward monotonicity is `Antitone` of every section. -/
theorem scopeDownMono_iff_antitone (q : GQ α) : ScopeDownwardMono q ↔ ∀ R, Antitone (q R) :=
  Iff.rfl

/-- Restrictor-upward monotonicity is `Monotone` of every restrictor section. -/
theorem restrictorUpMono_iff_monotone (q : GQ α) :
    RestrictorUpwardMono q ↔ ∀ S, Monotone (fun R => q R S) :=
  ⟨fun h S _ _ hle hq => h _ _ S hle hq, fun h _ _ S hle hq => h S hle hq⟩

/-- Restrictor-downward monotonicity is `Antitone` of every restrictor section. -/
theorem restrictorDownMono_iff_antitone (q : GQ α) :
    RestrictorDownwardMono q ↔ ∀ S, Antitone (fun R => q R S) :=
  ⟨fun h S _ _ hle hq => h _ _ S hle hq, fun h _ _ S hle hq => h S hle hq⟩

end GQ

/-! ### Type ⟨1⟩ quantifiers -/

namespace NP

/-- A type ⟨1⟩ quantifier lives on `A` when `Q(B) ↔ Q(A ∩ B)` for every `B`. -/
def LivesOn (Q : NP α) (A : α → Prop) : Prop :=
  ∀ B, Q B ↔ Q (fun x => A x ∧ B x)

/-- The Montague lift of an entity is the principal ultrafilter it generates, the type ⟨1⟩
quantifier of the properties it has; it is Partee's LIFT and the continuation `pure`. -/
def individual (a : α) : NP α := fun P => P a

/-- The Montague lift is injective, since an entity is recovered from its principal
ultrafilter. -/
theorem individual_injective : Function.Injective (individual (α := α)) :=
  fun a b h => (show b = a from (congrFun h (· = a)).mp rfl).symm

/-- The singleton property of an entity, `ident j = {j}`, whose lift is `individual j`. -/
def ident (j : α) : α → Prop := (· = j)

theorem ident_injective : Function.Injective (ident (α := α)) :=
  fun a _ h => (congrFun h a).mp rfl

end NP

end Quantifier
