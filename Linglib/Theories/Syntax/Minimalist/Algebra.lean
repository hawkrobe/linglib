import Linglib.Theories.Syntax.Minimalist.Basic
import Mathlib.Algebra.Free

/-!
# Algebraic Structure of Merge — Free Magma Encoding @cite{marcolli-chomsky-berwick-2025}

`SyntacticObject` is *defined* as `FreeMagma LIToken` (in `Basic.lean`),
so the algebraic content of @cite{marcolli-chomsky-berwick-2025}
Definition 1.1.1 is available without an isomorphism: `Mul`, `length`,
`length_pos`, `lift` come from mathlib's `FreeMagma` API directly.

## Planar vs. abstract — what mathlib `FreeMagma` gives us

@cite{marcolli-chomsky-berwick-2025} Definition 1.1.1 specifies
$\mathcal{SO} = \mathrm{Magma}_{na,c}(\mathcal{SO}_0, \mathfrak{M})$:
the free *non-associative commutative* magma, with binary Merge
$\mathfrak{M}(\alpha,\beta) = \{\alpha,\beta\}$. The set notation makes
the operation commutative — there is no left/right.

Mathlib's `FreeMagma α` is the free *non-associative non-commutative*
magma over $α$ — i.e., abstract binary trees *with* a planar embedding
(ordered pairs $(\alpha,\beta)$). MCB §1.1.3.1 (p. 25) and §1.13
discuss this distinction explicitly: planar trees correspond to the
externalized form of sentences, while abstract (nonplanar) trees are
the core syntactic object.

We use the planar `FreeMagma` encoding because:
- it gives us mathlib's algebraic infrastructure for free,
- planar SOs match the existing `linearize` / `phonYield` machinery
  that interprets the SO as carrying its externalization choice,
- the abstract MCB-faithful object is recoverable as the quotient of
  `SyntacticObject` by the commutativity setoid `nonplanarEquiv` below.

This file does *not* develop the abstract (nonplanar) quotient further;
operations and predicates that distinguish $a*b$ from $b*a$ should be
read as living on the externalized side of the syntax–PF pipeline, and
core-syntax theorems should be stated as respecting `nonplanarEquiv`.

## Wholesale Late Merger and countercyclicity

@cite{marcolli-chomsky-berwick-2025} §1.7 argues that countercyclic
operations (Late Merger, Wholesale Late Merger of
@cite{takahashi-hulsey-2009}) are *not* extensions of Merge but
operations on a separate Lie-algebra structure dual to the workspace
Hopf algebra; they reduce to External/Internal Merge under that
duality. Our `Step.wlm` constructor in `Derivation.lean` is therefore a
*derivational* convenience that should be eliminable in favor of a
combination of External/Internal Merge — that reduction is left as a
TODO at the derivation layer.

## Main definitions

- `nonplanarEquiv : Setoid SyntacticObject` — the smallest congruence
  making `*` commutative; quotient = MCB-faithful abstract $\mathcal{SO}$.
- `SyntacticObject.liftMagma` — universal property (alias of
  `FreeMagma.lift` precomposed with the magma-hom view of identity).
- `properSubterm` — proper-subterm relation in the magma.
- `contains_iff_properSubterm` — bridges `contains` (Basic.lean) with
  the algebraic subterm relation.
- `leafCount_pos` — derived from `FreeMagma.length_pos`.
- `leafCount_eq_freeMagma_length` — `leafCount = FreeMagma.length`
  (now `rfl`, since the abbrev is the FreeMagma).

-/

namespace Minimalist

open FreeMagma

/-! ## Planar vs. abstract: the commutativity congruence

The abstract (nonplanar) syntactic objects of
@cite{marcolli-chomsky-berwick-2025} Definition 1.1.1 are the
equivalence classes of `SyntacticObject` under the smallest congruence
that makes Merge commutative at every node.
-/

/-- Smallest congruence making Merge (`*`) commutative — its quotient
    is the abstract (MCB-faithful, nonplanar) syntactic-object set. -/
inductive nonplanarRel : SyntacticObject → SyntacticObject → Prop where
  | refl  (x : SyntacticObject) : nonplanarRel x x
  | symm  {x y : SyntacticObject} : nonplanarRel x y → nonplanarRel y x
  | trans {x y z : SyntacticObject} :
      nonplanarRel x y → nonplanarRel y z → nonplanarRel x z
  | comm  (a b : SyntacticObject) : nonplanarRel (a * b) (b * a)
  | congr_left  {a a'} (b : SyntacticObject) :
      nonplanarRel a a' → nonplanarRel (a * b) (a' * b)
  | congr_right (a : SyntacticObject) {b b'} :
      nonplanarRel b b' → nonplanarRel (a * b) (a * b')

/-- The nonplanar setoid; `Quotient nonplanarEquiv` is MCB's
    abstract $\mathcal{SO}$. -/
def nonplanarEquiv : Setoid SyntacticObject where
  r := nonplanarRel
  iseqv := ⟨nonplanarRel.refl, nonplanarRel.symm, nonplanarRel.trans⟩

/-! ## Mul and Merge identifications

`SyntacticObject` inherits `Mul` from `FreeMagma`. The `merge`
definition in `Basic.lean` is `FreeMagma.mul`, hence definitionally
equal to `(· * ·)`. -/

@[simp]
theorem mul_eq_merge (x y : SyntacticObject) : x * y = merge x y := rfl

@[simp]
theorem mul_eq_node (x y : SyntacticObject) : x * y = .node x y := rfl

/-- Merge IS magma multiplication (definitional). -/
theorem merge_is_freeMagma_mul (x y : SyntacticObject) :
    merge x y = x * y := rfl

/-! ## Universal property

The universal property of `FreeMagma` IS the universal property of
`SyntacticObject`: any function `LIToken → M` (with `M` a magma) lifts
uniquely to a magma homomorphism `SyntacticObject →ₙ* M`. -/

/-- Universal property: lift `LIToken → M` to `SyntacticObject →ₙ* M`. -/
def SyntacticObject.liftMagma {M : Type*} [Mul M] : (LIToken → M) ≃ (SyntacticObject →ₙ* M) :=
  FreeMagma.lift

@[simp]
theorem SyntacticObject.liftMagma_leaf {M : Type*} [Mul M]
    (f : LIToken → M) (tok : LIToken) :
    SyntacticObject.liftMagma f (.leaf tok) = f tok := rfl

@[simp]
theorem SyntacticObject.liftMagma_node {M : Type*} [Mul M]
    (f : LIToken → M) (a b : SyntacticObject) :
    SyntacticObject.liftMagma f (.node a b) =
      SyntacticObject.liftMagma f a * SyntacticObject.liftMagma f b := rfl

/-! ## Containment ↔ proper subterm

Connect `contains` (Basic.lean) with subterm structure in the free magma. -/

/-- An SO is a proper subterm of another iff it appears strictly within it. -/
inductive properSubterm : SyntacticObject → SyntacticObject → Prop where
  | left (a b : SyntacticObject) : properSubterm a (.node a b)
  | right (a b : SyntacticObject) : properSubterm b (.node a b)
  | trans_left (x a b : SyntacticObject) : properSubterm x a → properSubterm x (.node a b)
  | trans_right (x a b : SyntacticObject) : properSubterm x b → properSubterm x (.node a b)

/-- Immediate containment implies proper subterm. -/
theorem immediatelyContains_implies_properSubterm {x y : SyntacticObject}
    (h : immediatelyContains x y) : properSubterm y x := by
  match x, h with
  | .node a b, h =>
    simp [immediatelyContains] at h
    rcases h with rfl | rfl
    · exact .left y b
    · exact .right a y
  | .leaf _, h => exact h.elim

/-- Containment implies proper subterm. -/
theorem contains_implies_properSubterm {x y : SyntacticObject}
    (h : contains x y) : properSubterm y x := by
  induction h with
  | imm x y himm => exact immediatelyContains_implies_properSubterm himm
  | trans x _ z himm _hyz ih =>
    match x, himm with
    | .node l r, himm =>
      simp [immediatelyContains] at himm
      rcases himm with rfl | rfl
      · exact .trans_left _ _ r ih
      · exact .trans_right _ l _ ih
    | .leaf _, himm => exact himm.elim

/-- Proper subterm implies containment. -/
theorem properSubterm_implies_contains {x y : SyntacticObject}
    (h : properSubterm x y) : contains y x := by
  induction h with
  | left a b =>
    exact .imm (.node a b) a (by simp [immediatelyContains])
  | right a b =>
    exact .imm (.node a b) b (by simp [immediatelyContains])
  | trans_left x a b _hsub ih =>
    exact .trans (.node a b) x a (by simp [immediatelyContains]) ih
  | trans_right x a b _hsub ih =>
    exact .trans (.node a b) x b (by simp [immediatelyContains]) ih

/-- Containment = proper subterm (the bridge). -/
theorem contains_iff_properSubterm (x y : SyntacticObject) :
    contains x y ↔ properSubterm y x :=
  ⟨contains_implies_properSubterm, properSubterm_implies_contains⟩

/-! ## Bridge to mathlib `FreeMagma.length`

`FreeMagma.length` counts leaves (1 for `.of`, sum for `.mul`). Since
`SyntacticObject = FreeMagma LIToken` and `.leaf`/`.node` are the
`.of`/`.mul` shims, this is `leafCount` definitionally. -/

/-- `SyntacticObject.leafCount` is `FreeMagma.length`. -/
theorem leafCount_eq_freeMagma_length (so : SyntacticObject) :
    so.leafCount = so.length := by
  induction so with
  | leaf _ => rfl
  | node a b iha ihb =>
    simp [SyntacticObject.leafCount, FreeMagma.length, iha, ihb]

/-- `leafCount` is always positive — derived from `FreeMagma.length_pos`. -/
theorem leafCount_pos (so : SyntacticObject) : 0 < so.leafCount := by
  rw [leafCount_eq_freeMagma_length]
  exact so.length_pos

end Minimalist
