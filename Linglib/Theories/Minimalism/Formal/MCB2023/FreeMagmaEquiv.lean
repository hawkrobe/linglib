/-
# SyntacticObject ≅ FreeMagma LIToken

The key observation of Marcolli, Chomsky & Berwick (2023) is that Merge
endows syntactic objects with free magma structure. We make this precise:
`SyntacticObject` (leaf/node) and mathlib's `FreeMagma LIToken` (of/mul)
are literally the same inductive type.

Establishing this isomorphism connects linglib's syntax to mathlib's
entire algebraic hierarchy.

## Main definitions

- `toFreeMagma` / `fromFreeMagma`: the explicit maps
- `soFreeMagmaEquiv`: the type equivalence SO ≃ FreeMagma LIToken
- `Mul SyntacticObject`: positions SO as a magma via `merge`
- `toFreeMagmaMulHom`: magma homomorphism SO →ₙ* FreeMagma LIToken
- `SyntacticObject.liftMagma`: universal property via FreeMagma.lift

## References

- Marcolli, M., Chomsky, N. & Berwick, R.C. (2023). "Mathematical Structure of
  Syntactic Merge"
-/

import Linglib.Theories.Minimalism.Core.Containment
import Mathlib.Algebra.Free

namespace Minimalism

open FreeMagma

/-! ## The isomorphism -/

/-- Map SO to FreeMagma: leaf ↦ of, node ↦ mul -/
def toFreeMagma : SyntacticObject → FreeMagma LIToken
  | .leaf tok => .of tok
  | .node a b => toFreeMagma a * toFreeMagma b

/-- Map FreeMagma to SO: of ↦ leaf, mul ↦ node -/
def fromFreeMagma : FreeMagma LIToken → SyntacticObject
  | .of tok => .leaf tok
  | .mul a b => .node (fromFreeMagma a) (fromFreeMagma b)

@[simp]
theorem toFreeMagma_leaf (tok : LIToken) :
    toFreeMagma (.leaf tok) = .of tok := rfl

@[simp]
theorem toFreeMagma_node (a b : SyntacticObject) :
    toFreeMagma (.node a b) = toFreeMagma a * toFreeMagma b := rfl

@[simp]
theorem fromFreeMagma_of (tok : LIToken) :
    fromFreeMagma (.of tok) = .leaf tok := rfl

@[simp]
theorem fromFreeMagma_mul (a b : FreeMagma LIToken) :
    fromFreeMagma (a * b) = .node (fromFreeMagma a) (fromFreeMagma b) := rfl

theorem fromFreeMagma_toFreeMagma (so : SyntacticObject) :
    fromFreeMagma (toFreeMagma so) = so := by
  induction so with
  | leaf tok => simp
  | node a b iha ihb => simp [iha, ihb]

theorem toFreeMagma_fromFreeMagma (fm : FreeMagma LIToken) :
    toFreeMagma (fromFreeMagma fm) = fm := by
  induction fm with
  | ih1 tok => simp
  | ih2 a b iha ihb => simp [iha, ihb]

/-- SyntacticObject ≃ FreeMagma LIToken — the core bridge -/
def soFreeMagmaEquiv : SyntacticObject ≃ FreeMagma LIToken where
  toFun := toFreeMagma
  invFun := fromFreeMagma
  left_inv := fromFreeMagma_toFreeMagma
  right_inv := toFreeMagma_fromFreeMagma

/-! ## Mul instance: Merge is the magma operation -/

instance : Mul SyntacticObject := ⟨merge⟩

theorem mul_eq_merge (x y : SyntacticObject) : x * y = merge x y := rfl

theorem mul_eq_node (x y : SyntacticObject) : x * y = .node x y := rfl

/-- Merge is literally FreeMagma multiplication under the isomorphism (definitional) -/
theorem merge_is_freeMagma_mul (x y : SyntacticObject) :
    toFreeMagma (merge x y) = toFreeMagma x * toFreeMagma y := rfl

/-! ## Magma homomorphism -/

/-- toFreeMagma as a magma homomorphism -/
def toFreeMagmaMulHom : SyntacticObject →ₙ* FreeMagma LIToken where
  toFun := toFreeMagma
  map_mul' := λ _ _ => rfl

/-- fromFreeMagma as a magma homomorphism -/
def fromFreeMagmaMulHom : FreeMagma LIToken →ₙ* SyntacticObject where
  toFun := fromFreeMagma
  map_mul' := λ _ _ => rfl

/-! ## Universal property

`SyntacticObject` satisfies the same universal property as `FreeMagma`:
any function `LIToken → M` (where M is a magma) extends uniquely to a
magma homomorphism `SyntacticObject →ₙ* M`. -/

/-- Universal property: lift a function LIToken → M to a magma hom SO →ₙ* M -/
def SyntacticObject.liftMagma {M : Type*} [Mul M] (f : LIToken → M) :
    SyntacticObject →ₙ* M :=
  (FreeMagma.lift f).comp toFreeMagmaMulHom

theorem SyntacticObject.liftMagma_leaf {M : Type*} [Mul M] (f : LIToken → M) (tok : LIToken) :
    SyntacticObject.liftMagma f (.leaf tok) = f tok := by
  simp [SyntacticObject.liftMagma, MulHom.comp_apply, toFreeMagmaMulHom]

theorem SyntacticObject.liftMagma_node {M : Type*} [Mul M] (f : LIToken → M)
    (a b : SyntacticObject) :
    SyntacticObject.liftMagma f (.node a b) =
      SyntacticObject.liftMagma f a * SyntacticObject.liftMagma f b := by
  simp [SyntacticObject.liftMagma, MulHom.comp_apply, toFreeMagmaMulHom, map_mul]

/-! ## Containment ↔ proper subterm

Connect `contains` (Containment.lean) with subterm structure in the free magma. -/

/-- An SO is a proper subterm of another iff it appears strictly within it -/
inductive properSubterm : SyntacticObject → SyntacticObject → Prop where
  | left (a b : SyntacticObject) : properSubterm a (.node a b)
  | right (a b : SyntacticObject) : properSubterm b (.node a b)
  | trans_left (x a b : SyntacticObject) : properSubterm x a → properSubterm x (.node a b)
  | trans_right (x a b : SyntacticObject) : properSubterm x b → properSubterm x (.node a b)

/-- Immediate containment implies proper subterm -/
theorem immediatelyContains_implies_properSubterm {x y : SyntacticObject}
    (h : immediatelyContains x y) : properSubterm y x := by
  cases x with
  | leaf _ => exact absurd h (by simp [immediatelyContains])
  | node a b =>
    simp [immediatelyContains] at h
    rcases h with rfl | rfl
    · exact .left y b
    · exact .right a y

/-- Containment implies proper subterm -/
theorem contains_implies_properSubterm {x y : SyntacticObject}
    (h : contains x y) : properSubterm y x := by
  induction h with
  | imm x y himm => exact immediatelyContains_implies_properSubterm himm
  | trans x y z himm _hyz ih =>
    obtain ⟨l, r, rfl⟩ : ∃ l r, x = .node l r := by
      cases x with
      | leaf tok => simp [immediatelyContains] at himm
      | node l r => exact ⟨l, r, rfl⟩
    simp [immediatelyContains] at himm
    rcases himm with rfl | rfl
    · exact .trans_left y _ r ih
    · exact .trans_right y l _ ih

/-- Proper subterm implies containment -/
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

/-- Containment = proper subterm (the key bridge theorem) -/
theorem contains_iff_properSubterm (x y : SyntacticObject) :
    contains x y ↔ properSubterm y x :=
  ⟨contains_implies_properSubterm, properSubterm_implies_contains⟩

/-- toFreeMagma is injective -/
theorem toFreeMagma_injective : Function.Injective toFreeMagma := by
  intro a b h
  have := congr_arg fromFreeMagma h
  simp [fromFreeMagma_toFreeMagma] at this
  exact this

/-- nodeCount is preserved by the isomorphism -/
theorem toFreeMagma_preserves_structure (so : SyntacticObject) :
    so.leafCount = match toFreeMagma so with
      | .of _ => 1
      | .mul a b => (fromFreeMagma a).leafCount + (fromFreeMagma b).leafCount := by
  cases so with
  | leaf tok => simp [SyntacticObject.leafCount]
  | node a b =>
    simp [SyntacticObject.leafCount, fromFreeMagma_toFreeMagma]

/-! ## Bridge to FreeMagma.length

`FreeMagma.length` counts leaves (1 for `.of`, sum for `.mul`), matching
`SyntacticObject.leafCount` exactly under the isomorphism. This gives
access to mathlib's `FreeMagma.length_pos` for free. -/

/-- SO.leafCount = FreeMagma.length under the isomorphism -/
theorem leafCount_eq_freeMagma_length (so : SyntacticObject) :
    so.leafCount = (toFreeMagma so).length := by
  induction so with
  | leaf _ => simp [SyntacticObject.leafCount, toFreeMagma, FreeMagma.length]
  | node a b iha ihb =>
    simp [SyntacticObject.leafCount, toFreeMagma, FreeMagma.length, iha, ihb]

/-- leafCount is always positive — derived from mathlib's `FreeMagma.length_pos` -/
theorem leafCount_pos (so : SyntacticObject) : 0 < so.leafCount := by
  rw [leafCount_eq_freeMagma_length]
  exact (toFreeMagma so).length_pos

end Minimalism
