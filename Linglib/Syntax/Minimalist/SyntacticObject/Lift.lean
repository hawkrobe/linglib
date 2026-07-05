/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Group.Hom.Defs
import Linglib.Core.Data.List.Perm
import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# The universal property of the syntactic-object carrier

Leaf data valued in a commutative magma with zero extends to a morphism of magmas
out of `SyntacticObject` (`lift`, the `FreeMagma.lift` analogue), and two such
morphisms agreeing on the leaves are equal (`hom_ext`). The zero absorbs the
off-carrier arities, so one total algebra (`mergeAlgebra`) drives the fold, the
quotient descent, and the subtype restriction once and for all: consumers supply a
lexical-leaf value and a trace value, and inherit `Perm`-invariance from
`mul_comm` via `List.Perm.congr_arity₂` — no bespoke step induction.

## Main declarations

* `Minimalist.SyntacticObject.mergeAlgebra`: the node algebra induced by a
  magma-with-zero — lexical leaf ↦ `ℓ`, trace leaf ↦ `τ`, bare binary node ↦ `*`,
  other arities ↦ `0`.
* `Minimalist.SyntacticObject.liftN`: its evaluation on the nonplanar carrier.
* `Minimalist.SyntacticObject.liftFun`, `Minimalist.SyntacticObject.lift`: the
  induced map on syntactic objects, unbundled (computable) and as `→ₙ*`.

## Main results

* `Minimalist.SyntacticObject.hom_ext`: morphisms of magmas out of
  `SyntacticObject` agreeing on lexical and trace leaves are equal.
* `Minimalist.SyntacticObject.liftN_node`: the nonplanar magma law.
-/

namespace Minimalist.SyntacticObject

open RootedTree

variable {β : Type*}

/-- The node algebra of a magma-with-zero: lexical leaf ↦ `ℓ`, trace leaf ↦ `τ`,
    bare binary node ↦ `*`, off-carrier arities ↦ `0`. -/
def mergeAlgebra [Mul β] [Zero β] (ℓ : LIToken → β) (τ : β) : SOLabel → List β → β
  | .inl tok, _     => ℓ tok
  | .inr (), []     => τ
  | .inr (), [x, y] => x * y
  | .inr (), _      => 0

/-- A daughter list of three or more is off the carrier. -/
private theorem mergeAlgebra_big [Mul β] [Zero β] {ℓ : LIToken → β} {τ : β} {l : List β}
    (h : 2 < l.length) : mergeAlgebra ℓ τ (Sum.inr ()) l = 0 := by
  match l with
  | _ :: _ :: _ :: _ => rfl
  | [] | [_] | [_, _] => simp at h

/-- `mergeAlgebra` is invariant under permutation of the daughter values: only the
    binary shape is order-sensitive, and there `mul_comm` applies. -/
theorem mergeAlgebra_perm [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β) (a : SOLabel)
    {l₁ l₂ : List β} (h : l₁.Perm l₂) : mergeAlgebra ℓ τ a l₁ = mergeAlgebra ℓ τ a l₂ := by
  cases a with
  | inl tok => rfl
  | inr u =>
    cases u
    exact h.congr_arity₂ (fun x y => _root_.mul_comm x y) fun _ h => mergeAlgebra_big h

/-- The induced algebra on the nonplanar carrier: the catamorphism descends by
    `mergeAlgebra_perm`. -/
def liftN [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β) : Nonplanar SOLabel → β :=
  Nonplanar.lift (RoseTree.fold (mergeAlgebra ℓ τ))
    fun _ _ h => RoseTree.fold_perm (fun a _ _ h' => mergeAlgebra_perm ℓ τ a h') h

@[simp] theorem liftN_mk [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β)
    (p : RoseTree SOLabel) :
    liftN ℓ τ (Nonplanar.mk p) = RoseTree.fold (mergeAlgebra ℓ τ) p := rfl

/-- The nonplanar magma law: Merge multiplies values. -/
theorem liftN_node [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β)
    (a b : Nonplanar SOLabel) :
    liftN ℓ τ (Nonplanar.node (Sum.inr ()) {a, b}) = liftN ℓ τ a * liftN ℓ τ b := by
  refine Nonplanar.inductionOn₂ a b fun pa pb => ?_
  rw [Nonplanar.node_pair_mk]
  exact rfl

/-- The induced map on syntactic objects, unbundled — computable, `decide`-friendly. -/
def liftFun [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β) (s : SyntacticObject) : β :=
  liftN ℓ τ s.val

@[simp] theorem liftFun_lexLeaf [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β)
    (tok : LIToken) : liftFun ℓ τ (lexLeaf tok) = ℓ tok := rfl

@[simp] theorem liftFun_traceLeaf [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β) :
    liftFun ℓ τ traceLeaf = τ := rfl

@[simp] theorem liftFun_node [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β)
    (l r : SyntacticObject) :
    liftFun ℓ τ (node l r) = liftFun ℓ τ l * liftFun ℓ τ r := by
  show liftN ℓ τ (node l r).val = liftN ℓ τ l.val * liftN ℓ τ r.val
  rw [node_val, liftN_node]

/-- The universal property, existence half (cf. `FreeMagma.lift`): leaf data
    extends to a morphism of magmas out of the carrier. -/
noncomputable def lift [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β) :
    SyntacticObject →ₙ* β where
  toFun := liftFun ℓ τ
  map_mul' := liftFun_node ℓ τ

@[simp] theorem lift_apply [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β)
    (s : SyntacticObject) : lift ℓ τ s = liftFun ℓ τ s := rfl

/-- The universal property, uniqueness half: morphisms agreeing on the leaves are
    equal. -/
theorem hom_ext [Mul β] {f g : SyntacticObject →ₙ* β}
    (hlex : ∀ tok, f (lexLeaf tok) = g (lexLeaf tok))
    (htrace : f traceLeaf = g traceLeaf) : f = g :=
  MulHom.ext fun s => by
    induction s using SyntacticObject.ind with
    | lex tok => exact hlex tok
    | trace => exact htrace
    | node l r ihl ihr =>
      rw [show node l r = l * r from rfl, map_mul, map_mul, ihl, ihr]

end Minimalist.SyntacticObject
