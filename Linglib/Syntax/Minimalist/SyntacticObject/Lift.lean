/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Data.List.Perm.Basic
public import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# The universal property of the syntactic-object carrier

Leaf data valued in a commutative magma with zero extends to a morphism of magmas
out of `SyntacticObject` (`lift`, the `FreeMagma.lift` analogue), and two such
morphisms agreeing on the leaves are equal (`hom_ext`). The zero absorbs the
off-carrier arities, so one total algebra (`mergeAlgebra`) drives the fold, the
quotient descent, and the subtype restriction once and for all: consumers supply a
lexical-leaf value and a trace value, and inherit `Perm`-invariance from
`mul_comm` via a private permutation-invariance lemma — no bespoke step induction.

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
* `Minimalist.SyntacticObject.liftN_merge`: the magma law on the unordered carrier.
-/

@[expose] public section

namespace Minimalist.SyntacticObject

open RoseTree UnorderedTree

variable {β : Type*}

/-- The node algebra of a magma-with-zero: lexical leaf ↦ `ℓ`, trace leaf ↦ `τ`,
    bare binary node ↦ `*`, off-carrier arities ↦ `0`. -/
def mergeAlgebra [Mul β] [Zero β] (ℓ : LIToken → β) (τ : β) : Vertex → List β → β
  | .inl tok, _       => ℓ tok
  | .inr _, []        => τ
  | .inr none, [x, y] => x * y
  | .inr _, _         => 0

/-- The trace of a token is a leaf: any daughters put it off the carrier. -/
private theorem mergeAlgebra_some [Mul β] [Zero β] (ℓ : LIToken → β) (τ : β) (tok : LIToken)
    (l : List β) : mergeAlgebra ℓ τ (Sum.inr (some tok)) l = if l.isEmpty then τ else 0 := by
  match l with
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ => rfl

/-- A daughter list of three or more is off the carrier. -/
private theorem mergeAlgebra_big [Mul β] [Zero β] {ℓ : LIToken → β} {τ : β} {l : List β}
    (h : 2 < l.length) : mergeAlgebra ℓ τ (Sum.inr none) l = 0 := by
  match l with
  | _ :: _ :: _ :: _ => rfl
  | [] | [_] | [_, _] => simp at h

/-- A list function symmetric on pairs and constant above length two is `Perm`-invariant:
lengths at most one are rigid under permutation, pairs by the symmetry, longer lists by the
constancy. -/
private theorem perm_congr_arity₂ {β γ : Type*} {g : List β → γ} {c : γ}
    (hswap : ∀ x y, g [x, y] = g [y, x])
    (hbig : ∀ l : List β, 2 < l.length → g l = c)
    {l₁ l₂ : List β} (h : l₁.Perm l₂) : g l₁ = g l₂ := by
  induction h with
  | nil => rfl
  | @cons x l₁ l₂ h _ih =>
    match l₁, l₂, h with
    | [], l₂, h => rw [show l₂ = [] from h.symm.eq_nil]
    | [y], l₂, h => rw [show l₂ = [y] from List.perm_singleton.mp h.symm]
    | _ :: _ :: _, l₂, h =>
      have hl := h.length_eq
      rw [hbig _ (by simp +arith), hbig _ (by simp only [List.length_cons] at hl ⊢; omega)]
  | swap x y l =>
    match l with
    | [] => exact hswap y x
    | _ :: _ => rw [hbig _ (by simp +arith), hbig _ (by simp +arith)]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- `mergeAlgebra` is invariant under permutation of the daughter values: only the
    binary shape is order-sensitive, and there `mul_comm` applies. -/
theorem mergeAlgebra_perm [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β) (a : Vertex)
    {l₁ l₂ : List β} (h : l₁.Perm l₂) : mergeAlgebra ℓ τ a l₁ = mergeAlgebra ℓ τ a l₂ := by
  cases a with
  | inl tok => rfl
  | inr u =>
    cases u with
    | none =>
      exact perm_congr_arity₂ (fun x y => _root_.mul_comm x y) (fun _ h => mergeAlgebra_big h) h
    | some tok =>
      simp only [mergeAlgebra_some, List.isEmpty_iff_length_eq_zero, h.length_eq]

/-- The induced algebra on the nonplanar carrier: the catamorphism descends by
    `mergeAlgebra_perm`. -/
def liftN [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β) : UnorderedTree Vertex → β :=
  Quotient.lift (RoseTree.fold (mergeAlgebra ℓ τ))
    fun _ _ h => RoseTree.fold_perm (fun a _ _ h' => mergeAlgebra_perm ℓ τ a h') h

@[simp] theorem liftN_mk [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β)
    (p : RoseTree Vertex) :
    liftN ℓ τ (UnorderedTree.mk p) = RoseTree.fold (mergeAlgebra ℓ τ) p := rfl

/-- The nonplanar magma law: Merge multiplies values. -/
theorem liftN_merge [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β)
    (a b : UnorderedTree Vertex) :
    liftN ℓ τ (UnorderedTree.node (Sum.inr none) {a, b}) = liftN ℓ τ a * liftN ℓ τ b := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  rw [UnorderedTree.quot_mk_eq_mk, UnorderedTree.quot_mk_eq_mk, UnorderedTree.node_pair_mk]
  exact rfl

/-- The induced map on syntactic objects, unbundled — computable, `decide`-friendly. -/
def liftFun [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β) (s : SyntacticObject) : β :=
  liftN ℓ τ s.val

@[simp] theorem liftFun_leaf [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β)
    (tok : LIToken) : liftFun ℓ τ (SyntacticObject.leaf tok) = ℓ tok := rfl

@[simp] theorem liftFun_trace [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β) :
    liftFun ℓ τ trace = τ := rfl

@[simp] theorem liftFun_traceOf [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β)
    (tok : LIToken) : liftFun ℓ τ (traceOf tok) = τ := rfl

@[simp] theorem liftFun_merge [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β)
    (l r : SyntacticObject) :
    liftFun ℓ τ (merge l r) = liftFun ℓ τ l * liftFun ℓ τ r := by
  show liftN ℓ τ (merge l r).val = liftN ℓ τ l.val * liftN ℓ τ r.val
  rw [merge_val, liftN_merge]

/-- The universal property, existence half (cf. `FreeMagma.lift`): leaf data
    extends to a morphism of magmas out of the carrier. -/
noncomputable def lift [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β) :
    SyntacticObject →ₙ* β where
  toFun := liftFun ℓ τ
  map_mul' := liftFun_merge ℓ τ

@[simp] theorem lift_apply [CommMagma β] [Zero β] (ℓ : LIToken → β) (τ : β)
    (s : SyntacticObject) : lift ℓ τ s = liftFun ℓ τ s := rfl

/-- The universal property, uniqueness half: morphisms agreeing on the leaves are
    equal. -/
theorem hom_ext [Mul β] {f g : SyntacticObject →ₙ* β}
    (hlex : ∀ tok, f (SyntacticObject.leaf tok) = g (SyntacticObject.leaf tok))
    (htrace : f trace = g trace) (htraceOf : ∀ tok, f (traceOf tok) = g (traceOf tok)) :
    f = g :=
  MulHom.ext fun s => by
    induction s using SyntacticObject.ind with
    | leaf tok => exact hlex tok
    | trace => exact htrace
    | traceOf tok => exact htraceOf tok
    | merge l r ihl ihr =>
      rw [show merge l r = l * r from rfl, map_mul, map_mul, ihl, ihr]

end Minimalist.SyntacticObject
