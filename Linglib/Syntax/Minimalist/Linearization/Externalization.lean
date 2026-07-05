/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Selection

/-!
# Externalization on the `SyntacticObject` carrier

This file defines the selection-induced linearization of syntactic objects
([marcolli-chomsky-berwick-2025] §1.12.1, §1.13): the surface token order obtained by
placing the projecting daughter's yield on a language's harmonic head side. Lemma
1.13.5 identifies head functions on a binary tree with its planar embeddings, and
Lemma 1.13.7 identifies head functions with bare-phrase-structure projection
([chomsky-1995-bare]); composed with [adger-2003]'s identification of the projecting
item as the selecting item (a synthesis step of this formalization, not a claim of
the book), c-selection computes the planar order.

## Main declarations

* `Minimalist.LinearizationState`: the value of the book's head function in its two
  descriptions — the selection state enriched with the yield, `0` off `Dom(h)`; a
  `CommMagma` and `MulZeroClass` under the `side`-indexed Merge-local product.
* `Minimalist.LinearizationState.sel`: the projection morphism to `SelectionState`.
* `Minimalist.headHom`: the head function as a morphism of magmas
  `SyntacticObject →ₙ* LinearizationState side`, refining `selCheckHom`.
* `Minimalist.SyntacticObject.linearize`, `Minimalist.SyntacticObject.phonYield`:
  the yield readout and the pronounced surface forms.

## Main results

* `Minimalist.sel_comp_headHom`: fusion — the selection component of the head
  function's value is the selection check, by `SyntacticObject.hom_ext`.

## Implementation notes

Head functions are partial ([marcolli-chomsky-berwick-2025] §1.13.2): at exocentric
nodes no daughter projects and no order is determined — the book rejects inducing one
from a total order on labels as "not a realistic linguistic assumption" — so the
state is `0` there, the absorbing element of the book's renormalization reading of
partial head functions. The selection state and the yield are the book's two
descriptions of *one* head function: eq. (1.13.3) reads `h(T)` as "a single leaf
(the head)" or as the ordered leaf sequence, "switch[ing] between these two
descriptions without changing the notation". `LinearizationState` fuses them into
one partial value, making `Dom(yield) = Dom(h)` true by construction. **Naming**:
the head-function *maps* (`headHom` and the leaf data it lifts) carry the book's
name for `h`; the *value* type does not — the book restricts "the term head to
terminal elements" (quoting [chomsky-1995-bare] §4), and the strict head is
recovered via `sel`. `SyntacticObject.linearize` is the harmonic candidate for the
externalization section σ_L, defined on `Dom(h)` only — the book's σ_L must extend
it *noncanonically* off `Dom(h)`. Conceptually the yield component is
`WithZero (FreeMonoid LIToken)`: a silent trace is the unit, exocentricity the
absorbing zero, and head-final placement is multiplication in the opposite monoid.

Only the two harmonic sections are realized: uniform head-side placement is right
for head–complement structure but does not model specifier placement (that needs the
`headSide : Cat → ConventionDir` refinement noted at `ConventionDir`).
-/

namespace Minimalist

open RootedTree

/-- Place the head daughter's yield on the convention side: `.initial` → head-yield
    first, `.final` → head-yield last. -/
def placeYield : ConventionDir → List LIToken → List LIToken → List LIToken
  | .initial, headY, otherY => headY ++ otherY
  | .final,   headY, otherY => otherY ++ headY

/-! ### The linearization state -/

/-- The value of the head function in its two descriptions: the projecting head
    with its residual stack, enriched with the yield; `0` off `Dom(h)`. The `side`
    parameter is phantom in the carrier — the multiplication reads it. -/
structure LinearizationState (side : ConventionDir) : Type where
  toOption : Option ((LIToken × List Cat) × List LIToken)
deriving DecidableEq

namespace LinearizationState

variable {side : ConventionDir}

/-- A defined state: projecting head `tok`, residual stack `stack`, yield `yld`. -/
def of (tok : LIToken) (stack : List Cat) (yld : List LIToken) : LinearizationState side :=
  ⟨some ((tok, stack), yld)⟩

/-- Merge-local externalization: the `selCombine` decision places the projecting
    daughter's yield on the convention side; `0` is absorbing. -/
instance : MulZeroClass (LinearizationState side) where
  mul x y :=
    match x, y with
    | ⟨some (s₁, y₁)⟩, ⟨some (s₂, y₂)⟩ =>
        ⟨(selCombine ⟨some s₁⟩ ⟨some s₂⟩).map fun p =>
          (p.2, placeYield side (bif p.1 then y₁ else y₂) (bif p.1 then y₂ else y₁))⟩
    | _, _ => ⟨none⟩
  zero := ⟨none⟩
  zero_mul _ := rfl
  mul_zero x := by rcases x with ⟨_ | _⟩ <;> rfl

/-- `*` on defined states: the canonical accessor. -/
theorem some_mul_some (s₁ s₂ : LIToken × List Cat) (y₁ y₂ : List LIToken) :
    (⟨some (s₁, y₁)⟩ * ⟨some (s₂, y₂)⟩ : LinearizationState side) =
      ⟨(selCombine ⟨some s₁⟩ ⟨some s₂⟩).map fun p =>
          (p.2, placeYield side (bif p.1 then y₁ else y₂) (bif p.1 then y₂ else y₁))⟩ := rfl

instance : CommMagma (LinearizationState side) where
  mul_comm x y := by
    match x, y with
    | ⟨none⟩, ⟨none⟩ | ⟨none⟩, ⟨some _⟩ | ⟨some _⟩, ⟨none⟩ => rfl
    | ⟨some (s₁, y₁)⟩, ⟨some (s₂, y₂)⟩ =>
      rw [some_mul_some, some_mul_some, selCombine_comm]
      rcases selCombine ⟨some s₂⟩ ⟨some s₁⟩ with _ | ⟨_ | _, _, _⟩ <;> rfl

/-- The projection to the selection state: forgetting the order description. -/
def sel : LinearizationState side →ₙ* SelectionState where
  toFun x := ⟨x.toOption.map (·.1)⟩
  map_mul' x y := by
    match x, y with
    | ⟨none⟩, _ => rfl
    | ⟨some _⟩, ⟨none⟩ => exact (mul_zero _).symm
    | ⟨some (s₁, y₁)⟩, ⟨some (s₂, y₂)⟩ =>
      rw [some_mul_some]
      simp only [Option.map_map]
      rfl

@[simp] theorem sel_of (tok : LIToken) (stack : List Cat) (yld : List LIToken) :
    sel (of tok stack yld : LinearizationState side) = .of tok stack := rfl

@[simp] theorem sel_zero : sel (0 : LinearizationState side) = 0 := rfl

/-- The yield component: the ordered leaf sequence, `none` off `Dom(h)`. -/
def yield (x : LinearizationState side) : Option (List LIToken) :=
  x.toOption.map (·.2)

@[simp] theorem yield_of (tok : LIToken) (stack : List Cat) (yld : List LIToken) :
    (of tok stack yld : LinearizationState side).yield = some yld := rfl

@[simp] theorem yield_zero : (0 : LinearizationState side).yield = none := rfl

end LinearizationState

/-! ### Externalization on `SyntacticObject` -/

variable (side : ConventionDir)

/-- The head function's value on a syntactic object: the `SyntacticObject.liftFun`
    of pronounced lexical leaves and the silent, saturated trace. -/
def SyntacticObject.linearizationState (s : SyntacticObject) :
    LinearizationState side :=
  SyntacticObject.liftFun (fun tok => .of tok tok.item.outerSel [tok])
    (.of (mkTraceToken 0) [] []) s

@[simp] theorem SyntacticObject.linearizationState_lexLeaf
    (tok : LIToken) :
    (SyntacticObject.lexLeaf tok).linearizationState side =
      .of tok tok.item.outerSel [tok] := rfl

@[simp] theorem SyntacticObject.linearizationState_traceLeaf :
    SyntacticObject.traceLeaf.linearizationState side = .of (mkTraceToken 0) [] [] := rfl

@[simp] theorem SyntacticObject.linearizationState_node
    (l r : SyntacticObject) :
    (SyntacticObject.node l r).linearizationState side =
      l.linearizationState side * r.linearizationState side :=
  SyntacticObject.liftFun_node _ _ l r

/-- The head function as a morphism of magmas ([marcolli-chomsky-berwick-2025]
    §1.13's algebraic frame): Merge multiplies constituents, `h` multiplies states. -/
noncomputable def headHom :
    SyntacticObject →ₙ* LinearizationState side :=
  SyntacticObject.lift (fun tok => .of tok tok.item.outerSel [tok])
    (.of (mkTraceToken 0) [] [])

@[simp] theorem headHom_apply (s : SyntacticObject) :
    headHom side s = s.linearizationState side := rfl

/-- Fusion: the selection component of the head function's value is the selection
    check — two morphisms agreeing on the leaves (`SyntacticObject.hom_ext`). -/
theorem sel_comp_headHom :
    LinearizationState.sel.comp (headHom side) = selCheckHom :=
  SyntacticObject.hom_ext (fun _ => rfl) rfl

/-- The surface token order under head-side convention `side`
    ([marcolli-chomsky-berwick-2025] §1.12.1): the yield readout of the
    linearization state. Not a morphism — placing a yield needs the head. -/
def SyntacticObject.linearize (s : SyntacticObject) :
    Option (List LIToken) :=
  (s.linearizationState side).yield

/-- The pronounced surface forms: the yield with unpronounced tokens dropped. -/
def SyntacticObject.phonYield (s : SyntacticObject) :
    Option (List String) :=
  (s.linearize side).map (·.filterMap LIToken.phonForm?)

@[simp] theorem SyntacticObject.linearize_lexLeaf (tok : LIToken) :
    (SyntacticObject.lexLeaf tok).linearize side = some [tok] := rfl

@[simp] theorem SyntacticObject.linearize_traceLeaf :
    SyntacticObject.traceLeaf.linearize side = some [] := rfl

/-! ### `decide` demonstration

The order reduces on concrete `mk`-built trees, the head-side parameter flips it, and
exocentric Merge is order-undefined. -/

/-- A determiner over a noun: `D` selects `N`, so `D` projects. -/
private def demoTheDog : SyntacticObject :=
  ⟨Nonplanar.mk (.node (Sum.inr ())
    [.node (Sum.inl ⟨.simple .D [.N] (phonForm := "the"), 0⟩) [],
     .node (Sum.inl ⟨.simple .N [] (phonForm := "dog"), 1⟩) []]), by decide⟩

example : (demoTheDog.linearize .initial).map (·.map (·.id)) = some [0, 1] := by decide
example : (demoTheDog.linearize .final).map (·.map (·.id)) = some [1, 0] := by decide
example : demoTheDog.phonYield .initial = some ["the", "dog"] := by decide
example : demoTheDog.phonYield .final = some ["dog", "the"] := by decide

/-- Exocentric Merge: two saturated `N`s, neither selecting the other — no head, no
    order. -/
private def demoExo : SyntacticObject :=
  ⟨Nonplanar.mk (.node (Sum.inr ())
    [.node (Sum.inl ⟨.simple .N [] (phonForm := "cats"), 0⟩) [],
     .node (Sum.inl ⟨.simple .N [] (phonForm := "dogs"), 1⟩) []]), by decide⟩

example : demoExo.linearize .initial = none := by decide
example : demoExo.linearize .final = none := by decide

end Minimalist
