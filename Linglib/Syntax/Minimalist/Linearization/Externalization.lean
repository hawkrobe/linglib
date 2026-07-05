/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Selection

/-!
# Externalization on the `SO` carrier

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
  descriptions — the selection state enriched with the yield, `none` off `Dom(h)`;
  a `CommMagma` under the `side`-indexed Merge-local product.
* `Minimalist.LinearizationState.sel`: the projection morphism to `SelState`,
  forgetting the order description.
* `Minimalist.headHom`: the head function as a morphism of magmas
  `SO →ₙ* LinearizationState side`, refining `selCheckHom` with the yield.
* `Minimalist.SO.linearize`, `Minimalist.SO.phonYield`: the yield readout and the
  pronounced surface forms.

## Main results

* `Minimalist.sel_comp_headHom`: fusion — the selection component of the head
  function's value is the selection check, as a commuting triangle of magma
  morphisms.
* `Minimalist.headNode_perm`: the head algebra is permutation-invariant
  (`List.Perm.congr_arity₂` on `mul_comm`), so the state descends to the nonplanar
  quotient by `RoseTree.fold_perm`.

## Implementation notes

Head functions are partial ([marcolli-chomsky-berwick-2025] §1.13.2): at exocentric
nodes no daughter projects and no order is determined — the book rejects inducing one
from a total order on labels as "not a realistic linguistic assumption" — so the
state is `none` there, matching the book's elimination of nonparsable objects at
externalization. The selection state and the yield are the book's two descriptions
of *one* head function: eq. (1.13.3) reads `h(T)` as "a single leaf (the head)" or
as the ordered leaf sequence, "switch[ing] between these two descriptions without
changing the notation". `LinearizationState` fuses them into a single `Option`,
making `Dom(yield) = Dom(h)` true by construction. **Naming**: the head-function
*maps* (`headNode`, `headPlanar`, `headN`, `headHom`) carry the book's name for `h`;
the *value* type does not — the book restricts "the term head to terminal elements"
(quoting [chomsky-1995-bare] §4), and the strict head is recovered via `sel`. The
`side` index is phantom in the carrier and read by the multiplication (the `WithLp`
pattern); the head-leaf description is side-invariant, only the yield description is
convention-relative. Conceptually the yield component is
`WithZero (FreeMonoid LIToken)`: a silent trace is the unit, exocentricity the
absorbing zero, and head-final placement is multiplication in the opposite monoid.

Only the two harmonic sections are realized: uniform head-side placement is right
for head–complement structure but does not model specifier placement (that needs the
`headSide : Cat → ConventionDir` refinement noted at `ConventionDir`).
-/

namespace Minimalist

open RootedTree

/-- Place the head daughter's yield on the convention side: `.initial` (head-initial)
    → head-yield first, `.final` (head-final) → head-yield last. -/
def placeYield : ConventionDir → List LIToken → List LIToken → List LIToken
  | .initial, headY, otherY => headY ++ otherY
  | .final,   headY, otherY => otherY ++ headY

/-! ### The linearization state -/

set_option linter.unusedVariables false in
/-- The linearization state of a constituent under head-side convention `side`: the
    projecting head with its residual selectional stack (the `SelState` data)
    enriched with the yield, `none` off `Dom(h)` — the value of
    [marcolli-chomsky-berwick-2025]'s head function in its two descriptions, "a
    single leaf (the head)" or the ordered leaf sequence (eq. (1.13.3)), which the
    book reads interchangeably "without changing the notation". The `side` parameter
    is phantom in the carrier — the multiplication reads it (the `WithLp` pattern). -/
def LinearizationState (side : ConventionDir) : Type :=
  Option ((LIToken × List Cat) × List LIToken)

namespace LinearizationState

variable {side : ConventionDir}

/-- Merge-local externalization: the `selCombine` decision projects the head and
    places the projecting daughter's yield on the convention side. -/
instance : Mul (LinearizationState side) :=
  ⟨fun x y =>
    match x, y with
    | some (s₁, y₁), some (s₂, y₂) =>
        (selCombine (some s₁) (some s₂)).map fun p =>
          (p.2, placeYield side (bif p.1 then y₁ else y₂) (bif p.1 then y₂ else y₁))
    | _, _ => none⟩

instance : CommMagma (LinearizationState side) where
  mul_comm x y := by
    match x, y with
    | none, none | none, some _ | some _, none => rfl
    | some (s₁, y₁), some (s₂, y₂) =>
      show (selCombine (some s₁) (some s₂)).map _ = (selCombine (some s₂) (some s₁)).map _
      rw [selCombine_comm]
      cases selCombine (some s₂) (some s₁) with
      | none => rfl
      | some p => obtain ⟨b, hd, res⟩ := p; cases b <;> rfl

/-- The projection to the selection state, as a morphism of magmas: forgetting the
    order description of the head. -/
def sel : LinearizationState side →ₙ* SelState where
  toFun := Option.map (·.1)
  map_mul' x y := by
    match x, y with
    | none, _ => rfl
    | some _, none => exact (SelState.mul_none _).symm
    | some (s₁, y₁), some (s₂, y₂) =>
      show Option.map _ ((selCombine (some s₁) (some s₂)).map _) = _
      rw [Option.map_map]; rfl

end LinearizationState

/-! ### The head algebra -/

/-- The head algebra: a lexical leaf is pronounced carrying its `outerSel` stack, a
    bare trace leaf is silent and saturated (the cancelled copy of
    [marcolli-chomsky-berwick-2025] §1.12), a bare binary node is the `LinearizationState`
    product, and other arities are off `Dom(h)`. -/
def headNode (side : ConventionDir) :
    SOLabel → List (LinearizationState side) → LinearizationState side
  | .inl tok, _     => some ((tok, tok.item.outerSel), [tok])
  | .inr (), []     => some ((mkTraceToken 0, []), [])
  | .inr (), [x, y] => x * y
  | .inr (), _      => none

/-- A daughter list of three or more is off `Dom(h)`. -/
private theorem headNode_big {side : ConventionDir} {l : List (LinearizationState side)}
    (h : 2 < l.length) : headNode side (Sum.inr ()) l = none := by
  match l with
  | _ :: _ :: _ :: _ => rfl
  | [] | [_] | [_, _] => simp at h

/-- `headNode` is invariant under permutation of the daughter states: only the
    binary shape is order-sensitive, and there `mul_comm` applies. -/
theorem headNode_perm (side : ConventionDir) (a : SOLabel) {l₁ l₂ : List (LinearizationState side)}
    (h : l₁.Perm l₂) : headNode side a l₁ = headNode side a l₂ := by
  cases a with
  | inl tok => rfl
  | inr u => cases u; exact h.congr_arity₂ (fun x y => mul_comm x y) fun _ h => headNode_big h

/-- `LinearizationState.sel` intertwines the head and selection algebras. -/
theorem sel_headNode (side : ConventionDir) (a : SOLabel) (ps : List (LinearizationState side)) :
    LinearizationState.sel (headNode side a ps) = selNode a (ps.map LinearizationState.sel) := by
  match a, ps with
  | .inl tok, _ => rfl
  | .inr (), [] => rfl
  | .inr (), [x, y] => exact map_mul LinearizationState.sel x y
  | .inr (), [_] | .inr (), _ :: _ :: _ :: _ => rfl

/-! ### The head function on the planar and nonplanar carriers -/

/-- The head function on planar `SO`-trees: the catamorphism of the head algebra. -/
def headPlanar (side : ConventionDir) : RoseTree SOLabel → LinearizationState side :=
  RoseTree.fold (headNode side)

/-- **Fusion** on the planar carrier: the selection component of the head
    function's value is the selection check. -/
theorem sel_headPlanar (side : ConventionDir) (t : RoseTree SOLabel) :
    LinearizationState.sel (headPlanar side t) = selCheckPlanar t :=
  RoseTree.fold_hom _ (sel_headNode side) t

/-- The state is projection-determined, not representative-determined: it descends
    to the nonplanar quotient. -/
theorem headPlanar_perm (side : ConventionDir) {t s : RoseTree SOLabel}
    (h : RoseTree.Perm t s) : headPlanar side t = headPlanar side s :=
  RoseTree.fold_perm (fun a _ _ h' => headNode_perm side a h') h

/-- The head function on the nonplanar carrier. -/
def headN (side : ConventionDir) : Nonplanar SOLabel → LinearizationState side :=
  Nonplanar.lift (headPlanar side) fun _ _ h => headPlanar_perm side h

@[simp] theorem headN_mk (side : ConventionDir) (p : RoseTree SOLabel) :
    headN side (Nonplanar.mk p) = headPlanar side p := rfl

/-- The nonplanar magma law: Merge multiplies linearization states. -/
theorem headN_node (side : ConventionDir) (a b : Nonplanar SOLabel) :
    headN side (Nonplanar.node (Sum.inr ()) {a, b}) = headN side a * headN side b := by
  refine Quotient.inductionOn₂ a b fun pa pb => ?_
  show headN side (Nonplanar.node (Sum.inr ()) {Nonplanar.mk pa, Nonplanar.mk pb})
      = headN side (Nonplanar.mk pa) * headN side (Nonplanar.mk pb)
  rw [Nonplanar.node_pair_mk]; exact rfl

/-! ### Externalization on `SO` -/

/-- The linearization state of a syntactic object: the value of the head function
    in both descriptions. -/
def SO.linearizationState (side : ConventionDir) (s : SO) : LinearizationState side :=
  headN side s.val

@[simp] theorem SO.linearizationState_node (side : ConventionDir) (l r : SO) :
    (SO.node l r).linearizationState side
      = l.linearizationState side * r.linearizationState side := by
  show headN side (SO.node l r).val = headN side l.val * headN side r.val
  rw [SO.node_val, headN_node]

/-- **The head function is a morphism of magmas** `SO →ₙ* LinearizationState side`
    ([marcolli-chomsky-berwick-2025] §1.13's algebraic frame): Merge multiplies
    constituents, the head function multiplies linearization states. -/
noncomputable def headHom (side : ConventionDir) : SO →ₙ* LinearizationState side where
  toFun := SO.linearizationState side
  map_mul' := SO.linearizationState_node side

/-- **Fusion as a commuting triangle**: projecting the head function's value to its
    selection component is the selection check —
    `LinearizationState.sel ∘ headHom = selCheckHom`. -/
theorem sel_comp_headHom (side : ConventionDir) :
    LinearizationState.sel.comp (headHom side) = selCheckHom :=
  MulHom.ext fun s => by
    show LinearizationState.sel (headN side s.val) = selCheckN s.val
    exact Quotient.inductionOn s.val (sel_headPlanar side)

/-- The surface token order of a syntactic object under the head-side convention
    `side` ([marcolli-chomsky-berwick-2025] §1.12.1): the yield readout of the
    linearization state — the selection-induced harmonic candidate for the externalization
    section σ_L, defined on `Dom(h)` only (the book's σ_L must extend it
    *noncanonically* off `Dom(h)`). The readout alone is not a morphism: placing a
    yield needs the head leaf, which is why `LinearizationState` carries both descriptions. -/
def SO.linearize (side : ConventionDir) (s : SO) : Option (List LIToken) :=
  Option.map (·.2) (s.linearizationState side)

/-- The pronounced surface forms: the yield with unpronounced (empty-`phonForm`)
    tokens dropped. Traces, being the bare `Sum.inr ()` leaf, contribute nothing. -/
def SO.phonYield (side : ConventionDir) (s : SO) : Option (List String) :=
  (SO.linearize side s).map (·.filterMap LIToken.phonForm?)

@[simp] theorem SO.linearize_lexLeaf (side : ConventionDir) (tok : LIToken) :
    (SO.lexLeaf tok).linearize side = some [tok] := rfl

@[simp] theorem SO.linearize_traceLeaf (side : ConventionDir) :
    SO.traceLeaf.linearize side = some [] := rfl

/-! ### `decide` demonstration

The order reduces on concrete `mk`-built trees, the head-side parameter flips it, and
exocentric Merge is order-undefined. -/

/-- A determiner (category `D`, selecting `N`) over a noun: `D` projects, so
    head-initial yields `the dog` and head-final yields `dog the`. -/
private def demoTheDog : SO :=
  ⟨Nonplanar.mk (.node (Sum.inr ())
    [.node (Sum.inl ⟨.simple .D [.N] (phonForm := "the"), 0⟩) [],
     .node (Sum.inl ⟨.simple .N [] (phonForm := "dog"), 1⟩) []]), by decide⟩

example : (demoTheDog.linearize .initial).map (·.map (·.id)) = some [0, 1] := by decide
example : (demoTheDog.linearize .final).map (·.map (·.id)) = some [1, 0] := by decide
example : demoTheDog.phonYield .initial = some ["the", "dog"] := by decide
example : demoTheDog.phonYield .final = some ["dog", "the"] := by decide

/-- Exocentric Merge — two saturated `N`s, neither selecting the other — determines
    no head and hence no order: linearization is undefined off `Dom(h)`. -/
private def demoExo : SO :=
  ⟨Nonplanar.mk (.node (Sum.inr ())
    [.node (Sum.inl ⟨.simple .N [] (phonForm := "cats"), 0⟩) [],
     .node (Sum.inl ⟨.simple .N [] (phonForm := "dogs"), 1⟩) []]), by decide⟩

example : demoExo.linearize .initial = none := by decide
example : demoExo.linearize .final = none := by decide

end Minimalist
