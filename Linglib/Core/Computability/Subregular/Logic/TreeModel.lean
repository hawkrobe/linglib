import Linglib.Core.Combinatorics.RootedTree.Planar

/-!
# Tree models and quantifier-free logic over them

The hierarchical counterpart of `Logic/WordModel.lean` ([dolatian-2020] §4.5, after Courcelle's
relational tree models): morphological and prosodic structure as labeled trees, with the *same*
model-theoretic apparatus used for strings. A **tree model** is a `RootedTree.Planar L` — a node-
labeled rose tree — addressed by Gorn indices (`List ℕ`); its relations are dominance (parent/child)
and sibling precedence. Quantifier-free terms navigate by `parent`/`child`/`sibSucc`/`sibPred`
partial functions, giving the bounded reach that, as on strings, underlies tree-local computation.

The model is generic over the label type `L`, so it instantiates uniformly to morphological
structure (a tree of `root`/`stem`/`word`/affix categories) and to prosody (`Prosody.Tree`, a
`Planar` of prosodic labels — that instantiation lives downstream, since `Core` cannot import
`Phonology`). This genericity is Dolatian's point: one hierarchical apparatus for both.

## Main definitions

* `Subregular.Logic.TreeModel` — a labeled tree, addressed by Gorn indices.
* `TreeModel.nodeAt` / `labelAt?` — navigate to / read the label at an address.
* `TreeTerm` / `TreeTerm.eval` — QF tree terms (`parent`/`child`/`sibSucc`/`sibPred`) and their
  interpretation as partial address maps.
* `TreeAtom` / `TreeQF` / `TreeQF.Realize` — atomic and quantifier-free tree formulas, with
  decidable satisfaction.
-/

namespace Subregular.Logic

open RootedTree

variable {L V : Type*}

/-- A **tree model**: a node-labeled rose tree, addressed by Gorn indices (`List ℕ`). The carrier is
`RootedTree.Planar L` itself — a labeled tree *is* its model, as a string is its word model. -/
abbrev TreeModel (L : Type*) := Planar L

namespace TreeModel

/-- The subtree rooted at a Gorn address, `none` if the address leaves the tree. -/
def nodeAt : TreeModel L → List ℕ → Option (TreeModel L)
  | t, []      => some t
  | t, i :: rest =>
      match t.children[i]? with
      | none   => none
      | some c => nodeAt c rest

/-- The label at a Gorn address, `none` off the tree. -/
def labelAt? (t : TreeModel L) (a : List ℕ) : Option L := (t.nodeAt a).map Planar.label

/-- The address, if it names a node of `t`; otherwise `none`. -/
def posOf (t : TreeModel L) (a : List ℕ) : Option (List ℕ) :=
  if (t.nodeAt a).isSome then some a else none

end TreeModel

/-! ### Quantifier-free tree terms -/

/-- Quantifier-free **tree terms**: a variable, or a one-step move to the `parent`, the `i`-th
`child`, or the next/previous sibling. The moves are the bounded reach of tree-local logic. -/
inductive TreeTerm (V : Type*) where
  | var : V → TreeTerm V
  | parent : TreeTerm V → TreeTerm V
  | child : ℕ → TreeTerm V → TreeTerm V
  | sibSucc : TreeTerm V → TreeTerm V
  | sibPred : TreeTerm V → TreeTerm V

namespace TreeTerm

/-- Interpret a tree term in `t` under an assignment `ρ` of variables to addresses; `none` if a move
leaves the tree. -/
def eval (t : TreeModel L) (ρ : V → List ℕ) : TreeTerm V → Option (List ℕ)
  | .var v     => t.posOf (ρ v)
  | .parent s  => (eval t ρ s).bind fun a => match a with
      | []     => none
      | _ :: _ => some a.dropLast
  | .child i s => (eval t ρ s).bind fun a => t.posOf (a ++ [i])
  | .sibSucc s => (eval t ρ s).bind fun a => match a.getLast? with
      | none   => none
      | some k => t.posOf (a.dropLast ++ [k + 1])
  | .sibPred s => (eval t ρ s).bind fun a => match a.getLast? with
      | none        => none
      | some 0      => none
      | some (k + 1) => t.posOf (a.dropLast ++ [k])

end TreeTerm

/-- Atomic quantifier-free tree formulas. -/
inductive TreeAtom (L V : Type*) where
  | label : L → TreeTerm V → TreeAtom L V
  | eq : TreeTerm V → TreeTerm V → TreeAtom L V
  | defined : TreeTerm V → TreeAtom L V

/-- Quantifier-free tree formulas: boolean combinations of atoms (no quantifiers). -/
inductive TreeQF (L V : Type*) where
  | atom : TreeAtom L V → TreeQF L V
  | tru : TreeQF L V
  | fls : TreeQF L V
  | neg : TreeQF L V → TreeQF L V
  | conj : TreeQF L V → TreeQF L V → TreeQF L V
  | disj : TreeQF L V → TreeQF L V → TreeQF L V

variable [DecidableEq L]

/-- Satisfaction of a tree atom in `t` under assignment `ρ`. -/
def TreeAtom.Realize (t : TreeModel L) (ρ : V → List ℕ) : TreeAtom L V → Prop
  | .label l s => (s.eval t ρ).bind t.labelAt? = some l
  | .eq s₁ s₂  => s₁.eval t ρ = s₂.eval t ρ ∧ s₁.eval t ρ ≠ none
  | .defined s => s.eval t ρ ≠ none

instance (t : TreeModel L) (ρ : V → List ℕ) (a : TreeAtom L V) : Decidable (a.Realize t ρ) := by
  cases a <;> unfold TreeAtom.Realize <;> infer_instance

/-- Satisfaction of a quantifier-free tree formula in `t` under assignment `ρ`. -/
def TreeQF.Realize (t : TreeModel L) (ρ : V → List ℕ) : TreeQF L V → Prop
  | .atom a   => a.Realize t ρ
  | .tru      => True
  | .fls      => False
  | .neg φ    => ¬ φ.Realize t ρ
  | .conj φ ψ => φ.Realize t ρ ∧ ψ.Realize t ρ
  | .disj φ ψ => φ.Realize t ρ ∨ ψ.Realize t ρ

instance TreeQF.instDecidableRealize (t : TreeModel L) (ρ : V → List ℕ) :
    (φ : TreeQF L V) → Decidable (φ.Realize t ρ)
  | .atom a   => inferInstanceAs (Decidable (a.Realize t ρ))
  | .tru      => isTrue trivial
  | .fls      => isFalse not_false
  | .neg φ    => @instDecidableNot _ (TreeQF.instDecidableRealize t ρ φ)
  | .conj φ ψ => @instDecidableAnd _ _ (TreeQF.instDecidableRealize t ρ φ) (TreeQF.instDecidableRealize t ρ ψ)
  | .disj φ ψ => @instDecidableOr _ _ (TreeQF.instDecidableRealize t ρ φ) (TreeQF.instDecidableRealize t ρ ψ)

/-- `s` is the root: it has no parent. -/
def TreeQF.isRoot (s : TreeTerm V) : TreeQF L V :=
  .conj (.atom (.defined s)) (.neg (.atom (.defined s.parent)))

/-! ### Worked example: a morphological structure -/

section Example

private inductive Cat | word | stem | root | affix
  deriving DecidableEq

open TreeTerm Planar

/-- `[word [stem root affix] affix]` — a stem (root + suffix) with an outer suffix. -/
private def w : TreeModel Cat :=
  .node .word [.node .stem [.node .root [], .node .affix []], .node .affix []]

private def x : TreeTerm (Fin 1) := var 0

-- The node at `[0,0]` is a root whose mother is a stem; its right sibling is an affix.
example : (TreeQF.atom (.label .root x)).Realize w (fun _ => [0, 0]) := by decide
example : (TreeQF.atom (.label .stem x.parent)).Realize w (fun _ => [0, 0]) := by decide
example : (TreeQF.atom (.label .affix x.sibSucc)).Realize w (fun _ => [0, 0]) := by decide
-- The root has no further-out sibling, and the word node is the root of the tree.
example : ¬ (TreeQF.atom (.defined x.sibPred)).Realize w (fun _ => [0, 0]) := by decide
example : (TreeQF.isRoot (L := Cat) x).Realize w (fun _ => []) := by decide

end Example

end Subregular.Logic
