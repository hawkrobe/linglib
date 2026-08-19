/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Lemmas

/-!
# Bud generating systems on colored binary trees

A **bud generating system** ([giraudo-2019]) equips an operad with a set of
colors, a set of colored operations (the rules), and a set of terminal
colors; the generated language is the set of colored operations derivable
from a single-color unit by color-matching operad composition. This file
develops the construction over the free binary operad, whose operations are
binary trees and whose insertions graft a tree onto a leaf. A `Bud.Tree`
carries a color at every vertex: leaf colors are the operation's inputs,
the root color its output, and the internal colors record the colors
matched during composition — in a colored operad the color at a grafting
vertex is determined by the matched pair, so the decorations are exactly
the data of a decomposition into generators.

## Main declarations

* `Bud.Tree`, `Bud.Tree.out`, `Bud.Tree.inputs` — vertex-colored binary
  trees with their output and input colors.
* `Bud.Tree.graft` — insertion at the `i`-th leaf, the free binary operad's
  partial composition; `Bud.Tree.graft_graft` is the nested-insertion
  relation.
* `Bud.Tree.NodeLocal` — a predicate holds at every internal vertex; the
  invariant format preserved by color-matched grafting.
* `Bud.System`, `Bud.System.Derives`, `Bud.System.Lang` — bud generating
  systems with initial colors the non-terminal ones ([giraudo-2019]'s
  `I = Ω ∖ T` case), derivability from a unit, and the generated language.
* `Bud.System.Derives.compose` — derivations compose along color-matched
  inputs; `Bud.System.Derives.nodeLocal` — any vertex-local property of
  the rules holds throughout every derivable tree.

## Implementation notes

Bud generating systems are the operadic analogue of context-free
grammars, with trees in place of words ([giraudo-2019] develops the
correspondence); this file follows the register of
`Mathlib.Computability.ContextFreeGrammar` — a rule set, an inductive
derivation relation, and the generated language — with colors playing the
role of `Symbol` and the terminal-color set replacing the
terminal/nonterminal type split. Mathlib's `SimpleGraph.Coloring` is not
applicable: proper graph coloring constrains adjacent colors to *differ*,
while operadic coloring constrains composed colors to *match*.
-/

namespace Bud

variable {Ω : Type*}

/-- A binary tree with a color at every vertex: an operation of the bud
    operad over the free binary operad, decorated with the colors it
    propagates ([giraudo-2019]). -/
inductive Tree (Ω : Type*) where
  | leaf (c : Ω)
  | node (c : Ω) (l r : Tree Ω)
  deriving DecidableEq, Repr

namespace Tree

variable {x s y : Tree Ω} {c d : Ω} {i j : ℕ}

/-- The output color: the color at the root. -/
def out : Tree Ω → Ω
  | leaf c => c
  | node c _ _ => c

@[simp] theorem out_leaf : (leaf c).out = c := rfl

@[simp] theorem out_node {l r : Tree Ω} : (node c l r).out = c := rfl

/-- The input colors: the leaf colors, left to right. -/
def inputs : Tree Ω → List Ω
  | leaf c => [c]
  | node _ l r => l.inputs ++ r.inputs

@[simp] theorem inputs_leaf : (leaf c).inputs = [c] := rfl

@[simp] theorem inputs_node {l r : Tree Ω} :
    (node c l r).inputs = l.inputs ++ r.inputs := rfl

/-- The number of inputs. -/
def numInputs : Tree Ω → ℕ
  | leaf _ => 1
  | node _ l r => l.numInputs + r.numInputs

@[simp] theorem numInputs_leaf : (leaf c).numInputs = 1 := rfl

@[simp] theorem numInputs_node {l r : Tree Ω} :
    (node c l r).numInputs = l.numInputs + r.numInputs := rfl

@[simp] theorem length_inputs (x : Tree Ω) :
    x.inputs.length = x.numInputs := by
  induction x <;> simp [*]

theorem numInputs_pos (x : Tree Ω) : 0 < x.numInputs := by
  induction x with
  | leaf _ => exact Nat.one_pos
  | node c l r ihl ihr => simp only [numInputs_node]; omega

theorem getElem?_inputs_node {l r : Tree Ω} :
    (node c l r).inputs[i]? =
      if i < l.numInputs then l.inputs[i]? else r.inputs[i - l.numInputs]? := by
  by_cases h : i < l.numInputs
  · rw [if_pos h, inputs_node, List.getElem?_append_left (by simpa using h)]
  · rw [if_neg h, inputs_node,
      List.getElem?_append_right (by simpa using not_lt.mp h), length_inputs]

/-- Graft `s` onto the `i`-th leaf of `x`: the free binary operad's
    insertion `x ∘ᵢ s`. Out-of-range indices leave the tree unchanged. -/
def graft : Tree Ω → ℕ → Tree Ω → Tree Ω
  | leaf _, 0, s => s
  | leaf c, _ + 1, _ => leaf c
  | node c l r, i, s =>
      if i < l.numInputs then node c (l.graft i s) r
      else node c l (r.graft (i - l.numInputs) s)

@[simp] theorem graft_leaf_zero : (leaf c).graft 0 s = s := rfl

theorem graft_node {l r : Tree Ω} :
    (node c l r).graft i s =
      if i < l.numInputs then node c (l.graft i s) r
      else node c l (r.graft (i - l.numInputs) s) := rfl

/-- Color-matched grafting preserves the output color. -/
theorem out_graft (h : x.inputs[i]? = some s.out) :
    (x.graft i s).out = x.out := by
  cases x with
  | leaf c =>
    cases i with
    | zero => simpa using (by simpa using h : c = s.out).symm
    | succ n => rfl
  | node c l r => rw [graft_node]; split <;> rfl

/-- Grafting the unit of the matched color changes nothing. -/
theorem graft_unit (h : x.inputs[i]? = some d) : x.graft i (leaf d) = x := by
  induction x generalizing i with
  | leaf c =>
    cases i with
    | zero => simpa using congrArg leaf (by simpa using h : c = d).symm
    | succ n => rfl
  | node c l r ihl ihr =>
    rw [getElem?_inputs_node] at h
    rw [graft_node]
    by_cases hi : i < l.numInputs
    · rw [if_pos hi] at h ⊢
      rw [ihl h]
    · rw [if_neg hi] at h ⊢
      rw [ihr h]

/-- Grafting splices the inserted tree's inputs into the host's. -/
theorem inputs_graft (h : i < x.numInputs) :
    (x.graft i s).inputs =
      x.inputs.take i ++ s.inputs ++ x.inputs.drop (i + 1) := by
  induction x generalizing i with
  | leaf c =>
    obtain rfl : i = 0 := Nat.lt_one_iff.mp (by simpa using h)
    simp
  | node c l r ihl ihr =>
    have hlen : l.inputs.length = l.numInputs := l.length_inputs
    rw [graft_node]
    by_cases hi : i < l.numInputs
    · rw [if_pos hi]
      have h0 : i - l.numInputs = 0 := by omega
      have h1 : i + 1 - l.numInputs = 0 := by omega
      simp [ihl hi, List.take_append,
        List.drop_append, h0, h1]
    · rw [if_neg hi]
      have hle : l.inputs.length ≤ i := by omega
      have h2 : i - l.numInputs < r.numInputs := by
        have := numInputs_node (c := c) (l := l) (r := r) ▸ h
        omega
      have h3 : l.inputs.take i = l.inputs := List.take_of_length_le (by omega)
      have h4 : l.inputs.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
      have h5 : i + 1 - l.numInputs = i - l.numInputs + 1 := by omega
      simp [ihr h2, List.take_append,
        List.drop_append, h3, h4, h5, hlen]

theorem numInputs_graft (h : i < x.numInputs) :
    (x.graft i s).numInputs = x.numInputs + s.numInputs - 1 := by
  have h1 := congrArg List.length (inputs_graft (s := s) h)
  simp only [length_inputs, List.length_append, List.length_take,
    List.length_drop] at h1
  omega

/-- The inserted tree's inputs sit at offset `i` in the grafted tree. -/
theorem getElem?_inputs_graft_middle (hi : i < x.numInputs)
    (hj : j < s.numInputs) :
    (x.graft i s).inputs[i + j]? = s.inputs[j]? := by
  have hA : (x.inputs.take i).length = i := by
    simp only [List.length_take, length_inputs]
    omega
  rw [inputs_graft hi,
    List.getElem?_append_left (by simp [hA]; omega),
    List.getElem?_append_right (by omega : (x.inputs.take i).length ≤ i + j),
    hA]
  simp

/-- Nested insertions compose, with the inner index offset by the outer
    insertion point: the nested case of the operadic insertion relations. -/
theorem graft_graft (hi : i < x.numInputs) (hj : j < s.numInputs) :
    (x.graft i s).graft (i + j) y = x.graft i (s.graft j y) := by
  induction x generalizing i with
  | leaf c =>
    obtain rfl : i = 0 := Nat.lt_one_iff.mp (by simpa using hi)
    simp
  | node c l r ihl ihr =>
    by_cases hil : i < l.numInputs
    · have hlg : i + j < (l.graft i s).numInputs := by
        rw [numInputs_graft hil]
        omega
      rw [graft_node, if_pos hil, graft_node, if_pos hlg, graft_node,
        if_pos hil, ihl hil]
    · have hir : i - l.numInputs < r.numInputs := by
        have := numInputs_node (c := c) (l := l) (r := r) ▸ hi
        omega
      rw [graft_node, if_neg hil, graft_node, if_neg (by omega), graft_node,
        if_neg hil, (by omega : i + j - l.numInputs = i - l.numInputs + j),
        ihr hir]

/-- `P` holds at every internal vertex, of the vertex color and the two
    children's output colors. -/
def NodeLocal (P : Ω → Ω → Ω → Prop) : Tree Ω → Prop
  | leaf _ => True
  | node c l r => P c l.out r.out ∧ l.NodeLocal P ∧ r.NodeLocal P

@[simp] theorem nodeLocal_leaf {P : Ω → Ω → Ω → Prop} :
    (leaf c).NodeLocal P := trivial

@[simp] theorem nodeLocal_node {P : Ω → Ω → Ω → Prop} {l r : Tree Ω} :
    (node c l r).NodeLocal P ↔
      P c l.out r.out ∧ l.NodeLocal P ∧ r.NodeLocal P := Iff.rfl

/-- Color-matched grafting preserves vertex-local properties: the host's
    vertices keep their colors (the replaced leaf's color equals the
    inserted root's), and the inserted tree brings its own. -/
theorem NodeLocal.graft {P : Ω → Ω → Ω → Prop} (hx : x.NodeLocal P)
    (hs : s.NodeLocal P) (h : x.inputs[i]? = some s.out) :
    (x.graft i s).NodeLocal P := by
  induction x generalizing i with
  | leaf c =>
    cases i with
    | zero => simpa using hs
    | succ n => exact nodeLocal_leaf
  | node c l r ihl ihr =>
    obtain ⟨hP, hl, hr⟩ := hx
    rw [getElem?_inputs_node] at h
    rw [graft_node]
    by_cases hi : i < l.numInputs
    · rw [if_pos hi] at h ⊢
      exact ⟨(out_graft h).symm ▸ hP, ihl hl h, hr⟩
    · rw [if_neg hi] at h ⊢
      exact ⟨(out_graft h).symm ▸ hP, hl, ihr hr h⟩

end Tree

/-- A bud generating system over the free binary operad ([giraudo-2019],
    with initial colors `I = Ω ∖ Terminal`): a set of colored operations
    (the rules) and a set of terminal colors. -/
structure System (Ω : Type*) where
  rules : Set (Tree Ω)
  Terminal : Set Ω

namespace System

variable {B : System Ω} {c d : Ω} {x s : Tree Ω} {i : ℕ}

/-- Derivability from the unit of color `c`: start from the one-leaf tree
    and repeatedly graft rules onto color-matched leaves. -/
inductive Derives (B : System Ω) (c : Ω) : Tree Ω → Prop
  | unit (hc : c ∉ B.Terminal) : Derives B c (.leaf c)
  | graft {x s : Tree Ω} (i : ℕ) (hx : Derives B c x) (hs : s ∈ B.rules)
      (hm : x.inputs[i]? = some s.out) : Derives B c (x.graft i s)

/-- The generated language: trees derivable from some unit, all of whose
    inputs are terminal. -/
def Lang (B : System Ω) (x : Tree Ω) : Prop :=
  (∃ c, B.Derives c x) ∧ ∀ d ∈ x.inputs, d ∈ B.Terminal

/-- A derivation preserves the unit's color as output. -/
theorem Derives.out_eq (h : B.Derives c x) : x.out = c := by
  induction h with
  | unit => rfl
  | graft i _ _ hm ih => rw [Tree.out_graft hm, ih]

/-- The output color of a derivable tree is non-terminal. -/
theorem Derives.out_not_terminal (h : B.Derives c x) : c ∉ B.Terminal := by
  induction h with
  | unit hc => exact hc
  | graft _ _ _ _ ih => exact ih

/-- Derivations compose along a color-matched input: a derivation of the
    matched color can be carried out in place inside the host. -/
theorem Derives.compose (hx : B.Derives c x) (hi : i < x.numInputs)
    (hm : x.inputs[i]? = some d) (hs : B.Derives d s) :
    B.Derives c (x.graft i s) := by
  induction hs with
  | unit hc =>
    rw [Tree.graft_unit hm]
    exact hx
  | @graft y r j hy hr hm' ih =>
    have hjy : j < y.numInputs := by
      by_contra hj
      rw [List.getElem?_eq_none (by simpa using not_lt.mp hj)] at hm'
      simp at hm'
    rw [← Tree.graft_graft hi hjy]
    exact ih.graft (i + j) hr
      (by rw [Tree.getElem?_inputs_graft_middle hi hjy]; exact hm')

/-- Any vertex-local property of the rules holds throughout every
    derivable tree: the fundamental invariant of bud derivation. -/
theorem Derives.nodeLocal {P : Ω → Ω → Ω → Prop} (h : B.Derives c x)
    (hR : ∀ r ∈ B.rules, r.NodeLocal P) : x.NodeLocal P := by
  induction h with
  | unit _ => exact Tree.nodeLocal_leaf
  | graft i _ hs hm ih => exact ih.graft (hR _ hs) hm

end System

end Bud
