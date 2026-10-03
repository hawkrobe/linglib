module

public import Linglib.Core.Order.TreePath
public import Mathlib.Algebra.Free

/-!
# `Branching`: the rose-tree interface

A carrier `T` is `Branching` when each value exposes an **ordered list
of children**. One field derives, for every instance:

* Gorn-address machinery: `subtreeAt`, `validPaths`, `daughters`, and the subtree relation
  `IsSubtree`
* via `Core/Order/TreePath.lean`, mathlib's rooted-tree order stack on
  positions: root (`⊥`), parent (`Order.pred`), least common ancestor
  (`⊓`), finite ancestor chains.

Sibling order (the `List`) is the load-bearing choice: linear
precedence and planarity are real structure that mathlib's
`Quiver`/`Digraph`/`SimpleGraph` forget, so those are forgetful shadows
of this class, not its basis.

No well-foundedness is required: the path machinery recurses on the
*path* (a structurally decreasing `List ℕ`), not on `T`, so the class is
law-free on the carrier and carriers of infinite depth are admissible.
-/

@[expose] public section

namespace Core.Order

/-- A `Branching` carrier gives each value an ordered list of children, `[]` for leaves. See the
module docstring for what the one field buys. -/
class Branching (T : Type*) where
  /-- Ordered children. -/
  children : T → List T

namespace Branching

variable {T : Type*} [Branching T]

/-- The "is a child of" relation on a `Branching` carrier. -/
def IsChild (c t : T) : Prop := c ∈ children t

/-- Daughters of a node — `children`, by its linguistic name. -/
abbrev daughters (t : T) : List T := children t

/-- Subtree at a Gorn address; `none` if the path leaves the tree.
Recursion is on the path, so no well-foundedness on `T` is needed. -/
def subtreeAt (t : T) : List Nat → Option T
  | [] => some t
  | i :: rest => ((children t)[i]?).bind fun c => subtreeAt c rest

@[simp] theorem subtreeAt_nil (t : T) : subtreeAt t [] = some t := rfl

@[simp] theorem subtreeAt_cons (t : T) (i : Nat) (rest : List Nat) :
    subtreeAt t (i :: rest) =
    ((children t)[i]?).bind fun c => subtreeAt c rest := rfl

/-- `validPaths t` is the set of positions of `t`. Node identity is the position (`TreePath`),
never the subtree value, since identical subtrees occur at several positions, so orders and graphs
must live on paths. -/
def validPaths (t : T) : Set TreePath :=
  {p | (subtreeAt t p.toList).isSome}

theorem bot_mem_validPaths (t : T) : (⊥ : TreePath) ∈ validPaths t := by
  simp [validPaths, subtreeAt]

/-- Descending along `p ++ q` is descending along `p`, then along `q` from there. -/
theorem subtreeAt_append (t : T) (p q : List Nat) :
    subtreeAt t (p ++ q) = (subtreeAt t p).bind (subtreeAt · q) := by
  induction p generalizing t with
  | nil => rfl
  | cons i rest ih =>
    rw [List.cons_append, subtreeAt_cons, subtreeAt_cons]
    rcases hmem : (children t)[i]? with _ | c
    · rfl
    · exact ih c

theorem subtreeAt_cons_eq_some_iff {t s : T} {i : Nat} {p : List Nat} :
    subtreeAt t (i :: p) = some s ↔ ∃ c, (children t)[i]? = some c ∧ subtreeAt c p = some s := by
  simp [Option.bind_eq_some_iff]

/-- Every prefix of an address inside the tree is inside the tree. -/
theorem subtreeAt_take_isSome {t s : T} {p : List Nat} (h : subtreeAt t p = some s) (k : Nat) :
    (subtreeAt t (p.take k)).isSome := by
  rw [← List.take_append_drop k p, subtreeAt_append] at h
  exact Option.isSome_of_isSome_bind (by rw [h]; rfl)

/-- A non-root position descends to one child and is a position there. -/
theorem mem_validPaths_cons {t : T} {i : Nat} {rest : List Nat} :
    (⟨i :: rest⟩ : TreePath) ∈ validPaths t ↔
    ∃ c, (children t)[i]? = some c ∧ (⟨rest⟩ : TreePath) ∈ validPaths c := by
  simp only [validPaths, Set.mem_ofPred_eq, subtreeAt_cons]
  rcases hmem : (children t)[i]? with _ | c <;> simp

/-- Valid paths are closed under prefixes, since the ancestors of a position are positions, so the
set of positions is downward closed and inherits the rooted-tree order stack from `TreePath`. -/
theorem validPaths_prefix_closed {t : T} {p q : TreePath}
    (hq : q ∈ validPaths t) (hpq : p ≤ q) : p ∈ validPaths t := by
  obtain ⟨s, hs⟩ := hpq
  simp only [validPaths, Set.mem_ofPred_eq] at hq ⊢
  rw [← hs, subtreeAt_append] at hq
  exact Option.isSome_of_isSome_bind hq

/-! ### Subtrees -/

/-- `IsSubtree s t` holds when `s` is the subtree of `t` rooted at one of its nodes, reached from
`t` by descending through children. -/
def IsSubtree (s t : T) : Prop := Relation.ReflTransGen IsChild s t

@[refl]
theorem IsSubtree.refl (t : T) : IsSubtree t t := Relation.ReflTransGen.refl

theorem IsSubtree.trans {r s t : T} (h₁ : IsSubtree r s) (h₂ : IsSubtree s t) :
    IsSubtree r t :=
  Relation.ReflTransGen.trans h₁ h₂

instance : @Trans T T T IsSubtree IsSubtree IsSubtree := ⟨IsSubtree.trans⟩

theorem IsSubtree.of_isChild {c t : T} (h : IsChild c t) : IsSubtree c t :=
  Relation.ReflTransGen.single h

/-- The subtrees of `t` are exactly the values of `subtreeAt t` at addresses inside `t`. -/
theorem isSubtree_iff_exists_subtreeAt {s t : T} :
    IsSubtree s t ↔ ∃ p, subtreeAt t p = some s := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[], rfl⟩
    | head hc _ ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hc
      exact ⟨p ++ [i], by simp [subtreeAt_append, hp, hi]⟩
  · rintro ⟨p, hp⟩
    induction p generalizing t with
    | nil => cases hp; exact .refl _
    | cons i p ih =>
      obtain ⟨c, hc, hp⟩ := subtreeAt_cons_eq_some_iff.1 hp
      exact (ih hp).tail (List.mem_of_getElem? hc)

/-! ### Maps commuting with `children`

A map `f` with `children (f t) = (children t).map f` is a map of `Branching` carriers: it
commutes with navigation and preserves the positions. -/

theorem subtreeAt_map_of_children_map {U : Type*} [Branching U] {f : T → U}
    (hf : ∀ t, children (f t) = (children t).map f) (t : T) (p : List Nat) :
    subtreeAt (f t) p = (subtreeAt t p).map f := by
  induction p generalizing t with
  | nil => rfl
  | cons i rest ih =>
    rw [subtreeAt_cons, subtreeAt_cons, hf, List.getElem?_map]
    cases (children t)[i]? with
    | none => rfl
    | some c => exact ih c

theorem validPaths_map_of_children_map {U : Type*} [Branching U] {f : T → U}
    (hf : ∀ t, children (f t) = (children t).map f) (t : T) :
    validPaths (f t) = validPaths t := by
  ext p
  simp [validPaths, subtreeAt_map_of_children_map hf]

theorem isLowerSet_validPaths (t : T) : IsLowerSet (validPaths t) :=
  fun _ _ hpq hq => validPaths_prefix_closed hq hpq

/-- The daughters of a position are its extensions by an index below the arity of its
subtree. -/
theorem mem_validPaths_append_singleton_iff {t : T} {p : List Nat} {i : Nat} :
    (⟨p ++ [i]⟩ : TreePath) ∈ validPaths t ↔
      ∃ s, subtreeAt t p = some s ∧ i < (children s).length := by
  simp only [validPaths, Set.mem_ofPred_eq, subtreeAt_append, subtreeAt_cons, subtreeAt_nil]
  cases subtreeAt t p with
  | none => simp
  | some s => simp

end Branching

/-! ### Instance: `FreeMagma`

Mathlib's free magma is the binary rose tree (bare phrase structure in
the Minimalist reading); the instance lives here because mathlib types
take their instances in the class's home file. -/

instance {α : Type*} : Branching (FreeMagma α) where
  children
    | .of _ => []
    | .mul l r => [l, r]

@[simp] theorem freeMagma_children_of {α : Type*} (a : α) :
    Branching.children (FreeMagma.of a) = [] := rfl

@[simp] theorem freeMagma_children_mul {α : Type*} (l r : FreeMagma α) :
    Branching.children (l.mul r) = [l, r] := rfl

end Core.Order
