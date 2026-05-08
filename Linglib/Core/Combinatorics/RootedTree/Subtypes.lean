import Linglib.Core.Combinatorics.RootedTree.Planar

set_option autoImplicit false

/-!
# Arity-restricted subtypes of `RootedTree.Planar`
@cite{marcolli-chomsky-berwick-2025}

Predicates and subtypes for the arity restrictions MCB uses:

- `isBinary` — every internal vertex has exactly 2 children
  (MCB §1.1.2 "full binary"; book p. 20)
- `arityAtMost n` — every vertex has ≤ n children
  (MCB §1.11.6 "at most n-ary"; book p. 100)
- `arityExactly n` — every internal vertex has exactly n children
  (MCB §1.11.1 SO^(n); book p. 96 Definition 1.11.2)

The arity-exactly-2 case is the binary case (`arityExactly 2 = isBinary`).
The arity-at-most-2 case relaxes binary to also allow 1-child internal
vertices (these arise as remainders of Δ^p deletion-cuts on binary
inputs).

All three predicates are decidable. Subtypes are exposed as
`{ t : Planar α // p t }`.

## Status

`[UPSTREAM]` candidate. No sorries.
-/

namespace RootedTree

namespace Planar

variable {α : Type*}

/-! ## §1: Predicate machinery — recursive over tree structure -/

/-- A tree's root has arity at most `n`. -/
def hasArityAtMost (n : Nat) : Planar α → Prop
  | .node _ cs => cs.length ≤ n

/-- A tree's root has arity exactly `n`, OR is a leaf. -/
def hasArityExactlyOrLeaf (n : Nat) : Planar α → Prop
  | .node _ cs => cs.length = n ∨ cs.length = 0

mutual
/-- The "every vertex" lifting of a per-vertex predicate. Recursively:
    `p` holds at the root, AND at every vertex of every child. -/
def AllVertices (p : Planar α → Prop) : Planar α → Prop
  | .node a cs => p (.node a cs) ∧ AllVerticesList p cs
/-- Auxiliary: `AllVertices p` holds for every tree in the list. -/
def AllVerticesList (p : Planar α → Prop) : List (Planar α) → Prop
  | [] => True
  | t :: ts => AllVertices p t ∧ AllVerticesList p ts
end

mutual
/-- Decidability of `AllVertices` lifts from per-vertex decidability. -/
instance instAllVerticesDecidable
    (p : Planar α → Prop) [DecidablePred p] :
    ∀ (t : Planar α), Decidable (AllVertices p t)
  | .node a cs =>
    have h1 : Decidable (p (.node a cs)) := inferInstance
    have h2 : Decidable (AllVerticesList p cs) := instAllVerticesListDecidable p cs
    match h1, h2 with
    | isTrue ha, isTrue hb => isTrue ⟨ha, hb⟩
    | isFalse hna, _ => isFalse (fun h => hna h.1)
    | _, isFalse hnb => isFalse (fun h => hnb h.2)
/-- Auxiliary list-version of decidability. -/
instance instAllVerticesListDecidable
    (p : Planar α → Prop) [DecidablePred p] :
    ∀ (l : List (Planar α)), Decidable (AllVerticesList p l)
  | [] => isTrue trivial
  | t :: ts =>
    have h1 : Decidable (AllVertices p t) := instAllVerticesDecidable p t
    have h2 : Decidable (AllVerticesList p ts) := instAllVerticesListDecidable p ts
    match h1, h2 with
    | isTrue ha, isTrue hb => isTrue ⟨ha, hb⟩
    | isFalse hna, _ => isFalse (fun h => hna h.1)
    | _, isFalse hnb => isFalse (fun h => hnb h.2)
end

/-- `hasArityAtMost n` is decidable per-vertex. -/
instance (n : Nat) (t : Planar α) : Decidable (hasArityAtMost n t) := by
  cases t with
  | node _ cs => exact inferInstanceAs (Decidable (cs.length ≤ n))

/-- `hasArityExactlyOrLeaf n` is decidable per-vertex. -/
instance (n : Nat) (t : Planar α) : Decidable (hasArityExactlyOrLeaf n t) := by
  cases t with
  | node _ cs => exact inferInstanceAs (Decidable (cs.length = n ∨ cs.length = 0))

/-! ## §2: The three arity restrictions — global predicates -/

/-- A tree is **at-most n-ary** if every vertex has ≤ n children. -/
def isAtMost (n : Nat) : Planar α → Prop :=
  AllVertices (hasArityAtMost n)

/-- A tree is **exactly n-ary** if every internal vertex has exactly
    `n` children (and leaves have 0 children, which is automatic). For
    `n = 2` this is the binary "full binary" condition. -/
def isExactly (n : Nat) : Planar α → Prop :=
  AllVertices (hasArityExactlyOrLeaf n)

/-- A tree is **binary** (full-binary): every internal vertex has
    exactly 2 children. MCB §1.1.2 convention; book p. 20. -/
def isBinary : Planar α → Prop := isExactly 2

instance (n : Nat) (t : Planar α) : Decidable (isAtMost n t) :=
  instAllVerticesDecidable _ t

instance (n : Nat) (t : Planar α) : Decidable (isExactly n t) :=
  instAllVerticesDecidable _ t

instance (t : Planar α) : Decidable (isBinary t) :=
  inferInstanceAs (Decidable (isExactly 2 t))

/-! ## §3: Subtypes -/

/-- The subtype of trees with arity ≤ `n` everywhere. -/
abbrev SubAtMost (n : Nat) (α : Type*) : Type _ :=
  { t : Planar α // isAtMost n t }

/-- The subtype of trees with arity exactly `n` at every internal vertex. -/
abbrev SubExactly (n : Nat) (α : Type*) : Type _ :=
  { t : Planar α // isExactly n t }

/-- The subtype of binary (full-binary) trees. -/
abbrev SubBinary (α : Type*) : Type _ :=
  { t : Planar α // isBinary t }

/-! ## §4: Sanity checks -/

example : isBinary (leaf 1 : Planar Nat) := by
  unfold isBinary isExactly leaf AllVertices hasArityExactlyOrLeaf AllVerticesList
  exact ⟨Or.inr rfl, trivial⟩

example : isBinary (binary 1 (leaf 2) (leaf 3) : Planar Nat) := by
  unfold isBinary isExactly binary leaf AllVertices hasArityExactlyOrLeaf AllVerticesList
  refine ⟨Or.inl rfl, ⟨⟨Or.inr rfl, trivial⟩, ⟨Or.inr rfl, trivial⟩, trivial⟩⟩

example : ¬ isBinary (unary 1 (leaf 2) : Planar Nat) := by
  unfold isBinary isExactly unary leaf AllVertices hasArityExactlyOrLeaf AllVerticesList
  intro h
  rcases h.1 with h1 | h1 <;> simp at h1

example : isAtMost 2 (unary 1 (leaf 2) : Planar Nat) := by
  unfold isAtMost unary leaf AllVertices hasArityAtMost AllVerticesList
  exact ⟨Nat.le.step (Nat.le.refl), ⟨Nat.zero_le 2, trivial⟩, trivial⟩

end Planar

end RootedTree
