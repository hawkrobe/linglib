import Linglib.Core.Algebra.RootedTree.PreLie.Defs
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.Bind
import Mathlib.Tactic.Abel

set_option autoImplicit false

/-!
# Vertex classification + commutativity for `Planar.insertSum`
@cite{foissy-typed-decorated-rooted-trees-2018}
@cite{chapoton-livernet-2001}

Per-vertex bookkeeping for the pre-Lie identity proof: the vertices of
`insertAt e T₂` partition into three classes — lifted vertices of `T₂`,
the source vertex `e` itself (now carrying a new child), and preserved
vertices of `T` other than `e` — and this partition is a bijection
(`Vertex.classifyEquiv`). On top of that bijection we prove the
commutativity lemma `insertAt_commute_diff` and the lifted-equals-nested
identity `insertAt_lift_eq_nested`, which together feed the pre-Lie
cancellation in R.3d.

## Layout

- §5: `Vertex.lift` — embed a vertex of `T₂` into `insertAt e T₂`.
  Mutual recursion on `(Vertex, VertexList)`.
- §6: `Vertex.newGraft` — derived: the position of `T₂`'s root in
  `insertAt e T₂` (lifted root).
- §7: `Vertex.preserve?` / `VertexList.preserve?` — total
  Option-valued: returns `none` exactly on the diagonal, `some` of the
  preserved vertex otherwise.
- §8: `Vertex.preserveOf` / `VertexList.preserveOf` — Option-free
  variant assuming `f ≠ e`. Diagonal cases dispatched via `absurd rfl h`.
- §9: `Vertex.classifyEquiv` — the 3-class bijection
  `Vertex (insertAt e T₂) ≃ Vertex T₂ ⊕ Unit ⊕ {f : Vertex T // f ≠ e}`,
  packaged via a custom inductive `Vertex.Classify` for readability.
- §10: `insertAt_commute_diff` (different vertices commute) and
  `insertAt_lift_eq_nested` (the lifted-equals-nested identity).

## Relation to the deleted binary file

`Linglib/Core/Algebra/Free/PreLie.lean` (deleted at commit `e0876460`)
carried the analogous edge classification + commutativity for binary
trees with edge-subdivision insertion. The binary version had 4 `Edge`
constructors → 16-case `preserve?`, 5 classes (3 new edges from the
split), and ~600 LOC. The n-ary vertex version has 2 `Vertex`
constructors × 2 `VertexList` constructors → 4-case match with mutual
recursion, 3 classes (no new edges from grafting; T₂'s root is just a
lifted vertex), and similar LOC.

## File scope (R.3b)

This file extends `PreLie/Defs.lean` (R.3a) with sections §5-§10.
Sibling files in `PreLie/`:
- `Nonplanar.lean` (R.3c): descent through `Nonplanar.mk`.
- `Algebra.lean` (R.3d): bilinear extension + pre-Lie identity +
  `RightPreLieAlgebra ℤ` instance — uses `classifyEquiv`,
  `insertAt_commute_diff`, and `insertAt_lift_eq_nested`.

## Status

`[UPSTREAM]` candidate. Sorry-free.
-/

namespace RootedTree

namespace Planar

variable {α : Type*}

/-! ## §5: `Vertex.lift` — embed a vertex of `T₂` into `insertAt e T₂`

When `T₂` is grafted at vertex `e` of `T`, every vertex of `T₂` becomes
a vertex-position in `insertAt e T₂` (sitting under the new edge from
`e` to `T₂`'s root). `Vertex.lift e T₂ f` returns the position of
`f : Vertex T₂` inside the grafted tree. Mutual with `VertexList.lift`. -/

mutual
/-- Embed a vertex of `T₂` into `insertAt e T₂` at the position where
    `T₂` was grafted. Recursive on `e`. -/
def Vertex.lift : ∀ {T : Planar α} (e : Vertex T) (T₂ : Planar α),
    Vertex T₂ → Vertex (insertAt e T₂)
  | _, .root a cs,         T₂, f => .inChild a (T₂ :: cs) (.head T₂ cs f)
  | _, .inChild a cs vl,   T₂, f => .inChild a (insertAtList vl T₂)
                                       (VertexList.lift vl T₂ f)
/-- Embed a vertex of `T₂` into `insertAtList vl T₂`. Recursive on `vl`. -/
def VertexList.lift : ∀ {cs : List (Planar α)} (vl : VertexList cs)
      (T₂ : Planar α), Vertex T₂ → VertexList (insertAtList vl T₂)
  | _, .head c cs v,   T₂, f => .head (insertAt v T₂) cs (Vertex.lift v T₂ f)
  | _, .tail c cs vl,  T₂, f => .tail c (insertAtList vl T₂)
                                  (VertexList.lift vl T₂ f)
end

@[simp] theorem Vertex.lift_root (a : α) (cs : List (Planar α))
    (T₂ : Planar α) (f : Vertex T₂) :
    Vertex.lift (Vertex.root a cs) T₂ f =
      .inChild a (T₂ :: cs) (.head T₂ cs f) := rfl

@[simp] theorem Vertex.lift_inChild (a : α) (cs : List (Planar α))
    (vl : VertexList cs) (T₂ : Planar α) (f : Vertex T₂) :
    Vertex.lift (Vertex.inChild a cs vl) T₂ f =
      .inChild a (insertAtList vl T₂) (VertexList.lift vl T₂ f) := rfl

@[simp] theorem VertexList.lift_head (c : Planar α) (cs : List (Planar α))
    (v : Vertex c) (T₂ : Planar α) (f : Vertex T₂) :
    VertexList.lift (VertexList.head c cs v) T₂ f =
      .head (insertAt v T₂) cs (Vertex.lift v T₂ f) := rfl

@[simp] theorem VertexList.lift_tail (c : Planar α) (cs : List (Planar α))
    (vl : VertexList cs) (T₂ : Planar α) (f : Vertex T₂) :
    VertexList.lift (VertexList.tail c cs vl) T₂ f =
      .tail c (insertAtList vl T₂) (VertexList.lift vl T₂ f) := rfl

/-! ## §6: `Vertex.newGraft` — the position of `T₂`'s root after grafting

A derived definition: `T₂ = Planar.node b ds` has root vertex
`Vertex.root b ds`; lifting it through `Vertex.lift` gives the position
of `T₂`'s root in `insertAt e T₂`. Useful as a named handle for the
pre-Lie identity proof, where T₂'s root plays a distinguished role. -/

/-- The unique vertex of `insertAt e T₂` whose subtree is `T₂` — i.e.
    the root of the embedded `T₂` in the grafted tree. Defined as the
    lift of `T₂.rootVertex` through `Vertex.lift`. -/
def Vertex.newGraft {T : Planar α} (e : Vertex T) (T₂ : Planar α) :
    Vertex (insertAt e T₂) :=
  Vertex.lift e T₂ T₂.rootVertex

@[simp] theorem Vertex.newGraft_node {T : Planar α} (e : Vertex T) (b : α)
    (ds : List (Planar α)) :
    Vertex.newGraft e (Planar.node b ds) =
      Vertex.lift e (Planar.node b ds) (Vertex.root b ds) := rfl

/-! ## §7: `Vertex.preserve?` — Option-valued non-source vertex transport

`preserve? e f T₂` returns `some` of the position of `f` in
`insertAt e T₂` when `f ≠ e`, and `none` exactly on the diagonal `f = e`.

The 4 cases on `(e, f) : Vertex T × Vertex T`:
- `(root, root)` — diagonal, `none`.
- `(root, inChild _ _ vl)` — `vl` is preserved as a tail-of-T₂ position.
- `(inChild _ _ vl, root)` — root is preserved as the new root.
- `(inChild _ _ vl₁, inChild _ _ vl₂)` — recurse via `VertexList.preserve?`.
-/

mutual
/-- Total Option-valued preservation: `some` everywhere except on the
    diagonal `(e, e)`. -/
def Vertex.preserve? : ∀ {T : Planar α} (e _f : Vertex T) (T₂ : Planar α),
    Option (Vertex (insertAt e T₂))
  | _, .root _ _,         .root _ _,         _  => none
  | _, .root a cs,        .inChild _ _ vl,   T₂ =>
      some (.inChild a (T₂ :: cs) (.tail T₂ cs vl))
  | _, .inChild a cs vl,  .root _ _,         T₂ =>
      some (.root a (insertAtList vl T₂))
  | _, .inChild a cs vl₁, .inChild _ _ vl₂,  T₂ =>
      (VertexList.preserve? vl₁ vl₂ T₂).map
        (.inChild a (insertAtList vl₁ T₂))
/-- Sibling on `VertexList`. The 4 cases on `(vl₁, vl₂)`:
    - `(head, head)` — recurse on the head children's `Vertex.preserve?`.
    - `(head, tail)` — different children, preserved as `.tail`.
    - `(tail, head)` — different children, preserved as `.head`.
    - `(tail, tail)` — recurse on `VertexList.preserve?`. -/
def VertexList.preserve? : ∀ {cs : List (Planar α)}
      (vl₁ _vl₂ : VertexList cs) (T₂ : Planar α),
    Option (VertexList (insertAtList vl₁ T₂))
  | _, .head c cs v₁,   .head _ _ v₂,    T₂ =>
      (Vertex.preserve? v₁ v₂ T₂).map
        (.head (insertAt v₁ T₂) cs)
  | _, .head c cs v₁,   .tail _ _ vl₂,   T₂ =>
      some (.tail (insertAt v₁ T₂) cs vl₂)
  | _, .tail c cs vl₁,  .head _ _ v₂,    _  =>
      some (.head c (insertAtList vl₁ _) v₂)
  | _, .tail c cs vl₁,  .tail _ _ vl₂,   T₂ =>
      (VertexList.preserve? vl₁ vl₂ T₂).map
        (.tail c (insertAtList vl₁ T₂))
end

/-! ## §8: `Vertex.preserveOf` — Option-free variant assuming `f ≠ e`

The diagonal cases of `preserve?` are exactly the impossible cases
under the hypothesis `f ≠ e`; dispatching them via `absurd rfl h`
yields a total function. The recursion clauses pass a derived
inequality `vl₂ ≠ vl₁` to the recursive call, obtained by congruence
on the `inChild`/`tail` constructor. -/

mutual
/-- Option-free preservation: produces the position of `f` in
    `insertAt e T₂` directly, given `f ≠ e`. -/
def Vertex.preserveOf : ∀ {T : Planar α} (e f : Vertex T) (_h : f ≠ e)
      (T₂ : Planar α),
    Vertex (insertAt e T₂)
  | _, .root _ _,         .root _ _,         h, _  => absurd rfl h
  | _, .root a cs,        .inChild _ _ vl,   _, T₂ =>
      .inChild a (T₂ :: cs) (.tail T₂ cs vl)
  | _, .inChild a cs vl,  .root _ _,         _, T₂ =>
      .root a (insertAtList vl T₂)
  | _, .inChild a cs vl₁, .inChild _ _ vl₂,  h, T₂ =>
      .inChild a (insertAtList vl₁ T₂)
        (VertexList.preserveOf vl₁ vl₂
          (fun heq => h (by rw [heq])) T₂)
/-- Option-free preservation on `VertexList`. -/
def VertexList.preserveOf : ∀ {cs : List (Planar α)}
      (vl₁ vl₂ : VertexList cs) (_h : vl₂ ≠ vl₁) (T₂ : Planar α),
    VertexList (insertAtList vl₁ T₂)
  | _, .head c cs v₁,   .head _ _ v₂,    h, T₂ =>
      .head (insertAt v₁ T₂) cs
        (Vertex.preserveOf v₁ v₂ (fun heq => h (by rw [heq])) T₂)
  | _, .head c cs v₁,   .tail _ _ vl₂,   _, T₂ =>
      .tail (insertAt v₁ T₂) cs vl₂
  | _, .tail c cs vl₁,  .head _ _ v₂,    _, _  =>
      .head c (insertAtList vl₁ _) v₂
  | _, .tail c cs vl₁,  .tail _ _ vl₂,   h, T₂ =>
      .tail c (insertAtList vl₁ T₂)
        (VertexList.preserveOf vl₁ vl₂
          (fun heq => h (by rw [heq])) T₂)
end

/-! ### Diagonal lemmas: `preserve? e e = none` -/

mutual
theorem Vertex.preserve?_self : ∀ {T : Planar α} (e : Vertex T)
      (T₂ : Planar α),
    Vertex.preserve? e e T₂ = none
  | _, .root _ _,        _ => rfl
  | _, .inChild _ _ vl,  T₂ => by
    show (VertexList.preserve? vl vl T₂).map _ = none
    rw [VertexList.preserve?_self vl T₂]; rfl
theorem VertexList.preserve?_self : ∀ {cs : List (Planar α)}
      (vl : VertexList cs) (T₂ : Planar α),
    VertexList.preserve? vl vl T₂ = none
  | _, .head c cs v,   T₂ => by
    show (Vertex.preserve? v v T₂).map _ = none
    rw [Vertex.preserve?_self v T₂]; rfl
  | _, .tail c cs vl,  T₂ => by
    show (VertexList.preserve? vl vl T₂).map _ = none
    rw [VertexList.preserve?_self vl T₂]; rfl
end

/-! ### Off-diagonal: `preserve? e f = some (preserveOf e f h)` -/

mutual
theorem Vertex.preserve?_of_ne : ∀ {T : Planar α} (e f : Vertex T)
      (h : f ≠ e) (T₂ : Planar α),
    Vertex.preserve? e f T₂ = some (Vertex.preserveOf e f h T₂)
  | _, .root _ _,         .root _ _,         h, _  => absurd rfl h
  | _, .root _ _,         .inChild _ _ _,    _, _  => rfl
  | _, .inChild _ _ _,    .root _ _,         _, _  => rfl
  | _, .inChild _ _ vl₁,  .inChild _ _ vl₂,  h, T₂ => by
    show (VertexList.preserve? vl₁ vl₂ T₂).map _
        = some (Vertex.inChild _ _ (VertexList.preserveOf vl₁ vl₂ _ T₂))
    rw [VertexList.preserve?_of_ne vl₁ vl₂
          (fun heq => h (by rw [heq])) T₂]
    rfl
theorem VertexList.preserve?_of_ne : ∀ {cs : List (Planar α)}
      (vl₁ vl₂ : VertexList cs) (h : vl₂ ≠ vl₁) (T₂ : Planar α),
    VertexList.preserve? vl₁ vl₂ T₂
        = some (VertexList.preserveOf vl₁ vl₂ h T₂)
  | _, .head c cs v₁,   .head _ _ v₂,    h, T₂ => by
    show (Vertex.preserve? v₁ v₂ T₂).map _
        = some (VertexList.head _ _ (Vertex.preserveOf v₁ v₂ _ T₂))
    rw [Vertex.preserve?_of_ne v₁ v₂
          (fun heq => h (by rw [heq])) T₂]
    rfl
  | _, .head _ _ _,     .tail _ _ _,     _, _  => rfl
  | _, .tail _ _ _,     .head _ _ _,     _, _  => rfl
  | _, .tail c cs vl₁,  .tail _ _ vl₂,   h, T₂ => by
    show (VertexList.preserve? vl₁ vl₂ T₂).map _
        = some (VertexList.tail _ _ (VertexList.preserveOf vl₁ vl₂ _ T₂))
    rw [VertexList.preserve?_of_ne vl₁ vl₂
          (fun heq => h (by rw [heq])) T₂]
    rfl
end

/-! ## §9: `Vertex.classifyEquiv` — the 3-class bijection

Every vertex of `insertAt e T₂` falls into exactly one of three classes:
**lifted** (a vertex of `T₂`), **sourceSelf** (the source vertex `e`
itself, now carrying a new child), or **preserved** (a vertex of `T`
other than `e`). Packaged as a custom inductive `Vertex.Classify` (more
readable than the equivalent `Vertex T₂ ⊕ Unit ⊕ {f : Vertex T // f ≠ e}`),
with `fromClassify` and `toClassify` exhibiting the bijection. -/

/-- Disjoint union of the 3 vertex classes for `insertAt e T₂`:
    preserved vertices of `T` (other than `e`), the source vertex `e`
    itself, and lifted vertices of `T₂`.

    Preferred over the equivalent `Vertex T₂ ⊕ Unit ⊕ {f : Vertex T // f ≠ e}`
    because the indices `{T} {e} {T₂}` are implicit-and-shared across all
    three constructors: downstream `cases c with | preserved | sourceSelf
    | lifted` matches read cleanly without the nested `.inl/.inr`
    bookkeeping `⊕` would require. -/
inductive Vertex.Classify : ∀ {T : Planar α}, Vertex T → Planar α → Type _
  | preserved {T : Planar α} {e : Vertex T} {T₂ : Planar α}
      (f : Vertex T) (h : f ≠ e) : Vertex.Classify e T₂
  | sourceSelf {T : Planar α} {e : Vertex T} {T₂ : Planar α} :
      Vertex.Classify e T₂
  | lifted {T : Planar α} {e : Vertex T} {T₂ : Planar α}
      (g : Vertex T₂) : Vertex.Classify e T₂

/-- Sibling on `VertexList`: the 3 vertex classes for `insertAtList vl T₂`. -/
inductive VertexList.Classify : ∀ {cs : List (Planar α)},
    VertexList cs → Planar α → Type _
  | preserved {cs : List (Planar α)} {vl : VertexList cs} {T₂ : Planar α}
      (vl' : VertexList cs) (h : vl' ≠ vl) : VertexList.Classify vl T₂
  | sourceSelf {cs : List (Planar α)} {vl : VertexList cs} {T₂ : Planar α} :
      VertexList.Classify vl T₂
  | lifted {cs : List (Planar α)} {vl : VertexList cs} {T₂ : Planar α}
      (g : Vertex T₂) : VertexList.Classify vl T₂

/-! ### Helpers: source-vertex preservation -/

mutual
/-- The position of `e` itself in `insertAt e T₂` (still present, just
    with a new child). -/
def Vertex.sourceSelf : ∀ {T : Planar α} (e : Vertex T) (T₂ : Planar α),
    Vertex (insertAt e T₂)
  | _, .root a cs,        T₂ => .root a (T₂ :: cs)
  | _, .inChild a cs vl,  T₂ =>
      .inChild a (insertAtList vl T₂) (VertexList.sourceSelf vl T₂)
def VertexList.sourceSelf : ∀ {cs : List (Planar α)} (vl : VertexList cs)
      (T₂ : Planar α),
    VertexList (insertAtList vl T₂)
  | _, .head c cs v,   T₂ =>
      .head (insertAt v T₂) cs (Vertex.sourceSelf v T₂)
  | _, .tail c cs vl,  T₂ =>
      .tail c (insertAtList vl T₂) (VertexList.sourceSelf vl T₂)
end

/-! ### Realization: each class becomes a vertex of `insertAt e T₂` -/

/-- Realize a `Vertex.Classify` as a concrete vertex of `insertAt e T₂`. -/
def Vertex.fromClassify : ∀ {T : Planar α} {e : Vertex T} {T₂ : Planar α},
    Vertex.Classify e T₂ → Vertex (insertAt e T₂)
  | _, e, T₂, .preserved f h  => Vertex.preserveOf e f h T₂
  | _, e, T₂, .sourceSelf     => Vertex.sourceSelf e T₂
  | _, e, T₂, .lifted g       => Vertex.lift e T₂ g

/-- Realize a `VertexList.Classify` as a concrete entry of
    `insertAtList vl T₂`. -/
def VertexList.fromClassify : ∀ {cs : List (Planar α)}
      {vl : VertexList cs} {T₂ : Planar α},
    VertexList.Classify vl T₂ → VertexList (insertAtList vl T₂)
  | _, vl, T₂, .preserved vl' h => VertexList.preserveOf vl vl' h T₂
  | _, vl, T₂, .sourceSelf      => VertexList.sourceSelf vl T₂
  | _, vl, T₂, .lifted g        => VertexList.lift vl T₂ g

/-! ### Transport helpers: lift inner classifications to outer ones -/

/-- Lift a `Vertex.Classify v T₂` (for the head child `v`) to a
    `VertexList.Classify (.head c cs v) T₂`. The three cases pass
    through with constructor injectivity for the preserved case. -/
def VertexList.Classify.fromHead {c : Planar α} {cs : List (Planar α)}
    {v : Vertex c} (T₂ : Planar α) :
    Vertex.Classify v T₂ → VertexList.Classify (VertexList.head c cs v) T₂
  | .preserved f h =>
      .preserved (VertexList.head c cs f)
        (by intro heq; cases heq; exact h rfl)
  | .sourceSelf  => .sourceSelf
  | .lifted g    => .lifted g

/-- Lift a `VertexList.Classify vl T₂` (for the tail) to a
    `VertexList.Classify (.tail c cs vl) T₂`. -/
def VertexList.Classify.fromTail {c : Planar α} {cs : List (Planar α)}
    {vl : VertexList cs} (T₂ : Planar α) :
    VertexList.Classify vl T₂ → VertexList.Classify (VertexList.tail c cs vl) T₂
  | .preserved vl' h =>
      .preserved (VertexList.tail c cs vl')
        (by intro heq; cases heq; exact h rfl)
  | .sourceSelf  => .sourceSelf
  | .lifted g    => .lifted g

/-- Lift a `VertexList.Classify vl T₂` to a
    `Vertex.Classify (.inChild a cs vl) T₂`. -/
def Vertex.Classify.fromInChild (a : α) (cs : List (Planar α))
    {vl : VertexList cs} (T₂ : Planar α) :
    VertexList.Classify vl T₂ → Vertex.Classify (Vertex.inChild a cs vl) T₂
  | .preserved vl' h =>
      .preserved (Vertex.inChild a cs vl')
        (by intro heq; cases heq; exact h rfl)
  | .sourceSelf  => .sourceSelf
  | .lifted g    => .lifted g

/-! ### `toClassify`: classify a vertex of `insertAt e T₂` -/

mutual
/-- Classify a vertex of `insertAt e T₂` into one of the 3 classes. -/
def Vertex.toClassify : ∀ {T : Planar α} (e : Vertex T) (T₂ : Planar α),
    Vertex (insertAt e T₂) → Vertex.Classify e T₂
  | _, .root a cs,        _,  .root _ _ => .sourceSelf
  | _, .root a cs,        _,  .inChild _ _ (.head _ _ g) => .lifted g
  | _, .root a cs,        _,  .inChild _ _ (.tail _ _ vl) =>
      .preserved (.inChild a cs vl) (by intro h; cases h)
  | _, .inChild a cs vl,  _,  .root _ _ =>
      .preserved (.root a cs) (by intro h; cases h)
  | _, .inChild a cs vl,  T₂, .inChild _ _ vl' =>
      Vertex.Classify.fromInChild a cs T₂ (VertexList.toClassify vl T₂ vl')
/-- Classify an entry of `insertAtList vl T₂` into one of the 3 classes. -/
def VertexList.toClassify : ∀ {cs : List (Planar α)}
      (vl : VertexList cs) (T₂ : Planar α),
    VertexList (insertAtList vl T₂) → VertexList.Classify vl T₂
  | _, .head c cs v,   T₂, .head _ _ v' =>
      VertexList.Classify.fromHead T₂ (Vertex.toClassify v T₂ v')
  | _, .head c cs v,   _,  .tail _ _ vl' =>
      .preserved (.tail c cs vl') (by intro h; cases h)
  | _, .tail c cs vl,  _,  .head _ _ v' =>
      .preserved (.head c cs v') (by intro h; cases h)
  | _, .tail c cs vl,  T₂, .tail _ _ vl' =>
      VertexList.Classify.fromTail T₂ (VertexList.toClassify vl T₂ vl')
end

/-! ### Round-trip: `fromClassify ∘ toClassify = id` -/

mutual
theorem Vertex.fromClassify_toClassify : ∀ {T : Planar α} (e : Vertex T)
      (T₂ : Planar α) (f : Vertex (insertAt e T₂)),
    Vertex.fromClassify (Vertex.toClassify e T₂ f) = f
  | _, .root a cs,        T₂, .root _ _ => rfl
  | _, .root a cs,        T₂, .inChild _ _ (.head _ _ g) => rfl
  | _, .root a cs,        T₂, .inChild _ _ (.tail _ _ vl) => rfl
  | _, .inChild a cs vl,  T₂, .root _ _ => rfl
  | _, .inChild a cs vl,  T₂, .inChild _ _ vl' => by
    have ih := VertexList.fromClassify_toClassify vl T₂ vl'
    show Vertex.fromClassify
            (Vertex.Classify.fromInChild a cs T₂
              (VertexList.toClassify vl T₂ vl')) = _
    cases hC : VertexList.toClassify vl T₂ vl' with
    | preserved g hg =>
      rw [hC] at ih
      show Vertex.inChild _ _ (VertexList.preserveOf vl g hg T₂) = _
      rw [show VertexList.preserveOf vl g hg T₂ = vl' from ih]
    | sourceSelf =>
      rw [hC] at ih
      show Vertex.inChild _ _ (VertexList.sourceSelf vl T₂) = _
      rw [show VertexList.sourceSelf vl T₂ = vl' from ih]
    | lifted g =>
      rw [hC] at ih
      show Vertex.inChild _ _ (VertexList.lift vl T₂ g) = _
      rw [show VertexList.lift vl T₂ g = vl' from ih]
theorem VertexList.fromClassify_toClassify : ∀ {cs : List (Planar α)}
      (vl : VertexList cs) (T₂ : Planar α)
      (vl' : VertexList (insertAtList vl T₂)),
    VertexList.fromClassify (VertexList.toClassify vl T₂ vl') = vl'
  | _, .head c cs v,   T₂, .head _ _ v' => by
    have ih := Vertex.fromClassify_toClassify v T₂ v'
    show VertexList.fromClassify
            (VertexList.Classify.fromHead T₂
              (Vertex.toClassify v T₂ v')) = _
    cases hC : Vertex.toClassify v T₂ v' with
    | preserved g hg =>
      rw [hC] at ih
      show VertexList.head _ _ (Vertex.preserveOf v g hg T₂) = _
      rw [show Vertex.preserveOf v g hg T₂ = v' from ih]
    | sourceSelf =>
      rw [hC] at ih
      show VertexList.head _ _ (Vertex.sourceSelf v T₂) = _
      rw [show Vertex.sourceSelf v T₂ = v' from ih]
    | lifted g =>
      rw [hC] at ih
      show VertexList.head _ _ (Vertex.lift v T₂ g) = _
      rw [show Vertex.lift v T₂ g = v' from ih]
  | _, .head c cs v,   T₂, .tail _ _ vl' => rfl
  | _, .tail c cs vl,  T₂, .head _ _ v' => rfl
  | _, .tail c cs vl,  T₂, .tail _ _ vl' => by
    have ih := VertexList.fromClassify_toClassify vl T₂ vl'
    show VertexList.fromClassify
            (VertexList.Classify.fromTail T₂
              (VertexList.toClassify vl T₂ vl')) = _
    cases hC : VertexList.toClassify vl T₂ vl' with
    | preserved g hg =>
      rw [hC] at ih
      show VertexList.tail _ _ (VertexList.preserveOf vl g hg T₂) = _
      rw [show VertexList.preserveOf vl g hg T₂ = vl' from ih]
    | sourceSelf =>
      rw [hC] at ih
      show VertexList.tail _ _ (VertexList.sourceSelf vl T₂) = _
      rw [show VertexList.sourceSelf vl T₂ = vl' from ih]
    | lifted g =>
      rw [hC] at ih
      show VertexList.tail _ _ (VertexList.lift vl T₂ g) = _
      rw [show VertexList.lift vl T₂ g = vl' from ih]
end

/-! ### Round-trip: `toClassify ∘ fromClassify = id` -/

mutual
theorem Vertex.toClassify_preserved : ∀ {T : Planar α} (e f : Vertex T)
      (h : f ≠ e) (T₂ : Planar α),
    Vertex.toClassify e T₂ (Vertex.preserveOf e f h T₂) =
      .preserved f h
  | _, .root _ _,         .root _ _,         h, _  => absurd rfl h
  | _, .root a cs,        .inChild _ _ vl,   _, _  => rfl
  | _, .inChild a cs vl,  .root _ _,         _, _  => rfl
  | _, .inChild a cs vl₁, .inChild _ _ vl₂,  h, T₂ => by
    show Vertex.Classify.fromInChild a cs T₂
            (VertexList.toClassify vl₁ T₂
              (VertexList.preserveOf vl₁ vl₂ _ T₂)) = _
    rw [VertexList.toClassify_preserved vl₁ vl₂
          (fun heq => h (by rw [heq])) T₂]
    rfl
theorem VertexList.toClassify_preserved : ∀ {cs : List (Planar α)}
      (vl₁ vl₂ : VertexList cs) (h : vl₂ ≠ vl₁) (T₂ : Planar α),
    VertexList.toClassify vl₁ T₂ (VertexList.preserveOf vl₁ vl₂ h T₂) =
      .preserved vl₂ h
  | _, .head c cs v₁,   .head _ _ v₂,    h, T₂ => by
    show VertexList.Classify.fromHead T₂
            (Vertex.toClassify v₁ T₂
              (Vertex.preserveOf v₁ v₂ _ T₂)) = _
    rw [Vertex.toClassify_preserved v₁ v₂
          (fun heq => h (by rw [heq])) T₂]
    rfl
  | _, .head _ _ _,     .tail _ _ _,     _, _  => rfl
  | _, .tail _ _ _,     .head _ _ _,     _, _  => rfl
  | _, .tail c cs vl₁,  .tail _ _ vl₂,   h, T₂ => by
    show VertexList.Classify.fromTail T₂
            (VertexList.toClassify vl₁ T₂
              (VertexList.preserveOf vl₁ vl₂ _ T₂)) = _
    rw [VertexList.toClassify_preserved vl₁ vl₂
          (fun heq => h (by rw [heq])) T₂]
    rfl
end

mutual
theorem Vertex.toClassify_sourceSelf : ∀ {T : Planar α} (e : Vertex T)
      (T₂ : Planar α),
    Vertex.toClassify e T₂ (Vertex.sourceSelf e T₂) = .sourceSelf
  | _, .root _ _,        _ => rfl
  | _, .inChild a cs vl, T₂ => by
    show Vertex.Classify.fromInChild a cs T₂
            (VertexList.toClassify vl T₂ (VertexList.sourceSelf vl T₂)) = _
    rw [VertexList.toClassify_sourceSelf vl T₂]
    rfl
theorem VertexList.toClassify_sourceSelf : ∀ {cs : List (Planar α)}
      (vl : VertexList cs) (T₂ : Planar α),
    VertexList.toClassify vl T₂ (VertexList.sourceSelf vl T₂) =
      .sourceSelf
  | _, .head c cs v,   T₂ => by
    show VertexList.Classify.fromHead T₂
            (Vertex.toClassify v T₂ (Vertex.sourceSelf v T₂)) = _
    rw [Vertex.toClassify_sourceSelf v T₂]
    rfl
  | _, .tail c cs vl,  T₂ => by
    show VertexList.Classify.fromTail T₂
            (VertexList.toClassify vl T₂ (VertexList.sourceSelf vl T₂)) = _
    rw [VertexList.toClassify_sourceSelf vl T₂]
    rfl
end

mutual
theorem Vertex.toClassify_lift : ∀ {T : Planar α} (e : Vertex T)
      (T₂ : Planar α) (g : Vertex T₂),
    Vertex.toClassify e T₂ (Vertex.lift e T₂ g) = .lifted g
  | _, .root _ _,        _,  _ => rfl
  | _, .inChild a cs vl, T₂, g => by
    show Vertex.Classify.fromInChild a cs T₂
            (VertexList.toClassify vl T₂ (VertexList.lift vl T₂ g)) = _
    rw [VertexList.toClassify_lift vl T₂ g]
    rfl
theorem VertexList.toClassify_lift : ∀ {cs : List (Planar α)}
      (vl : VertexList cs) (T₂ : Planar α) (g : Vertex T₂),
    VertexList.toClassify vl T₂ (VertexList.lift vl T₂ g) = .lifted g
  | _, .head c cs v,   T₂, g => by
    show VertexList.Classify.fromHead T₂
            (Vertex.toClassify v T₂ (Vertex.lift v T₂ g)) = _
    rw [Vertex.toClassify_lift v T₂ g]
    rfl
  | _, .tail c cs vl,  T₂, g => by
    show VertexList.Classify.fromTail T₂
            (VertexList.toClassify vl T₂ (VertexList.lift vl T₂ g)) = _
    rw [VertexList.toClassify_lift vl T₂ g]
    rfl
end

/-- `toClassify ∘ fromClassify = id`. -/
theorem Vertex.toClassify_fromClassify {T : Planar α} (e : Vertex T)
    (T₂ : Planar α) (c : Vertex.Classify e T₂) :
    Vertex.toClassify e T₂ (Vertex.fromClassify c) = c := by
  cases c with
  | preserved f h => exact Vertex.toClassify_preserved e f h T₂
  | sourceSelf    => exact Vertex.toClassify_sourceSelf e T₂
  | lifted g      => exact Vertex.toClassify_lift e T₂ g

/-- The headline `Equiv` between `Vertex (insertAt e T₂)` and the 3-class
    decomposition `Vertex.Classify e T₂`. -/
def Vertex.classifyEquiv {T : Planar α} (e : Vertex T) (T₂ : Planar α) :
    Vertex (insertAt e T₂) ≃ Vertex.Classify e T₂ where
  toFun := Vertex.toClassify e T₂
  invFun := Vertex.fromClassify
  left_inv f := Vertex.fromClassify_toClassify e T₂ f
  right_inv c := Vertex.toClassify_fromClassify e T₂ c

/-! ## §10: Commutativity + lifted-equals-nested

The substrate for the pre-Lie identity (R.3d):

- `insertAt_commute_diff`: inserting `T₂` at `e` and `T₃` at `f`
  commutes when `e ≠ f`. The "preserved" class of the §9 decomposition
  carries the bookkeeping.
- `insertAt_lift_eq_nested`: inserting `T₃` at a lifted vertex of `T₂`
  equals first inserting `T₃` at `g` in `T₂`, then inserting the
  resulting tree at `e` in `T`. The "lifted" class of §9.
-/

/-! ### Commutativity: insertions at different vertices commute -/

mutual
/-- Inserting `T₂` at `e` then `T₃` at the `f`-image, equals inserting
    `T₃` at `f` then `T₂` at the `e`-image (both produce the same tree).
    The 4-case match on `(e, f)` mirrors `preserveOf`'s recursion. -/
theorem insertAt_commute_diff : ∀ {T : Planar α} (e f : Vertex T)
      (h : f ≠ e) (T₂ T₃ : Planar α),
    insertAt (Vertex.preserveOf e f h T₂) T₃
      = insertAt (Vertex.preserveOf f e h.symm T₃) T₂
  | _, .root _ _,         .root _ _,         h, _,  _  => absurd rfl h
  | _, .root a cs,        .inChild _ _ vl,   _, T₂, T₃ => by
    -- preserveOf root (inChild vl) T₂ = inChild a (T₂ :: cs) (.tail T₂ cs vl)
    -- preserveOf (inChild vl) root T₃ = root a (insertAtList vl T₃)
    -- Both insertAt sides reduce to `node a (T₂ :: insertAtList vl T₃)`.
    show Planar.node a (T₂ :: insertAtList vl T₃)
        = Planar.node a (T₂ :: insertAtList vl T₃)
    rfl
  | _, .inChild a cs vl,  .root _ _,         _, T₂, T₃ => by
    show Planar.node a (T₃ :: insertAtList vl T₂)
        = Planar.node a (T₃ :: insertAtList vl T₂)
    rfl
  | _, .inChild a cs vl₁, .inChild _ _ vl₂,  h, T₂, T₃ => by
    show Planar.node a (insertAtList (VertexList.preserveOf vl₁ vl₂ _ T₂) T₃)
        = Planar.node a (insertAtList (VertexList.preserveOf vl₂ vl₁ _ T₃) T₂)
    congr 1
    exact insertAtList_commute_diff vl₁ vl₂
            (fun heq => h (by rw [heq])) T₂ T₃
/-- Sibling on `VertexList`: insertions at different children commute. -/
theorem insertAtList_commute_diff : ∀ {cs : List (Planar α)}
      (vl₁ vl₂ : VertexList cs) (h : vl₂ ≠ vl₁) (T₂ T₃ : Planar α),
    insertAtList (VertexList.preserveOf vl₁ vl₂ h T₂) T₃
      = insertAtList (VertexList.preserveOf vl₂ vl₁ h.symm T₃) T₂
  | _, .head c cs v₁,   .head _ _ v₂,    h, T₂, T₃ => by
    show insertAt (Vertex.preserveOf v₁ v₂ _ T₂) T₃ :: cs
        = insertAt (Vertex.preserveOf v₂ v₁ _ T₃) T₂ :: cs
    congr 1
    exact insertAt_commute_diff v₁ v₂
            (fun heq => h (by rw [heq])) T₂ T₃
  | _, .head c cs v₁,   .tail _ _ vl₂,   _, T₂, T₃ => by
    show insertAt v₁ T₂ :: insertAtList vl₂ T₃
        = insertAt v₁ T₂ :: insertAtList vl₂ T₃
    rfl
  | _, .tail c cs vl₁,  .head _ _ v₂,    _, T₂, T₃ => by
    show insertAt v₂ T₃ :: insertAtList vl₁ T₂
        = insertAt v₂ T₃ :: insertAtList vl₁ T₂
    rfl
  | _, .tail c cs vl₁,  .tail _ _ vl₂,   h, T₂, T₃ => by
    show c :: insertAtList (VertexList.preserveOf vl₁ vl₂ _ T₂) T₃
        = c :: insertAtList (VertexList.preserveOf vl₂ vl₁ _ T₃) T₂
    congr 1
    exact insertAtList_commute_diff vl₁ vl₂
            (fun heq => h (by rw [heq])) T₂ T₃
end

/-! ### Lifted-equals-nested: insertion at a lifted vertex of `T₂` -/

mutual
/-- **Lifted-equals-nested**: inserting `T₃` at a lifted vertex of `T₂`
    (lifted into `insertAt e T₂`) factors as `insertAt e (insertAt g T₃)`. -/
theorem insertAt_lift_eq_nested : ∀ {T : Planar α} (e : Vertex T)
      (T₂ T₃ : Planar α) (g : Vertex T₂),
    insertAt (Vertex.lift e T₂ g) T₃ = insertAt e (insertAt g T₃)
  | _, .root a cs,        T₂, T₃, g => by
    -- lift (root a cs) T₂ g = inChild a (T₂ :: cs) (.head T₂ cs g)
    -- insertAt (inChild a (T₂ :: cs) (.head T₂ cs g)) T₃
    --   = node a (insertAtList (.head T₂ cs g) T₃)
    --   = node a (insertAt g T₃ :: cs)
    -- insertAt (root a cs) (insertAt g T₃) = node a (insertAt g T₃ :: cs)
    show Planar.node a (insertAt g T₃ :: cs)
        = Planar.node a (insertAt g T₃ :: cs)
    rfl
  | _, .inChild a cs vl,  T₂, T₃, g => by
    show Planar.node a (insertAtList (VertexList.lift vl T₂ g) T₃)
        = Planar.node a (insertAtList vl (insertAt g T₃))
    congr 1
    exact insertAtList_lift_eq_nested vl T₂ T₃ g
/-- Sibling on `VertexList`. -/
theorem insertAtList_lift_eq_nested : ∀ {cs : List (Planar α)}
      (vl : VertexList cs) (T₂ T₃ : Planar α) (g : Vertex T₂),
    insertAtList (VertexList.lift vl T₂ g) T₃
      = insertAtList vl (insertAt g T₃)
  | _, .head c cs v,   T₂, T₃, g => by
    show insertAt (Vertex.lift v T₂ g) T₃ :: cs
        = insertAt v (insertAt g T₃) :: cs
    congr 1
    exact insertAt_lift_eq_nested v T₂ T₃ g
  | _, .tail c cs vl,  T₂, T₃, g => by
    show c :: insertAtList (VertexList.lift vl T₂ g) T₃
        = c :: insertAtList vl (insertAt g T₃)
    congr 1
    exact insertAtList_lift_eq_nested vl T₂ T₃ g
end

/-! ## §11: Multiset decomposition of `vertices (insertAt v t₂)`

The 3-class bijection `Vertex.classifyEquiv` (§9) gives a clean
combinatorial counting principle: the vertices of `insertAt v t₂`
partition into preserved + sourceSelf + lifted. Realized at the
multiset level here as a List/Multiset equality, this is the
substrate behind the pre-Lie identity proof in `Algebra.lean` (R.3d):
double-grafting `(t₁ ◁ t₂) ◁ t₃` decomposes into a "lifted" block
(matching `t₁ ◁ (t₂ ◁ t₃)`), a "preserved" block (a double-graft
into `t₁` at distinct vertices, symmetric in t₂ ↔ t₃), and a
"sourceSelf" block (a double-graft at the same vertex of t₁,
Nonplanar-equal under t₂ ↔ t₃ via `swapAtRoot`).

The use of `Vertex.preserve?` (Option-valued) handles the diagonal
without a `DecidableEq Vertex T` instance: `preserve? v w t₂ = none`
exactly when `w = v`, and `Multiset.filterMap` collects only the
`some` cases. -/

mutual
/-- The multiset decomposition: `vertices (insertAt v t₂)` equals the
    sum of the preserved (one per `w ∈ vertices T` with `w ≠ v`),
    sourceSelf (a singleton), and lifted (one per `g ∈ vertices t₂`)
    sub-multisets. Mutually proved with the `VertexList` version. -/
private theorem vertices_insertAt_decomp_aux : ∀ {T : Planar α}
      (v : Vertex T) (t₂ : Planar α),
    ((vertices (insertAt v t₂) : List _) : Multiset (Vertex (insertAt v t₂))) =
      ((vertices T : Multiset _).filterMap (fun w => Vertex.preserve? v w t₂))
      + ({Vertex.sourceSelf v t₂} : Multiset _)
      + ((vertices t₂ : Multiset _).map (Vertex.lift v t₂))
  | _, .root a cs, t₂ => by
    -- v = root a cs, T = node a cs, insertAt v t₂ = node a (t₂ :: cs).
    -- LHS unfolds via vertices_node + verticesList_cons + List.map_append + List.map_map + coe.
    -- RHS: filterMap on (root :: ...) — head matches preserve?_self (none),
    --      tail collapses via filterMap_map + (some ∘ f) → map f.
    dsimp only [insertAt_root, Vertex.sourceSelf, Vertex.lift]
    rw [vertices_node, verticesList_cons, List.map_append, List.map_map, List.map_map,
        (Multiset.cons_coe (Vertex.root a (t₂ :: cs))
          (List.map (Vertex.inChild a (t₂ :: cs) ∘ VertexList.head t₂ cs) (vertices t₂) ++
            List.map (Vertex.inChild a (t₂ :: cs) ∘ VertexList.tail t₂ cs) (verticesList cs))).symm,
        (Multiset.coe_add
          (List.map (Vertex.inChild a (t₂ :: cs) ∘ VertexList.head t₂ cs) (vertices t₂))
          (List.map (Vertex.inChild a (t₂ :: cs) ∘ VertexList.tail t₂ cs) (verticesList cs))).symm,
        ← Multiset.map_coe (Vertex.inChild a (t₂ :: cs) ∘ VertexList.head t₂ cs) (vertices t₂),
        ← Multiset.map_coe (Vertex.inChild a (t₂ :: cs) ∘ VertexList.tail t₂ cs) (verticesList cs)]
    rw [show ((vertices (Planar.node a cs) : List _) :
              Multiset (Vertex (Planar.node a cs))) =
              Vertex.root a cs ::ₘ (((verticesList cs).map (Vertex.inChild a cs) : List _) :
                  Multiset (Vertex (Planar.node a cs))) from rfl,
        Multiset.filterMap_cons_none _ _ (Vertex.preserve?_self _ _),
        ← Multiset.map_coe (Vertex.inChild a cs) (verticesList cs),
        Multiset.filterMap_map]
    simp only [Function.comp_def]
    -- The composition `(fun w => preserve? (root) (inChild w) t₂)` collapses to `some ∘ ...`,
    -- but rw struggles on the implicit β arg (`Vertex (insertAt root t₂)` vs `Vertex (node a (t₂::cs))`).
    -- Workaround: a universal hfmA lemma with explicit @β ascription.
    have hfmA :
        ∀ M : Multiset (VertexList cs),
        @Multiset.filterMap (VertexList cs) (Vertex (Planar.node a (t₂ :: cs)))
          (fun x : VertexList cs =>
            (Vertex.root a cs).preserve? (Vertex.inChild a cs x) t₂) M =
        @Multiset.map (VertexList cs) (Vertex (Planar.node a (t₂ :: cs)))
          (fun x : VertexList cs => Vertex.inChild a (t₂ :: cs) (VertexList.tail t₂ cs x)) M := by
      intro M
      have h : (fun x : VertexList cs =>
                  (Vertex.root a cs).preserve? (Vertex.inChild a cs x) t₂) =
                some ∘ (fun x : VertexList cs =>
                          Vertex.inChild a (t₂ :: cs) (VertexList.tail t₂ cs x)) := rfl
      rw [h]; exact congr_fun (Multiset.filterMap_eq_map _) M
    rw [hfmA, ← Multiset.singleton_add,
        Multiset.add_comm
          (Multiset.map (fun x => Vertex.inChild a (t₂ :: cs) (VertexList.head t₂ cs x))
            ((↑(vertices t₂) : Multiset (Vertex t₂))))
          (Multiset.map (fun x => Vertex.inChild a (t₂ :: cs) (VertexList.tail t₂ cs x))
            ((↑(verticesList cs) : Multiset (VertexList cs)))),
        ← Multiset.add_assoc,
        Multiset.add_comm
          ({Vertex.root a (t₂ :: cs)} : Multiset (Vertex (Planar.node a (t₂ :: cs))))
          (Multiset.map (fun x => Vertex.inChild a (t₂ :: cs) (VertexList.tail t₂ cs x))
            ((↑(verticesList cs) : Multiset (VertexList cs))))]
    rfl
  | _, .inChild a cs vl, t₂ => by
    -- v = inChild a cs vl, T = node a cs. IH on vl (verticesList).
    have ih := verticesList_insertAtList_decomp_aux vl t₂
    dsimp only [insertAt_inChild, Vertex.sourceSelf, Vertex.lift]
    rw [vertices_node,
        (Multiset.cons_coe (Vertex.root a (insertAtList vl t₂))
          (List.map (Vertex.inChild a (insertAtList vl t₂))
            (verticesList (insertAtList vl t₂)))).symm,
        ← Multiset.map_coe (Vertex.inChild a (insertAtList vl t₂))
            (verticesList (insertAtList vl t₂))]
    -- Apply IH on vl.
    rw [ih, Multiset.map_add, Multiset.map_add, Multiset.map_singleton]
    -- RHS: use universal cons_some + map_filterMap helpers with explicit β-ascriptions
    -- to bypass the dependent-type pitfall.
    have hcons :
        ∀ M : Multiset (Vertex (Planar.node a cs)),
        @Multiset.filterMap (Vertex (Planar.node a cs))
            (Vertex (Planar.node a (insertAtList vl t₂)))
          (fun w => (Vertex.inChild a cs vl).preserve? w t₂)
          (Vertex.root a cs ::ₘ M) =
        Vertex.root a (insertAtList vl t₂) ::ₘ
          @Multiset.filterMap (Vertex (Planar.node a cs))
              (Vertex (Planar.node a (insertAtList vl t₂)))
            (fun w => (Vertex.inChild a cs vl).preserve? w t₂) M := by
      intro M
      exact Multiset.filterMap_cons_some
        (fun w => (Vertex.inChild a cs vl).preserve? w t₂)
        (Vertex.root a cs)
        M (b := Vertex.root a (insertAtList vl t₂)) rfl
    rw [show ((vertices (Planar.node a cs) : List _) :
              Multiset (Vertex (Planar.node a cs))) =
              Vertex.root a cs ::ₘ (((verticesList cs).map (Vertex.inChild a cs) : List _) :
                  Multiset (Vertex (Planar.node a cs))) from rfl,
        hcons,
        ← Multiset.map_coe (Vertex.inChild a cs) (verticesList cs),
        Multiset.filterMap_map]
    simp only [Function.comp_def]
    -- Inner filterMap collapses via Multiset.map_filterMap.
    have hfm :
        ∀ M : Multiset (VertexList cs),
        @Multiset.filterMap (VertexList cs) (Vertex (Planar.node a (insertAtList vl t₂)))
          (fun x : VertexList cs =>
            (Vertex.inChild a cs vl).preserve? (Vertex.inChild a cs x) t₂) M =
        @Multiset.map (VertexList (insertAtList vl t₂))
            (Vertex (Planar.node a (insertAtList vl t₂)))
          (Vertex.inChild a (insertAtList vl t₂))
          (M.filterMap (fun x : VertexList cs => VertexList.preserve? vl x t₂)) := by
      intro M
      have h : (fun x : VertexList cs =>
                  (Vertex.inChild a cs vl).preserve? (Vertex.inChild a cs x) t₂) =
                (fun x : VertexList cs =>
                  (VertexList.preserve? vl x t₂).map (Vertex.inChild a (insertAtList vl t₂))) := rfl
      rw [h]
      exact (Multiset.map_filterMap _ _ M).symm
    rw [hfm]
    simp only [Multiset.map_map, Function.comp_def]
    -- Convert LHS root cons to singleton, then reassociate for matching.
    rw [show (Vertex.root a (insertAtList vl t₂) ::ₘ
                (Multiset.map (Vertex.inChild a (insertAtList vl t₂))
                  (Multiset.filterMap (fun vl' => vl.preserve? vl' t₂)
                    ((↑(verticesList cs) : Multiset (VertexList cs)))) +
                 ({Vertex.inChild a (insertAtList vl t₂) (vl.sourceSelf t₂)} :
                    Multiset (Vertex (Planar.node a (insertAtList vl t₂)))) +
                 Multiset.map (fun x => Vertex.inChild a (insertAtList vl t₂) (vl.lift t₂ x))
                    ((↑(vertices t₂) : Multiset (Vertex t₂))))) =
              ({Vertex.root a (insertAtList vl t₂)} :
                Multiset (Vertex (Planar.node a (insertAtList vl t₂)))) +
              (Multiset.map (Vertex.inChild a (insertAtList vl t₂))
                (Multiset.filterMap (fun vl' => vl.preserve? vl' t₂)
                  ((↑(verticesList cs) : Multiset (VertexList cs)))) +
              ({Vertex.inChild a (insertAtList vl t₂) (vl.sourceSelf t₂)} :
                Multiset (Vertex (Planar.node a (insertAtList vl t₂)))) +
              Multiset.map (fun x => Vertex.inChild a (insertAtList vl t₂) (vl.lift t₂ x))
                ((↑(vertices t₂) : Multiset (Vertex t₂)))) from
            (Multiset.singleton_add _ _).symm,
        ← Multiset.add_assoc,
        ← Multiset.add_assoc,
        Multiset.singleton_add]
    rfl
/-- Sibling on `VertexList`: same decomposition principle for vertex
    enumerations of an inserted children-list. Mutually proved with the
    `Vertex` version. -/
private theorem verticesList_insertAtList_decomp_aux : ∀ {cs : List (Planar α)}
      (vl : VertexList cs) (t₂ : Planar α),
    ((verticesList (insertAtList vl t₂) : List _) :
        Multiset (VertexList (insertAtList vl t₂))) =
      ((verticesList cs : Multiset _).filterMap
        (fun vl' => VertexList.preserve? vl vl' t₂))
      + ({VertexList.sourceSelf vl t₂} : Multiset _)
      + ((vertices t₂ : Multiset _).map (VertexList.lift vl t₂))
  | _, .head c cs' v, t₂ => by
    -- vl = .head c cs' v; cs = c :: cs'. IH on v.
    have ih := vertices_insertAt_decomp_aux v t₂
    dsimp only [insertAtList_head, VertexList.sourceSelf, VertexList.lift]
    rw [verticesList_cons,
        (Multiset.coe_add
          (List.map (VertexList.head (insertAt v t₂) cs') (vertices (insertAt v t₂)))
          (List.map (VertexList.tail (insertAt v t₂) cs') (verticesList cs'))).symm,
        ← Multiset.map_coe (VertexList.head (insertAt v t₂) cs') (vertices (insertAt v t₂)),
        ← Multiset.map_coe (VertexList.tail (insertAt v t₂) cs') (verticesList cs')]
    -- Apply IH on v: ↑(vertices (insertAt v t₂)) = preserved-v + {sourceSelf v t₂} + lifted-from-t₂.
    rw [ih, Multiset.map_add, Multiset.map_add, Multiset.map_singleton]
    -- RHS: verticesList (c :: cs') decomposes structurally; filterMap on each branch.
    rw [show ((verticesList (c :: cs') : List _) :
              Multiset (VertexList (c :: cs'))) =
              (((vertices c).map (VertexList.head c cs') ++
                (verticesList cs').map (VertexList.tail c cs') : List _) :
                Multiset (VertexList (c :: cs'))) from rfl,
        ← Multiset.coe_add ((vertices c).map (VertexList.head c cs'))
          ((verticesList cs').map (VertexList.tail c cs')),
        ← Multiset.map_coe (VertexList.head c cs') (vertices c),
        ← Multiset.map_coe (VertexList.tail c cs') (verticesList cs'),
        Multiset.filterMap_add,
        Multiset.filterMap_map, Multiset.filterMap_map]
    simp only [Function.comp_def]
    -- Tail-branch collapse: filterMap (some ∘ tail) → map tail.
    have hfmT :
        ∀ M : Multiset (VertexList cs'),
        @Multiset.filterMap (VertexList cs') (VertexList (insertAt v t₂ :: cs'))
          (fun x : VertexList cs' =>
            (VertexList.head c cs' v).preserve? (VertexList.tail c cs' x) t₂) M =
        @Multiset.map (VertexList cs') (VertexList (insertAt v t₂ :: cs'))
          (fun x : VertexList cs' => VertexList.tail (insertAt v t₂) cs' x) M := by
      intro M
      have h : (fun x : VertexList cs' =>
                  (VertexList.head c cs' v).preserve? (VertexList.tail c cs' x) t₂) =
                some ∘ (fun x : VertexList cs' => VertexList.tail (insertAt v t₂) cs' x) := rfl
      rw [h]; exact congr_fun (Multiset.filterMap_eq_map _) M
    -- Head-branch collapse: filterMap (fun v' => (preserve? v v' t₂).map (head ...)) →
    -- map (head ...) of (filterMap (preserve? v · t₂)). Use Multiset.map_filterMap (in reverse).
    have hfmH :
        ∀ M : Multiset (Vertex c),
        @Multiset.filterMap (Vertex c) (VertexList (insertAt v t₂ :: cs'))
          (fun x : Vertex c =>
            (VertexList.head c cs' v).preserve? (VertexList.head c cs' x) t₂) M =
        @Multiset.map (Vertex (insertAt v t₂)) (VertexList (insertAt v t₂ :: cs'))
          (VertexList.head (insertAt v t₂) cs')
          (M.filterMap (fun x : Vertex c => Vertex.preserve? v x t₂)) := by
      intro M
      have h : (fun x : Vertex c =>
                  (VertexList.head c cs' v).preserve? (VertexList.head c cs' x) t₂) =
                (fun x : Vertex c =>
                  (Vertex.preserve? v x t₂).map (VertexList.head (insertAt v t₂) cs')) := rfl
      rw [h]
      exact (Multiset.map_filterMap _ _ M).symm
    rw [hfmH, hfmT]
    -- Compose maps in LHS to single-map form, normalize tail-η.
    simp only [Multiset.map_map, Function.comp_def]
    -- LHS: A + {S} + B + C; RHS: A + C + {S} + B. Use Multiset-specific AC lemmas.
    rw [Multiset.add_assoc
          (Multiset.map (VertexList.head (insertAt v t₂) cs')
            ((↑(vertices c) : Multiset (Vertex c)).filterMap
              (fun w => Vertex.preserve? v w t₂)))
          ({VertexList.head (insertAt v t₂) cs' (Vertex.sourceSelf v t₂)} :
            Multiset (VertexList (insertAt v t₂ :: cs')))
          (Multiset.map
            (fun x : Vertex t₂ => VertexList.head (insertAt v t₂) cs' (Vertex.lift v t₂ x))
            (↑(vertices t₂) : Multiset (Vertex t₂))),
        Multiset.add_comm
          ({VertexList.head (insertAt v t₂) cs' (Vertex.sourceSelf v t₂)} :
            Multiset (VertexList (insertAt v t₂ :: cs')))
          (Multiset.map
            (fun x : Vertex t₂ => VertexList.head (insertAt v t₂) cs' (Vertex.lift v t₂ x))
            (↑(vertices t₂) : Multiset (Vertex t₂))),
        ← Multiset.add_assoc]
    -- Now: A + B + {S} + C. Move C between B and {S}: A + B + C + {S} via swap (S, C) at end?
    -- Wait, we have (A + B) + {S} + C; we want (A + B) + C + {S}. Use add_right_comm... no, generic.
    -- Use Multiset.add_assoc to (A+B) + ({S} + C); add_comm {S} C; ← add_assoc.
    rw [Multiset.add_assoc
          ((Multiset.map (VertexList.head (insertAt v t₂) cs')
            ((↑(vertices c) : Multiset (Vertex c)).filterMap
              (fun w => Vertex.preserve? v w t₂))) +
            Multiset.map
              (fun x : Vertex t₂ => VertexList.head (insertAt v t₂) cs' (Vertex.lift v t₂ x))
              (↑(vertices t₂) : Multiset (Vertex t₂)))
          ({VertexList.head (insertAt v t₂) cs' (Vertex.sourceSelf v t₂)} :
            Multiset (VertexList (insertAt v t₂ :: cs')))
          (Multiset.map (VertexList.tail (insertAt v t₂) cs')
            (↑(verticesList cs') : Multiset (VertexList cs'))),
        Multiset.add_comm
          ({VertexList.head (insertAt v t₂) cs' (Vertex.sourceSelf v t₂)} :
            Multiset (VertexList (insertAt v t₂ :: cs')))
          (Multiset.map (VertexList.tail (insertAt v t₂) cs')
            (↑(verticesList cs') : Multiset (VertexList cs')))]
    -- Now: (A + B) + C + {S}. RHS = A + C + {S} + B = ((A + C) + {S}) + B.
    -- Need to move B from second to last. Use ← add_assoc to get (A + B + C) + {S},
    -- then swap B and C in the inner: (A + C + B) + {S} = (A + C) + B + {S}.
    rw [← Multiset.add_assoc,
        Multiset.add_assoc
          (Multiset.map (VertexList.head (insertAt v t₂) cs')
            ((↑(vertices c) : Multiset (Vertex c)).filterMap
              (fun w => Vertex.preserve? v w t₂)))
          (Multiset.map
            (fun x : Vertex t₂ => VertexList.head (insertAt v t₂) cs' (Vertex.lift v t₂ x))
            (↑(vertices t₂) : Multiset (Vertex t₂)))
          (Multiset.map (VertexList.tail (insertAt v t₂) cs')
            (↑(verticesList cs') : Multiset (VertexList cs'))),
        Multiset.add_comm
          (Multiset.map
            (fun x : Vertex t₂ => VertexList.head (insertAt v t₂) cs' (Vertex.lift v t₂ x))
            (↑(vertices t₂) : Multiset (Vertex t₂)))
          (Multiset.map (VertexList.tail (insertAt v t₂) cs')
            (↑(verticesList cs') : Multiset (VertexList cs')))]
    -- Now LHS = ((A + (C + B)) + {S}) = ((A + C + B) + {S}); want ((A + C + {S}) + B).
    -- Use add_right_comm-style: (X + B) + {S} = (X + {S}) + B with X = A + C.
    rw [← Multiset.add_assoc,
        Multiset.add_assoc
          ((Multiset.map (VertexList.head (insertAt v t₂) cs')
            ((↑(vertices c) : Multiset (Vertex c)).filterMap
              (fun w => Vertex.preserve? v w t₂))) +
            Multiset.map (VertexList.tail (insertAt v t₂) cs')
              (↑(verticesList cs') : Multiset (VertexList cs')))
          (Multiset.map
            (fun x : Vertex t₂ => VertexList.head (insertAt v t₂) cs' (Vertex.lift v t₂ x))
            (↑(vertices t₂) : Multiset (Vertex t₂)))
          ({VertexList.head (insertAt v t₂) cs' (Vertex.sourceSelf v t₂)} :
            Multiset (VertexList (insertAt v t₂ :: cs'))),
        Multiset.add_comm
          (Multiset.map
            (fun x : Vertex t₂ => VertexList.head (insertAt v t₂) cs' (Vertex.lift v t₂ x))
            (↑(vertices t₂) : Multiset (Vertex t₂)))
          ({VertexList.head (insertAt v t₂) cs' (Vertex.sourceSelf v t₂)} :
            Multiset (VertexList (insertAt v t₂ :: cs'))),
        ← Multiset.add_assoc]
    rfl
  | _, .tail c cs' vl', t₂ => by
    -- vl = .tail c cs' vl'; cs = c :: cs'. IH on vl' (verticesList recursive).
    have ih := verticesList_insertAtList_decomp_aux vl' t₂
    dsimp only [insertAtList_tail, VertexList.sourceSelf, VertexList.lift]
    rw [verticesList_cons,
        (Multiset.coe_add
          (List.map (VertexList.head c (insertAtList vl' t₂)) (vertices c))
          (List.map (VertexList.tail c (insertAtList vl' t₂))
            (verticesList (insertAtList vl' t₂)))).symm,
        ← Multiset.map_coe (VertexList.head c (insertAtList vl' t₂)) (vertices c),
        ← Multiset.map_coe (VertexList.tail c (insertAtList vl' t₂))
            (verticesList (insertAtList vl' t₂))]
    -- Apply IH on vl'.
    rw [ih, Multiset.map_add, Multiset.map_add, Multiset.map_singleton]
    -- RHS:
    rw [show ((verticesList (c :: cs') : List _) :
              Multiset (VertexList (c :: cs'))) =
              (((vertices c).map (VertexList.head c cs') ++
                (verticesList cs').map (VertexList.tail c cs') : List _) :
                Multiset (VertexList (c :: cs'))) from rfl,
        ← Multiset.coe_add ((vertices c).map (VertexList.head c cs'))
          ((verticesList cs').map (VertexList.tail c cs')),
        ← Multiset.map_coe (VertexList.head c cs') (vertices c),
        ← Multiset.map_coe (VertexList.tail c cs') (verticesList cs'),
        Multiset.filterMap_add,
        Multiset.filterMap_map, Multiset.filterMap_map]
    simp only [Function.comp_def]
    -- Head-of-cs' branch: preserve? (tail c cs' vl') (head c cs' v') t₂ = some (head c (insertAtList vl' t₂) v').
    have hfmH :
        ∀ M : Multiset (Vertex c),
        @Multiset.filterMap (Vertex c) (VertexList (c :: insertAtList vl' t₂))
          (fun x : Vertex c =>
            (VertexList.tail c cs' vl').preserve? (VertexList.head c cs' x) t₂) M =
        @Multiset.map (Vertex c) (VertexList (c :: insertAtList vl' t₂))
          (fun x : Vertex c => VertexList.head c (insertAtList vl' t₂) x) M := by
      intro M
      have h : (fun x : Vertex c =>
                  (VertexList.tail c cs' vl').preserve? (VertexList.head c cs' x) t₂) =
                some ∘ (fun x : Vertex c => VertexList.head c (insertAtList vl' t₂) x) := rfl
      rw [h]; exact congr_fun (Multiset.filterMap_eq_map _) M
    -- Tail-of-cs' branch: preserve? (tail c cs' vl') (tail c cs' vl'') t₂ = (preserve? vl' vl'' t₂).map (tail c ...).
    have hfmT :
        ∀ M : Multiset (VertexList cs'),
        @Multiset.filterMap (VertexList cs') (VertexList (c :: insertAtList vl' t₂))
          (fun x : VertexList cs' =>
            (VertexList.tail c cs' vl').preserve? (VertexList.tail c cs' x) t₂) M =
        @Multiset.map (VertexList (insertAtList vl' t₂)) (VertexList (c :: insertAtList vl' t₂))
          (VertexList.tail c (insertAtList vl' t₂))
          (M.filterMap (fun x : VertexList cs' => VertexList.preserve? vl' x t₂)) := by
      intro M
      have h : (fun x : VertexList cs' =>
                  (VertexList.tail c cs' vl').preserve? (VertexList.tail c cs' x) t₂) =
                (fun x : VertexList cs' =>
                  (VertexList.preserve? vl' x t₂).map
                    (VertexList.tail c (insertAtList vl' t₂))) := rfl
      rw [h]
      exact (Multiset.map_filterMap _ _ M).symm
    rw [hfmH, hfmT]
    simp only [Multiset.map_map, Function.comp_def]
    -- LHS and RHS are EQUAL (4 pieces in the same order, only η-difference on head).
    rw [← Multiset.add_assoc, ← Multiset.add_assoc]
    rfl
end

/-- Public API: the Multiset decomposition of `vertices (insertAt v t₂)`,
    the substrate behind the pre-Lie identity proof in `Algebra.lean`. -/
theorem vertices_insertAt_decomp {T : Planar α} (v : Vertex T) (t₂ : Planar α) :
    ((vertices (insertAt v t₂) : List _) : Multiset (Vertex (insertAt v t₂))) =
      ((vertices T : Multiset _).filterMap (fun w => Vertex.preserve? v w t₂))
      + ({Vertex.sourceSelf v t₂} : Multiset _)
      + ((vertices t₂ : Multiset _).map (Vertex.lift v t₂)) :=
  vertices_insertAt_decomp_aux v t₂

/-! ## §11.5: Preserved-class swap

The (v, w) ↔ (w, v) symmetry for preserved-class double sums. Used by
`assoc_symm_planar` to identify the preserved class of `(t₁ ◁ t₂) ◁ t₃`
with the preserved class of `(t₁ ◁ t₃) ◁ t₂`.

The pointwise bridge is `insertAt_commute_diff`: at distinct vertices
`v ≠ w` of `t₁`, grafting `t₂` at `v` then `t₃` at the `w`-image equals
grafting `t₃` at `w` then `t₂` at the `v`-image. The diagonal `v = w` is
discarded by `preserve?_self = none` on both sides. -/

/-- Preserved-class swap: the double sum
`Σ_v Σ_{w ≠ v} insertAt (preserveOf v w t₂) t₃` (LHS) equals the same
sum with `t₂` and `t₃` swapped (RHS). Proof: Fubini swap (`bind_bind`)
plus pointwise `insertAt_commute_diff`. -/
theorem bind_filterMap_preserve?_swap (t₁ t₂ t₃ : Planar α) :
    Multiset.bind (↑(vertices t₁) : Multiset (Vertex t₁)) (fun v =>
        Multiset.filterMap (fun w =>
          (Vertex.preserve? v w t₂).map (fun pos => insertAt pos t₃))
          (↑(vertices t₁) : Multiset (Vertex t₁)))
    = Multiset.bind (↑(vertices t₁) : Multiset (Vertex t₁)) (fun v =>
        Multiset.filterMap (fun w =>
          (Vertex.preserve? v w t₃).map (fun pos => insertAt pos t₂))
          (↑(vertices t₁) : Multiset (Vertex t₁))) := by
  -- Pointwise: at each (v, w), the LHS Option agrees with the RHS Option
  -- under the (v, w) ↔ (w, v) swap.
  have hpw : ∀ v w : Vertex t₁,
      (Vertex.preserve? v w t₂).map (fun pos => insertAt pos t₃)
      = (Vertex.preserve? w v t₃).map (fun pos => insertAt pos t₂) := by
    intro v w
    by_cases h : w = v
    · subst h
      rw [Vertex.preserve?_self, Vertex.preserve?_self]; rfl
    · rw [Vertex.preserve?_of_ne v w h t₂,
          Vertex.preserve?_of_ne w v (Ne.symm h) t₃]
      simp only [Option.map_some]
      congr 1
      exact insertAt_commute_diff v w h t₂ t₃
  -- Convert both sides to bind-of-bind via filterMap_eq_bind, apply hpw inside
  -- LHS, then use bind_bind for the (v ↔ w) Fubini swap.
  simp_rw [Multiset.filterMap_eq_bind]
  -- LHS = m.bind (fun v => m.bind (fun w => ((preserve? v w t₂).map (insertAt · t₃)
  --                                           |>.map singleton).getD 0))
  -- RHS = m.bind (fun v => m.bind (fun w => ((preserve? v w t₃).map (insertAt · t₂)
  --                                           |>.map singleton).getD 0))
  -- Step 1: pointwise rewrite LHS via hpw to get preserve? in (w, v) form on LHS.
  have step1 : ∀ v w : Vertex t₁,
      (((Vertex.preserve? v w t₂).map (fun pos => insertAt pos t₃)).map
          (fun b : Planar α => ({b} : Multiset (Planar α)))).getD 0
      = (((Vertex.preserve? w v t₃).map (fun pos => insertAt pos t₂)).map
          (fun b : Planar α => ({b} : Multiset (Planar α)))).getD 0 := by
    intros v w; rw [hpw v w]
  rw [show (fun v : Vertex t₁ =>
            (↑(vertices t₁) : Multiset (Vertex t₁)).bind (fun w =>
              (((Vertex.preserve? v w t₂).map (fun pos => insertAt pos t₃)).map
                (fun b : Planar α => ({b} : Multiset (Planar α)))).getD 0)) =
          (fun v =>
            (↑(vertices t₁) : Multiset (Vertex t₁)).bind (fun w =>
              (((Vertex.preserve? w v t₃).map (fun pos => insertAt pos t₂)).map
                (fun b : Planar α => ({b} : Multiset (Planar α)))).getD 0)) from
        funext fun v => Multiset.bind_congr (fun w _ => step1 v w)]
  -- Step 2: bind_bind to swap v ↔ w.
  rw [Multiset.bind_bind]

/-! ## §12: Sanity tests at compile time -/

section Tests

/-- The 3-class equiv exists and has the expected source/target types. -/
example (T : Planar Nat) (e : Vertex T) (T₂ : Planar Nat) :
    Vertex (insertAt e T₂) ≃ Vertex.Classify e T₂ :=
  Vertex.classifyEquiv e T₂

/-- `newGraft` of a leaf produces the expected vertex. -/
example (a b : Nat) :
    Vertex.newGraft (Vertex.root a ([] : List (Planar Nat)))
        (Planar.leaf b) =
      Vertex.inChild a [Planar.leaf b]
        (VertexList.head (Planar.leaf b) [] (Vertex.root b [])) := rfl

end Tests

end Planar

end RootedTree
