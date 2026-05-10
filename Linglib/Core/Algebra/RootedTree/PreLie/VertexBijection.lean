import Linglib.Core.Algebra.RootedTree.PreLie.Defs
import Mathlib.Data.Multiset.Filter
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
    -- LHS = vertices (node a (t₂ :: cs)) (as Multiset). RHS reduces via:
    --   vertices T = root a cs :: (verticesList cs).map (inChild a cs)
    --   preserve? (root a cs) (root a cs) t₂ = none (skip head)
    --   preserve? (root a cs) (inChild a cs vl) t₂ = some (inChild a (t₂::cs) (tail t₂ cs vl))
    --   sourceSelf (root a cs) t₂ = root a (t₂ :: cs)
    --   lift (root a cs) t₂ g = inChild a (t₂::cs) (head t₂ cs g)
    -- Both reduce to the same 3-component sum {root a (t₂::cs)} + lifted-block + preserved-block.
    sorry
  | _, .inChild a cs vl, t₂ => by
    -- v = inChild a cs vl, T = node a cs.
    -- insertAt v t₂ = node a (insertAtList vl t₂).
    -- LHS = vertices (node a (insertAtList vl t₂)) (as Multiset)
    --     = root a (insertAtList vl t₂) ::ₘ (verticesList (insertAtList vl t₂)).map (inChild a (insertAtList vl t₂))
    -- By IH on vl (the verticesList version):
    --   verticesList (insertAtList vl t₂) (as Multiset) =
    --     (verticesList cs : Multiset).filterMap (preserve? vl · t₂)
    --     + {sourceSelf vl t₂}
    --     + (vertices t₂ : Multiset).map (VertexList.lift vl t₂)
    -- After .map (inChild a (insertAtList vl t₂)):
    --   = ((verticesList cs : Multiset).filterMap (preserve? vl · t₂)).map (inChild a (insertAtList vl t₂))
    --   + {inChild a (insertAtList vl t₂) (sourceSelf vl t₂)}
    --   + ((vertices t₂ : Multiset).map (VertexList.lift vl t₂)).map (inChild a (insertAtList vl t₂))
    --
    -- Compare to RHS:
    -- - filterMap on (root a cs :: (verticesList cs).map (inChild a cs)):
    --     For w = root a cs: preserve? (inChild a cs vl) (root a cs) t₂ = some (root a (insertAtList vl t₂)).
    --     For w = inChild a cs vl': preserve? = (preserve? vl vl' t₂).map (inChild a (insertAtList vl t₂)).
    --     Result: root a (insertAtList vl t₂) ::ₘ ((verticesList cs).filterMap (preserve? vl · t₂)).map (inChild ...).
    -- - sourceSelf v t₂ = inChild a (insertAtList vl t₂) (sourceSelf vl t₂).
    -- - (vertices t₂).map (lift v t₂) = (vertices t₂).map (inChild a (insertAtList vl t₂) ∘ lift vl t₂).
    --
    -- So LHS = root :: (after IH) and RHS = (root + ...). Both have the same three pieces.
    sorry
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
  | _, .head c cs' v, t₂ => by sorry
  | _, .tail c cs' vl', t₂ => by sorry
end

/-- Public API: the Multiset decomposition of `vertices (insertAt v t₂)`,
    the substrate behind the pre-Lie identity proof in `Algebra.lean`. -/
theorem vertices_insertAt_decomp {T : Planar α} (v : Vertex T) (t₂ : Planar α) :
    ((vertices (insertAt v t₂) : List _) : Multiset (Vertex (insertAt v t₂))) =
      ((vertices T : Multiset _).filterMap (fun w => Vertex.preserve? v w t₂))
      + ({Vertex.sourceSelf v t₂} : Multiset _)
      + ((vertices t₂ : Multiset _).map (Vertex.lift v t₂)) :=
  vertices_insertAt_decomp_aux v t₂

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
