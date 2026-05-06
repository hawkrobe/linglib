import Mathlib.Algebra.Free
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.MapFold
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Decorated Binary Rooted Trees @cite{marcolli-chomsky-berwick-2025} @cite{foissy-2002}

The decorated binary rooted tree carrier of the Connes-Kreimer-style
Hopf algebra of (binary nonplanar) decorated forests, parameterized
over a leaf type `α : Type*`.

## Substrate choice

`DecoratedTree α` is a single inductive with three constructors:

- `leaf  : α → DecoratedTree α`
- `trace : DecoratedTree α → DecoratedTree α`
- `node  : DecoratedTree α → DecoratedTree α → DecoratedTree α`

Mathematically this is the free term algebra over the signature
`{leaf : α → 1, trace : 1 → 1, node : 1 × 1 → 1}`. The carrier shape
is the standard one for *decorated* Connes-Kreimer Hopf algebras
(cf. @cite{foissy-2002} on planar decorated rooted-tree Hopf algebras
H^D_{P,R} — generalizing the non-planar Connes-Kreimer H^D_R). Note:
M-C-B themselves do not cite Foissy directly; they appeal to the
Connes-Kreimer-Feynman-graph proof for coassociativity (book p. 38
references). The Foissy attribution here is the formaliser's reading
of the closest mathematical predecessor for the *decorated* binary
case. The `Mul (DecoratedTree α)` instance (via `node`) recovers
`FreeMagma`-style `*` notation; the recursor `recOnMul` mirrors
`FreeMagma.recOnMul`.

## Two faithfulness gaps re. M-C-B Definition 1.1.1

@cite{marcolli-chomsky-berwick-2025} Definition 1.1.1 says the
abstract syntactic-object set is a free non-associative *commutative*
magma `Magma_{na,c}(SO_0, M)`. mathlib's `FreeMagma α` is the
non-commutative version. Two distinct gaps relative to mathlib
infrastructure:

**Gap 1 — Planar vs nonplanar.** `DecoratedTree α` inherits the
planar structure: `node l r ≠ node r l` as an equality. A faithful
encoding would `Quotient` by `node l r ~ node r l`. Proofs that need
the abstract identification require that quotient; this file does
not develop it (see CHANGELOG 0.230.655's note on the in-flight
`FreeCommMagma` work). M-C-B handle this gap implicitly via
equivalence-class drawings — book p. 23 example shows
α∧β∧γ = α∧γ∧β as the same nonplanar tree.

**Gap 2 — Set vs multiset (the singleton-collapse).** M-C-B p. 25
§1.1.3.1's "very mild" remark refers SPECIFICALLY to the
set-vs-multiset clash for syntactic objects: since trees are binary
(not n-ary for n ≥ 3), repeated-label ambiguity at a single node is
limited, and they explicitly identify {a, a} with {a} for binary
nodes. (This is the `idem` axiom the comm-quotient does NOT add by
default.) NOT to be confused with Gap 1 — this is a separate concern.

For workspaces (`Forest α := Multiset (DecoratedTree α)`), the
multiset structure handles the analogous gap at the workspace level
automatically. Both gaps remain open at the *intra-tree* level until
the comm-quotient + singleton-collapse are wired in (Stage 4a/4b per
`scratch/mcb_stage1_plan.md`).

## Trace constructor and self-reference

Per @cite{marcolli-chomsky-berwick-2025} Definition 1.2.4, the
contraction quotient T/^c T_v carries a trace label *T_v* that holds
the contracted subtree as data. The recursive `.trace t` constructor
here is retained for **CI-side / FormCopy** consumers — operations
that need to inspect the original moved subtree at the
Conceptual-Intensional interface. Per @cite{marcolli-skigin-2025}
§10.1 (which clarifies and disambiguates the brief discussion in
M-C-B's §1.3), the recursive payload is **not** required for the
bialgebra structure itself: M-S Lemma 10.4 proves coassociativity of
Δ^c with scalar trace labels (see `TraceTree α β` below). The
recursive `DecoratedTree α → DecoratedTree α` shape is kept here
because FormCopy and similar linguistic operations consume the
contracted subtree as data; the bialgebra carrier (`Hc R α`) projects
through `.anon` to a scalar-trace `TraceTree α Unit`.

## Layer status

`[UPSTREAM]` candidate. Future home is something like
`Mathlib.Combinatorics.HopfAlgebra.ConnesKreimer.DecoratedTree`. This
file is part of the Stage 0.5 hoist out of `Theories/Syntax/Minimalist/Hopf/`
(per `scratch/mcb_stage1_plan.md`). Namespace is `ConnesKreimer`
(renamed from `Minimalist.Hopf` in Stage 0.7).
-/

namespace ConnesKreimer

/-! ## DecoratedTree -/

/-- A binary nonplanar rooted tree with leaves labelled by `α` and
    self-decoration via `trace`. Three constructors:

    - `leaf a` — a leaf vertex labelled with `a : α`
    - `trace t` — a trace leaf carrying a subtree `t` as data
      (treated as a leaf for tree-traversal; `t` is metadata)
    - `node l r` — a binary internal vertex with children `l` and `r`

    The `trace` constructor enables nested decorations (a trace can
    contain trace-bearing trees), which is essential for iterated
    coproducts `(Δ ⊗ id) ∘ Δ`. -/
inductive DecoratedTree (α : Type*) where
  | leaf  (a : α) : DecoratedTree α
  | trace (t : DecoratedTree α) : DecoratedTree α
  | node  (l r : DecoratedTree α) : DecoratedTree α
  deriving Repr, DecidableEq

namespace DecoratedTree

/-! ## Mathlib-style algebra hooks -/

/-- `DecoratedTree α` is a magma via the `node` constructor, mirroring
    `FreeMagma`. This gives `l * r = .node l r` for free. -/
instance {α : Type*} : Mul (DecoratedTree α) := ⟨.node⟩

/-- `node l r = l * r` by definition. -/
@[simp] theorem node_eq_mul {α : Type*} (l r : DecoratedTree α) :
    node l r = l * r := rfl

/-- Recursor using `*` notation in the `node`/`mul` case, mirroring
    `FreeMagma.recOnMul`. Useful for proofs and definitions that
    prefer the multiplicative interface. -/
@[elab_as_elim]
def recOnMul {α : Type*} {motive : DecoratedTree α → Sort*}
    (t : DecoratedTree α)
    (leaf  : ∀ a, motive (.leaf a))
    (trace : ∀ s, motive s → motive (.trace s))
    (mul   : ∀ a b, motive a → motive b → motive (a * b)) : motive t :=
  match t with
  | .leaf a   => leaf a
  | .trace s  => trace s (recOnMul s leaf trace mul)
  | .node a b => mul a b (recOnMul a leaf trace mul) (recOnMul b leaf trace mul)

/-- Number of leaves in a `DecoratedTree`. Both `.leaf` and `.trace` count
    as leaves (each occupies one leaf vertex in the tree shape; the
    contracted subtree carried by `.trace` is metadata, not part of the
    visible tree). -/
def leafCount {α : Type*} : DecoratedTree α → Nat
  | .leaf _   => 1
  | .trace _  => 1
  | .node l r => l.leafCount + r.leafCount

@[simp] theorem leafCount_leaf {α : Type*} (a : α) :
    (DecoratedTree.leaf a).leafCount = 1 := rfl

@[simp] theorem leafCount_trace {α : Type*} (t : DecoratedTree α) :
    (DecoratedTree.trace t).leafCount = 1 := rfl

@[simp] theorem leafCount_node {α : Type*} (l r : DecoratedTree α) :
    (DecoratedTree.node l r).leafCount = l.leafCount + r.leafCount := rfl

theorem leafCount_pos {α : Type*} (t : DecoratedTree α) : 0 < t.leafCount := by
  induction t with
  | leaf _ => exact Nat.one_pos
  | trace _ _ => exact Nat.one_pos
  | node l r ihl _ihr =>
    simp only [leafCount]
    omega

/-! ## `IsNotTrace` predicate

For Connes-Kreimer coassociativity to hold (M-C-B Lemma 1.2.10), cuts that
extract a child subtree (`bothCut`, `onlyLeftCut`, `onlyRightCut` on `.node`)
must NOT be allowed when the relevant child is a `.trace` marker. Without this
restriction, iterated cuts on the remainder accumulate `.trace (.trace _)`
nesting, breaking the cuts-of-cuts bijection — see `scratch/mcb_stage1_plan.md`
or `Linglib/Scratch/CoassocCheck.lean` for the full analysis.

`IsNotTrace t : Prop` is `True` for `.leaf` and `.node`, `False` for `.trace`.
Decidable; used as a hypothesis in `CutShape`'s extracting constructors. -/

/-- A tree is "not a trace marker" — required for cuts that extract this tree
    as a subtree. Predicate is decidable. -/
def IsNotTrace {α : Type*} : DecoratedTree α → Prop
  | .leaf _   => True
  | .trace _  => False
  | .node _ _ => True

instance {α : Type*} : DecidablePred (@IsNotTrace α) := fun t =>
  match t with
  | .leaf _   => isTrue trivial
  | .trace _  => isFalse id
  | .node _ _ => isTrue trivial

@[simp] theorem isNotTrace_leaf {α : Type*} (a : α) :
    IsNotTrace (DecoratedTree.leaf a) := trivial

@[simp] theorem isNotTrace_node {α : Type*} (l r : DecoratedTree α) :
    IsNotTrace (DecoratedTree.node l r) := trivial

@[simp] theorem not_isNotTrace_trace {α : Type*} (t : DecoratedTree α) :
    ¬ IsNotTrace (DecoratedTree.trace t) := id

end DecoratedTree

/-! ## TraceTree — trace label as a first-class scalar

The `.trace t` constructor of `DecoratedTree α` carries the contracted
subtree `t` as metadata, motivated by the linguistic FormCopy operation
(@cite{marcolli-chomsky-berwick-2025} Definition 1.2.4). However, the
Hopf algebra coassociativity proof in the M-C-B book Lemma 1.2.10 appeals
to @cite{connes-kreimer-1998} for the Feynman-graph CK Hopf algebra,
where contraction markers carry no recursive payload. Treating `.trace t`
literally as a data-carrying basis element of `Hc R α` would break
coassociativity: iterated coproducts produce `.trace _` markers whose
contents differ between the two iteration orders, even though the
underlying combinatorial "3-coloring" structures match. (A concrete
counterexample for `T = .node l (.node a b)` is verified kernel-checked
in `scratch/SlotThreeMismatch.lean`.)

@cite{marcolli-skigin-2025} §10.1 ("Labels of traces of movement")
explicitly addresses this. M-S frame their §10 as clarifying and
disambiguating M-C-B's §1.3, observing: the trace label "in fact does
not have to retain the full structure of T_v as a syntactic object …
the extracted term T_v is still present, on the other side of the
coproduct, so that information is not lost." Their Definition 10.3
redefines the trace label as a scalar `α̅_{h_T(v)}` — the *struck-through*
head label, an element of `̄SO₀ := {̄α | α ∈ SO₀}` (a **disjoint marked
copy** of the leaf alphabet, NOT just an element of `SO₀`). The leaf
alphabet is enlarged to the disjoint union `SO₀ ⊔ ̄SO₀`. M-S Lemma 10.4
proves Δ^c coassociativity under this scheme via **head-function
transparency**: `h_{T_v}(w) = h_T(w)` for `w ∈ T_v`, so iterated traces
all resolve to the same label as the original subtree.

`TraceTree α β` realizes the disjoint-leaf-and-trace shape with a
polymorphic trace-label type `β`:
- `.leaf (a : α)`: a leaf carrying a label of type `α`.
- `.trace (b : β)`: a trace marker carrying a scalar label of type `β`
  (NOT a recursive subtree). The constructor distinction encodes the
  disjoint-copy structure of `SO₀ ⊔ ̄SO₀`: even when `β = α`, the
  `.trace`-vs-`.leaf` distinction marks the struck-through copy.
- `.node l r`: an internal binary vertex.

`Hc R α` is fixed to `Multiset (TraceTree α Unit)` — the **simplest**
realization, where trace labels carry no information at all. This is
sufficient for coassociativity (M-S Lemma 10.4 holds vacuously when the
extractor is constant) but is a strict simplification of M-S, who use a
non-trivial scalar label via the head function. The polymorphism stays
available so linguistic-layer code can use `TraceTree α α` (M-S aligned)
or richer label types when head-function infrastructure lands.

The projection `DecoratedTree.anon (h : DecoratedTree α → β)` takes an
extractor function for the trace label. For `Hc`-level coassoc to behave,
`h` must be **transparent under contraction**: `h (.trace t) = h t`.
This is an explicit hypothesis on theorems that need it (mathlib idiom:
unbundled function plus side-condition, since trace-label choice is not
canonical). Examples of transparent extractors:
- `fun _ => ()` (trivial) — used by `Hc R α` itself.
- `DecoratedTree.leftmostLeaf` (when defined) — recursive descent through
  `.trace`, picking the leftmost actual leaf label.
- The M-S head function (when head-function infrastructure lands).

The labelled `.trace t` data remains available at the `DecoratedTree`
level for linguistic operations (FormCopy, cancellation-of-deeper-copies). -/

/-- A binary rooted tree with leaf labels in `α` and scalar trace labels
    in `β`. Used as the basis-key type of `Hc R α` (with `β = Unit`).
    The polymorphic `β` accommodates richer linguistic-layer projections
    (e.g., `β = α` plus a head function realizes
    @cite{marcolli-skigin-2025} Definition 10.3, modulo the
    head-function-transparency requirement on the extractor). -/
inductive TraceTree (α : Type*) (β : Type*) where
  | leaf  (a : α) : TraceTree α β
  | trace (b : β) : TraceTree α β
  | node  (l r : TraceTree α β) : TraceTree α β
  deriving Repr, DecidableEq

namespace TraceTree

/-- A `TraceTree` is "not a trace marker" — required for cuts that extract
    this tree as a subtree. Predicate is decidable. Same shape as
    `DecoratedTree.IsNotTrace`. -/
def IsNotTrace {α β : Type*} : TraceTree α β → Prop
  | .leaf _   => True
  | .trace _  => False
  | .node _ _ => True

instance {α β : Type*} : DecidablePred (@IsNotTrace α β) := fun t =>
  match t with
  | .leaf _   => isTrue trivial
  | .trace _  => isFalse id
  | .node _ _ => isTrue trivial

@[simp] theorem isNotTrace_leaf {α β : Type*} (a : α) :
    IsNotTrace (TraceTree.leaf a : TraceTree α β) := trivial

@[simp] theorem isNotTrace_node {α β : Type*} (l r : TraceTree α β) :
    IsNotTrace (TraceTree.node l r) := trivial

@[simp] theorem not_isNotTrace_trace {α β : Type*} (b : β) :
    ¬ IsNotTrace (TraceTree.trace b : TraceTree α β) := id

/-- Size measure on `TraceTree`: count of constructors (each `.leaf` /
    `.trace` / `.node` adds 1). Used as the structural-recursion measure
    for proving `cutForest` extracts proper subtrees. -/
def size {α β : Type*} : TraceTree α β → Nat
  | .leaf _   => 1
  | .trace _  => 1
  | .node l r => 1 + l.size + r.size

@[simp] theorem size_leaf {α β : Type*} (a : α) :
    (TraceTree.leaf a : TraceTree α β).size = 1 := rfl

@[simp] theorem size_trace {α β : Type*} (b : β) :
    (TraceTree.trace b : TraceTree α β).size = 1 := rfl

@[simp] theorem size_node {α β : Type*} (l r : TraceTree α β) :
    (TraceTree.node l r).size = 1 + l.size + r.size := rfl

theorem size_pos {α β : Type*} (t : TraceTree α β) : 0 < t.size := by
  cases t <;> simp only [size] <;> omega

/-- Vertex count excluding `.trace` markers. The trace-aware analog of
    `size`. Used by Δ^c counting because per @cite{marcolli-chomsky-berwick-2025}
    Lemma 1.6.3 eq. 1.6.8 (book p. 65), trace markers in T/^c T_v are NOT
    counted as accessible terms ("cancellation of the deeper copy"). -/
def nonTraceSize {α β : Type*} : TraceTree α β → Nat
  | .leaf _   => 1
  | .trace _  => 0
  | .node l r => 1 + l.nonTraceSize + r.nonTraceSize

@[simp] theorem nonTraceSize_leaf {α β : Type*} (a : α) :
    (TraceTree.leaf a : TraceTree α β).nonTraceSize = 1 := rfl

@[simp] theorem nonTraceSize_trace {α β : Type*} (b : β) :
    (TraceTree.trace b : TraceTree α β).nonTraceSize = 0 := rfl

@[simp] theorem nonTraceSize_node {α β : Type*} (l r : TraceTree α β) :
    (TraceTree.node l r).nonTraceSize = 1 + l.nonTraceSize + r.nonTraceSize := rfl

theorem nonTraceSize_le_size {α β : Type*} (t : TraceTree α β) :
    t.nonTraceSize ≤ t.size := by
  induction t with
  | leaf _ => simp only [nonTraceSize_leaf, size_leaf]; omega
  | trace _ => simp only [nonTraceSize_trace, size_trace]; omega
  | node l r ihl ihr => simp only [nonTraceSize, size]; omega

/-- Leaf count of a `TraceTree`. The Hopf-algebra grading on
    `Hc R α = AddMonoidAlgebra R (TraceForest α Unit)` per
    @cite{marcolli-chomsky-berwick-2025} Definition 1.6.2 (book p. 64):
    `deg(a) = #L(T_a)`. Both `.leaf` and `.trace` count as 1 (a trace marker
    occupies a leaf position in the tree); `.node l r` sums children. Same
    shape as `DecoratedTree.leafCount`. -/
def leafCount {α β : Type*} : TraceTree α β → Nat
  | .leaf _   => 1
  | .trace _  => 1
  | .node l r => l.leafCount + r.leafCount

@[simp] theorem leafCount_leaf {α β : Type*} (a : α) :
    (TraceTree.leaf a : TraceTree α β).leafCount = 1 := rfl

@[simp] theorem leafCount_trace {α β : Type*} (b : β) :
    (TraceTree.trace b : TraceTree α β).leafCount = 1 := rfl

@[simp] theorem leafCount_node {α β : Type*} (l r : TraceTree α β) :
    (TraceTree.node l r).leafCount = l.leafCount + r.leafCount := rfl

theorem leafCount_pos {α β : Type*} (t : TraceTree α β) : 0 < t.leafCount := by
  induction t with
  | leaf _ => simp only [leafCount_leaf]; omega
  | trace _ => simp only [leafCount_trace]; omega
  | node l r ihl _ => simp only [leafCount]; omega

end TraceTree

namespace DecoratedTree

/-- Project a `DecoratedTree α` to a `TraceTree α β`, computing each
    trace's label via the extractor `h`. Recurses through `.node`;
    applies `h` once at each `.trace`.

    For Hc-level coassoc (`forestToHc`-respecting equality of iterated
    coproducts), `h` must satisfy the **transparency** condition
    `∀ t, h (.trace t) = h t` so that nested traces resolve to the same
    label as the original subtree. The condition is stated as an
    explicit hypothesis on theorems that need it. -/
def anon {α β : Type*} (h : DecoratedTree α → β) :
    DecoratedTree α → TraceTree α β
  | .leaf a   => .leaf a
  | .trace t  => .trace (h t)
  | .node l r => .node (anon h l) (anon h r)

@[simp] theorem anon_leaf {α β : Type*} (h : DecoratedTree α → β) (a : α) :
    DecoratedTree.anon h (.leaf a) = TraceTree.leaf a := rfl

@[simp] theorem anon_trace {α β : Type*} (h : DecoratedTree α → β)
    (t : DecoratedTree α) :
    DecoratedTree.anon h (.trace t) = TraceTree.trace (h t) := rfl

@[simp] theorem anon_node {α β : Type*} (h : DecoratedTree α → β)
    (l r : DecoratedTree α) :
    DecoratedTree.anon h (.node l r) = TraceTree.node (anon h l) (anon h r) := rfl

end DecoratedTree

/-! ## Forest

A forest is a multiset of decorated trees. Disjoint union ⊔
corresponds to `· + ·` on multisets (commutative, ∅ = 0).
@cite{marcolli-chomsky-berwick-2025} Definition 1.2.1. -/

/-- A decorated forest: a multiset of decorated trees. -/
abbrev Forest (α : Type*) := Multiset (DecoratedTree α)

/-- A forest of `TraceTree`s with leaf labels in `α` and trace labels
    in `β`. Used as the basis-key type of `Hc R α` (with `β = Unit`). -/
abbrev TraceForest (α : Type*) (β : Type*) := Multiset (TraceTree α β)

/-- The total leaf count of a `TraceForest`: sum of `TraceTree.leafCount`
    over its components. The Hopf-algebra grading on `Hc R α` per
    @cite{marcolli-chomsky-berwick-2025} Definition 1.6.2 (book p. 64):
    `deg(F) = #L(F)`. M-C-B's degree-conservation observation (book p. 64,
    paragraph after Def 1.6.2): `deg(F)` is conserved across any Merge
    operation since no lexical items are removed. -/
def TraceForest.degForest {α β : Type*} (F : TraceForest α β) : Nat :=
  Multiset.sum (Multiset.map TraceTree.leafCount F)

@[simp] theorem TraceForest.degForest_zero {α β : Type*} :
    TraceForest.degForest (0 : TraceForest α β) = 0 := rfl

@[simp] theorem TraceForest.degForest_singleton {α β : Type*} (T : TraceTree α β) :
    TraceForest.degForest ({T} : TraceForest α β) = T.leafCount := by
  simp only [degForest, Multiset.map_singleton, Multiset.sum_singleton]

@[simp] theorem TraceForest.degForest_add {α β : Type*} (F G : TraceForest α β) :
    TraceForest.degForest (F + G : TraceForest α β) =
      TraceForest.degForest F + TraceForest.degForest G := by
  unfold degForest
  rw [Multiset.map_add, Multiset.sum_add]

@[simp] theorem TraceForest.degForest_cons {α β : Type*} (T : TraceTree α β)
    (F : TraceForest α β) :
    TraceForest.degForest (T ::ₘ F : TraceForest α β) =
      T.leafCount + TraceForest.degForest F := by
  unfold degForest
  rw [Multiset.map_cons, Multiset.sum_cons]

/-- Pair forest: `degForest {l, r} = l.leafCount + r.leafCount`. Avoids
    repeating the `({l, r} : Multiset _) = l ::ₘ {r}` rewrite + `_cons` +
    `_singleton` chain at each call site (notably in
    `AdmissibleCut.cut_leafCount_conservation`'s bothCut arm). -/
@[simp] theorem TraceForest.degForest_pair {α β : Type*} (l r : TraceTree α β) :
    TraceForest.degForest ({l, r} : TraceForest α β) = l.leafCount + r.leafCount := by
  show TraceForest.degForest (l ::ₘ ({r} : TraceForest α β)) = _
  rw [TraceForest.degForest_cons, TraceForest.degForest_singleton]

/-- Total vertex count of a `TraceForest`: sum of `TraceTree.size` over its
    components. Vertex-count analog of `degForest` (which sums `leafCount`).
    Used by `cut_size_conservation` (in `AdmissibleCut.lean`) to express the
    Δ^d size analog of MCB's leafCount-conservation observation. -/
def TraceForest.sizeForest {α β : Type*} (F : TraceForest α β) : Nat :=
  Multiset.sum (Multiset.map TraceTree.size F)

@[simp] theorem TraceForest.sizeForest_zero {α β : Type*} :
    TraceForest.sizeForest (0 : TraceForest α β) = 0 := rfl

@[simp] theorem TraceForest.sizeForest_singleton {α β : Type*} (T : TraceTree α β) :
    TraceForest.sizeForest ({T} : TraceForest α β) = T.size := by
  simp only [sizeForest, Multiset.map_singleton, Multiset.sum_singleton]

@[simp] theorem TraceForest.sizeForest_cons {α β : Type*} (T : TraceTree α β)
    (F : TraceForest α β) :
    TraceForest.sizeForest (T ::ₘ F) = T.size + F.sizeForest := by
  unfold sizeForest
  rw [Multiset.map_cons, Multiset.sum_cons]

@[simp] theorem TraceForest.sizeForest_add {α β : Type*} (F G : TraceForest α β) :
    TraceForest.sizeForest (F + G) = F.sizeForest + G.sizeForest := by
  unfold sizeForest
  rw [Multiset.map_add, Multiset.sum_add]

@[simp] theorem TraceForest.sizeForest_pair {α β : Type*} (l r : TraceTree α β) :
    TraceForest.sizeForest ({l, r} : TraceForest α β) = l.size + r.size := by
  show TraceForest.sizeForest (l ::ₘ ({r} : TraceForest α β)) = _
  rw [TraceForest.sizeForest_cons, TraceForest.sizeForest_singleton]

/-- Project a forest to a `TraceForest α β` via the per-tree `anon h` map.

    Defined as prefix `Forest.anon h F` rather than dot-notation `F.anon`,
    because `Forest` is an `abbrev` for `Multiset (DecoratedTree α)` and
    dot-notation on abbrevs routes to the underlying type's namespace. -/
def Forest.anon {α β : Type*} (h : DecoratedTree α → β) (F : Forest α) :
    TraceForest α β :=
  F.map (DecoratedTree.anon h)

@[simp] theorem Forest.anon_zero {α β : Type*} (h : DecoratedTree α → β) :
    Forest.anon h (0 : Forest α) = (0 : TraceForest α β) :=
  Multiset.map_zero _

@[simp] theorem Forest.anon_add {α β : Type*} (h : DecoratedTree α → β)
    (F G : Forest α) :
    Forest.anon h (F + G) = Forest.anon h F + Forest.anon h G :=
  Multiset.map_add _ _ _

@[simp] theorem Forest.anon_singleton {α β : Type*} (h : DecoratedTree α → β)
    (T : DecoratedTree α) :
    Forest.anon h ({T} : Forest α) = ({DecoratedTree.anon h T} : TraceForest α β) :=
  Multiset.map_singleton _ _

@[simp] theorem Forest.anon_cons {α β : Type*} (h : DecoratedTree α → β)
    (T : DecoratedTree α) (F : Forest α) :
    Forest.anon h (T ::ₘ F : Forest α)
      = DecoratedTree.anon h T ::ₘ Forest.anon h F :=
  Multiset.map_cons _ _ _

/-! ## §6: Forest size measures (b₀, α, σ)
@cite{marcolli-chomsky-berwick-2025} §1.2 + §1.6.1

Three counting functions on a `TraceForest α β`, parallel to `degForest`
and `sizeForest` above:

- **`b₀(F)` — number of components**: cardinality of `F` as a multiset.
- **`α(F)` — accessible terms**: per MCB Def 1.2.2 (the "more precise
  discussion" of the §1.1 prose-definition on book p. 21: "the accessible
  terms of a syntactic object T are the subtrees T_v, with v a non-root
  vertex of T"), `α(F) = Σ_T #Acc(T)`. For a `TraceTree`, every vertex
  is the root of some subtree, so `#Acc(T) = #V(T) - 1 = T.size - 1`.
- **`σ(F) = b₀(F) + α(F)`** (MCB §1.6.1).

Lemma 1.6.3 (book §1.6.2) supplies counting identities for these under
`merge` (the `.node` constructor); the merge-side identities matching MCB
eq. 1.6.5 / 1.6.6 are proven below. The cut-quotient identities (eq. 1.6.7-
1.6.10) need substrate from `AdmissibleCut.lean` and live in
`Theories/Syntax/Minimalist/Merge/MinimalYield.lean`.

Generic over leaf alphabet `α` and trace alphabet `β`. -/

/-- Number of accessible terms of a tree: `#V(T) - 1` per MCB Def 1.2.2,
    where accessible terms are subtrees `T_v` with `v` a non-root vertex
    of `T` (book p. 21). -/
def TraceTree.accCount {α β : Type*} : TraceTree α β → Nat := fun T => T.size - 1

@[simp] theorem TraceTree.accCount_leaf {α β : Type*} (a : α) :
    (TraceTree.leaf a : TraceTree α β).accCount = 0 := rfl

@[simp] theorem TraceTree.accCount_trace {α β : Type*} (b : β) :
    (TraceTree.trace b : TraceTree α β).accCount = 0 := rfl

@[simp] theorem TraceTree.accCount_node {α β : Type*} (l r : TraceTree α β) :
    (TraceTree.node l r).accCount = l.size + r.size := by
  show (1 + l.size + r.size) - 1 = l.size + r.size
  omega

/-- **MCB Lemma 1.6.3 eq. 1.6.5** (book p. 65): `α(M(T_v, T_w)) = α(T_v) +
    α(T_w) + 2`. Trivially follows from `accCount_node` plus `size_pos`. -/
theorem TraceTree.accCount_merge {α β : Type*} (T_v T_w : TraceTree α β) :
    (TraceTree.node T_v T_w).accCount = T_v.accCount + T_w.accCount + 2 := by
  rw [TraceTree.accCount_node]
  show T_v.size + T_w.size = T_v.size - 1 + (T_w.size - 1) + 2
  have := T_v.size_pos
  have := T_w.size_pos
  omega

/-- `b₀(F)` — number of components. M-C-B Definition 1.2.2. -/
def TraceForest.b₀ {α β : Type*} (F : TraceForest α β) : Nat := Multiset.card F

@[simp] theorem TraceForest.b₀_zero {α β : Type*} :
    TraceForest.b₀ (0 : TraceForest α β) = 0 := rfl

@[simp] theorem TraceForest.b₀_singleton {α β : Type*} (T : TraceTree α β) :
    TraceForest.b₀ ({T} : TraceForest α β) = 1 := by
  unfold b₀; exact Multiset.card_singleton _

@[simp] theorem TraceForest.b₀_cons {α β : Type*} (T : TraceTree α β)
    (F : TraceForest α β) :
    TraceForest.b₀ (T ::ₘ F) = 1 + F.b₀ := by
  show Multiset.card (T ::ₘ F) = 1 + Multiset.card F
  rw [Multiset.card_cons]; omega

@[simp] theorem TraceForest.b₀_add {α β : Type*} (F G : TraceForest α β) :
    TraceForest.b₀ (F + G) = F.b₀ + G.b₀ :=
  Multiset.card_add F G

/-- `α(F)` — total accessible terms across components. M-C-B Def 1.2.2 / §1.6.1. -/
def TraceForest.alpha {α β : Type*} (F : TraceForest α β) : Nat :=
  Multiset.sum (Multiset.map TraceTree.accCount F)

@[simp] theorem TraceForest.alpha_zero {α β : Type*} :
    TraceForest.alpha (0 : TraceForest α β) = 0 := rfl

@[simp] theorem TraceForest.alpha_singleton {α β : Type*} (T : TraceTree α β) :
    TraceForest.alpha ({T} : TraceForest α β) = T.accCount := by
  unfold alpha
  rw [Multiset.map_singleton, Multiset.sum_singleton]

@[simp] theorem TraceForest.alpha_cons {α β : Type*} (T : TraceTree α β)
    (F : TraceForest α β) :
    TraceForest.alpha (T ::ₘ F) = T.accCount + F.alpha := by
  show Multiset.sum (Multiset.map _ (T ::ₘ F)) = T.accCount + Multiset.sum _
  rw [Multiset.map_cons, Multiset.sum_cons]

@[simp] theorem TraceForest.alpha_add {α β : Type*} (F G : TraceForest α β) :
    TraceForest.alpha (F + G) = F.alpha + G.alpha := by
  show Multiset.sum (Multiset.map _ (F + G)) = _
  rw [Multiset.map_add, Multiset.sum_add]
  rfl

/-- `σ(F) = b₀(F) + α(F)` — total accessible-terms-of-forest measure
    (MCB §1.6.1 eq. 1.6.1). -/
def TraceForest.sigma {α β : Type*} (F : TraceForest α β) : Nat := F.b₀ + F.alpha

@[simp] theorem TraceForest.sigma_zero {α β : Type*} :
    TraceForest.sigma (0 : TraceForest α β) = 0 := by
  unfold sigma; simp only [b₀_zero, alpha_zero]

@[simp] theorem TraceForest.sigma_singleton {α β : Type*} (T : TraceTree α β) :
    TraceForest.sigma ({T} : TraceForest α β) = 1 + T.accCount := by
  unfold sigma; rw [b₀_singleton, alpha_singleton]

@[simp] theorem TraceForest.sigma_cons {α β : Type*} (T : TraceTree α β)
    (F : TraceForest α β) :
    TraceForest.sigma (T ::ₘ F) = 1 + T.accCount + F.sigma := by
  unfold sigma; rw [b₀_cons, alpha_cons]; omega

@[simp] theorem TraceForest.sigma_add {α β : Type*} (F G : TraceForest α β) :
    TraceForest.sigma (F + G) = F.sigma + G.sigma := by
  unfold sigma; rw [b₀_add, alpha_add]; omega

/-- **MCB Lemma 1.6.3 eq. 1.6.6** (book p. 65): `σ(M(T_v, T_w)) = σ(T_v) +
    σ(T_w) + 1` at the singleton-forest level. -/
theorem TraceForest.sigma_merge_singleton {α β : Type*} (T_v T_w : TraceTree α β) :
    TraceForest.sigma ({TraceTree.node T_v T_w} : TraceForest α β)
      = TraceForest.sigma ({T_v} : TraceForest α β)
        + TraceForest.sigma ({T_w} : TraceForest α β) + 1 := by
  rw [sigma_singleton, sigma_singleton, sigma_singleton,
      TraceTree.accCount_merge]
  omega

/-! ## §7: Δ^c-aware forest measures (αᶜ, σᶜ)
@cite{marcolli-chomsky-berwick-2025} §1.6.2

Trace-aware analogs of `accCount` and `sigma` for the Δ^c counting (MCB
Lemma 1.6.3 eq. 1.6.8 and 1.6.10). These count trace markers as zero
contribution to "accessible terms" — implementing MCB's "cancellation of
the deeper copy" principle (book p. 65-66). For trace-free trees,
`accCountC = accCount`; the difference shows up only in contraction-
quotient trees.

Distinction from `accCount`:
- `accCount T = T.size - 1` (every non-root vertex counted)
- `accCountC T = T.nonTraceSize - 1` (only non-trace non-root vertices)

For trace-free trees `nonTraceSize = size`, so `accCountC = accCount`.
The two measures diverge on `T/^c T_v` (a trace marker for the cancelled
copy), which is exactly where MCB's eq. 1.6.8/1.6.10 use them. -/

/-- Δ^c-aware accCount: non-root non-trace vertex count. Excludes trace
    markers per MCB Lemma 1.6.3 eq. 1.6.8 (book p. 65). For trace-free
    trees agrees with `accCount`. -/
def TraceTree.accCountC {α β : Type*} : TraceTree α β → Nat := fun T => T.nonTraceSize - 1

@[simp] theorem TraceTree.accCountC_leaf {α β : Type*} (a : α) :
    (TraceTree.leaf a : TraceTree α β).accCountC = 0 := rfl

@[simp] theorem TraceTree.accCountC_trace {α β : Type*} (b : β) :
    (TraceTree.trace b : TraceTree α β).accCountC = 0 := rfl

@[simp] theorem TraceTree.accCountC_node {α β : Type*} (l r : TraceTree α β) :
    (TraceTree.node l r).accCountC = l.nonTraceSize + r.nonTraceSize := by
  show (1 + l.nonTraceSize + r.nonTraceSize) - 1 = l.nonTraceSize + r.nonTraceSize
  omega

/-- αᶜ on a forest. Non-trace non-root vertex count summed across components. -/
def TraceForest.alphaC {α β : Type*} (F : TraceForest α β) : Nat :=
  Multiset.sum (Multiset.map TraceTree.accCountC F)

@[simp] theorem TraceForest.alphaC_zero {α β : Type*} :
    TraceForest.alphaC (0 : TraceForest α β) = 0 := rfl

@[simp] theorem TraceForest.alphaC_singleton {α β : Type*} (T : TraceTree α β) :
    TraceForest.alphaC ({T} : TraceForest α β) = T.accCountC := by
  unfold alphaC
  rw [Multiset.map_singleton, Multiset.sum_singleton]

@[simp] theorem TraceForest.alphaC_cons {α β : Type*} (T : TraceTree α β)
    (F : TraceForest α β) :
    TraceForest.alphaC (T ::ₘ F) = T.accCountC + F.alphaC := by
  show Multiset.sum (Multiset.map _ (T ::ₘ F)) = T.accCountC + Multiset.sum _
  rw [Multiset.map_cons, Multiset.sum_cons]

@[simp] theorem TraceForest.alphaC_add {α β : Type*} (F G : TraceForest α β) :
    TraceForest.alphaC (F + G) = F.alphaC + G.alphaC := by
  show Multiset.sum (Multiset.map _ (F + G)) = _
  rw [Multiset.map_add, Multiset.sum_add]
  rfl

/-- σᶜ on a forest: `σᶜ(F) = b₀(F) + αᶜ(F)`. Δ^c analog of `sigma`. -/
def TraceForest.sigmaC {α β : Type*} (F : TraceForest α β) : Nat := F.b₀ + F.alphaC

@[simp] theorem TraceForest.sigmaC_zero {α β : Type*} :
    TraceForest.sigmaC (0 : TraceForest α β) = 0 := by
  unfold sigmaC; simp only [b₀_zero, alphaC_zero]

@[simp] theorem TraceForest.sigmaC_singleton {α β : Type*} (T : TraceTree α β) :
    TraceForest.sigmaC ({T} : TraceForest α β) = 1 + T.accCountC := by
  unfold sigmaC; rw [b₀_singleton, alphaC_singleton]

@[simp] theorem TraceForest.sigmaC_cons {α β : Type*} (T : TraceTree α β)
    (F : TraceForest α β) :
    TraceForest.sigmaC (T ::ₘ F) = 1 + T.accCountC + F.sigmaC := by
  unfold sigmaC; rw [b₀_cons, alphaC_cons]; omega

@[simp] theorem TraceForest.sigmaC_add {α β : Type*} (F G : TraceForest α β) :
    TraceForest.sigmaC (F + G) = F.sigmaC + G.sigmaC := by
  unfold sigmaC; rw [b₀_add, alphaC_add]; omega

end ConnesKreimer
