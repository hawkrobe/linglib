import Linglib.Theories.Syntax.MereologicalSyntax.Basic
import Linglib.Theories.Syntax.SynGraph

set_option autoImplicit false

/-!
# Bridge: SynObj → SynGraph
@cite{adger-2025}

Embeds tree-based syntactic objects (`SynObj`) into graph-based structures
(`SynGraph MLabel`), making `SynGraph` the canonical operational type for
Angular Locality while preserving `SynObj` as an ergonomic builder.

`SynObj` is an inductive type that gives structural recursion and `rfl`
proofs — useful for tree-shaped work (classifier hierarchies, basic clause
structure). `SynGraph` supports multiparthood (unbounded in-degree),
required for movement in mereological syntax. The embedding connects them:
build with `SynObj`, convert to `SynGraph` when you need AL, movement,
or island constraints.

## Pre-order Indexing

The embedding assigns node indices via pre-order traversal:
- Root = 0
- 1-part subtree: indices `[1, 1 + onePart.size)`
- 2-part subtree: indices `[1 + onePart.size, size)`

## Key Results

- `toSynGraph`: embeds any `SynObj` as a `SynGraph MLabel`
- `isTree` verified on all test structures
- `compLine` agrees with `onePartChain`
- `angularLocalityOK` (tree, label-based) agrees with `satisfiesAL`
  (graph, index-based) — verified on the critical cross-dimensional
  structure from @cite{adger-2025} p. 95
-/

namespace MereologicalSyntax

-- ════════════════════════════════════════════════════
-- § 1. Size
-- ════════════════════════════════════════════════════

/-- Number of nodes in a `SynObj` tree. -/
def SynObj.size : SynObj → Nat
  | .leaf _ => 1
  | .sub₁ _ one => 1 + one.size
  | .sub₁₂ _ one two => 1 + one.size + two.size

theorem SynObj.size_pos (t : SynObj) : 0 < t.size := by
  cases t <;> simp [size] <;> omega

-- ════════════════════════════════════════════════════
-- § 2. Pre-order Flattening
-- ════════════════════════════════════════════════════

/-- Labels in pre-order traversal. -/
def SynObj.preorderLabels : SynObj → List MLabel
  | .leaf l => [l]
  | .sub₁ l one => l :: one.preorderLabels
  | .sub₁₂ l one two => l :: one.preorderLabels ++ two.preorderLabels

/-- 1-part edges as (parent, child) index pairs. -/
def SynObj.onePartEdges (offset : Nat) : SynObj → List (Nat × Nat)
  | .leaf _ => []
  | .sub₁ _ one =>
    (offset, offset + 1) :: one.onePartEdges (offset + 1)
  | .sub₁₂ _ one two =>
    (offset, offset + 1) :: one.onePartEdges (offset + 1) ++
    two.onePartEdges (offset + 1 + one.size)

/-- 2-part edges as (parent, child) index pairs. -/
def SynObj.twoPartEdges (offset : Nat) : SynObj → List (Nat × Nat)
  | .leaf _ => []
  | .sub₁ _ one => one.twoPartEdges (offset + 1)
  | .sub₁₂ _ one two =>
    let twoOff := offset + 1 + one.size
    (offset, twoOff) :: one.twoPartEdges (offset + 1) ++ two.twoPartEdges twoOff

-- ════════════════════════════════════════════════════
-- § 3. Embedding
-- ════════════════════════════════════════════════════

/-- Embed a `SynObj` tree into a `SynGraph MLabel`.

    Node indexing follows pre-order: root = 0, then 1-part subtree,
    then 2-part subtree. The result satisfies `isTree` (acyclic,
    in-degree ≤ 1). -/
def SynObj.toSynGraph (t : SynObj) : SynGraph MLabel :=
  let n := t.size
  let labels := t.preorderLabels
  let ones := t.onePartEdges 0
  let twos := t.twoPartEdges 0
  { numNodes := n
    label := λ i => labels.getD i.val .N
    onePart := λ i =>
      match ones.find? (λ p => p.1 == i.val) with
      | some (_, c) => if h : c < n then some ⟨c, h⟩ else none
      | none => none
    twoPart := λ i =>
      match twos.find? (λ p => p.1 == i.val) with
      | some (_, c) => if h : c < n then some ⟨c, h⟩ else none
      | none => none }

-- ════════════════════════════════════════════════════
-- § 4. Graph-Based AL Check (via labels)
-- ════════════════════════════════════════════════════

/-- Angular Locality check via the graph representation: does any node
    with label `l` satisfy `satisfiesAL` for the root (node 0)?

    This is the existential analogue of `satisfiesAL` that operates
    on labels rather than node indices, making it directly comparable
    to the tree-based `angularLocalityOK`. -/
def SynObj.alOK_via_graph (l : MLabel) (t : SynObj) : Bool :=
  let g := t.toSynGraph
  (List.range g.numNodes).any λ i =>
    if h : i < g.numNodes then
      g.label ⟨i, h⟩ == l && g.satisfiesAL ⟨i, h⟩ ⟨0, t.size_pos⟩
    else false

-- ════════════════════════════════════════════════════
-- § 5. Verification
-- ════════════════════════════════════════════════════

section BridgeTests

-- ────────────────────────────────────────────────────
-- (a) Antilocal: C ──1──▶ N
-- ────────────────────────────────────────────────────

private def t_antilocal := SynObj.sub₁ .C (.leaf .N)

theorem antilocal_al_agrees :
    angularLocalityOK .N t_antilocal = t_antilocal.alOK_via_graph .N := by native_decide

theorem antilocal_isTree :
    t_antilocal.toSynGraph.isTree = true := by native_decide

-- ────────────────────────────────────────────────────
-- (b) Rollup: C ──1──▶ T ──1──▶ v ──1──▶ V, v ──2──▶ D
-- ────────────────────────────────────────────────────

private def t_rollup := SynObj.sub₁ .C (.sub₁ .T (.sub₁₂ .v (.leaf .V) (.leaf .D)))

theorem rollup_2part_agrees :
    angularLocalityOK .D t_rollup = t_rollup.alOK_via_graph .D := by native_decide

theorem rollup_1part_agrees :
    angularLocalityOK .V t_rollup = t_rollup.alOK_via_graph .V := by native_decide

theorem rollup_isTree :
    t_rollup.toSynGraph.isTree = true := by native_decide

theorem rollup_compLine :
    t_rollup.compLine =
    t_rollup.toSynGraph.onePartChain ⟨0, t_rollup.size_pos⟩ := by native_decide

-- ────────────────────────────────────────────────────
-- (c) Cross-dimensional (@cite{adger-2025} p. 95)
--     C ──1──▶ T ──1──▶ V,  T ──2──▶ v ──1──▶ N,  v ──2──▶ D
--
--     D (within dim-2) CAN subjoin to C.
--     N (cross-dim: N <₁ v <₂ T) CANNOT subjoin to C.
--     This is the critical test that the corrected AL gets right.
-- ────────────────────────────────────────────────────

private def t_crossdim := SynObj.sub₁ .C
  (.sub₁₂ .T (.leaf .V) (.sub₁₂ .v (.leaf .N) (.leaf .D)))

theorem crossdim_allows_agrees :
    angularLocalityOK .D t_crossdim = t_crossdim.alOK_via_graph .D := by native_decide

theorem crossdim_blocks_agrees :
    angularLocalityOK .N t_crossdim = t_crossdim.alOK_via_graph .N := by native_decide

theorem crossdim_isTree :
    t_crossdim.toSynGraph.isTree = true := by native_decide

theorem crossdim_compLine :
    t_crossdim.compLine =
    t_crossdim.toSynGraph.onePartChain ⟨0, t_crossdim.size_pos⟩ := by native_decide

-- ────────────────────────────────────────────────────
-- (d) Classifier structure: D ──1──▶ Cl ──1──▶ N
-- ────────────────────────────────────────────────────

private def t_classifier := SynObj.sub₁ .D (.sub₁ .Cl (.leaf .N))

theorem classifier_compLine :
    t_classifier.compLine =
    t_classifier.toSynGraph.onePartChain ⟨0, t_classifier.size_pos⟩ := by native_decide

theorem classifier_isTree :
    t_classifier.toSynGraph.isTree = true := by native_decide

end BridgeTests

-- ════════════════════════════════════════════════════
-- § 6. General Agreement
-- ════════════════════════════════════════════════════

/-- The tree-based Angular Locality check agrees with the graph-based
    version on all `SynObj` trees: `angularLocalityOK l t` returns
    the same answer as the existential check "does any node with label
    `l` satisfy `satisfiesAL` in the embedded graph?"

    TODO: proof by induction on `SynObj`, showing that the pre-order
    embedding preserves within-dimension chains. -/
theorem al_bridge (t : SynObj) (l : MLabel) :
    angularLocalityOK l t = t.alOK_via_graph l := by sorry

end MereologicalSyntax
