import Linglib.Theories.Syntax.DependencyGrammar.Core.Basic

/-!
# Mildly Non-Projective Dependency Structures

Formalizes the structural theory of non-projectivity from:

- Kuhlmann & Nivre (2006). Mildly Non-Projective Dependency Structures.
  COLING/ACL 2006, pp. 507–514.
- Kuhlmann (2013). Mildly Non-Projective Dependency Grammar.
  Computational Linguistics 39(2):355–387.
- Müller (2013). Unifying Everything. Language 89(4):920–950.
- Hudson (1984, 1990, 2007). Word Grammar.

## Core Concepts

Five structural constraints on dependency trees, ordered by restrictiveness:

    projective ⊂ planar ⊂ well-nested ⊂ unrestricted

- **Projective**: every projection is an interval (gap degree 0, block-degree 1)
- **Planar**: no edges cross when drawn above the sentence
- **Well-nested**: no two disjoint subtrees interleave
- **Gap degree**: max number of discontinuities in any node's projection
- **Block-degree**: max number of contiguous blocks (= gap degree + 1 = LCFRS fan-out)
- **Edge degree**: max number of non-dominated components spanned by any edge

## Key Results

- Well-nestedness + gap degree ≤ 1 covers 99.89% of PDT and DDT (K&N 2006 Table 1)
- Block-degree = fan-out of extracted LCFRS grammar (Kuhlmann 2013, §7.3)
- Bounded block-degree + well-nestedness → polynomial parsing (Kuhlmann 2013, Lemma 10)

## Bridges

- → `Core/Basic.lean`: `projection`, `isProjective`, `gaps`, `blocks`, `gapDegreeAt`, `blockDegreeAt`
- → `Catena.lean`: blocks are special catenae (contiguous, connected)
- → `Discontinuity.lean`: risen catenae witness non-projectivity
- → `DependencyLength.lean`: non-projective orderings tend to longer dep length
-/

namespace DepGrammar

-- ============================================================================
-- §1: Arc-Crossing Detection
-- ============================================================================

/-- Two dependencies cross iff their spans overlap without containment.
    (Kuhlmann & Nivre 2006, implicit in Definition 4) -/
def depsCross (d1 d2 : Dependency) : Bool :=
  if d1 == d2 then false
  else if d1.headIdx == d2.headIdx then false
  else
    let (min1, max1) := (min d1.headIdx d1.depIdx, max d1.headIdx d1.depIdx)
    let (min2, max2) := (min d2.headIdx d2.depIdx, max d2.headIdx d2.depIdx)
    ¬(max1 <= min2 || max2 <= min1 ||
      (min1 <= min2 && max2 <= max1) ||
      (min2 <= min1 && max1 <= max2))

/-- All non-projective (crossing) dependencies in a tree. -/
def nonProjectiveDeps (t : DepTree) : List Dependency :=
  t.deps.filter λ d1 => t.deps.any λ d2 => depsCross d1 d2

/-- Whether a specific dependency crosses other arcs in the tree. -/
def isNonProjectiveDep (t : DepTree) (d : Dependency) : Bool :=
  t.deps.any λ d2 => depsCross d d2

/-- Whether a tree has any non-projective dependencies. -/
def hasFillerGap (t : DepTree) : Bool :=
  (nonProjectiveDeps t).length > 0

-- ============================================================================
-- §2: Filler-Gap Dependencies
-- ============================================================================

/-- A filler-gap dependency is a non-projective dependency modelling extraction.

In DG, wh-fronting creates crossing arcs — the analogue of:
- Minimalism: Internal Merge (movement)
- HPSG: SLASH feature propagation + Head-Filler discharge
- CCG: function composition for extraction -/
structure FillerGapDep where
  dep : Dependency
  tree : DepTree
  inTree : dep ∈ tree.deps
  nonProj : isNonProjectiveDep tree dep = true

-- ============================================================================
-- §3: Planarity (Kuhlmann & Nivre 2006, Definition 4)
-- ============================================================================

/-- Whether two positions are linked by an edge (in either direction). -/
def linked (deps : List Dependency) (a b : Nat) : Bool :=
  deps.any λ d =>
    (d.headIdx == a && d.depIdx == b) || (d.headIdx == b && d.depIdx == a)

/-- A dependency tree is **planar** if its edges can be drawn above the
    sentence without crossing. Formally: no nodes a < b < c < d with
    linked(a,c) ∧ linked(b,d).

    (Kuhlmann & Nivre 2006, Definition 4; traced to Mel'čuk 1988) -/
def DepTree.isPlanar (t : DepTree) : Bool :=
  let deps := t.deps
  let n := t.words.length
  !(List.range n |>.any λ a =>
    List.range n |>.any λ b =>
      List.range n |>.any λ c =>
        List.range n |>.any λ d =>
          a < b && b < c && c < d && linked deps a c && linked deps b d)

-- ============================================================================
-- §4: Well-Nestedness (Kuhlmann & Nivre 2006, Definition 8;
--     Kuhlmann 2013, §8.1)
-- ============================================================================

/-- Two subtrees **interleave** if there exist nodes l₁, r₁ in T₁ and
    l₂, r₂ in T₂ such that l₁ < l₂ < r₁ < r₂.
    (Kuhlmann & Nivre 2006, Definition 8) -/
def projectionsInterleave (p1 p2 : List Nat) : Bool :=
  p1.any λ l1 => p2.any λ l2 => p1.any λ r1 => p2.any λ r2 =>
    l1 < l2 && l2 < r1 && r1 < r2

/-- Two nodes are **disjoint** if neither dominates the other — i.e.,
    neither appears in the other's projection. -/
def disjoint (deps : List Dependency) (u v : Nat) : Bool :=
  let pu := projection deps u
  let pv := projection deps v
  !(pu.contains v) && !(pv.contains u)

/-- A dependency tree is **well-nested** if no two disjoint subtrees interleave.
    (Kuhlmann & Nivre 2006, Definition 8)

    Equivalent to: no sibling nodes u, v have blocks ū₁, ū₂ of u and
    v̄₁, v̄₂ of v such that ū₁ < v̄₁ < ū₂ < v̄₂ (Kuhlmann 2013, Lemma 9). -/
def DepTree.isWellNested (t : DepTree) : Bool :=
  let deps := t.deps
  let n := t.words.length
  !(List.range n |>.any λ u =>
    List.range n |>.any λ v =>
      u != v && disjoint deps u v &&
      projectionsInterleave (projection deps u) (projection deps v))

-- ============================================================================
-- §5: Edge Degree (Kuhlmann & Nivre 2006, Definition 9)
-- ============================================================================

/-- The **span** of an edge (i, j): the interval [min(i,j), max(i,j)].
    (Kuhlmann & Nivre 2006, §3.3) -/
def edgeSpan (d : Dependency) : List Nat :=
  let lo := min d.headIdx d.depIdx
  let hi := max d.headIdx d.depIdx
  List.range (hi - lo + 1) |>.map (· + lo)

/-- Find the root of a node's connected component by following head edges upward.
    Returns the highest ancestor reachable. -/
private def findRoot (deps : List Dependency) (node : Nat) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => node
  | fuel' + 1 =>
    match deps.find? (·.depIdx == node) with
    | some d => findRoot deps d.headIdx fuel'
    | none => node

/-- The **degree** of an edge e: the number of connected components in the
    subgraph induced by span(e) whose root is NOT dominated by head(e).
    (Kuhlmann & Nivre 2006, Definition 9)

    Edge degree measures intervening "foreign" material within an arc's span. -/
def edgeDegreeOf (deps : List Dependency) (d : Dependency) (fuel : Nat) : Nat :=
  let spanNodes := edgeSpan d
  let headProj := projection deps d.headIdx
  -- For each node in the span that has no incoming edge from within the span
  -- (i.e., is a local root), check if it's dominated by the head of d
  let localRoots := spanNodes.filter λ node =>
    node != d.headIdx && node != d.depIdx &&
    !(deps.any λ dep => dep.depIdx == node && spanNodes.contains dep.headIdx)
  -- Count those whose root is NOT in the head's projection
  localRoots.filter (λ node =>
    let root := findRoot deps node fuel
    !(headProj.contains root)
  ) |>.length

/-- **Edge degree** of a tree: max edge degree over all edges.
    (Kuhlmann & Nivre 2006, Definition 9)
    Edge degree 0 ⟺ projective. -/
def DepTree.edgeDegree (t : DepTree) : Nat :=
  let fuel := t.words.length + 1
  t.deps.map (edgeDegreeOf t.deps · fuel) |>.foldl max 0

-- ============================================================================
-- §6: Well-Formedness
-- ============================================================================

/-- Relaxed well-formedness allowing non-projective dependencies.
    Drops the projectivity constraint from `isWellFormed`. -/
def isWellFormedNonProj (t : DepTree) : Bool :=
  hasUniqueHeads t &&
  isAcyclic t &&
  checkSubjVerbAgr t &&
  checkDetNounAgr t &&
  checkVerbSubcat t

/-- Non-projective well-formedness implies unique heads and acyclicity. -/
theorem nonProj_implies_structural (t : DepTree) :
    isWellFormedNonProj t = true →
    hasUniqueHeads t = true ∧ isAcyclic t = true := by
  intro h
  unfold isWellFormedNonProj at h
  revert h
  cases hasUniqueHeads t <;> cases isAcyclic t <;> simp [Bool.and]

/-- Projective well-formedness implies non-projective well-formedness. -/
theorem projective_implies_nonProj_wf (t : DepTree) :
    isWellFormed t = true → isWellFormedNonProj t = true := by
  unfold isWellFormed isWellFormedNonProj
  intro h; revert h
  cases hasUniqueHeads t <;> cases isAcyclic t <;> cases isProjective t <;>
    cases checkSubjVerbAgr t <;> cases checkDetNounAgr t <;> cases checkVerbSubcat t <;>
    simp [Bool.and]

-- ============================================================================
-- §7: Example Trees from Kuhlmann & Nivre (2006)
-- ============================================================================

/-! ### Figure 3 examples: gap degree, edge degree, well-nestedness -/

/-- K&N 2006 Figure 3a: gd=0, ed=0, well-nested.
    6 nodes, edges form nested (projective) structure.
         j(0) ← 4(root)
         i(1) ← 0
         2 ← 1, 3 ← 1, 4 ← 1 → 5 -/
def kn_fig3a : DepTree :=
  { words := List.replicate 6 (Word.mk' "_" .NOUN)
    deps := [ ⟨4, 0, .dep⟩, ⟨0, 1, .dep⟩
            , ⟨1, 2, .dep⟩, ⟨1, 3, .dep⟩, ⟨1, 4, .dep⟩ ]
    rootIdx := 5 }

/-- K&N 2006 Figure 3b: gd=1, ed=1, well-nested.
    Node i has projection [2, 3, 6] — one gap at (3, 6).
    1 ← 0(root), 2 ← 1, 3 ← 2, 4 ← 1 → 5, 2 → 6 -/
def kn_fig3b : DepTree :=
  { words := List.replicate 7 (Word.mk' "_" .NOUN)
    deps := [ ⟨0, 1, .dep⟩, ⟨1, 2, .dep⟩, ⟨2, 3, .dep⟩
            , ⟨1, 4, .dep⟩, ⟨4, 5, .dep⟩, ⟨2, 6, .dep⟩ ]
    rootIdx := 0 }

/-- K&N 2006 Figure 3c: gd=2, ed=1, NOT well-nested.
    Nodes i and j have interleaving projections.
    i at 1: projection includes {2, 4}; j at 2: includes {3, 5}
    These interleave: 2 < 3 < 4 < 5. -/
def kn_fig3c : DepTree :=
  { words := List.replicate 7 (Word.mk' "_" .NOUN)
    deps := [ ⟨0, 1, .dep⟩, ⟨0, 2, .dep⟩, ⟨1, 3, .dep⟩
            , ⟨2, 4, .dep⟩, ⟨1, 5, .dep⟩, ⟨2, 6, .dep⟩ ]
    rootIdx := 0 }

/-- Minimal crossing tree: arcs 0→2 and 1→3 cross. -/
def nonProjectiveTree : DepTree :=
  { words := [ ⟨"A", .NOUN, {}⟩, ⟨"B", .VERB, {}⟩, ⟨"C", .NOUN, {}⟩, ⟨"D", .VERB, {}⟩ ]
    deps := [ ⟨0, 2, .obj⟩, ⟨1, 3, .obj⟩ ]
    rootIdx := 0 }

/-! ### Cross-serial dependencies (Kuhlmann 2013, Figure 1)

The canonical motivation for non-projectivity. In Dutch, verb–argument
dependencies cross ("cross-serial"), producing a non-projective tree.
In German, the same dependencies nest, producing a projective tree.

Dutch: dat Jan₁ Piet₂ Marie₃ zag₁ helpen₂ lezen₃
German: dass Jan₁ Piet₂ Marie₃ lesen₃ helfen₂ sah₁ -/

/-- Dutch cross-serial: "dat Jan Piet Marie zag helpen lezen"
    Dependencies: zag→Jan, helpen→Piet, lezen→Marie
    These cross: zag(4)→Jan(1) spans helpen(5)→Piet(2). -/
def dutchCrossSerial : DepTree :=
  { words := [ Word.mk' "dat" .SCONJ, Word.mk' "Jan" .PROPN
             , Word.mk' "Piet" .PROPN, Word.mk' "Marie" .PROPN
             , Word.mk' "zag" .VERB, Word.mk' "helpen" .VERB
             , Word.mk' "lezen" .VERB ]
    deps := [ ⟨0, 4, .dep⟩       -- dat → zag
            , ⟨4, 1, .nsubj⟩     -- zag ← Jan
            , ⟨4, 5, .xcomp⟩     -- zag → helpen
            , ⟨5, 2, .nsubj⟩     -- helpen ← Piet
            , ⟨5, 6, .xcomp⟩     -- helpen → lezen
            , ⟨6, 3, .nsubj⟩     -- lezen ← Marie
            ]
    rootIdx := 0 }

/-- German nested: "dass Jan Piet Marie lesen helfen sah"
    Same dependencies, but verbs are in reverse order → nested, projective. -/
def germanNested : DepTree :=
  { words := [ Word.mk' "dass" .SCONJ, Word.mk' "Jan" .PROPN
             , Word.mk' "Piet" .PROPN, Word.mk' "Marie" .PROPN
             , Word.mk' "lesen" .VERB, Word.mk' "helfen" .VERB
             , Word.mk' "sah" .VERB ]
    deps := [ ⟨0, 6, .dep⟩       -- dass → sah
            , ⟨6, 1, .nsubj⟩     -- sah ← Jan
            , ⟨6, 5, .xcomp⟩     -- sah → helfen
            , ⟨5, 2, .nsubj⟩     -- helfen ← Piet
            , ⟨5, 4, .xcomp⟩     -- helfen → lesen
            , ⟨4, 3, .nsubj⟩     -- lesen ← Marie
            ]
    rootIdx := 0 }

-- ============================================================================
-- §8: Verified Properties
-- ============================================================================

/-! ### Projectivity -/

example : isProjective nonProjectiveTree = false := by native_decide
example : hasFillerGap nonProjectiveTree = true := by native_decide
example : isProjective dutchCrossSerial = false := by native_decide
example : isProjective germanNested = true := by native_decide

/-! ### Gap degree and block-degree (Core/Basic.lean) -/

example : DepTree.gapDegree germanNested = 0 := by native_decide
example : DepTree.blockDegree germanNested = 1 := by native_decide

example : DepTree.gapDegree dutchCrossSerial = 1 := by native_decide
example : DepTree.blockDegree dutchCrossSerial = 2 := by native_decide

example : DepTree.gapDegree nonProjectiveTree = 1 := by native_decide
example : DepTree.blockDegree nonProjectiveTree = 2 := by native_decide

/-! ### Planarity -/

/-- German nested is planar (no crossing edges). -/
example : DepTree.isPlanar germanNested = true := by native_decide

/-- Dutch cross-serial is NOT planar (verb-argument edges cross). -/
example : DepTree.isPlanar dutchCrossSerial = false := by native_decide

/-- The minimal crossing tree is NOT planar. -/
example : DepTree.isPlanar nonProjectiveTree = false := by native_decide

/-! ### Well-nestedness -/

/-- German nested is well-nested. -/
example : DepTree.isWellNested germanNested = true := by native_decide

/-- Dutch cross-serial: well-nested despite being non-projective.
    The subtrees don't interleave because each verb dominates its argument. -/
example : DepTree.isWellNested dutchCrossSerial = true := by native_decide

/-- The minimal crossing tree is NOT well-nested: subtrees {0,2} and {1,3}
    interleave (0 < 1 < 2 < 3). -/
example : DepTree.isWellNested nonProjectiveTree = false := by native_decide

-- ============================================================================
-- §9: Hierarchy Theorems
-- ============================================================================

/-- **Projective ⟺ gap degree 0**: a tree is projective iff no node's
    projection has any gaps.
    (Kuhlmann & Nivre 2006, Definition 3 + Definition 7) -/
theorem projective_iff_gapDegree_zero (t : DepTree) :
    isProjective t = true ↔ t.gapDegree = 0 := by
  unfold isProjective DepTree.gapDegree
  constructor
  · -- Forward: all isInterval → gapDegree = 0
    intro hall
    rw [foldl_max_zero_iff]
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    unfold gapDegreeAt
    have hiv : isInterval (projection t.deps i) = true := by
      rw [List.all_eq_true] at hall
      exact hall i hi
    have := (isInterval_iff_gaps_nil _ (projection_chain' _ _)).mp hiv
    simp [this]
  · -- Backward: gapDegree = 0 → all isInterval
    intro hzero
    rw [foldl_max_zero_iff] at hzero
    rw [List.all_eq_true]
    intro i hi
    rw [(isInterval_iff_gaps_nil _ (projection_chain' _ _))]
    have := hzero (gapDegreeAt t.deps i)
      (List.mem_map.mpr ⟨i, hi, rfl⟩)
    unfold gapDegreeAt at this
    exact List.eq_nil_of_length_eq_zero this

/-- **Projective ⟺ block-degree 1**: every node has exactly one block.
    (Kuhlmann 2013, §7.1)
    Requires at least one word (blockDegree of empty tree is 0, not 1).

    Proof: projective ↔ gap degree 0 (Theorem 1). When gap degree = 0,
    every gapDegreeAt = 0, so by blocks_length = gaps_length + 1,
    every blockDegreeAt = 1, so foldl max 0 = 1. -/
theorem projective_iff_blockDegree_one (t : DepTree)
    (hne_tree : t.words.length > 0) :
    isProjective t = true ↔ t.blockDegree = 1 := by
  rw [projective_iff_gapDegree_zero]
  unfold DepTree.gapDegree DepTree.blockDegree
  constructor
  · -- gapDegree = 0 → blockDegree = 1
    intro hgap
    have hall_gap : ∀ x ∈ (List.range t.words.length).map (gapDegreeAt t.deps), x = 0 :=
      (foldl_max_zero_iff _).mp hgap
    -- Every blockDegreeAt = 1
    have hall_block : ∀ x ∈ (List.range t.words.length).map (blockDegreeAt t.deps), x = 1 := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have hgap_i : gapDegreeAt t.deps i = 0 :=
        hall_gap _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
      unfold blockDegreeAt gapDegreeAt at *
      rw [blocks_length_eq_gaps_length_succ _ (projection_nonempty t.deps i)
          (projection_chain' t.deps i)]
      omega
    -- foldl max 0 of all-1 nonempty list = 1
    have hne : (List.range t.words.length).map (blockDegreeAt t.deps) ≠ [] := by
      intro h
      have h1 : ((List.range t.words.length).map (blockDegreeAt t.deps)).length = 0 := by
        rw [h]; rfl
      simp only [List.length_map, List.length_range] at h1
      exact absurd h1 (by omega)
    exact foldl_max_const _ 1 hne hall_block
  · -- blockDegree = 1 → gapDegree = 0
    intro hblock
    rw [foldl_max_zero_iff]
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    -- blockDegreeAt i ≤ 1 (since max is 1)
    have hblock_bound : blockDegreeAt t.deps i ≤ 1 := by
      have hmem : blockDegreeAt t.deps i ∈
          (List.range t.words.length).map (blockDegreeAt t.deps) :=
        List.mem_map.mpr ⟨i, hi, rfl⟩
      have hge := foldl_max_ge_mem _ 0 _ hmem
      omega
    unfold blockDegreeAt gapDegreeAt at *
    rw [blocks_length_eq_gaps_length_succ _ (projection_nonempty t.deps i)
        (projection_chain' t.deps i)] at hblock_bound
    omega

/-- **Block-degree = gap degree + 1** for non-empty projections.
    (Kuhlmann 2013, §7.1 footnote 2) -/
theorem blockDegree_eq_gapDegree_succ (deps : List Dependency) (root : Nat) :
    blockDegreeAt deps root = gapDegreeAt deps root + 1 := by
  unfold blockDegreeAt gapDegreeAt
  exact blocks_length_eq_gaps_length_succ
    (projection deps root) (projection_nonempty deps root)
    (projection_chain' deps root)

/-- From `linked = true`, extract the witnessing edge and direction. -/
private theorem linked_exists {deps : List Dependency} {a c : Nat}
    (h : linked deps a c = true) :
    ∃ e ∈ deps, (e.headIdx = a ∧ e.depIdx = c) ∨ (e.headIdx = c ∧ e.depIdx = a) := by
  simp only [linked, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true,
             beq_iff_eq] at h
  obtain ⟨e, he_mem, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ := h
  · exact ⟨e, he_mem, Or.inl ⟨h1, h2⟩⟩
  · exact ⟨e, he_mem, Or.inr ⟨h1, h2⟩⟩

/-- From `isProjective = true`, the projection of any node in range is an interval. -/
private theorem projective_interval {t : DepTree} (hproj : isProjective t = true)
    (i : Nat) (hi : i < t.words.length) :
    isInterval (projection t.deps i) = true := by
  simp only [isProjective, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hproj
  exact hproj i hi

/-- From `hasUniqueHeads = true`, if a node c has any incoming edge, then
    all incoming edges have the same head. (The edge existence implies
    c ≠ root, since root has in-degree 0 under `hasUniqueHeads`.) -/
private theorem unique_parent_of_hasUniqueHeads {t : DepTree}
    (hwf : hasUniqueHeads t = true) {c : Nat} (hc : c < t.words.length)
    {e₁ e₂ : Dependency} (he₁ : e₁ ∈ t.deps) (he₂ : e₂ ∈ t.deps)
    (hd₁ : e₁.depIdx = c) (hd₂ : e₂.depIdx = c) :
    e₁.headIdx = e₂.headIdx := by
  -- Both edges are in the filter for c
  have hf₁ : e₁ ∈ t.deps.filter (·.depIdx == c) :=
    List.mem_filter.mpr ⟨he₁, beq_iff_eq.mpr hd₁⟩
  have hf₂ : e₂ ∈ t.deps.filter (·.depIdx == c) :=
    List.mem_filter.mpr ⟨he₂, beq_iff_eq.mpr hd₂⟩
  -- Extract from hasUniqueHeads: if c = root then count = 0 else count = 1
  have hspec : (if c = t.rootIdx then
      (t.deps.filter (·.depIdx == c)).length == 0
    else (t.deps.filter (·.depIdx == c)).length == 1) = true := by
    have hwf' := hwf
    unfold hasUniqueHeads at hwf'
    have hmem : (c, (t.deps.filter (·.depIdx == c)).length) ∈
        (List.range ((List.range t.words.length |>.map fun i =>
          (t.deps.filter (·.depIdx == i)).length).length)).zip
          (List.range t.words.length |>.map fun i =>
            (t.deps.filter (·.depIdx == i)).length) := by
      rw [List.mem_iff_getElem]
      simp only [List.length_zip, List.length_range, List.length_map]
      exact ⟨c, by omega, by simp [List.getElem_zip, List.getElem_range, List.getElem_map]⟩
    have h := (List.all_eq_true.mp hwf') _ hmem
    simp only [beq_iff_eq] at h
    exact h
  -- c ≠ rootIdx: root has 0 incoming edges, but e₁ is incoming for c
  have hroot : c ≠ t.rootIdx := by
    intro heq
    rw [if_pos heq, beq_iff_eq] at hspec
    exact absurd hspec (by have := List.length_pos_of_mem hf₁; omega)
  -- Filter has length 1 (non-root node with unique heads)
  rw [if_neg hroot, beq_iff_eq] at hspec
  -- Singleton list: both e₁ and e₂ must equal the single element
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hspec
  rw [hx] at hf₁ hf₂
  rw [List.eq_of_mem_singleton hf₁, List.eq_of_mem_singleton hf₂]

/-- **Projective ⊂ planar** (for well-formed trees): every projective tree
    with unique heads and no cycles is planar.
    (Kuhlmann & Nivre 2006, §3.5: projectivity implies no crossing edges)

    The `hasUniqueHeads` precondition is necessary: without it, a node can
    have two heads, and the resulting multi-headed graph can be projective
    (all projections are intervals) yet non-planar (edges cross).

    **Counterexample without `hasUniqueHeads`**: 4 nodes, edges
    (0,1), (0,2), (1,2), (1,3). Node 2 has two heads (0 and 1).
    All projections are intervals, but linked(0,2) and linked(1,3) cross.

    The `isAcyclic` precondition is necessary: without it, `hasUniqueHeads`
    allows cycles (e.g., edges (1,2),(2,1) with root=0), and the dominance
    antisymmetry argument fails.

    Proof: by contrapositive. If ¬planar, there exist a < b < c < d with
    edges linking a–c and b–d. Each edge endpoint pair shares a projection
    (the head's). Projectivity makes that projection an interval. The interval
    containing {a, c} must contain b; the interval containing {b, d} must
    contain c. With unique heads, `dominates_to_parent` lifts the intermediate
    dominance to the other edge's head, creating a dominance cycle v→w→v.
    By `dominates_antisymm` (acyclicity), v = w, contradicting v < w. -/
theorem projective_implies_planar (t : DepTree)
    (hwf : hasUniqueHeads t = true) (hacyc : isAcyclic t = true)
    (h_dep_wf : ∀ d ∈ t.deps, d.depIdx < t.words.length)
    (hproj : isProjective t = true) : t.isPlanar = true := by
  by_contra h_np
  -- Extract crossing: ∃ a b c d with a < b < c < d, linked edges
  simp only [DepTree.isPlanar] at h_np
  simp at h_np
  obtain ⟨a, ha_lt, b, hb_lt, c, hc_lt, d, hd_lt,
          hab, hbc, hcd, hlink_ac, hlink_bd⟩ := h_np
  -- Extract edges from linked
  obtain ⟨e₁, he₁_mem, he₁_dir⟩ := linked_exists hlink_ac
  obtain ⟨e₂, he₂_mem, he₂_dir⟩ := linked_exists hlink_bd
  -- Helper: from unique_parent, all edges into node have the same head
  have mk_parent : ∀ {node head : Nat}, node < t.words.length →
      ∀ (e_ref : Dependency), e_ref ∈ t.deps → e_ref.headIdx = head →
      e_ref.depIdx = node → ∀ dep ∈ t.deps, dep.depIdx = node → dep.headIdx = head :=
    fun hnode e_ref he_ref_mem hh_ref hd_ref dep hdep hdep_node =>
      (unique_parent_of_hasUniqueHeads hwf hnode he_ref_mem hdep hd_ref hdep_node).symm.trans hh_ref
  -- Case split on head of edge (a,c) × head of edge (b,d)
  rcases he₁_dir with ⟨hh₁, hd₁⟩ | ⟨hh₁, hd₁⟩ <;>
  rcases he₂_dir with ⟨hh₂, hd₂⟩ | ⟨hh₂, hd₂⟩
  · -- Case (head=a, dep=c) × (head=b, dep=d)
    have hc_in_a := child_mem_projection t.deps a c ⟨e₁, he₁_mem, hh₁, hd₁⟩
    have hd_in_b := child_mem_projection t.deps b d ⟨e₂, he₂_mem, hh₂, hd₂⟩
    have hint_a := projective_interval hproj a ha_lt
    have hint_b := projective_interval hproj b hb_lt
    have hb_in_a := interval_mem_between _ (projection_chain' t.deps a) hint_a
      a b c (root_mem_projection t.deps a) hc_in_a hab hbc
    have hc_in_b := interval_mem_between _ (projection_chain' t.deps b) hint_b
      b c d (root_mem_projection t.deps b) hd_in_b hbc hcd
    have h_a_dom_b := dominates_of_mem_projection hb_in_a
    have h_b_dom_c := dominates_of_mem_projection hc_in_b
    have h_c_parent := mk_parent hc_lt e₁ he₁_mem hh₁ hd₁
    have h_b_dom_a := dominates_to_parent h_b_dom_c (Nat.ne_of_lt hbc) h_c_parent
    exact absurd (dominates_antisymm t hwf hacyc h_dep_wf a b h_a_dom_b h_b_dom_a) (Nat.ne_of_lt hab)
  · -- Case (head=a, dep=c) × (head=d, dep=b)
    have hc_in_a := child_mem_projection t.deps a c ⟨e₁, he₁_mem, hh₁, hd₁⟩
    have hb_in_d := child_mem_projection t.deps d b ⟨e₂, he₂_mem, hh₂, hd₂⟩
    have hint_a := projective_interval hproj a ha_lt
    have hint_d := projective_interval hproj d hd_lt
    have hb_in_a := interval_mem_between _ (projection_chain' t.deps a) hint_a
      a b c (root_mem_projection t.deps a) hc_in_a hab hbc
    have hc_in_d := interval_mem_between _ (projection_chain' t.deps d) hint_d
      b c d hb_in_d (root_mem_projection t.deps d) hbc hcd
    have h_a_dom_b := dominates_of_mem_projection hb_in_a
    have h_d_dom_c := dominates_of_mem_projection hc_in_d
    have h_c_parent := mk_parent hc_lt e₁ he₁_mem hh₁ hd₁
    have h_b_parent : ∀ dep ∈ t.deps, dep.depIdx = b → dep.headIdx = d :=
      mk_parent hb_lt e₂ he₂_mem hh₂ hd₂
    have h_d_dom_a := dominates_to_parent h_d_dom_c (Nat.ne_of_lt hcd).symm h_c_parent
    have h_a_dom_d := dominates_to_parent h_a_dom_b (Nat.ne_of_lt hab) h_b_parent
    exact absurd (dominates_antisymm t hwf hacyc h_dep_wf a d h_a_dom_d h_d_dom_a)
      (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_trans hab hbc) hcd))
  · -- Case (head=c, dep=a) × (head=b, dep=d)
    have ha_in_c := child_mem_projection t.deps c a ⟨e₁, he₁_mem, hh₁, hd₁⟩
    have hd_in_b := child_mem_projection t.deps b d ⟨e₂, he₂_mem, hh₂, hd₂⟩
    have hint_c := projective_interval hproj c hc_lt
    have hint_b := projective_interval hproj b hb_lt
    have hb_in_c := interval_mem_between _ (projection_chain' t.deps c) hint_c
      a b c ha_in_c (root_mem_projection t.deps c) hab hbc
    have hc_in_b := interval_mem_between _ (projection_chain' t.deps b) hint_b
      b c d (root_mem_projection t.deps b) hd_in_b hbc hcd
    have h_c_dom_b := dominates_of_mem_projection hb_in_c
    have h_b_dom_c := dominates_of_mem_projection hc_in_b
    exact absurd (dominates_antisymm t hwf hacyc h_dep_wf b c h_b_dom_c h_c_dom_b) (Nat.ne_of_lt hbc)
  · -- Case (head=c, dep=a) × (head=d, dep=b)
    have ha_in_c := child_mem_projection t.deps c a ⟨e₁, he₁_mem, hh₁, hd₁⟩
    have hb_in_d := child_mem_projection t.deps d b ⟨e₂, he₂_mem, hh₂, hd₂⟩
    have hint_c := projective_interval hproj c hc_lt
    have hint_d := projective_interval hproj d hd_lt
    have hb_in_c := interval_mem_between _ (projection_chain' t.deps c) hint_c
      a b c ha_in_c (root_mem_projection t.deps c) hab hbc
    have hc_in_d := interval_mem_between _ (projection_chain' t.deps d) hint_d
      b c d hb_in_d (root_mem_projection t.deps d) hbc hcd
    have h_c_dom_b := dominates_of_mem_projection hb_in_c
    have h_d_dom_c := dominates_of_mem_projection hc_in_d
    have h_b_parent : ∀ dep ∈ t.deps, dep.depIdx = b → dep.headIdx = d :=
      mk_parent hb_lt e₂ he₂_mem hh₂ hd₂
    have h_c_dom_d := dominates_to_parent h_c_dom_b (Nat.ne_of_lt hbc).symm h_b_parent
    exact absurd (dominates_antisymm t hwf hacyc h_dep_wf c d h_c_dom_d h_d_dom_c) (Nat.ne_of_lt hcd)

/-- **Planar ⊂ well-nested** (for well-formed trees): every planar tree
    with unique heads is well-nested.
    (Kuhlmann & Nivre 2006, §3.5)

    The `hasUniqueHeads` precondition ensures the dependency structure is
    a tree, so that disjoint nodes have disjoint projections.

    TODO: Proof by contrapositive. If ¬wellNested, extract disjoint nodes
    u, v with interleaving projections: l₁ ∈ π(u), l₂ ∈ π(v), r₁ ∈ π(u),
    r₂ ∈ π(v) with l₁ < l₂ < r₁ < r₂. With unique heads + acyclicity,
    projections of disjoint nodes are disjoint sets (if x ∈ π(u) ∩ π(v),
    the unique parent chain from x reaches both u and v, so one dominates
    the other, contradicting disjointness). Then show ¬isPlanar by finding
    two crossing edges from π(u) and π(v). This requires:
    1. `projection_disjoint_of_disjoint`: π(u) ∩ π(v) = ∅ when disjoint
       (provable via `dominates_iterParent_uh` + `iterParent_add_uh`)
    2. Connectivity of projections: if a, b ∈ π(u), there exists a path
       a → ... → b within π(u) (chain of parent-child edges)
    3. Discrete IVT: on a path within π(u) from l₁ to r₁, since l₂ ∉ π(u)
       and l₁ < l₂ < r₁, some edge (x, y) has x < l₂ < y. Similarly for
       π(v) and r₁. The two spanning edges must cross.
    Infrastructure (2) and (3) require formalizing undirected tree paths,
    which is not yet available. -/
theorem planar_implies_wellNested (t : DepTree)
    (hwf : hasUniqueHeads t = true) (hacyc : isAcyclic t = true)
    (h_dep_wf : ∀ d ∈ t.deps, d.depIdx < t.words.length)
    (h : t.isPlanar = true) : t.isWellNested = true := by
  sorry

/-- Dutch cross-serial witnesses the gap: non-projective yet well-nested.
    (Kuhlmann & Nivre 2006, §4: 99.89% of treebank data is well-nested) -/
theorem wellNested_not_projective_witness :
    DepTree.isWellNested dutchCrossSerial = true ∧
    isProjective dutchCrossSerial = false := by
  exact ⟨by native_decide, by native_decide⟩

/-- The minimal crossing tree witnesses: not well-nested and not planar. -/
theorem not_wellNested_witness :
    DepTree.isWellNested nonProjectiveTree = false ∧
    DepTree.isPlanar nonProjectiveTree = false := by
  exact ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- §10: Bridge Theorems
-- ============================================================================

/-- Non-projective dependencies → gap degree ≥ 1.
    Contrapositive of `projective_iff_gapDegree_zero`. -/
theorem nonProjective_implies_gapDeg_ge1 (t : DepTree)
    (h : isProjective t = false) : t.gapDegree ≥ 1 := by
  by_contra hlt
  have hzero : t.gapDegree = 0 := by omega
  have := (projective_iff_gapDegree_zero t).mpr hzero
  simp [this] at h

/-- Dutch cross-serial is non-projective but well-nested with gap degree 1.
    This exemplifies K&N's key finding: the vast majority of non-projective
    structures in treebanks are well-nested with low gap degree. -/
theorem dutch_mildly_nonProjective :
    isProjective dutchCrossSerial = false ∧
    DepTree.isWellNested dutchCrossSerial = true ∧
    DepTree.gapDegree dutchCrossSerial = 1 := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- German nested is fully projective (gap degree 0), confirming that
    the nested verb order avoids crossing dependencies. -/
theorem german_fully_projective :
    isProjective germanNested = true ∧
    DepTree.gapDegree germanNested = 0 := by
  exact ⟨by native_decide, by native_decide⟩

end DepGrammar
