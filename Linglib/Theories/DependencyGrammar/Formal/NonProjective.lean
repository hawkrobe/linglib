import Linglib.Theories.DependencyGrammar.Core.Basic
import Linglib.Phenomena.NonProjectivity.Data

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

/-- The minimal crossing tree is well-nested (gap degree 1, no interleaving
    because the two subtrees {0,2} and {1,3} do interleave: 0 < 1 < 2 < 3.
    Actually this IS interleaving — let's verify. -/
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
theorem blockDegree_eq_gapDegree_succ (deps : List Dependency) (root : Nat)
    (h : (projection deps root).length > 0) :
    blockDegreeAt deps root = gapDegreeAt deps root + 1 := by
  unfold blockDegreeAt gapDegreeAt
  have hne : projection deps root ≠ [] := by
    intro heq; simp [heq] at h
  exact blocks_length_eq_gaps_length_succ
    (projection deps root) hne (projection_chain' deps root)

/-- **Projective ⊂ planar**: every projective tree is planar.
    (Kuhlmann & Nivre 2006, §3.5: projectivity implies no crossing edges)

    Proof approach: if d₁ = (a, c) and d₂ = (b, d) with a < b < c < d cross,
    then b is in π(a) but not adjacent to a's other dependents — contradicting
    that π(a) is an interval containing both a and c but not all of [a..c].
    Formalizing this requires relating edge spans to projection membership. -/
theorem projective_implies_planar (t : DepTree)
    (h : isProjective t = true) : t.isPlanar = true := by
  sorry -- TODO: requires edge_in_projection lemma linking deps to projections

/-- **Planar ⊂ well-nested**: every planar tree is well-nested.
    A graph with interleaving subtrees cannot be drawn without crossing edges.
    (Kuhlmann & Nivre 2006, §3.5)

    Proof approach: if π(u) and π(v) interleave with l₁ < l₂ < r₁ < r₂,
    there must be edges on the path from l₂ to v and from r₁ to u that cross,
    contradicting planarity. -/
theorem planar_implies_wellNested (t : DepTree)
    (h : t.isPlanar = true) : t.isWellNested = true := by
  sorry -- TODO: requires projection_subset lemma relating dominance to projection

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
-- §10: Empirical Data Verification
-- (Data in Phenomena/NonProjectivity/Data.lean)
-- ============================================================================

/-- Well-nestedness covers ≥99% of both treebanks (K&N 2006 Table 1). -/
theorem wellNested_near_universal :
    Phenomena.pdt.wellNested ≥ 9900 ∧ Phenomena.ddt.wellNested ≥ 9900 := by
  exact ⟨by native_decide, by native_decide⟩

/-- Gap degree ≤ 1 covers ≥99% of both treebanks. -/
theorem gapDeg_leq1_sufficient :
    Phenomena.pdt.gapDeg0 + Phenomena.pdt.gapDeg1 ≥ 9900 ∧
    Phenomena.ddt.gapDeg0 + Phenomena.ddt.gapDeg1 ≥ 9900 := by
  exact ⟨by native_decide, by native_decide⟩

/-- Planarity covers far less than well-nestedness. -/
theorem planarity_insufficient :
    Phenomena.pdt.planar < Phenomena.pdt.wellNested ∧
    Phenomena.ddt.planar < Phenomena.ddt.wellNested := by
  exact ⟨by native_decide, by native_decide⟩

/-- Fan-out ≤ 2 (block-degree ≤ 2) loses very few trees across all languages
    (Kuhlmann 2013 Tables 3-4). -/
theorem fanout2_good_coverage :
    Phenomena.arabic.treesLostFanout2 ≤ 1 ∧
    Phenomena.czech.treesLostFanout2 * 100 / Phenomena.czech.totalTrees < 1 ∧
    Phenomena.danish.treesLostFanout2 * 100 / Phenomena.danish.totalTrees < 1 ∧
    Phenomena.slovene.treesLostFanout2 * 100 / Phenomena.slovene.totalTrees < 1 ∧
    Phenomena.turkish.treesLostFanout2 * 100 / Phenomena.turkish.totalTrees < 1 := by
  exact ⟨by native_decide, by native_decide, by native_decide,
         by native_decide, by native_decide⟩

-- ============================================================================
-- §12: Bridge Theorems
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
