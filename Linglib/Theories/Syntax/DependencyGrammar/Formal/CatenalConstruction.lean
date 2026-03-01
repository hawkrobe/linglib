import Linglib.Theories.Syntax.DependencyGrammar.Formal.Catena
import Linglib.Theories.Syntax.ConstructionGrammar.Basic

/-!
# Catenal Construction: CxG ↔ DG Bridge Type @cite{osborne-gross-2012}

Defines the `CatenalCx` type — the fundamental bridge between Construction
Grammar and Dependency Grammar. A catenal construction pairs a CxG
`Construction` (form–meaning description) with a DG catena witness
(dependency tree + connected node set).

Osborne & Groß (2012) argue that every construction corresponds to a catena.
This type makes that claim checkable: to instantiate `CatenalCx`, one must
provide a `Construction`, a `DepTree`, the relevant node indices, and a
proof that those nodes form a catena.

## Key Definitions

- `CatenalCx`: the bridge structure itself
- `CatenalCx.singleton`: every single word is a trivial catenal construction
- `CatenalCx.isConstituent`: whether the catena is also a constituent
- `CatenalCx.isNonConstituentCatena`: the constructions that *require*
  catena theory — things that constituency cannot capture
- `CatenalCx.isContiguous`: whether the yield is contiguous (non-risen)

## Key Results

- `CatenalCx.nodes_nonempty`: a CatenalCx always has ≥ 1 node
- `CatenalCx.singleton_isSingleWord`: the singleton constructor yields
  a single-word construction
- `constituent_implies_catena`: every constituent is a catena (general
  statement; per-tree instances verified via `native_decide` in the bridge)

Concrete instances and verified claims are in
`Phenomena/Constructions/DG_OsborneGross2012Bridge.lean`.

-/

namespace DepGrammar.CatenalConstruction

open DepGrammar Catena ConstructionGrammar

-- ============================================================================
-- §1: Core Bridge Type
-- ============================================================================

/-- A **catenal construction** (Osborne & Groß 2012): a construction whose
    form-side corresponds to a catena in a dependency tree. This is the
    fundamental bridge type connecting CxG and DG — every construction
    can be witnessed as a catena over some dependency tree.

    The `construction` field carries the CxG description. The `tree`,
    `nodes`, and `catena` fields provide the DG verification: the
    construction's words form a connected subgraph. -/
structure CatenalCx where
  /-- CxG description of the construction -/
  construction : Construction
  /-- A dependency tree instantiating the construction -/
  tree : DepTree
  /-- Node indices that carry the construction -/
  nodes : List Nat
  /-- The construction nodes form a catena -/
  catena : isCatena tree.deps nodes = true

-- ============================================================================
-- §2: Derived Predicates
-- ============================================================================

/-- Number of nodes in the catenal construction. -/
def CatenalCx.nodeCount (cx : CatenalCx) : Nat := cx.nodes.length

/-- Whether the catenal construction is a single word. Single-word
    constructions are always catenae (trivially connected). -/
def CatenalCx.isSingleWord (cx : CatenalCx) : Bool := cx.nodes.length == 1

/-- Whether the catena also forms a constituent (complete subtree rooted at
    some node). When true, the construction can be captured by constituent
    structure; when false, the catena concept is essential. -/
def CatenalCx.isConstituent (cx : CatenalCx) : Bool :=
  Catena.isConstituent cx.tree.deps cx.tree.words.length cx.nodes

/-- Whether the catenal construction is a **non-constituent catena** — the
    case that motivates the entire CxG ↔ DG bridge. These constructions
    cannot be captured by any constituent-based framework: their form-side
    is connected in dependency structure but does not correspond to any
    subtree. Idioms ("spill the beans"), LVCs ("take a bath"), and
    displacement ("beans she spilled") are typical examples. -/
def CatenalCx.isNonConstituentCatena (cx : CatenalCx) : Bool :=
  !cx.isConstituent

/-- Whether the catena's yield is contiguous in linear order. A catena with
    contiguous yield occupies a consecutive span of positions; a non-contiguous
    catena is a **risen catena** (Osborne 2019, Ch 7) — connected in the tree
    but separated by intervening material in the string. -/
def CatenalCx.isContiguous (cx : CatenalCx) : Bool :=
  isInterval (cx.nodes.mergeSort (· ≤ ·))

-- ============================================================================
-- §3: Smart Constructors
-- ============================================================================

/-- Smart constructor: any single word in a tree trivially forms a CatenalCx.
    Uses `singleton_isCatena` — a single node is always connected. -/
def CatenalCx.singleton (cx : Construction) (tree : DepTree) (v : Nat) :
    CatenalCx :=
  { construction := cx
    tree := tree
    nodes := [v]
    catena := singleton_isCatena tree.deps v }

-- ============================================================================
-- §4: Structural Theorems
-- ============================================================================

/-- The node set of a CatenalCx is always non-empty.
    Follows directly from the catena requirement (`isCatena` checks
    `!nodes.isEmpty`). -/
theorem CatenalCx.nodes_nonempty (cx : CatenalCx) : cx.nodes ≠ [] := by
  intro h
  have hc := cx.catena
  rw [isCatena, h] at hc
  exact Bool.noConfusion hc

/-- A singleton CatenalCx is always a single word. -/
theorem CatenalCx.singleton_isSingleWord (cx : Construction) (tree : DepTree)
    (v : Nat) : (CatenalCx.singleton cx tree v).isSingleWord = true := by
  simp [singleton, isSingleWord]

/-- A singleton CatenalCx always has node count 1. -/
theorem CatenalCx.singleton_nodeCount (cx : Construction) (tree : DepTree)
    (v : Nat) : (CatenalCx.singleton cx tree v).nodeCount = 1 := by
  simp [singleton, nodeCount]

/-- A singleton CatenalCx always has contiguous yield (trivially). -/
theorem CatenalCx.singleton_isContiguous (cx : Construction) (tree : DepTree)
    (v : Nat) : (CatenalCx.singleton cx tree v).isContiguous = true := by
  simp [singleton, isContiguous, isInterval]

-- ============================================================================
-- §5: Constituent–Catena Relationship
-- ============================================================================

/-- Lift bidirectional reachability to a superset of allowed nodes. -/
private theorem bidir_lift {deps : List Dependency} {allowed allowed' : List Nat}
    {u v : Nat} (hsub : ∀ x, x ∈ allowed → x ∈ allowed')
    (h : BidirReachable deps allowed u v) :
    BidirReachable deps allowed' u v := by
  induction h with
  | here w hw => exact .here w (hsub w hw)
  | step a b _ ha hb hedge _ ih =>
    exact .step a b _ (hsub a ha) (hsub b hb) hedge ih

/-- If `Dominates deps root x`, then `x` is bidirectionally reachable from
    `root` within `projection deps root`. -/
private theorem bidir_of_dominates (deps : List Dependency) (root x : Nat)
    (hdom : Dominates deps root x) :
    BidirReachable deps (projection deps root) root x := by
  induction hdom with
  | refl v => exact .here v (root_mem_projection deps v)
  | step v w _ hedge hdomWX ih =>
    -- ih is about (projection deps w), lift to (projection deps v)
    have hsubset : ∀ z, z ∈ projection deps w → z ∈ projection deps v := by
      intro z hz
      exact mem_projection_of_dominates
        (Dominates.trans (Dominates.edge hedge) (dominates_of_mem_projection hz))
    have hv_mem := root_mem_projection deps v
    have hw_mem := child_mem_projection deps v w hedge
    have hedge' : ∃ d ∈ deps, (d.headIdx = v ∧ d.depIdx = w) ∨
                                (d.depIdx = v ∧ d.headIdx = w) := by
      obtain ⟨d, hd, h1, h2⟩ := hedge
      exact ⟨d, hd, Or.inl ⟨h1, h2⟩⟩
    exact .step v w _ hv_mem hw_mem hedge' (bidir_lift hsubset ih)

/-- Any two nodes in a projection are bidirectionally reachable via the root. -/
private theorem bidir_in_projection (deps : List Dependency) (root u v : Nat)
    (hu : u ∈ projection deps root) (hv : v ∈ projection deps root) :
    BidirReachable deps (projection deps root) u v :=
  bidir_trans (bidir_symm (bidir_of_dominates deps root u (dominates_of_mem_projection hu)))
    (bidir_of_dominates deps root v (dominates_of_mem_projection hv))

/-- **Constituent → Catena** (Osborne et al. 2012, p. 360): every constituent
    is a catena. Constituents are complete subtrees (projections rooted at some
    node), and complete subtrees are connected in the dependency tree.

    This is the fundamental containment result establishing that catenae
    strictly generalize constituents: {constituents} ⊂ {catenae} ⊂ {subsets}.

    Proof: a constituent `nodes` equals `projection deps r` for some root `r`.
    Every node in the projection is dominated by `r`, giving downward paths.
    The catena BFS traverses edges bidirectionally, so any start node can
    walk up to `r` (reversed dominance edges) then down to any target. -/
theorem constituent_implies_catena (deps : List Dependency) (n : Nat)
    (nodes : List Nat) (h : Catena.isConstituent deps n nodes = true) :
    isCatena deps nodes = true := by
  -- Extract root from isConstituent
  simp only [isConstituent] at h
  obtain ⟨root, _, hroot⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hroot
  obtain ⟨⟨hlen, hnodes_sub⟩, hsub_nodes⟩ := hroot
  -- Mutual containment between nodes and projection
  have h_n2p : ∀ x, x ∈ nodes → x ∈ projection deps root := by
    intro x hx; exact List.mem_of_elem_eq_true (List.all_eq_true.mp hnodes_sub x hx)
  have h_p2n : ∀ x, x ∈ projection deps root → x ∈ nodes := by
    intro x hx; exact List.mem_of_elem_eq_true (List.all_eq_true.mp hsub_nodes x hx)
  -- Non-emptiness: projection is non-empty, so nodes is non-empty
  have hne : nodes ≠ [] := by
    intro hemp
    have : (projection deps root).length = 0 := by
      rw [hemp] at hlen; simp at hlen; exact hlen.symm
    exact projection_nonempty deps root (List.eq_nil_of_length_eq_zero this)
  -- isCatena = !isEmpty && isConnected
  unfold isCatena
  have : nodes.isEmpty = false := by cases nodes <;> simp_all
  simp only [this, Bool.not_false, Bool.true_and]
  -- Connectivity: BFS from nodes.head reaches all of nodes
  unfold isConnected
  match hm : nodes, hne with
  | start :: rest, _ =>
    simp only [List.all_eq_true]
    intro x hx
    -- Both start and x are in nodes, hence in the projection, hence bidir reachable
    have hbidir : BidirReachable deps (start :: rest) start x :=
      bidir_lift h_p2n (bidir_in_projection deps root start x
        (h_n2p start List.mem_cons_self) (h_n2p x hx))
    exact List.elem_eq_true_of_mem (bfsReachable_complete deps _ start x hbidir)

end DepGrammar.CatenalConstruction
