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

## References

- Osborne, T. & Groß, T. (2012). Constructions are catenae: Construction
  Grammar meets Dependency Grammar. *Cognitive Linguistics* 23(1):165–216.
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

/-- **Constituent → Catena** (Osborne et al. 2012, p. 360): every constituent
    is a catena. Constituents are complete subtrees (projections rooted at some
    node), and complete subtrees are connected in the dependency tree.

    This is the fundamental containment result establishing that catenae
    strictly generalize constituents: {constituents} ⊂ {catenae} ⊂ {subsets}.

    ## Proof Sketch

    A constituent `nodes` equals `projection deps r` for some root `r`.
    For any node `v ∈ nodes`, `Dominates deps r v` (by
    `dominates_of_mem_projection`). The catena BFS from any start node `s`
    can walk up parent edges to `r` (since edges are bidirectional in the
    catena graph) and then down child edges to any other node `v`. So every
    node is BFS-reachable from `s`.

    ## Blockers

    Requires the `isCatena_iff_IsCatena` bridge (currently sorry'd in
    Catena.lean) or an independent BFS correctness proof for subtrees.
    All per-tree instances are verified via `native_decide` in the bridge. -/
theorem constituent_implies_catena (deps : List Dependency) (n : Nat)
    (nodes : List Nat) (h : Catena.isConstituent deps n nodes = true) :
    isCatena deps nodes = true := by
  sorry

end DepGrammar.CatenalConstruction
