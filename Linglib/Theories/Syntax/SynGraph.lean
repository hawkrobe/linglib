set_option autoImplicit false

/-!
# Syntactic Graphs
@cite{adger-2025}

Graph-based representation of syntactic structure that generalizes across
frameworks. Each node has a label and at most two children (1-part and
2-part), enforcing Dimensionality. In-degree is unbounded, permitting
multiparthood — a single node simultaneously serving as part of multiple
parents (@cite{adger-2025}).

## Design

- **Out-degree ≤ 2**: each node has at most one 1-part (complement) and
  one 2-part (specifier). This is the Dimensionality axiom.
- **In-degree unbounded**: a node may be pointed to by multiple parents.
  This is multiparthood — the mechanism for movement in mereological
  syntax, distinct from both copies and multidominance.
- **Framework predicates**: `isTree` (in-degree ≤ 1, ≈ BPS), `acyclic`
  (required for well-formed structures). Trees are the special case.

## Angular Locality

The central locality constraint (@cite{adger-2025}, definition 29):

    If γ is a part, then γ can subjoin to β only if there is an α s.t.
    γ is a n-part of α and α is a 1-part of β.

Crucially, "n-part" means transitive parthood **within a single dimension**.
Transitivity does NOT cross dimensions: if x <₁ u and u <₂ e, then x is
NOT a part of e in either dimension. This restriction is what makes
Angular Locality derive island constraints, antilocality, and the
impossibility of sideward/downward movement.

## Relationship to Existing Types

- `MereologicalSyntax.SynObj`: tree-based, cannot express multiparthood.
  Embeds into `SynGraph` by construction.
- `Minimalist.SyntacticObject`: binary tree. Embeds as a `SynGraph`
  satisfying `isTree`.
- `Core.Tree C W`: n-ary tree for compositional interpretation, not a
  syntactic structure type.
-/

-- ════════════════════════════════════════════════════
-- § 1. Graph Structure
-- ════════════════════════════════════════════════════

/-- A syntactic graph with labeled nodes and dimensioned edges.

    Nodes are indexed by `Fin numNodes`. Each node has a label of type `L`
    and at most two children: a 1-part (complement) and a 2-part (specifier).
    Multiple nodes may point to the same child — this is multiparthood. -/
structure SynGraph (L : Type) where
  numNodes : Nat
  label : Fin numNodes → L
  onePart : Fin numNodes → Option (Fin numNodes)
  twoPart : Fin numNodes → Option (Fin numNodes)

variable {L : Type}

-- ════════════════════════════════════════════════════
-- § 2. Chain & Descendants
-- ════════════════════════════════════════════════════

/-- Follow a single-dimension pointer chain from `start`, returning
    visited nodes (not including `start`). Fuel bounds traversal depth. -/
def SynGraph.chain (g : SynGraph L) (f : Fin g.numNodes → Option (Fin g.numNodes))
    (start : Fin g.numNodes) : (fuel : Nat) → List (Fin g.numNodes)
  | 0 => []
  | fuel + 1 => match f start with
    | none => []
    | some next => next :: g.chain f next fuel

/-- All strict descendants of `root` reachable via 1-part and 2-part
    edges (cross-dimensional). May contain duplicates. -/
def SynGraph.descendants (g : SynGraph L) (root : Fin g.numNodes) :
    (fuel : Nat) → List (Fin g.numNodes)
  | 0 => (g.onePart root).toList ++ (g.twoPart root).toList
  | fuel + 1 =>
    let one := match g.onePart root with
      | none => []
      | some c => c :: g.descendants c fuel
    let two := match g.twoPart root with
      | none => []
      | some c => c :: g.descendants c fuel
    one ++ two

-- ════════════════════════════════════════════════════
-- § 3. Parthood
-- ════════════════════════════════════════════════════

/-- `x` is an immediate 1-part (complement) of `y`. -/
def SynGraph.isImm1PartOf (g : SynGraph L) (x y : Fin g.numNodes) : Bool :=
  g.onePart y == some x

/-- `x` is an immediate 2-part (specifier) of `y`. -/
def SynGraph.isImm2PartOf (g : SynGraph L) (x y : Fin g.numNodes) : Bool :=
  g.twoPart y == some x

/-- `x` is an immediate part of `y` in either dimension. -/
def SynGraph.isImmPartOf (g : SynGraph L) (x y : Fin g.numNodes) : Bool :=
  g.isImm1PartOf x y || g.isImm2PartOf x y

/-- `x` is a transitive 1-part of `y` (reachable via onePart only).
    Within-dimension transitivity without crossing dimensions. -/
def SynGraph.isTrans1PartOf (g : SynGraph L) (x y : Fin g.numNodes) : Bool :=
  (g.chain g.onePart y g.numNodes).any (· == x)

/-- `x` is a transitive 2-part of `y` (reachable via twoPart only).
    Within-dimension transitivity without crossing dimensions. -/
def SynGraph.isTrans2PartOf (g : SynGraph L) (x y : Fin g.numNodes) : Bool :=
  (g.chain g.twoPart y g.numNodes).any (· == x)

/-- `x` is a within-dimension transitive n-part of `y` for some n.
    This is the parthood relation relevant to Angular Locality:
    γ is reachable from α by following ONLY 1-part edges or ONLY 2-part
    edges, never crossing dimensions (@cite{adger-2025}, p. 95). -/
def SynGraph.isWithinDimPartOf (g : SynGraph L) (x y : Fin g.numNodes) : Bool :=
  g.isTrans1PartOf x y || g.isTrans2PartOf x y

/-- `x` is a transitive part of `y` (reachable via any combination of
    1-part and 2-part edges). Cross-dimensional — NOT the parthood
    relation used by Angular Locality. -/
def SynGraph.isTransPartOf (g : SynGraph L) (x y : Fin g.numNodes) : Bool :=
  (g.descendants y g.numNodes).any (· == x)

-- ════════════════════════════════════════════════════
-- § 4. Parents & Multiparthood
-- ════════════════════════════════════════════════════

/-- Number of parents of `target` (nodes pointing to it via either edge). -/
def SynGraph.parentCount (g : SynGraph L) (target : Fin g.numNodes) : Nat :=
  (List.range g.numNodes).foldl (fun acc j =>
    if h : j < g.numNodes then
      let jf : Fin g.numNodes := ⟨j, h⟩
      acc + (if g.onePart jf == some target then 1 else 0)
          + (if g.twoPart jf == some target then 1 else 0)
    else acc) 0

/-- Node `i` is multiply dominated — more than one parent.
    This is multiparthood: the node occupies multiple structural positions
    simultaneously, not by copying but by being pointed to twice. -/
def SynGraph.isMultipart (g : SynGraph L) (i : Fin g.numNodes) : Bool :=
  g.parentCount i > 1

-- ════════════════════════════════════════════════════
-- § 5. Complementation Line (Extended Projection)
-- ════════════════════════════════════════════════════

/-- Labels along the 1-part chain from `root`, including `root` itself.
    Corresponds to @cite{grimshaw-2005}'s Extended Projection:
    the sequence N <₁ Cl <₁ Q <₁ D emerges from successive 1-parts. -/
def SynGraph.onePartChain (g : SynGraph L) (root : Fin g.numNodes) : List L :=
  g.label root :: (g.chain g.onePart root g.numNodes).map g.label

-- ════════════════════════════════════════════════════
-- § 6. Label Containment
-- ════════════════════════════════════════════════════

/-- Does the subtree rooted at `root` contain a node labeled `l`? -/
def SynGraph.containsLabel [BEq L] (g : SynGraph L) (l : L)
    (root : Fin g.numNodes) : Bool :=
  g.label root == l ||
  (g.descendants root g.numNodes).any (fun i => g.label i == l)

-- ════════════════════════════════════════════════════
-- § 7. Angular Locality
-- ════════════════════════════════════════════════════

/-- Angular Locality (@cite{adger-2025}, definition 29, p. 91):

    If γ is a part, then γ can subjoin to β only if there is an α s.t.
    γ is a n-part of α and α is a 1-part of β.

    "n-part" means transitive parthood **within a single dimension**.
    Transitivity does NOT cross dimensions (@cite{adger-2025}, p. 95):
    if x <₁ u and u <₂ e, x is neither a 1-part nor a 2-part of e.

    This derives:
    - Antilocality (complement-to-specifier of same head)
    - No sideward movement (to a specifier/2-part)
    - No downward movement
    - No parallel merge (to an unattached object)
    - No long-distance movement across Extended Projections
    — all without stipulating phases or PIC. -/
def SynGraph.satisfiesAL (g : SynGraph L) (γ β : Fin g.numNodes) : Bool :=
  let alphas := g.chain g.onePart β g.numNodes
  alphas.any fun α => g.isWithinDimPartOf γ α

-- ════════════════════════════════════════════════════
-- § 8. Subjoin
-- ════════════════════════════════════════════════════

/-- External subjoin: make `x` a part of `y` in the next available
    dimension. Returns `none` if `y` already has two parts (Dimensionality
    violation) or if `x == y` (irreflexivity). -/
def SynGraph.subjoin (g : SynGraph L) (x y : Fin g.numNodes) :
    Option (SynGraph L) :=
  if x == y then none
  else match g.onePart y with
  | none =>
    some { g with onePart := fun i => if i == y then some x else g.onePart i }
  | some _ => match g.twoPart y with
    | none =>
      some { g with twoPart := fun i => if i == y then some x else g.twoPart i }
    | some _ => none

/-- Internal subjoin: subjoin `γ` to `β` only if Angular Locality is
    satisfied. Models movement — the element already exists and is
    re-subjoined to a higher position, creating multiparthood. -/
def SynGraph.internalSubjoin (g : SynGraph L) (γ β : Fin g.numNodes) :
    Option (SynGraph L) :=
  if g.satisfiesAL γ β then g.subjoin γ β else none

-- ════════════════════════════════════════════════════
-- § 9. Framework Predicates
-- ════════════════════════════════════════════════════

/-- No node is a descendant of itself. -/
def SynGraph.acyclic (g : SynGraph L) : Bool :=
  (List.range g.numNodes).all fun i =>
    if h : i < g.numNodes then
      let node : Fin g.numNodes := ⟨i, h⟩
      !(g.descendants node g.numNodes).any (· == node)
    else true

/-- Every node has in-degree ≤ 1 (at most one parent). -/
def SynGraph.maxInDegree1 (g : SynGraph L) : Bool :=
  (List.range g.numNodes).all fun i =>
    if h : i < g.numNodes then g.parentCount ⟨i, h⟩ ≤ 1 else true

/-- The graph is a tree: acyclic with in-degree ≤ 1 everywhere.
    `Minimalist.SyntacticObject` and `MereologicalSyntax.SynObj` both
    satisfy this. Mereological structures with multiparthood do NOT. -/
def SynGraph.isTree (g : SynGraph L) : Bool :=
  g.acyclic && g.maxInDegree1

/-- Well-formed mereological structure: acyclic, but multiparthood
    (in-degree > 1) is permitted. -/
def SynGraph.isMereological (g : SynGraph L) : Bool :=
  g.acyclic

-- ════════════════════════════════════════════════════
-- § 10. Angular Locality Derivations
-- ════════════════════════════════════════════════════

/-! The five key results derived from Angular Locality in
@cite{adger-2025}, Chapter 4, list (35), p. 93. Each is demonstrated
on a concrete `SynGraph` and verified by `native_decide`.

We construct small graphs with specific edge configurations and
verify that `satisfiesAL` returns the expected result. -/

section ALDerivations

abbrev N := Nat

/-- Helper: build a SynGraph from edge lists. -/
def mkGraph (n : Nat)
    (ones : List (Fin n × Fin n))
    (twos : List (Fin n × Fin n)) : SynGraph N :=
  { numNodes := n
    label := fun i => i.val
    onePart := fun i => (ones.find? (·.1 == i)).map (·.2)
    twoPart := fun i => (twos.find? (·.1 == i)).map (·.2) }

-- ────────────────────────────────────────────────────
-- (35a) Superlocal / antilocal subjunction ruled out
-- ────────────────────────────────────────────────────

/-! Structure (28), @cite{adger-2025} p. 90:
    a (0) ──1──▶ b (1)

    b trying to subjoin to a. AL requires an α that is a 1-part of a
    such that b is a within-dim n-part of α. The only 1-part of a is b
    itself, and b is not a part of itself. AL fails. -/

private def g_superlocal := mkGraph 2
  [(⟨0, by omega⟩, ⟨1, by omega⟩)] []

theorem al_blocks_superlocal :
    g_superlocal.satisfiesAL ⟨1, by decide⟩ ⟨0, by decide⟩ = false := by native_decide

-- ────────────────────────────────────────────────────
-- (35c) Sideward subjunction ruled out
-- ────────────────────────────────────────────────────

/-! Structure (31a), @cite{adger-2025} p. 92:
    c (0) ──1──▶ b (1),  c (0) ──2──▶ a (2)

    a trying to subjoin to b (sibling). b has no 1-parts, so the
    candidate α set is empty. AL fails. -/

private def g_sideward := mkGraph 3
  [(⟨0, by omega⟩, ⟨1, by omega⟩)]
  [(⟨0, by omega⟩, ⟨2, by omega⟩)]

theorem al_blocks_sideward :
    g_sideward.satisfiesAL ⟨2, by decide⟩ ⟨1, by decide⟩ = false := by native_decide

-- ────────────────────────────────────────────────────
-- (35d) Parallel subjunction ruled out
-- ────────────────────────────────────────────────────

/-! @cite{adger-2025} p. 91 (30): subjunction to an unattached object.
    a (0) ──1──▶ b (1);  c (2) disconnected.

    c trying to subjoin to a. a's 1-part chain = [b]. c is not a
    within-dim part of b. AL fails. -/

private def g_parallel := mkGraph 3
  [(⟨0, by omega⟩, ⟨1, by omega⟩)] []

theorem al_blocks_parallel :
    g_parallel.satisfiesAL ⟨2, by decide⟩ ⟨0, by decide⟩ = false := by native_decide

-- ────────────────────────────────────────────────────
-- (35e) Cross-dimensional long-distance ruled out
-- ────────────────────────────────────────────────────

/-! Structure (38), @cite{adger-2025} p. 95:
    y (0) ──1──▶ e (1) ──1──▶ w (3)
                 e (1) ──2──▶ u (2) ──2──▶ z (4)
                              u (2) ──1──▶ x (5)

    The paper states: "u is a 2-part of e", "z is a 2-part of u",
    "x is a 1-part of u."

    z CAN subjoin to y: α = e is a 1-part of y. z <₂ u <₂ e
    (transitive 2-part of e, within dimension 2). AL satisfied.

    x CANNOT subjoin to y: x <₁ u, u <₂ e. "Since transitivity does
    not cross dimensions, x is neither a 2-part nor a 1-part of e"
    (p. 95). The corrected `satisfiesAL` using within-dimension chains
    correctly rejects this; the old version using `descendants` would
    have incorrectly allowed it. -/

private def g_crossdim := mkGraph 6
  [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨3, by omega⟩),
   (⟨2, by omega⟩, ⟨5, by omega⟩)]
  [(⟨1, by omega⟩, ⟨2, by omega⟩), (⟨2, by omega⟩, ⟨4, by omega⟩)]

/-- z (transitive 2-part of e) CAN subjoin to y. -/
theorem al_allows_within_dim :
    g_crossdim.satisfiesAL ⟨4, by decide⟩ ⟨0, by decide⟩ = true := by native_decide

/-- x (cross-dimensional from e) CANNOT subjoin to y.
    This is the critical test that distinguishes the corrected AL from
    the buggy version: x <₁ u <₂ e crosses dimensions, so x is not
    a within-dimension part of e. -/
theorem al_blocks_cross_dim :
    g_crossdim.satisfiesAL ⟨5, by decide⟩ ⟨0, by decide⟩ = false := by native_decide

-- ────────────────────────────────────────────────────
-- (35b) Lowering / downward subjunction ruled out
-- ────────────────────────────────────────────────────

/-! Structure (32), @cite{adger-2025} p. 92:
    e (0) ──1──▶ a (1) ──1──▶ d (3)
    e (0) ──2──▶ f (2)
                 a (1) ──2──▶ b (4) ──1──▶ c (5) ──1──▶ g (6)

    d trying to subjoin to c (lowering). c's 1-part chain = [g].
    d is not a within-dim part of g. AL fails. -/

private def g_lowering := mkGraph 7
  [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨3, by omega⟩),
   (⟨4, by omega⟩, ⟨5, by omega⟩), (⟨5, by omega⟩, ⟨6, by omega⟩)]
  [(⟨0, by omega⟩, ⟨2, by omega⟩), (⟨1, by omega⟩, ⟨4, by omega⟩)]

theorem al_blocks_lowering :
    g_lowering.satisfiesAL ⟨3, by decide⟩ ⟨5, by decide⟩ = false := by native_decide

-- ────────────────────────────────────────────────────
-- (24a) Roll-up movement ALLOWED
-- ────────────────────────────────────────────────────

/-! Structure (24a), @cite{adger-2025} p. 89:
    e (0) ──1──▶ d (1) ──1──▶ a (2) ──1──▶ c (3)
                                    ──2──▶ b (4)

    b subjoins to e: a is in e's 1-part chain, b <₂ a. AL satisfied.
    c subjoins to e: a is in e's 1-part chain, c <₁ a. AL satisfied. -/

private def g_rollup := mkGraph 5
  [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
   (⟨2, by omega⟩, ⟨3, by omega⟩)]
  [(⟨2, by omega⟩, ⟨4, by omega⟩)]

/-- Roll-up: b (2-part of a) CAN subjoin to e. -/
theorem al_allows_rollup_2part :
    g_rollup.satisfiesAL ⟨4, by decide⟩ ⟨0, by decide⟩ = true := by native_decide

/-- Roll-up: c (1-part of a) CAN subjoin to e. -/
theorem al_allows_rollup_1part :
    g_rollup.satisfiesAL ⟨3, by decide⟩ ⟨0, by decide⟩ = true := by native_decide

-- ────────────────────────────────────────────────────
-- Successive cyclicity: cross-clausal movement requires stops
-- ────────────────────────────────────────────────────

/-! @cite{adger-2025}, Chapter 4.3: Angular Locality forces successive-
cyclic movement across clause boundaries. Within a single Extended
Projection (EP), movement is unrestricted — the 1-part chain connects
everything. But when movement crosses from an embedded EP to a matrix
EP (connected via a 2-part edge), AL blocks direct movement.

Cross-clausal structure:
    Matrix:   C₁(0) ──1──▶ T₁(1) ──1──▶ v₁(2) ──1──▶ V₁(3)
                           T₁(1) ──2──▶ subj(4)
    Embedded: C₂(5) ──1──▶ T₂(6) ──1──▶ v₂(7) ──1──▶ V₂(8)
    Link:     v₁(2) ──2──▶ C₂(5)  ← embedded CP is 2-part of matrix v
    wh(9) is a 2-part of v₂(7).

    wh CANNOT reach C₁ directly: C₁'s 1-part chain = [T₁, v₁, V₁].
    wh is in the embedded EP, connected to v₁ only via C₂ which is a
    2-part of v₁ — cross-dimensional, so invisible to AL.

    wh CAN reach C₂ (same EP — within-dim 2-part of v₂, v₂ <₁ T₂ <₁ C₂).
    After wh subjoins to C₂ (becoming C₂'s 2-part), wh <₂ C₂ <₂ v₁,
    making wh a transitive 2-part of v₁. Since v₁ is in C₁'s 1-part
    chain, wh can NOW reach C₁. This is successive cyclicity: the
    intermediate stop at C₂ is forced by AL. -/

-- Step 1: Before movement. Embedded wh cannot reach matrix C₁.
private def g_succ_cyc_0 := mkGraph 10
  -- 1-parts: C₁─T₁─v₁─V₁, C₂─T₂─v₂─V₂
  [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
   (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨5, by omega⟩, ⟨6, by omega⟩),
   (⟨6, by omega⟩, ⟨7, by omega⟩), (⟨7, by omega⟩, ⟨8, by omega⟩)]
  -- 2-parts: T₁─subj, v₁─C₂, v₂─wh
  [(⟨1, by omega⟩, ⟨4, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩),
   (⟨7, by omega⟩, ⟨9, by omega⟩)]

/-- wh CANNOT reach matrix C₁ directly — cross-clausal boundary. -/
theorem succ_cyc_blocked_cross_clause :
    g_succ_cyc_0.satisfiesAL ⟨9, by decide⟩ ⟨0, by decide⟩ = false := by native_decide

/-- wh CAN reach embedded C₂ — within the same EP. -/
theorem succ_cyc_wh_reaches_embedded_C :
    g_succ_cyc_0.satisfiesAL ⟨9, by decide⟩ ⟨5, by decide⟩ = true := by native_decide

-- Step 2: After wh subjoins to C₂ (C₂ ──2──▶ wh, multiparthood).
-- Now wh <₂ C₂ <₂ v₁, so wh is a transitive 2-part of v₁.
-- v₁ is in C₁'s 1-part chain. AL satisfied for C₁.
private def g_succ_cyc_1 := mkGraph 10
  [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
   (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨5, by omega⟩, ⟨6, by omega⟩),
   (⟨6, by omega⟩, ⟨7, by omega⟩), (⟨7, by omega⟩, ⟨8, by omega⟩)]
  [(⟨1, by omega⟩, ⟨4, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩),
   (⟨7, by omega⟩, ⟨9, by omega⟩), (⟨5, by omega⟩, ⟨9, by omega⟩)]

/-- After stopping at C₂, wh CAN now reach matrix C₁.
    This is successive cyclicity: the C₂ intermediate landing site
    is forced by AL, just as phase edges force cyclic movement
    in Minimalism. -/
theorem succ_cyc_wh_reaches_C1_after_stop :
    g_succ_cyc_1.satisfiesAL ⟨9, by decide⟩ ⟨0, by decide⟩ = true := by native_decide

-- ────────────────────────────────────────────────────
-- Nominal island: D's filled 2-part blocks extraction
-- ────────────────────────────────────────────────────

/-! @cite{adger-2025}, Chapter 6: When D has a 2-part (because Det/Dem
subjoins to it), its 2-part slot is "used up." The mechanism has two
parts:

1. wh CAN satisfy AL for D (wh <₂ P, P is D's 1-part), so AL alone
   does not block movement. But D already has both parts filled
   (Dimensionality blocks subjoin).
2. wh CANNOT satisfy AL for any node above D (C, T), because D is
   connected to the matrix clause via a 2-part edge, and the path
   from wh through D to v crosses dimensions.

This derives the Specificity Condition: definite nominals (whose D has
a 2-part) are islands, indefinite ones (free 2-part) are transparent.

Structure:
    C (0) ──1──▶ T (1) ──1──▶ v (2) ──1──▶ V (3)
                 T (1) ──2──▶ subj (4)
                              v (2) ──2──▶ D (5) ──1──▶ P (6) ──1──▶ N (7)
                                           D (5) ──2──▶ Det (8)
                                                        P (6) ──2──▶ wh (9)
-/

private def g_definite_island := mkGraph 10
  -- 1-part edges: C─T─v─V, D─P─N
  [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
   (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨5, by omega⟩, ⟨6, by omega⟩),
   (⟨6, by omega⟩, ⟨7, by omega⟩)]
  -- 2-part edges: T─subj, v─D, D─Det, P─wh
  [(⟨1, by omega⟩, ⟨4, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩),
   (⟨5, by omega⟩, ⟨8, by omega⟩), (⟨6, by omega⟩, ⟨9, by omega⟩)]

/-- wh CANNOT reach matrix C when D has a 2-part (definite = island).
    The path wh <₂ P <₁ D <₂ v crosses dimensions, so wh is not
    a within-dimension part of any node in C's 1-part chain. -/
theorem nominal_island_definite_blocks :
    g_definite_island.satisfiesAL ⟨9, by decide⟩ ⟨0, by decide⟩ = false := by native_decide

/-- wh satisfies AL for D (wh <₂ P, P <₁ D), but D is full —
    `internalSubjoin` returns none because Dimensionality blocks it. -/
theorem nominal_island_d_full :
    g_definite_island.internalSubjoin ⟨9, by decide⟩ ⟨5, by decide⟩ = none := by native_decide

/-! Indefinite structure: D has no 2-part (Det does not subjoin).
    wh can subjoin to D, filling its free 2-part slot. -/

private def g_indefinite_transparent := mkGraph 10
  [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
   (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨5, by omega⟩, ⟨6, by omega⟩),
   (⟨6, by omega⟩, ⟨7, by omega⟩)]
  [(⟨1, by omega⟩, ⟨4, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩),
   (⟨6, by omega⟩, ⟨9, by omega⟩)]  -- no D──2──▶Det edge

/-- wh CAN reach D when D has a free 2-part (indefinite = transparent). -/
theorem nominal_island_indefinite_allows :
    g_indefinite_transparent.satisfiesAL ⟨9, by decide⟩ ⟨5, by decide⟩ = true := by native_decide

/-- After wh subjoins to D, wh CAN reach matrix C.
    wh <₂ D <₂ v, so wh is a transitive 2-part of v.
    v is in C's 1-part chain. AL satisfied. -/
private def g_indefinite_after := mkGraph 10
  [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
   (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨5, by omega⟩, ⟨6, by omega⟩),
   (⟨6, by omega⟩, ⟨7, by omega⟩)]
  [(⟨1, by omega⟩, ⟨4, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩),
   (⟨6, by omega⟩, ⟨9, by omega⟩), (⟨5, by omega⟩, ⟨9, by omega⟩)]

theorem nominal_island_indefinite_reaches_C :
    g_indefinite_after.satisfiesAL ⟨9, by decide⟩ ⟨0, by decide⟩ = true := by native_decide

-- ────────────────────────────────────────────────────
-- Subject island: extraction from within a subject
-- ────────────────────────────────────────────────────

/-! @cite{adger-2025}, Chapter 6: Extraction from within a subject DP
is blocked because the path from the extracted element to the matrix
clause crosses dimensions.

Structure:
    C (0) ──1──▶ T (1) ──1──▶ v (2) ──1──▶ V (3)
                 T (1) ──2──▶ DP_subj (4) ──1──▶ NP (5) ──1──▶ N_friend (6)
                                                  NP (5) ──2──▶ PP (7) ──1──▶ N_who (8)

"*Who did [a friend of t] arrive?" — extraction of N_who from within
the subject DP.

The path N_who(8) <₁ PP(7) <₂ NP(5) <₁ DP(4) <₂ T(1) crosses
dimensions twice. N_who is not a within-dimension transitive part of
any node in C's 1-part chain [T, v, V].

Crucially, the SUBJECT DP ITSELF can extract (it is T's 2-part):
this correctly predicts "Who [t arrived]?" is grammatical. -/

private def g_subject_island := mkGraph 9
  -- 1-parts: C─T─v─V, DP─NP─N_friend, PP─N_who
  [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
   (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨4, by omega⟩, ⟨5, by omega⟩),
   (⟨5, by omega⟩, ⟨6, by omega⟩), (⟨7, by omega⟩, ⟨8, by omega⟩)]
  -- 2-parts: T─DP_subj, NP─PP
  [(⟨1, by omega⟩, ⟨4, by omega⟩), (⟨5, by omega⟩, ⟨7, by omega⟩)]

/-- Extraction from within a subject is blocked: N_who CANNOT reach C.
    The cross-dimensional path N_who <₁ PP <₂ NP <₁ DP <₂ T prevents
    N_who from being a within-dimension transitive part of any α in
    C's 1-part chain. -/
theorem subject_island_blocks :
    g_subject_island.satisfiesAL ⟨8, by decide⟩ ⟨0, by decide⟩ = false := by native_decide

/-- The subject DP itself CAN reach C (it is T's 2-part, and T is
    in C's 1-part chain). Subjects can extract, just not their subparts. -/
theorem subject_itself_can_extract :
    g_subject_island.satisfiesAL ⟨4, by decide⟩ ⟨0, by decide⟩ = true := by native_decide

-- ────────────────────────────────────────────────────
-- Adjunct island: extraction from within an adjunct
-- ────────────────────────────────────────────────────

/-! @cite{adger-2025}, Chapter 6: Extraction from within an adjunct
is blocked by the same cross-dimensional mechanism as subject islands.

Structure:
    C (0) ──1──▶ T (1) ──1──▶ v (2) ──1──▶ V (3)
                 T (1) ──2──▶ subj (4)
                              v (2) ──2──▶ AdvP (5) ──1──▶ PP (6) ──1──▶ NP_wh (7)

"*What did John arrive [after fixing t]?" — extraction of NP_wh from
the adjunct AdvP.

The path NP_wh(7) <₁ PP(6) <₁ AdvP(5) <₂ v(2) crosses dimensions
at the AdvP-to-v boundary. Within v's 2-part chain: AdvP is there,
but NP_wh is not (NP_wh is in AdvP's 1-part chain, not its 2-part chain). -/

private def g_adjunct_island := mkGraph 8
  -- 1-parts: C─T─v─V, AdvP─PP─NP_wh
  [(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
   (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨5, by omega⟩, ⟨6, by omega⟩),
   (⟨6, by omega⟩, ⟨7, by omega⟩)]
  -- 2-parts: T─subj, v─AdvP
  [(⟨1, by omega⟩, ⟨4, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩)]

/-- Extraction from within an adjunct is blocked: NP_wh CANNOT reach C. -/
theorem adjunct_island_blocks :
    g_adjunct_island.satisfiesAL ⟨7, by decide⟩ ⟨0, by decide⟩ = false := by native_decide

/-- The adjunct AdvP itself CAN reach C (it is v's 2-part, and v is
    in C's 1-part chain). Adjuncts can be fronted, just not extracted from. -/
theorem adjunct_itself_can_extract :
    g_adjunct_island.satisfiesAL ⟨5, by decide⟩ ⟨0, by decide⟩ = true := by native_decide

-- ────────────────────────────────────────────────────
-- General antilocality
-- ────────────────────────────────────────────────────

/-! Antilocality: complement-to-specifier movement within the same
head is always blocked. This is (35a) stated as a general test:
for any 2-node structure where β has exactly one 1-part γ and no
further substructure, γ cannot re-subjoin to β. The only candidate α
(γ itself) fails because γ is not a part of itself.

We verify this for minimal structures of each shape: sub₁ and sub₁₂. -/

/-- Antilocality for a bare sub₁: the sole complement cannot re-subjoin. -/
theorem antilocality_sub1 :
    let g := mkGraph 2 [(⟨0, by omega⟩, ⟨1, by omega⟩)] []
    g.satisfiesAL ⟨1, by decide⟩ ⟨0, by decide⟩ = false := by native_decide

/-- Antilocality for sub₁₂: neither the complement nor the specifier
    can re-subjoin to the head. -/
theorem antilocality_sub12 :
    let g := mkGraph 3
      [(⟨0, by omega⟩, ⟨1, by omega⟩)]
      [(⟨0, by omega⟩, ⟨2, by omega⟩)]
    g.satisfiesAL ⟨1, by decide⟩ ⟨0, by decide⟩ = false ∧
    g.satisfiesAL ⟨2, by decide⟩ ⟨0, by decide⟩ = false := by
  exact ⟨by native_decide, by native_decide⟩

end ALDerivations
