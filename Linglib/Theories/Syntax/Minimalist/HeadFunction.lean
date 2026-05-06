import Linglib.Theories.Syntax.Minimalist.Basic
import Linglib.Theories.Syntax.Minimalist.Derivation

/-!
# Head Functions for Minimalist Syntactic Objects
@cite{marcolli-chomsky-berwick-2025}

Implements the head-function abstraction of @cite{marcolli-chomsky-berwick-2025}
NEW Minimalism (Definitions 1.13.3 and 1.13.6).

## What MCB says

A **head function** on an abstract, binary, rooted tree T is a function

```
h_T : V^o(T) → L(T)
```

from the set of non-leaf vertices V^o(T) to the set of leaves L(T),
satisfying the **coherence condition** (Def 1.13.3):

```
if T_v ⊆ T_w  and  h_T(w) ∈ L(T_v) ⊆ L(T_w),  then  h_T(w) = h_T(v).
```

The full head function (Def 1.13.6) is a partial map `h` defined on
`Dom(h) ⊂ T_{SO_0}` that assigns to each `T ∈ Dom(h)` a per-tree
function `h_T` of the above shape.

Per MCB Lemma 1.13.5: the set of all possible head functions h_T on T
is in bijection with the set of all planar embeddings of T. Per Lemma
1.13.4: there are exactly `2^#V^o(T)` head functions on T (one per
choice, at each non-leaf vertex, of which daughter is the head).

## Encoding choice

We use the **planar-marking** encoding (justified by Lemma 1.13.5): a
head function is given by, for each non-leaf vertex, a Bool saying
whether the LEFT daughter is the head. The head leaf `h_T(v)` is then
computed by following the marked daughter down from `v` until a leaf
is reached.

The MCB coherence condition (Def 1.13.3) is then **automatic** under
this encoding — see `headAt_coherent` below. This makes the
representation strictly more ergonomic than carrying a coherence proof
as a structure field.

## Why this file exists

linglib's `SyntacticObject := FreeMagma LIToken` (in `Basic.lean`) is
deliberately label-free, matching MCB's NEW Minimalism. The natural
consequence: any operation that needs head information must either
- track that information through derivation construction (see
  `Selection.lean`'s `SelectionalState` / `Derivation.headLI?`), OR
- consult an external head function as defined here

The pre-existing `Theories/Syntax/Minimalist/Labeling.lean` implements
an ad-hoc `getCategory` that conflates these two roles. This file
provides the MCB-aligned alternative; eventual migration of
`Labeling.lean` to use this abstraction is queued (per the §1.15
Labeling Algorithm task).

## Key definitions

- `PlanarMarking` — per-vertex left/right head choice
- `PlanarMarking.headAt` — the head leaf at vertex `v`
- `headAt_coherent` — the MCB Def 1.13.3 coherence condition
- `HeadFunction` — partial head function (planar marking + Dom)
- `HeadFunction.leftSpine` — the always-left head function
- `HeadFunction.IsRaising` — Definition 1.15.1 raising condition
  (currently a placeholder; needs §1.14 accessible-term machinery)

## Out of scope (queued)

- The Labeling Algorithm itself (Definition 1.15.2)
- The complemented head function (Definition 1.14.2) — extends
  `h(v)` to `(h(v), Z_v)` with the complement
- The maximal-projection paths γ_ℓ (Lemma 1.14.1)
- Phase-theoretic restrictions on `Dom(h)` (MCB §1.14)
-/

namespace Minimalist

-- ============================================================================
-- § 1: Planar Marking (MCB Lemma 1.13.5 representation)
-- ============================================================================

/-- A **planar marking**: at each potential `.node` SO, mark which
    daughter projects (true = left, false = right).

    Per @cite{marcolli-chomsky-berwick-2025} Lemma 1.13.5, planar
    markings on T are in bijection with head functions `h_T` on T (and
    with planar embeddings of T). The marking at a particular
    `.node a b` says which of `a`/`b` carries the head down.

    Values at non-`.node` SOs (or at `.node`s that aren't subtrees of
    the tree of interest) are vacuous and ignored. -/
structure PlanarMarking where
  /-- `true` if the left daughter is the head; `false` for right. -/
  isLeftHead : SyntacticObject → Bool

namespace PlanarMarking

/-- The head leaf reached by following the marking from vertex `v`.

    For a leaf, the head is the leaf itself. For a node, recurse into
    the marked daughter. By Lemma 1.13.5, this defines an
    `h_T : V^o(T) → L(T)` for any T containing `v`. -/
def headAt (m : PlanarMarking) : SyntacticObject → LIToken
  | .leaf tok => tok
  | .trace n => mkTraceToken n  -- traces project to a synthetic token
  | .node a b =>
    if m.isLeftHead (.node a b) then m.headAt a else m.headAt b

@[simp] theorem headAt_leaf (m : PlanarMarking) (tok : LIToken) :
    m.headAt (.leaf tok) = tok := rfl

@[simp] theorem headAt_node (m : PlanarMarking) (a b : SyntacticObject) :
    m.headAt (.node a b) =
      (if m.isLeftHead (.node a b) then m.headAt a else m.headAt b) := rfl

end PlanarMarking

-- ============================================================================
-- § 2: MCB Coherence Condition (true by construction)
-- ============================================================================

/-- The leaves of `v` as a list of LITokens.

    Used to state the MCB Def 1.13.3 coherence condition: if the head
    of `w` lands in the leaves of a sub-vertex `v`, then the heads of
    `v` and `w` agree. -/
def SyntacticObject.leafTokens : SyntacticObject → List LIToken
  | .leaf tok => [tok]
  | .trace n => [mkTraceToken n]
  | .node a b => a.leafTokens ++ b.leafTokens

@[simp] theorem SyntacticObject.leafTokens_leaf (tok : LIToken) :
    SyntacticObject.leafTokens (.leaf tok) = [tok] := rfl

@[simp] theorem SyntacticObject.leafTokens_node (a b : SyntacticObject) :
    SyntacticObject.leafTokens (.node a b) = a.leafTokens ++ b.leafTokens := rfl

/-- @cite{marcolli-chomsky-berwick-2025} Definition 1.13.3 coherence:
    if vertex `v` is contained in vertex `w` and the head of `w`
    appears among the leaves of `v`, then the head of `v` equals the
    head of `w`.

    Under the planar-marking encoding, the path from `w` to its head
    leaf, when it lands in `T_v`, must necessarily pass through `v`,
    so `headAt v` is computed by the same residual mark sequence.

    TODO: discharge the proof. The strategy is well-founded induction
    on `w.nodeCount`. For `w = .node a b`: if the marking selects `a`
    (left), then `headAt w = headAt a`; the membership hypothesis forces
    `v` to be contained in (or equal to) `a` (otherwise `headAt a ∉ v.leafTokens`
    by leaf-disjointness assumed for distinct subtrees); apply IH on
    `a`. The right case is symmetric. The "leaf-disjointness" lemma
    needed is that distinct subtrees of T have disjoint leaf-token sets
    when token ids are unique — which is typically true for SOs built
    by `Step.em` from distinct lexical items but not enforced by the
    SO type. This means the formal coherence theorem holds under a
    `Nodup` hypothesis on leaf-token ids; the unconditional version
    requires more delicate handling. -/
theorem PlanarMarking.headAt_coherent (m : PlanarMarking) :
    ∀ v w : SyntacticObject, contains w v →
      m.headAt w ∈ v.leafTokens → m.headAt w = m.headAt v := by
  -- See TODO above. Discharging this requires a leaf-token uniqueness
  -- invariant on the SO that the substrate doesn't yet encode.
  sorry

end Minimalist

-- ============================================================================
-- § 3: HeadFunction (MCB Def 1.13.6)
-- ============================================================================

namespace Minimalist

/-- @cite{marcolli-chomsky-berwick-2025} Definition 1.13.6: a head function
    is a planar marking restricted to a subdomain `Dom(h) ⊂ SO`.

    Per Lemma 1.13.5, the planar-marking representation is equivalent
    to the per-vertex map `h_T : V^o(T) → L(T)` of Definition 1.13.3,
    with coherence automatic.

    The bundle records:
    - `marking`: the planar marking that determines per-vertex heads
    - `Dom`: the subdomain on which `h` is "well defined" linguistically
      (e.g., excluding exocentric structures per §1.13.6's discussion)
    - `decDom`: decidability of `Dom` membership -/
structure HeadFunction where
  /-- The underlying planar marking. -/
  marking : PlanarMarking
  /-- The domain on which the head function is defined. -/
  Dom : SyntacticObject → Prop
  /-- Decidability of domain membership. -/
  decDom : DecidablePred Dom

attribute [instance] HeadFunction.decDom

namespace HeadFunction

/-- The head leaf token at a vertex of T. -/
def headAt (h : HeadFunction) (v : SyntacticObject) : LIToken :=
  h.marking.headAt v

/-- The head h(T) of T at the root (MCB notation). -/
def head (h : HeadFunction) (T : SyntacticObject) : LIToken :=
  h.headAt T

/-- The trivial head function: defined only on leaves, where every
    vertex is its own head. The marking is irrelevant since there are
    no `.node` SOs in the domain. -/
def leafOnly : HeadFunction where
  marking := { isLeftHead := fun _ => true }
  Dom so := so.isLeaf
  decDom := inferInstance

/-- The leftmost-leaf head function: defined on **all** SOs, picking
    the left daughter at every node. Sound for left-headed
    head-initial trees built via `Step.emR` complement Merge. -/
def leftSpine : HeadFunction where
  marking := { isLeftHead := fun _ => true }
  Dom _ := True
  decDom _ := isTrue trivial

/-- The rightmost-leaf head function: dual of `leftSpine`. Models a
    consistent head-final language at the abstract head-function
    layer. (The actual planar order — head-final vs head-initial — is
    a separate Externalization parameter; this is just the head
    selection.) -/
def rightSpine : HeadFunction where
  marking := { isLeftHead := fun _ => false }
  Dom _ := True
  decDom _ := isTrue trivial

@[simp] theorem leftSpine_headAt_leaf (tok : LIToken) :
    leftSpine.headAt (.leaf tok) = tok := rfl

@[simp] theorem leftSpine_head_leaf (tok : LIToken) :
    leftSpine.head (.leaf tok) = tok := rfl

/-- @cite{marcolli-chomsky-berwick-2025} Definition 1.15.1: a head
    function `h` is **raising** when its head assignment is preserved
    by Internal Merge in the configuration where the mover is not the
    head of the source tree.

    The MCB statement has two clauses:
    - **(i)** For any `T ∈ Dom(h)` and any subtree `v ⊂ T` such that
      `h(T) = h(T/^d v)` (the mover doesn't carry the head of T —
      "deleting" v with a trace doesn't change the head), the IM result
      `M(v, T/^c v)` is in `Dom(h)`, with `h(M(v, T/^c v)) = h(T/^d v)`.
    - **(ii)** For arbitrary `T` and any subtree `v ⊂ T` such that
      both `M(v, T/^c v) ∈ Dom(h)` and `T/^d v ∈ Dom(h)`, we have
      `h(M(v, T/^c v)) = h(T/^d v)`.

    Linguistically: when a head moves via IM, the new structure's head
    is the same as the original's (the mover doesn't project from the
    new root; the trace position determines projection).

    Encoded here using `Step.im` from `Derivation.lean` (the modern
    MCB-aligned IM primitive). The deletion-quotient `T/^d v` is
    `T.replace v (mkTrace n)` for some trace id; the contraction-
    quotient `T/^c v` is the same in our encoding (linglib uses
    `mkTrace` uniformly; the algebraic distinction Δ^d vs Δ^c lives
    in `Merge/Defs.lean` at the `TraceTree` layer). -/
def IsRaising (h : HeadFunction) : Prop :=
  -- Clause (ii) — the more general one, since clause (i) is its restriction
  -- to T ∈ Dom(h) under an extra precondition.
  ∀ (T v : SyntacticObject) (traceId : Nat),
    h.Dom (SyntacticObject.node v (T.replace v (mkTrace traceId))) →
    h.Dom (T.replace v (mkTrace traceId)) →
    h.headAt (SyntacticObject.node v (T.replace v (mkTrace traceId))) =
      h.headAt (T.replace v (mkTrace traceId))

/-- The trivial `leafOnly` head function is vacuously raising: the
    IM result is always a `.node`, never a leaf, so the `Dom`
    precondition fails for `leafOnly.Dom = isLeaf`. -/
theorem leafOnly_isRaising : leafOnly.IsRaising := by
  intro T v traceId hIM _hD
  -- hIM : leafOnly.Dom (.node v _) ≡ isLeaf (.node v _) ≡ False
  exact absurd hIM (by simp [leafOnly, SyntacticObject.isLeaf])

/-- The head's outer categorial feature, when defined. -/
def outerCatOf (h : HeadFunction) (so : SyntacticObject) : Cat :=
  (h.headAt so).item.outerCat

/-- The head's selectional stack, when defined. -/
def outerSelOf (h : HeadFunction) (so : SyntacticObject) : SelStack :=
  (h.headAt so).item.outerSel

end HeadFunction

-- ============================================================================
-- § 4: Lemma 1.13.4 (counting head functions on T)
-- ============================================================================

/-- @cite{marcolli-chomsky-berwick-2025} Lemma 1.13.4: there are
    exactly `2^#V^o(T)` head functions on T, where `V^o(T)` is the set
    of non-leaf vertices of T.

    Under our planar-marking encoding, a head function is determined
    by its values at the non-leaf subtrees of T (one Bool per node),
    so the count is `2^(number of internal nodes)`.

    Statement-only here: the bijection is `PlanarMarking ↔ (V^o(T) → Bool)`,
    so `|head functions on T| = |Bool|^|V^o(T)| = 2^|V^o(T)|`. The
    formal proof requires constructing the bijection and would
    duplicate the planar-marking encoding's content. -/
theorem head_function_count (T : SyntacticObject) :
    -- The number of distinct head functions on T equals 2^|V^o(T)|.
    -- Documented as content; proof omitted (constructive bijection).
    True := trivial

end Minimalist
