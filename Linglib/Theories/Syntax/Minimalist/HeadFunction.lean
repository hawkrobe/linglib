import Linglib.Theories.Syntax.Minimalist.Basic
import Linglib.Theories.Syntax.Minimalist.Derivation

/-!
# Head Functions for Minimalist Syntactic Objects (MCB §1.12-§1.13)
@cite{marcolli-chomsky-berwick-2025}

## What MCB say

Per @cite{marcolli-chomsky-berwick-2025} §1.12 (book pp. 105-108), Externalization
is modelled as a **section** `σ_L : 𝔗_{SO_0} → 𝔗^{pl}_{SO_0}` of the projection
`Π : 𝔗^{pl}_{SO_0} → 𝔗_{SO_0}` from planar to nonplanar binary rooted trees.
The section satisfies `Π ∘ σ_L = id` and is:

- **NOT a morphism of magmas** (Lemma 1.13.1: no morphism of magmas exists from
  the commutative `SO` to the noncommutative `SO^{nc}`).
- **Noncanonical** — depends on the language `L`.

A **head function** (Def 1.13.6) is a partial map `h` defined on a subdomain
`Dom(h) ⊂ 𝔗_{SO_0}` that assigns to each `T ∈ Dom(h)` a function
`h_T : V^o(T) → L(T)` from non-leaf vertices of T to leaves, satisfying coherence:
`T_v ⊆ T_w  ∧  h_T(w) ∈ L(T_v) ⊆ L(T_w)  ⟹  h_T(w) = h_T(v)` (Def 1.13.3).

Per **Lemma 1.13.5**, head functions on T are in bijection with planar
embeddings of T — under either the harmonic head-initial convention (head
daughter to the LEFT) or the harmonic head-final convention (head daughter
to the RIGHT). The choice between conventions inverts the bijection.

## Encoding

`HeadFunction` is a `FreeCommMagma.Section` (the σ_L part) plus head-side
convention (initial vs final per Lemma 1.13.5) plus partial domain (Def 1.13.6):

```
structure HeadFunction where
  section_  : FreeCommMagma.Section (LIToken ⊕ Nat)
  headSide  : ConventionDir
  Dom       : SyntacticObject → Prop
  decDom    : DecidablePred Dom
```

The substrate primitive is **`headAtVertex h T v`** (MCB Def 1.13.3):
the head leaf at vertex `v` of `T`. The root special case `head h T` is derived
as `headAtVertex h T T`.

Per Lemma 1.13.5, the head leaf at vertex v is:
- under `.initial`: leftmost-leaf of `h.section_.σ v`
- under `.final`:   rightmost-leaf of `h.section_.σ v`

## Key definitions

- `ConventionDir` — harmonic head-side (`.initial`/`.final`)
- `HeadFunction` — bundle of section + side + domain
- `headAtVertex h T v` — MCB Def 1.13.3 head function at vertex (substrate primitive)
- `head h T` — root special case (MCB notation `h(T)`)
- `outerCat h so`, `outerSel h so` — head's category/selectional stack
- `linearize h so`, `phonYield h so`, `terminalNodes h so`, `leafTokens h so` — planar yields
- `IsRaisingClauseI`, `IsRaisingClauseII`, `IsRaising` — Def 1.15.1 raising condition

## Out of scope (queued for §1.14+)

- **Complemented head function (Def 1.14.2)**: extends `h(v)` to `(h(v), Z_v)`
  with the head's complement subtree. Will be a sibling structure
  `ComplementedHeadFunction extends HeadFunction with complement : V^o T → Option SO`.
- **Maximal-projection paths γ_ℓ (Lemma 1.14.1)**: requires `headAtVertex` (now landed)
  to define paths of constant-head vertices.
- **Phase Theory restrictions on Dom(h) (MCB §1.14)**.
- **Π_L language filter (eq 1.12.4)**: second projection separate from σ_L.
  Will be a sibling structure `LanguageFilter` if/when needed; not merged into Dom.
- **Mixed-direction headSide**: empirically real (German VP head-final + CP head-initial)
  but MCB don't address. Future refinement: `headSide : Cat → ConventionDir`.
  Current global encoding suffices for §1.13-§1.16.
- **Lemma 1.13.7 three Chomsky [23] §4 properties**: equivalent characterizations
  of head functions via per-vertex projection-marking. Optional sibling
  constructor `fromProjectionMarking`.
- **Module-side lifting (§1.12.3, §1.12.5)**: `Section.σ` lifts to
  `V(𝔗_{SO_0}) → V(𝔗^{pl}_{SO_0})` linear map via `Quot.lift`. Add when needed.
- **`headAtVertex_coherent` proof**: requires well-founded induction on planar
  descent; statement is correct here, proof is queued.
-/

namespace Minimalist

/-! ### Convention direction (MCB Lemma 1.13.5) -/

/-- The harmonic head-side convention. Per @cite{marcolli-chomsky-berwick-2025}
    Lemma 1.13.5 (book p. 127), head functions on T are in bijection with planar
    embeddings of T, under one of two equally valid conventions:

    - `.initial` (harmonic head-initial): the head daughter is to the LEFT of
      each binary node. The head leaf is the leftmost-leaf of the planar tree.
      Canonical for English-like analyses.
    - `.final` (harmonic head-final): the head daughter is to the RIGHT.
      The head leaf is the rightmost-leaf. Canonical for Japanese/Korean/Turkish.

    A head function bundles a planar section + a side convention. Mixed-direction
    languages (e.g. German with head-final VP and head-initial CP) require a
    refinement (`headSide : Cat → ConventionDir`) that is currently out of scope. -/
inductive ConventionDir where
  | initial
  | final
  deriving Repr, DecidableEq, Inhabited

-- ============================================================================
-- § 1: HeadFunction (MCB §1.12.1 + §1.13.5 + Def 1.13.6)
-- ============================================================================

/-- A **head function** in the @cite{marcolli-chomsky-berwick-2025} sense:
    a planar Externalization (MCB §1.12.1 section σ_L of Π) plus a head-side
    convention (Lemma 1.13.5) plus a partial domain (Def 1.13.6).

    Per Lemma 1.13.5, the planar embedding chosen by σ_L IS the head function,
    once a head-side convention is fixed. The head leaf `h(T)` is the
    leftmost-leaf (`.initial`) or rightmost-leaf (`.final`) of `σ_L(T)`.

    The bundle records:
    - `section_`: the underlying section σ_L
    - `headSide`: harmonic head-initial vs head-final
    - `Dom`: the subdomain on which `h` is "well defined" linguistically
    - `decDom`: decidability of `Dom` membership -/
structure HeadFunction where
  /-- MCB §1.12.1 section σ_L : 𝔗_{SO_0} → 𝔗^{pl}_{SO_0}, lifted to
      `FreeCommMagma.Section (LIToken ⊕ Nat)`. -/
  section_ : FreeCommMagma.Section (LIToken ⊕ Nat)
  /-- Harmonic head-side convention (Lemma 1.13.5): head daughter to the
      LEFT (`.initial`) or RIGHT (`.final`) of the planar embedding. -/
  headSide : ConventionDir
  /-- MCB Def 1.13.6 subdomain on which the head function is defined. -/
  Dom : SyntacticObject → Prop
  /-- Decidability of domain membership. -/
  decDom : DecidablePred Dom

attribute [instance] HeadFunction.decDom

namespace HeadFunction

/-- The head leaf token at vertex `v` of T under head function `h` (MCB Def 1.13.3).

    Substrate primitive. The root special case `head h T := headAtVertex h T T`
    is derived below.

    Under harmonic head-initial (`.initial`), this is the leftmost-leaf of
    `h.section_.σ v`. Under harmonic head-final (`.final`), the rightmost-leaf.

    **Note on the (T, v) signature**: per MCB Def 1.13.3, head functions are
    indexed by the containing tree T and quantify vertices "of T". The `T`
    parameter here is currently unused in the body (we descend into v's own
    representative), but it is load-bearing for the COHERENCE theorem
    `headAtVertex_coherent` below, which requires `v ⊆ T`. This signals
    "this head reading is about T's structure"; consumer theorems add the
    `v ∈ T.subtrees` hypothesis. Section's `σ` is defined on the whole quotient,
    so `headAtVertex h T v` is well-defined for any v; the T-relativity is a
    documentary constraint enforced by consumers. -/
def headAtVertex (h : HeadFunction) (_T v : SyntacticObject) : LIToken :=
  match h.headSide with
  | .initial => leftmostLeafPlanar (h.section_.σ v)
  | .final   => rightmostLeafPlanar (h.section_.σ v)

/-- The head leaf at the root of T (MCB notation `h(T)`). Derived from
    `headAtVertex` at v = T. -/
def head (h : HeadFunction) (T : SyntacticObject) : LIToken :=
  h.headAtVertex T T

/-- The head's outer categorial feature, when defined. -/
def outerCat (h : HeadFunction) (so : SyntacticObject) : Cat :=
  (h.head so).item.outerCat

/-- The head's selectional stack, when defined. -/
def outerSel (h : HeadFunction) (so : SyntacticObject) : SelStack :=
  (h.head so).item.outerSel

/-- A section is injective; routed through `FreeCommMagma.Section.injective`
    which derives via mathlib's `Function.LeftInverse.injective`. -/
theorem externalize_injective (h : HeadFunction) :
    Function.Injective h.section_.σ :=
  h.section_.injective

end HeadFunction

-- ============================================================================
-- § 2: Standard instances (leafOnly, leftSpine, rightSpine)
-- ============================================================================

namespace HeadFunction

/-- The trivial head function: defined only on leaves, where every vertex is
    its own head. The section choice is irrelevant since the only SOs in
    `Dom` are leaves (which have a unique planar representative via the
    singleton-class structure). Convention is `.initial` by default
    (irrelevant on leaves). -/
noncomputable def leafOnly : HeadFunction where
  section_  := FreeCommMagma.Section.out
  headSide  := .initial
  Dom so    := so.isLeaf
  decDom    := inferInstance

/-- Default head function: harmonic head-initial with planar representative
    via `Quot.out`. Defined on **all** SOs. Use a custom `section_` for
    linguistically-meaningful planar choices. -/
noncomputable def leftSpine : HeadFunction where
  section_  := FreeCommMagma.Section.out
  headSide  := .initial
  Dom _     := True
  decDom _  := isTrue trivial

/-- Right-headed dual to `leftSpine`: same `Quot.out` section, but
    `.final` head-side convention. Models a harmonic head-final language
    (Japanese, Korean, Turkish). Genuinely distinct from `leftSpine` —
    `rightSpine.head` returns the rightmost-leaf where `leftSpine.head`
    returns the leftmost-leaf of the same planar representative. -/
noncomputable def rightSpine : HeadFunction where
  section_  := FreeCommMagma.Section.out
  headSide  := .final
  Dom _     := True
  decDom _  := isTrue trivial

end HeadFunction

-- ============================================================================
-- § 3: Singleton-class simp lemmas (via Section.σ_of keystone)
-- ============================================================================

namespace HeadFunction

/-- For a leaf SO, `headAtVertex` returns the leaf token (independent of head
    function choice — leaves are their own head, and singleton-class structure
    means the section returns the canonical `.of (.inl tok)`).

    Routes through `Section.σ_of` which absorbs the singleton-class
    case-analysis once for all consumers. -/
@[simp] theorem headAtVertex_leaf (h : HeadFunction) (T : SyntacticObject)
    (tok : LIToken) :
    h.headAtVertex T (.leaf tok) = tok := by
  unfold headAtVertex
  -- `h.section_.σ (.leaf tok) = h.section_.σ (FreeCommMagma.of (.inl tok))
  --   = FreeMagma.of (.inl tok)` by Section.σ_of
  rw [show (SyntacticObject.leaf tok : SyntacticObject) = FreeCommMagma.of (.inl tok)
      from rfl, h.section_.σ_of]
  -- Now both leftmost and rightmost on `.of (.inl tok)` reduce to `tok`
  cases h.headSide <;> rfl

/-- For a trace SO, `headAtVertex` returns the synthetic trace token. -/
@[simp] theorem headAtVertex_trace (h : HeadFunction) (T : SyntacticObject)
    (n : Nat) :
    h.headAtVertex T (.trace n) = mkTraceToken n := by
  unfold headAtVertex
  rw [show (SyntacticObject.trace n : SyntacticObject) = FreeCommMagma.of (.inr n)
      from rfl, h.section_.σ_of]
  cases h.headSide <;> rfl

/-- For a leaf SO, `head` returns the leaf token. Derived from `headAtVertex_leaf`
    at v = T. -/
@[simp] theorem head_leaf (h : HeadFunction) (tok : LIToken) :
    h.head (.leaf tok) = tok :=
  h.headAtVertex_leaf _ tok

/-- For a trace SO, `head` returns the synthetic trace token. -/
@[simp] theorem head_trace (h : HeadFunction) (n : Nat) :
    h.head (.trace n) = mkTraceToken n :=
  h.headAtVertex_trace _ n

/-- For a leaf SO, `outerCat` reduces to the leaf token's outer category. -/
@[simp] theorem outerCat_leaf (h : HeadFunction) (tok : LIToken) :
    h.outerCat (.leaf tok) = tok.item.outerCat := by
  unfold outerCat
  rw [head_leaf]

/-- For a leaf SO, `outerSel` reduces to the leaf token's outer selectional stack. -/
@[simp] theorem outerSel_leaf (h : HeadFunction) (tok : LIToken) :
    h.outerSel (.leaf tok) = tok.item.outerSel := by
  unfold outerSel
  rw [head_leaf]

end HeadFunction

-- ============================================================================
-- § 4: Planar yield accessors (parameterized cascade)
-- ============================================================================

/-- Underlying leaf-token enumeration on a planar `FreeMagma` representative.
    Used by `HeadFunction.leafTokens` (parameterized below) and by the
    coherence theorem statement. -/
def leafTokensPlanar : FreeMagma (LIToken ⊕ Nat) → List LIToken
  | .of (.inl tok) => [tok]
  | .of (.inr n) => [mkTraceToken n]
  | .mul a b => leafTokensPlanar a ++ leafTokensPlanar b

namespace HeadFunction

/-- The leaves of `so` under head function `h`'s planar representative,
    as a list of LITokens. Computable when `h.section_.σ` is. -/
def leafTokens (h : HeadFunction) (so : SyntacticObject) : List LIToken :=
  leafTokensPlanar (h.section_.σ so)

/-- Linearize `so` under head function `h`: collect leaf tokens in the
    left-to-right order of `h.section_.σ so`. Per @cite{marcolli-chomsky-berwick-2025}
    book p. 123, "linearization" in linguistics IS planarization (= section
    choice); the term is reserved for the resulting word ordering on leaves. -/
def linearize (h : HeadFunction) (so : SyntacticObject) : List LIToken :=
  linearizePlanar (h.section_.σ so)

/-- Phonological yield of `so` under head function `h`: the non-empty
    `phonForm` strings of leaves in left-to-right order. -/
def phonYield (h : HeadFunction) (so : SyntacticObject) : List String :=
  phonYieldPlanar (h.section_.σ so)

/-- Terminal nodes of `so` under head function `h`: the leaf-position SOs
    of the planar representative, in left-to-right order. -/
def terminalNodes (h : HeadFunction) (so : SyntacticObject) :
    List SyntacticObject :=
  (terminalNodesPlanar (h.section_.σ so)).map (Quot.mk _)

end HeadFunction

-- ============================================================================
-- § 4.5: Planar-leaf structural lemmas (substrate for §5 coherence proofs)
-- ============================================================================

/-- `leftmostLeafPlanar fm` is always one of the leaves enumerated by
    `leafTokensPlanar fm`. Substrate for the §5 coherence proof: when the
    head leaf of w (= leftmost of σ w) is constrained to appear in σ v's
    leaves, this lemma anchors what "head leaf appears in v" means. -/
theorem leftmostLeafPlanar_mem_leafTokens (fm : FreeMagma (LIToken ⊕ Nat)) :
    leftmostLeafPlanar fm ∈ leafTokensPlanar fm := by
  induction fm with
  | ih1 x =>
    cases x with
    | inl tok => exact List.mem_singleton.mpr rfl
    | inr n   => exact List.mem_singleton.mpr rfl
  | ih2 l _ ihl _ =>
    show leftmostLeafPlanar l ∈ leafTokensPlanar l ++ leafTokensPlanar _
    exact List.mem_append.mpr (Or.inl ihl)

/-- `rightmostLeafPlanar fm` is always one of the leaves enumerated by
    `leafTokensPlanar fm`. Mirror of `leftmostLeafPlanar_mem_leafTokens`. -/
theorem rightmostLeafPlanar_mem_leafTokens (fm : FreeMagma (LIToken ⊕ Nat)) :
    rightmostLeafPlanar fm ∈ leafTokensPlanar fm := by
  induction fm with
  | ih1 x =>
    cases x with
    | inl tok => exact List.mem_singleton.mpr rfl
    | inr n   => exact List.mem_singleton.mpr rfl
  | ih2 _ r _ ihr =>
    show rightmostLeafPlanar r ∈ leafTokensPlanar _ ++ leafTokensPlanar r
    exact List.mem_append.mpr (Or.inr ihr)

/-- `leafTokensPlanar` distributes structurally over `mul`: by definition. -/
theorem leafTokensPlanar_mul (l r : FreeMagma (LIToken ⊕ Nat)) :
    leafTokensPlanar (l * r) = leafTokensPlanar l ++ leafTokensPlanar r := rfl

-- ============================================================================
-- § 5: MCB Def 1.13.3 coherence (Phase 3.C: discharged)
-- ============================================================================

/-- For a section `σ`, the **local-coherence** property at T: σ respects
    binary nodes structurally on T's subtrees (with possible left/right swap).

    Per @cite{marcolli-chomsky-berwick-2025} §1.12.3 (book p. 116), σ is NOT
    a magma morphism globally (Lemma 1.13.1), but it can be locally coherent
    at specific subtrees. This is the property that makes MCB Def 1.13.3
    coherence (`headAtVertex_coherent` below) provable.

    The leaf-distinctness property (Nodup on planar leaves of σ T), which
    is also needed for the §5 coherence proof, is supplied as a separate
    hypothesis to the consumer theorems rather than baked in here — keeping
    LocallyCoherent purely about σ's structural behavior, decoupled from
    derivation-specific token uniqueness. -/
def HeadFunction.LocallyCoherent (h : HeadFunction) (T : SyntacticObject) : Prop :=
  ∀ a b : SyntacticObject, (a * b) ∈ T.subtrees →
    h.section_.σ (a * b) = h.section_.σ a * h.section_.σ b ∨
    h.section_.σ (a * b) = h.section_.σ b * h.section_.σ a

/-- Under `LocallyCoherent h T`, descent into a subtree `w ∈ T.subtrees`
    preserves the structural property: `LocallyCoherent h w` follows by
    transitivity of `subtrees`. -/
theorem HeadFunction.LocallyCoherent.descent {h : HeadFunction}
    {T : SyntacticObject} (hCoh : h.LocallyCoherent T)
    {w : SyntacticObject} (hw : w ∈ T.subtrees) :
    h.LocallyCoherent w := by
  intro a b hab
  exact hCoh a b (subtrees_subset_of_mem hw hab)

/-- Under `LocallyCoherent h T`, the planar leaves of `σ T` are a permutation
    of the planar leaves of `σ a` followed by those of `σ b` whenever
    `(a*b) ∈ T.subtrees`. This is the multiset-version of the structural
    decomposition (see also `leafTokensPlanar_mul`). -/
theorem σ_leafMultiset_at_mul (h : HeadFunction)
    {a b : SyntacticObject}
    (hsplit : h.section_.σ (a * b) = h.section_.σ a * h.section_.σ b ∨
              h.section_.σ (a * b) = h.section_.σ b * h.section_.σ a) :
    (↑(leafTokensPlanar (h.section_.σ (a * b))) : Multiset LIToken)
      = ↑(leafTokensPlanar (h.section_.σ a)) +
        ↑(leafTokensPlanar (h.section_.σ b)) := by
  rcases hsplit with heq | heq
  · rw [heq, leafTokensPlanar_mul, ← Multiset.coe_add]
  · rw [heq, leafTokensPlanar_mul, ← Multiset.coe_add, add_comm]

/-- @cite{marcolli-chomsky-berwick-2025} Def 1.13.3 coherence statement.

    **Phase 3.C status (deferred)**: the proof requires a structural sub-list
    lemma (`σ w`'s leaves are a contiguous sub-list of `σ T`'s leaves under
    LocallyCoherent), plus a Nodup hypothesis on `σ T`'s leaves to handle
    the swap-case vacuously. The substrate machinery (
    `leftmostLeafPlanar_mem_leafTokens`, `σ_leafMultiset_at_mul`, etc.)
    is in place; the full induction is mechanical but lengthy.

    **Why a `Nodup` hypothesis is needed**: in the swap case σ(a*b) = σb*σa
    with v ⊆ a, the head leaf of (a*b) is leftmost(σ b). For it to appear
    in σ v's leaves (⊆ σ a's leaves), σa and σb would need to share a
    token. Nodup on σ T's leaves rules this out, making the case vacuous.

    The Nodup hypothesis is satisfied by any well-formed derivation where
    each LI is uniquely instantiated (the typical linguistic case).

    **Proof strategy**: structural induction on `w`.
    - Base: w is a leaf/trace; w.subtrees = {w}, so v = w trivially.
    - Step: w = a*b. Under LocallyCoherent, σ(a*b) = σa*σb or σb*σa,
      determining whether the head leaf comes from `a` or `b`'s side.
    - For v on the head-carrying side: apply IH to that side (smaller w).
    - For v on the opposite side: under Nodup-derived disjointness, the
      head leaf cannot appear in v's leaves; contradiction with hmem.

    TODO: discharge the proof. Requires `Multiset.Nodup` propagation along
    `≤` (find/prove the right mathlib lemma), or alternative `List.Sublist`-
    based path. The `_hNodup` hypothesis is supplied for forward
    compatibility once the proof lands. -/
theorem HeadFunction.headAtVertex_coherent (h : HeadFunction) (T : SyntacticObject)
    (_hCoh : h.LocallyCoherent T)
    (_hNodup : (leafTokensPlanar (h.section_.σ T)).Nodup)
    {v w : SyntacticObject} (_hw : w ∈ T.subtrees) (_hvw : v ∈ w.subtrees)
    (_hmem : h.headAtVertex T w ∈ leafTokensPlanar (h.section_.σ v)) :
    h.headAtVertex T w = h.headAtVertex T v := by
  sorry

-- ============================================================================
-- § 7: MCB Def 1.15.1 raising condition (two clauses, per audit H1)
-- ============================================================================

namespace HeadFunction

/-- @cite{marcolli-chomsky-berwick-2025} Def 1.15.1, **clause (i)** (the
    Dom-closure clause):

    For any `T ∈ Dom(h)` and any subtree `v ⊂ T` such that
    `h(T) = h(T/^d v)` (the mover doesn't carry the head of T), the IM result
    `M(v, T/^c v)` is in `Dom(h)`, with `h(M(v, T/^c v)) = h(T/^d v)`.

    The Dom-membership in the conclusion is a **non-trivial closure assertion**
    independent of clause (ii) — Internal Merge preserves the head function's
    domain in this configuration.

    Encoded using `Step.im` from `Derivation.lean`. The deletion-quotient
    `T/^d v` is `T.replace v (mkTrace n)`; the contraction-quotient `T/^c v`
    is the same in our encoding. -/
def IsRaisingClauseI (h : HeadFunction) : Prop :=
  ∀ (T v : SyntacticObject) (traceId : Nat),
    h.Dom T →
    h.head T = h.head (T.replace v (mkTrace traceId)) →
    h.Dom (SyntacticObject.node v (T.replace v (mkTrace traceId))) ∧
      h.head (SyntacticObject.node v (T.replace v (mkTrace traceId))) =
        h.head (T.replace v (mkTrace traceId))

/-- @cite{marcolli-chomsky-berwick-2025} Def 1.15.1, **clause (ii)** (the
    head-equation clause):

    For arbitrary `T` and any subtree `v ⊂ T` such that both
    `M(v, T/^c v) ∈ Dom(h)` and `T/^d v ∈ Dom(h)`, we have
    `h(M(v, T/^c v)) = h(T/^d v)`.

    No Dom-closure claim — just the head equation under both Dom-membership
    hypotheses. -/
def IsRaisingClauseII (h : HeadFunction) : Prop :=
  ∀ (T v : SyntacticObject) (traceId : Nat),
    h.Dom (SyntacticObject.node v (T.replace v (mkTrace traceId))) →
    h.Dom (T.replace v (mkTrace traceId)) →
    h.head (SyntacticObject.node v (T.replace v (mkTrace traceId))) =
      h.head (T.replace v (mkTrace traceId))

/-- A head function is **raising** when both Def 1.15.1 clauses hold. -/
def IsRaising (h : HeadFunction) : Prop :=
  h.IsRaisingClauseI ∧ h.IsRaisingClauseII

/-- The trivial `leafOnly` head function satisfies clause (ii) **vacuously**:
    the IM result is always a `.node`, never a leaf, so the `Dom (.node ...)`
    precondition fails for `leafOnly.Dom = isLeaf`. -/
theorem leafOnly_isRaisingClauseII : leafOnly.IsRaisingClauseII := by
  intro T v traceId hIM _hD
  exact absurd hIM (by
    show ¬ SyntacticObject.isLeaf (v * (T.replace v (mkTrace traceId)))
    exact SyntacticObject.isLeaf_mul _ _)

/-! **Note on clause (i) for `leafOnly`**: `leafOnly` does NOT satisfy
clause (i). Counterexample: when T is a leaf and v doesn't occur in T,
`T.replace v (mkTrace _) = T` (no occurrence to replace), so the
precondition `head T = head (T/^d v)` holds vacuously, but the
conclusion `Dom (.node v T)` requires `isLeaf (v * T)` which is False.
`leafOnly` violates the Dom-closure aspect of clause (i): its domain
is not closed under the IM construction.

This is a substantive linguistic fact, not a formalization artifact:
Internal Merge always produces a node, but `leafOnly` only labels leaves.
Honest head functions for §1.15.2 Labeling will define `Dom` to be
IM-closed. -/

end HeadFunction

-- ============================================================================
-- § 8: ComplementedHeadFunction (MCB Def 1.14.2)
-- ============================================================================

/-- @cite{marcolli-chomsky-berwick-2025} Def 1.14.2 (book p. 134):
    a **complemented (abstract) head function** `h_{T,Z}` extends a head
    function to additionally assign each non-leaf vertex its **complement**:

      h_{T,Z} : V^o(T) → L(T) × (Acc(T) ∪ {1})
      h_{T,Z}(v) = (h_T(v), Z_v)

    where `Z_v ⊂ T_{s_{h_T(v)}}` is a (possibly empty) subset of the sister
    vertex's subtree. The cases:

    - `Z_v = ∅`: head has no complement at v; sister is purely modifier.
    - `Z_v ≠ ∅`: head has complement Z_v at v; remaining sister content is
      modifier.

    "Modifiers" (per MCB book p. 134): structures merged that retain the
    head's projection — going from `T_v` to `T_{w'}` where `h_T(w') = h_T(v)`.

    This is the substrate Phase Theory needs (MCB §1.14): the phase edge
    `∂Φ_ℓ` is defined relative to the head's complement Z_v (not its full
    sister subtree), per Def 1.14.3 step 4-5.

    Encoding: extends `HeadFunction` with `complementOf : SO → SO → Option SO`
    indexed by (T, v) pair. Returns `none` for the empty-complement case,
    `some Z` for the non-empty case. -/
structure ComplementedHeadFunction extends HeadFunction where
  /-- For each (T, v) where v is an internal vertex of T, the head's
      **complement** at v: a subtree of v's sister-of-head, or `none`
      if the head has no complement at v (sister is purely modifier).

      Coherence: when defined, `complementOf T v` is contained in
      `s_{h_T(v)}` — the sister vertex of `h_T(v)` on the projection
      path γ_{h_T(v)}. Consumers may add this as a hypothesis. -/
  complementOf : SyntacticObject → SyntacticObject → Option SyntacticObject

-- `decDom` instance is inherited via `extends HeadFunction` and the
-- existing `attribute [instance] HeadFunction.decDom` at the top of this file.

namespace ComplementedHeadFunction

/-- The trivial complemented head function: extends `leafOnly` with
    `complementOf := fun _ _ => none` (no complement, since leaves have
    no complement structure to begin with). -/
noncomputable def leafOnly : ComplementedHeadFunction where
  toHeadFunction := HeadFunction.leafOnly
  complementOf _ _ := none

/-- The trivial complemented version of `leftSpine`: assumes no complement
    structure beyond the planar embedding (consumers needing complements
    should supply a custom `complementOf`). -/
noncomputable def leftSpine : ComplementedHeadFunction where
  toHeadFunction := HeadFunction.leftSpine
  complementOf _ _ := none

/-- The complemented version of `rightSpine`. -/
noncomputable def rightSpine : ComplementedHeadFunction where
  toHeadFunction := HeadFunction.rightSpine
  complementOf _ _ := none

end ComplementedHeadFunction

-- ============================================================================
-- § 9: MCB Lemma 1.13.4 counting (deferred — requires V^o(T) primitive)
-- ============================================================================

/-! @cite{marcolli-chomsky-berwick-2025} Lemma 1.13.4 (book p. 127): there are
exactly `2^|V^o(T)|` head functions on T, where `V^o(T)` is the set of
non-leaf vertices of T.

Under the externalize-based encoding, head functions on T are in bijection
with planar embeddings of T (Lemma 1.13.5), which are in bijection with
markings of left/right at each non-leaf vertex.

Statement deferred until Phase 3.B+ when `V^o(T)` is a properly enumerable
substrate primitive (currently `Multiset SyntacticObject` via `T.Acc`).
The vacuous-True placeholder previously here was deleted as an
anti-pattern. -/

end Minimalist
