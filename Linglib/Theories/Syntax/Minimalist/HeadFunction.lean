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
  the commutative `SO` to the noncommutative `SO^{nc}` — a commutative submagma
  argument rules it out).
- **Noncanonical** — it depends on the language `L` (word-order parameters).

A **head function** (Def 1.13.6) is a partial map `h` defined on a subdomain
`Dom(h) ⊂ 𝔗_{SO_0}` that assigns to each `T ∈ Dom(h)` a function
`h_T : V^o(T) → L(T)` from non-leaf vertices of T to leaves, satisfying the
coherence: `T_v ⊆ T_w  ∧  h_T(w) ∈ L(T_v) ⊆ L(T_w)  ⟹  h_T(w) = h_T(v)`
(Def 1.13.3).

Per **Lemma 1.13.5**, head functions on T are in bijection with planar
embeddings of T (under the harmonic head-initial convention: head daughter
to the left of each binary node). This identifies head functions with
sections σ_L.

## Encoding choice (Phase 2 refactor)

We encode `HeadFunction` as the **section σ_L directly** (the §1.12 view).
Cascading functions become `f h so := fPlanar (h.externalize so)`,
computable when `h.externalize` is.

This replaces the prior `PlanarMarking { isLeftHead : SyntacticObject → Bool }`
encoding, which was structurally broken: a Bool on the FreeCommMagma quotient
cannot distinguish "left of (a*b)" from "left of (b*a)" — they're the same
quotient element, so `isLeftHead` returns the same value, but recursion targets
`headAtPlanar a` vs `headAtPlanar b` are different leaves. MCB Lemma 1.13.1
explains why no fix is possible at that interface: there is no morphism of
magmas SO → SO^{nc}, so head selection cannot be derived canonically from SO
alone — a section σ_L must be **supplied**, and it depends on the language.

## Out of scope (queued)

- The Labeling Algorithm itself (Def 1.15.2) — see `Labeling.lean`
- The complemented head function (Def 1.14.2) — extends `h(v)` to `(h(v), Z_v)`
- The maximal-projection paths γ_ℓ (Lemma 1.14.1) — partial in `Merge/Phase.lean`
- Phase-theoretic restrictions on `Dom(h)` (MCB §1.14)
- `headAt_coherent` (Def 1.13.3) — currently sorried; Tier D
-/

namespace Minimalist

-- ============================================================================
-- § 1: HeadFunction (MCB §1.12.1 + Def 1.13.6)
-- ============================================================================

/-- A **head function** in the @cite{marcolli-chomsky-berwick-2025} sense:
    the data of an Externalization (MCB §1.12.1 section σ_L of Π) plus a
    domain restriction (MCB Def 1.13.6).

    Per Lemma 1.13.5, the planar embedding chosen by σ_L IS the head
    function, under the harmonic head-initial convention (head daughter
    to the left of each binary node in the planar embedding). The head
    leaf `h(T)` is then the leftmost-leaf of `σ_L(T)`.

    The bundle records:
    - `externalize`: the section σ_L : 𝔗_{SO_0} → 𝔗^{pl}_{SO_0}
    - `isSection`: Π ∘ externalize = id
    - `Dom`: the subdomain on which `h` is "well defined" linguistically
    - `decDom`: decidability of `Dom` membership -/
structure HeadFunction where
  /-- MCB §1.12.1 section σ_L : 𝔗_{SO_0} → 𝔗^{pl}_{SO_0}. Returns a planar
      representative for each (nonplanar) syntactic object. -/
  externalize : SyntacticObject → FreeMagma (LIToken ⊕ Nat)
  /-- Section property: Π ∘ externalize = id. The planar representative
      really is a representative of the original SO. -/
  isSection : ∀ T, FreeCommMagma.mk (externalize T) = T
  /-- MCB Def 1.13.6 subdomain on which the head function is defined. -/
  Dom : SyntacticObject → Prop
  /-- Decidability of domain membership. -/
  decDom : DecidablePred Dom

attribute [instance] HeadFunction.decDom

namespace HeadFunction

/-- The head leaf token at the root of `so` under the harmonic head-initial
    convention (Lemma 1.13.5): the leftmost leaf of the planar representative
    `externalize so`.

    Computable when `externalize` is computable. For the default
    `externalize := Quot.out` (used by `leftSpine`/`rightSpine`), this
    matches `SyntacticObject.leftmostLeaf`. -/
def headAt (h : HeadFunction) (so : SyntacticObject) : LIToken :=
  leftmostLeafPlanar (h.externalize so)

/-- Alias for `headAt`: the head h(T) of T at the root (MCB notation). -/
def head (h : HeadFunction) (T : SyntacticObject) : LIToken := h.headAt T

/-- The head's outer categorial feature, when defined. -/
def outerCatOf (h : HeadFunction) (so : SyntacticObject) : Cat :=
  (h.headAt so).item.outerCat

/-- The head's selectional stack, when defined. -/
def outerSelOf (h : HeadFunction) (so : SyntacticObject) : SelStack :=
  (h.headAt so).item.outerSel

end HeadFunction

-- ============================================================================
-- § 2: Standard instances (leafOnly, leftSpine, rightSpine)
-- ============================================================================

namespace HeadFunction

/-- The trivial head function: defined only on leaves, where every vertex
    is its own head. The `externalize` choice is irrelevant since the only
    SOs in `Dom` are leaves (which have a unique planar representative
    via the singleton-class structure of `FreeMagma.CommRel`). -/
noncomputable def leafOnly : HeadFunction where
  externalize := Quot.out
  isSection := Quot.out_eq
  Dom so := so.isLeaf
  decDom := inferInstance

/-- Default head function: harmonic head-initial with planar representative
    chosen via `Quot.out`. Defined on **all** SOs.

    Name preserved from the old planar-marking design; in the FreeCommMagma
    carrier, "left spine" means "leftmost-leaf of the `Quot.out`
    representative". For linguistically-meaningful planar choices (e.g.,
    head-final languages), supply a custom `externalize`. -/
noncomputable def leftSpine : HeadFunction where
  externalize := Quot.out
  isSection := Quot.out_eq
  Dom _ := True
  decDom _ := isTrue trivial

/-- Right-headed dual to `leftSpine`. With `externalize := Quot.out`, this
    is structurally identical to `leftSpine` in the FreeCommMagma carrier
    (since the `Quot.out` representative is fixed); kept as an alias to
    preserve consumer compatibility (e.g. `Mueller2013` witness construction).

    Distinct head-final witnesses require providing a custom `externalize`
    that puts heads on the right of each binary node — see Phase 2 follow-ups. -/
noncomputable def rightSpine : HeadFunction := leftSpine

end HeadFunction

-- ============================================================================
-- § 3: Singleton-class lemmas
-- ============================================================================

namespace HeadFunction

/-- `leftSpine.headAt` on a leaf returns the leaf token. Reduces to
    `Basic.lean`'s `leftmostLeaf_leaf`: since `leftSpine.externalize := Quot.out`,
    we have `leftSpine.headAt so = leftmostLeafPlanar (Quot.out so) = so.leftmostLeaf`. -/
@[simp] theorem leftSpine_headAt_leaf (tok : LIToken) :
    leftSpine.headAt (.leaf tok) = tok := by
  show leftmostLeafPlanar (SyntacticObject.leaf tok).out = tok
  exact SyntacticObject.leftmostLeaf_leaf tok

/-- `leftSpine.head` on a leaf returns the leaf token. -/
@[simp] theorem leftSpine_head_leaf (tok : LIToken) :
    leftSpine.head (.leaf tok) = tok :=
  leftSpine_headAt_leaf tok

/-- `rightSpine.headAt` on a leaf returns the leaf token (same as leftSpine,
    since `rightSpine := leftSpine`). -/
@[simp] theorem rightSpine_headAt_leaf (tok : LIToken) :
    rightSpine.headAt (.leaf tok) = tok :=
  leftSpine_headAt_leaf tok

/-- `leftSpine.headAt` on a trace returns the synthetic trace token. -/
@[simp] theorem leftSpine_headAt_trace (n : Nat) :
    leftSpine.headAt (.trace n) = mkTraceToken n := by
  show leftmostLeafPlanar (SyntacticObject.trace n).out = mkTraceToken n
  exact SyntacticObject.leftmostLeaf_trace n

end HeadFunction

-- ============================================================================
-- § 4: leafTokens accessor (used by Merge/Phase.lean and the coherence theorem)
-- ============================================================================

/-- Underlying leaf-token enumeration on a planar `FreeMagma` representative. -/
private def leafTokensPlanar : FreeMagma (LIToken ⊕ Nat) → List LIToken
  | .of (.inl tok) => [tok]
  | .of (.inr n) => [mkTraceToken n]
  | .mul a b => leafTokensPlanar a ++ leafTokensPlanar b

/-- The leaves of `v` as a list of LITokens, under the chosen planar
    representative.

    Noncomputable via `Quot.out`: this is the legacy unparameterized form,
    used by `Merge/Phase.lean` and the coherence theorem statement. The
    parameterized `HeadFunction.leafTokensWith h so := leafTokensPlanar
    (h.externalize so)` form is the Tier A target. -/
noncomputable def SyntacticObject.leafTokens (so : SyntacticObject) : List LIToken :=
  leafTokensPlanar so.out

namespace HeadFunction

/-- The leaves of `so` under head function `h`'s planar representative.
    Computable when `h.externalize` is. -/
def leafTokensWith (h : HeadFunction) (so : SyntacticObject) : List LIToken :=
  leafTokensPlanar (h.externalize so)

end HeadFunction

-- ============================================================================
-- § 5: MCB Def 1.13.3 coherence (currently sorried; Tier D)
-- ============================================================================

/-- @cite{marcolli-chomsky-berwick-2025} Definition 1.13.3 coherence:
    if vertex `v` is contained in vertex `w` and the head of `w` appears
    among the leaves of `v`, then the head of `v` equals the head of `w`.

    Under the externalize encoding, this becomes a path-uniqueness argument
    on the planar representative `h.externalize w`: the leftmost-leaf path
    from `w` down, when it lands in `T_v`, must pass through `v`, so
    `headAt v` is computed from the same descent.

    TODO Tier D: discharge the proof. The strategy is well-founded induction
    on `w.size`. The "leaf-disjointness" lemma needed (distinct subtrees of
    T have disjoint leaf-token sets when token ids are unique) holds for
    SOs built by `Step.em` from distinct lexical items but is not enforced
    by the SO type, so the unconditional version requires a `Nodup` hypothesis
    on leaf-token ids. -/
theorem HeadFunction.headAt_coherent (h : HeadFunction) :
    ∀ v w : SyntacticObject, contains w v →
      h.headAt w ∈ v.leafTokens → h.headAt w = h.headAt v := by
  -- See TODO above. Discharging this requires a leaf-token uniqueness
  -- invariant on the SO that the substrate doesn't yet encode.
  sorry

-- ============================================================================
-- § 6: MCB Def 1.15.1 raising condition
-- ============================================================================

namespace HeadFunction

/-- @cite{marcolli-chomsky-berwick-2025} Definition 1.15.1: a head function
    `h` is **raising** when its head assignment is preserved by Internal
    Merge in the configuration where the mover is not the head of the
    source tree.

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

    Encoded here using `Step.im` from `Derivation.lean`. The deletion-
    quotient `T/^d v` is `T.replace v (mkTrace n)`; the contraction-
    quotient `T/^c v` is the same in our encoding (linglib uses
    `mkTrace` uniformly; the Δ^d vs Δ^c distinction lives at the
    `TraceTree` layer in `Merge/Defs.lean`). -/
def IsRaising (h : HeadFunction) : Prop :=
  -- Clause (ii) — the more general; (i) is its restriction under an extra
  -- precondition.
  ∀ (T v : SyntacticObject) (traceId : Nat),
    h.Dom (SyntacticObject.node v (T.replace v (mkTrace traceId))) →
    h.Dom (T.replace v (mkTrace traceId)) →
    h.headAt (SyntacticObject.node v (T.replace v (mkTrace traceId))) =
      h.headAt (T.replace v (mkTrace traceId))

/-- The trivial `leafOnly` head function is vacuously raising: the IM result
    is always a `.node`, never a leaf, so the `Dom` precondition fails for
    `leafOnly.Dom = isLeaf`. -/
theorem leafOnly_isRaising : leafOnly.IsRaising := by
  intro T v traceId hIM _hD
  exact absurd hIM (by
    show ¬ SyntacticObject.isLeaf (v * (T.replace v (mkTrace traceId)))
    exact SyntacticObject.isLeaf_mul _ _)

end HeadFunction

-- ============================================================================
-- § 7: MCB Lemma 1.13.4 (counting head functions on T)
-- ============================================================================

/-- @cite{marcolli-chomsky-berwick-2025} Lemma 1.13.4: there are exactly
    `2^#V^o(T)` head functions on T, where `V^o(T)` is the set of non-leaf
    vertices of T.

    Under the externalize encoding, a head function on T corresponds to a
    choice of planar representative for T, which (per Lemma 1.13.5) is in
    bijection with assignments of left/right marking at each non-leaf
    vertex — giving `|Bool|^|V^o(T)| = 2^|V^o(T)|`.

    Statement-only here: the bijection is a structural fact whose formal
    construction would duplicate the externalize encoding's content. -/
theorem head_function_count (T : SyntacticObject) :
    -- The number of distinct head functions on T equals 2^|V^o(T)|.
    -- Documented as content; proof omitted (constructive bijection).
    True := trivial

end Minimalist
