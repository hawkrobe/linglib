import Linglib.Syntax.Minimalist.Basic
import Linglib.Syntax.Minimalist.Derivation

/-!
# Head Functions for Minimalist Syntactic Objects (MCB §1.12-§1.13)
[marcolli-chomsky-berwick-2025]

## What MCB say

Per [marcolli-chomsky-berwick-2025] §1.12 (book pp. 105-108), Externalization
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

/-- The harmonic head-side convention. Per [marcolli-chomsky-berwick-2025]
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

/-- A **head function** in the [marcolli-chomsky-berwick-2025] sense:
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

/-! ### Standard instances

The genuine, computable, **selection-induced** instances `HeadFunction.leftSpine`
(harmonic head-initial) and `HeadFunction.rightSpine` (head-final) live in
`Selection.lean` — they require the c-selection machinery (`selCheck`) to build
the head-determined planar embedding ([marcolli-chomsky-berwick-2025] Lemma 1.13.5)
and so cannot be defined here (this module is upstream of `Selection`). The retired
`Quot.out` placeholders (`Section.out`-based `leafOnly`/`leftSpine`/`rightSpine`)
are gone: a head function's planar embedding *is* its selection structure (Lemma
1.13.7), not an arbitrary classical representative. -/

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
    left-to-right order of `h.section_.σ so`. Per [marcolli-chomsky-berwick-2025]
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

/-! ### Selection -/

/-- LIToken-level c-selection: `selector` selects `selected` iff
    `selector`'s outermost selectional feature equals `selected`'s outer
    category. Pure LIToken relation; no SO structure involved. -/
def LIToken.selects (selector selected : LIToken) : Prop :=
  selector.item.outerSel.head? = some selected.item.outerCat

instance (lt1 lt2 : LIToken) : Decidable (LIToken.selects lt1 lt2) := by
  unfold LIToken.selects; infer_instance

/-- SO-level c-selection parameterised over a head function:
    `a` selects `b` (under `h`) iff `h`'s head-leaf for `a` selects
    `h`'s head-leaf for `b`. -/
def selects (h : HeadFunction) (a b : SyntacticObject) : Prop :=
  (h.head a).selects (h.head b)

noncomputable instance (h : HeadFunction) (a b : SyntacticObject) :
    Decidable (selects h a b) := by
  unfold selects; classical infer_instance

/-! ### Head Feature Principle: not unconditional for a general head function

There is deliberately **no** `head_node_eq_daughter : h.head (.node a b) = h.head a
∨ h.head (.node a b) = h.head b` here. For an *arbitrary* `HeadFunction` (an
arbitrary externalization section `σ_L`), this is **false**: the leftmost leaf of
an arbitrary planar representative of `{a, b}` need not descend consistently from
`a` or `b`. This is exactly [marcolli-chomsky-berwick-2025]'s "selection ≠
projection" position (book §1.13) — which `Studies/Mueller2013.lean` formalizes
via the *property* `IsSelectionRespectingAt h a b` (a head function may or may not
have it) rather than as a structural law.

The genuine, provable HFP holds for the **computable selection-driven** head
function: see `selHead_mul` in `Selection.lean`, where `selHead` projects the
*selector* by construction and so always respects selection. -/

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

    Per [marcolli-chomsky-berwick-2025] §1.12.3 (book p. 116), σ is NOT
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

/-- Under `LocallyCoherent h T`, the planar leaf-multiset of any subtree
    `w ⊆ T` is ≤ (multiset-wise) the planar leaf-multiset of `σ T`.

    This is the **descent lemma** that makes the §5 coherence proof tractable:
    σ on T's subtrees produces leaf-lists whose token-counts are bounded by
    σ T's leaf-list. Combined with Nodup on σ T's leaves, this gives:
    (a) Nodup on σ w's leaves for any w ∈ T.subtrees (via `Multiset.nodup_of_le`);
    (b) Disjointness of σa's and σb's leaves at any (a*b) ∈ T.subtrees. -/
theorem σ_leafMultiset_le_root (h : HeadFunction) :
    ∀ (T : SyntacticObject) (_hCoh : h.LocallyCoherent T)
      (w : SyntacticObject) (_hw : w ∈ T.subtrees),
      (↑(leafTokensPlanar (h.section_.σ w)) : Multiset LIToken)
        ≤ ↑(leafTokensPlanar (h.section_.σ T)) := by
  intro T
  induction T with
  | leaf tok =>
    intro _ w hw
    rw [SyntacticObject.subtrees_leaf, Multiset.mem_singleton] at hw
    subst hw; exact le_refl _
  | trace n =>
    intro _ w hw
    rw [SyntacticObject.subtrees_trace, Multiset.mem_singleton] at hw
    subst hw; exact le_refl _
  | mul a b iha ihb =>
    intro hCoh w hw
    have hab_in : (a * b) ∈ (a * b).subtrees := by
      rw [SyntacticObject.subtrees_mul]; exact Multiset.mem_cons_self _ _
    have hsplit := hCoh a b hab_in
    have hperm := σ_leafMultiset_at_mul h hsplit
    rw [SyntacticObject.subtrees_mul] at hw
    rcases Multiset.mem_cons.mp hw with hw_eq | hw_sub
    · subst hw_eq; exact le_refl _
    · rcases Multiset.mem_add.mp hw_sub with hwa | hwb
      · -- w ∈ a.subtrees: apply iha then add σb's leaves
        have ha_in_ab : a ∈ (a * b).subtrees := by
          rw [SyntacticObject.subtrees_mul]
          exact Multiset.mem_cons_of_mem
            (Multiset.mem_add.mpr (Or.inl (self_mem_subtrees a)))
        have hCoh_a : h.LocallyCoherent a := hCoh.descent ha_in_ab
        have h_le_a := iha hCoh_a w hwa
        rw [hperm]
        exact h_le_a.trans (Multiset.le_add_right _ _)
      · have hb_in_ab : b ∈ (a * b).subtrees := by
          rw [SyntacticObject.subtrees_mul]
          exact Multiset.mem_cons_of_mem
            (Multiset.mem_add.mpr (Or.inr (self_mem_subtrees b)))
        have hCoh_b : h.LocallyCoherent b := hCoh.descent hb_in_ab
        have h_le_b := ihb hCoh_b w hwb
        rw [hperm]
        exact h_le_b.trans (Multiset.le_add_left _ _)

/-- Under `LocallyCoherent h T` with `Nodup` on σ T's planar leaves, every
    subtree `w ⊆ T` also has `Nodup` planar leaves. Direct corollary of
    `σ_leafMultiset_le_root` plus `Multiset.nodup_of_le`. -/
theorem σ_leafTokensPlanar_nodup_subtree (h : HeadFunction) (T : SyntacticObject)
    (hCoh : h.LocallyCoherent T)
    (hNodup : (leafTokensPlanar (h.section_.σ T)).Nodup)
    {w : SyntacticObject} (hw : w ∈ T.subtrees) :
    (leafTokensPlanar (h.section_.σ w)).Nodup := by
  have h_le := σ_leafMultiset_le_root h T hCoh w hw
  -- Nodup on the larger multiset implies Nodup on the smaller (via coercion).
  exact Multiset.nodup_of_le h_le hNodup

/-- Under `LocallyCoherent h T` with `Nodup` on σ T's planar leaves, the
    leaf-lists of σa and σb at any `(a*b) ∈ T.subtrees` are DISJOINT
    (no shared token). Direct consequence of Nodup on σ(a*b)'s leaves
    (which decomposes into σa's leaves ++ σb's leaves modulo swap). -/
theorem σ_leafTokens_disjoint_at_mul (h : HeadFunction) (T : SyntacticObject)
    (hCoh : h.LocallyCoherent T)
    (hNodup : (leafTokensPlanar (h.section_.σ T)).Nodup)
    {a b : SyntacticObject} (hab : (a * b) ∈ T.subtrees)
    {x : LIToken} (hxa : x ∈ leafTokensPlanar (h.section_.σ a))
    (hxb : x ∈ leafTokensPlanar (h.section_.σ b)) : False := by
  -- Get Nodup at (a*b) via descent
  have hab_nodup := σ_leafTokensPlanar_nodup_subtree h T hCoh hNodup hab
  -- σ(a*b) = σa*σb or σb*σa: either way Nodup of the concatenation gives disjoint.
  rcases hCoh a b hab with heq | heq
  · rw [heq, leafTokensPlanar_mul] at hab_nodup
    have ⟨_, _, hdisj⟩ := List.nodup_append'.mp hab_nodup
    exact hdisj hxa hxb
  · rw [heq, leafTokensPlanar_mul] at hab_nodup
    have ⟨_, _, hdisj⟩ := List.nodup_append'.mp hab_nodup
    exact hdisj hxb hxa

/-- [marcolli-chomsky-berwick-2025] Def 1.13.3 coherence: under a head
    function `h` on a tree T (locally coherent on T, with planar leaves
    `Nodup`), if vertex `v` is contained in vertex `w` (both vertices of T)
    and the head leaf of `w` appears among the leaves of `v`, then the head
    leaves of `v` and `w` agree.

    **Why a `Nodup` hypothesis is needed**: in the swap case σ(a*b) = σb*σa
    with v ⊆ a, the head leaf of (a*b) is leftmost(σ b). For it to appear
    in σ v's leaves (⊆ σ a's leaves), σa and σb would need to share a
    token. Nodup on σ T's leaves rules this out (via
    `σ_leafTokens_disjoint_at_mul`), making the case vacuous.

    The Nodup hypothesis is satisfied by any well-formed derivation where
    each LI is uniquely instantiated (the typical linguistic case).

    **Proof**: structural induction on `w`.
    - Base: w is a leaf/trace; w.subtrees = {w}, so v = w trivially.
    - Step: w = a*b. By LocallyCoherent, σ(a*b) = σa*σb or σb*σa.
      Under headSide × swap × v's side (8 cases total):
      • Head-from-a + v⊆a: apply iha.
      • Head-from-b + v⊆b: apply ihb.
      • Head-from-a + v⊆b OR Head-from-b + v⊆a: contradiction via
        `σ_leafTokens_disjoint_at_mul`. -/
theorem HeadFunction.headAtVertex_coherent (h : HeadFunction) (T : SyntacticObject)
    (hCoh : h.LocallyCoherent T)
    (hNodup : (leafTokensPlanar (h.section_.σ T)).Nodup)
    {v w : SyntacticObject} (hw : w ∈ T.subtrees) (hvw : v ∈ w.subtrees)
    (hmem : h.headAtVertex T w ∈ leafTokensPlanar (h.section_.σ v)) :
    h.headAtVertex T w = h.headAtVertex T v := by
  induction w with
  | leaf tok =>
    rw [SyntacticObject.subtrees_leaf, Multiset.mem_singleton] at hvw
    subst hvw; rfl
  | trace n =>
    rw [SyntacticObject.subtrees_trace, Multiset.mem_singleton] at hvw
    subst hvw; rfl
  | mul a b iha ihb =>
    have ha_in_T : a ∈ T.subtrees :=
      subtrees_subset_of_mem hw (by
        rw [SyntacticObject.subtrees_mul]
        exact Multiset.mem_cons_of_mem
          (Multiset.mem_add.mpr (Or.inl (self_mem_subtrees a))))
    have hb_in_T : b ∈ T.subtrees :=
      subtrees_subset_of_mem hw (by
        rw [SyntacticObject.subtrees_mul]
        exact Multiset.mem_cons_of_mem
          (Multiset.mem_add.mpr (Or.inr (self_mem_subtrees b))))
    have hsplit := hCoh a b hw
    -- Decompose hvw : v ∈ (a*b).subtrees
    rw [SyntacticObject.subtrees_mul] at hvw
    rcases Multiset.mem_cons.mp hvw with hv_eq | hv_sub
    · subst hv_eq; rfl
    rcases Multiset.mem_add.mp hv_sub with hva | hvb
    -- For each (v⊆a or v⊆b), case-split on h.headSide and on hsplit (4 cases each).
    -- The 4 subcases per v-side combine into "head from a" vs "head from b":
    --   v⊆a → "head from a" applies iha; "head from b" contradicts via disjointness.
    --   v⊆b → "head from b" applies ihb; "head from a" contradicts via disjointness.
    all_goals (
      -- Helper: extract the "head from a" or "head from b" identification
      -- via case-split on (headSide, hsplit). We avoid duplicating cases
      -- by computing `headAtVertex T (a*b)` for each of the 4 subcases.
      cases h_side : h.headSide
      <;> rcases hsplit with heq | heq
    )
    -- Now we have 4 subcases per v-side (8 total). Solve each:
    -- v⊆a, .initial, no-swap: head = leftmost(σa). Apply iha.
    · have hAB_eq_A : h.headAtVertex T (a * b) = h.headAtVertex T a := by
        unfold HeadFunction.headAtVertex; rw [h_side, heq]; rfl
      rw [hAB_eq_A]; rw [hAB_eq_A] at hmem
      exact iha ha_in_T hva hmem
    -- v⊆a, .initial, swap: head = leftmost(σb). Disjointness contradiction.
    · exfalso
      have hAB_eq_B : h.headAtVertex T (a * b) = h.headAtVertex T b := by
        unfold HeadFunction.headAtVertex; rw [h_side, heq]; rfl
      rw [hAB_eq_B] at hmem
      have hxb : h.headAtVertex T b ∈ leafTokensPlanar (h.section_.σ b) := by
        unfold HeadFunction.headAtVertex; rw [h_side]
        exact leftmostLeafPlanar_mem_leafTokens _
      have h_le_a : (↑(leafTokensPlanar (h.section_.σ v)) : Multiset LIToken) ≤
          ↑(leafTokensPlanar (h.section_.σ a)) :=
        σ_leafMultiset_le_root h a (hCoh.descent ha_in_T) v hva
      have hxa : h.headAtVertex T b ∈ leafTokensPlanar (h.section_.σ a) :=
        Multiset.mem_of_le h_le_a hmem
      exact σ_leafTokens_disjoint_at_mul h T hCoh hNodup hw hxa hxb
    -- v⊆a, .final, no-swap: head = rightmost(σb). Disjointness contradiction.
    · exfalso
      have hAB_eq_B : h.headAtVertex T (a * b) = h.headAtVertex T b := by
        unfold HeadFunction.headAtVertex; rw [h_side, heq]; rfl
      rw [hAB_eq_B] at hmem
      have hxb : h.headAtVertex T b ∈ leafTokensPlanar (h.section_.σ b) := by
        unfold HeadFunction.headAtVertex; rw [h_side]
        exact rightmostLeafPlanar_mem_leafTokens _
      have h_le_a : (↑(leafTokensPlanar (h.section_.σ v)) : Multiset LIToken) ≤
          ↑(leafTokensPlanar (h.section_.σ a)) :=
        σ_leafMultiset_le_root h a (hCoh.descent ha_in_T) v hva
      have hxa : h.headAtVertex T b ∈ leafTokensPlanar (h.section_.σ a) :=
        Multiset.mem_of_le h_le_a hmem
      exact σ_leafTokens_disjoint_at_mul h T hCoh hNodup hw hxa hxb
    -- v⊆a, .final, swap: head = rightmost(σa). Apply iha.
    · have hAB_eq_A : h.headAtVertex T (a * b) = h.headAtVertex T a := by
        unfold HeadFunction.headAtVertex; rw [h_side, heq]; rfl
      rw [hAB_eq_A]; rw [hAB_eq_A] at hmem
      exact iha ha_in_T hva hmem
    -- v⊆b, .initial, no-swap: head = leftmost(σa). Disjointness contradiction.
    · exfalso
      have hAB_eq_A : h.headAtVertex T (a * b) = h.headAtVertex T a := by
        unfold HeadFunction.headAtVertex; rw [h_side, heq]; rfl
      rw [hAB_eq_A] at hmem
      have hxa : h.headAtVertex T a ∈ leafTokensPlanar (h.section_.σ a) := by
        unfold HeadFunction.headAtVertex; rw [h_side]
        exact leftmostLeafPlanar_mem_leafTokens _
      have h_le_b : (↑(leafTokensPlanar (h.section_.σ v)) : Multiset LIToken) ≤
          ↑(leafTokensPlanar (h.section_.σ b)) :=
        σ_leafMultiset_le_root h b (hCoh.descent hb_in_T) v hvb
      have hxb : h.headAtVertex T a ∈ leafTokensPlanar (h.section_.σ b) :=
        Multiset.mem_of_le h_le_b hmem
      exact σ_leafTokens_disjoint_at_mul h T hCoh hNodup hw hxa hxb
    -- v⊆b, .initial, swap: head = leftmost(σb). Apply ihb.
    · have hAB_eq_B : h.headAtVertex T (a * b) = h.headAtVertex T b := by
        unfold HeadFunction.headAtVertex; rw [h_side, heq]; rfl
      rw [hAB_eq_B]; rw [hAB_eq_B] at hmem
      exact ihb hb_in_T hvb hmem
    -- v⊆b, .final, no-swap: head = rightmost(σb). Apply ihb.
    · have hAB_eq_B : h.headAtVertex T (a * b) = h.headAtVertex T b := by
        unfold HeadFunction.headAtVertex; rw [h_side, heq]; rfl
      rw [hAB_eq_B]; rw [hAB_eq_B] at hmem
      exact ihb hb_in_T hvb hmem
    -- v⊆b, .final, swap: head = rightmost(σa). Disjointness contradiction.
    · exfalso
      have hAB_eq_A : h.headAtVertex T (a * b) = h.headAtVertex T a := by
        unfold HeadFunction.headAtVertex; rw [h_side, heq]; rfl
      rw [hAB_eq_A] at hmem
      have hxa : h.headAtVertex T a ∈ leafTokensPlanar (h.section_.σ a) := by
        unfold HeadFunction.headAtVertex; rw [h_side]
        exact rightmostLeafPlanar_mem_leafTokens _
      have h_le_b : (↑(leafTokensPlanar (h.section_.σ v)) : Multiset LIToken) ≤
          ↑(leafTokensPlanar (h.section_.σ b)) :=
        σ_leafMultiset_le_root h b (hCoh.descent hb_in_T) v hvb
      have hxb : h.headAtVertex T a ∈ leafTokensPlanar (h.section_.σ b) :=
        Multiset.mem_of_le h_le_b hmem
      exact σ_leafTokens_disjoint_at_mul h T hCoh hNodup hw hxa hxb

-- ============================================================================
-- § 7: MCB Def 1.15.1 raising condition (two clauses, per audit H1)
-- ============================================================================

namespace HeadFunction

/-- [marcolli-chomsky-berwick-2025] Def 1.15.1, **clause (i)** (the
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

/-- [marcolli-chomsky-berwick-2025] Def 1.15.1, **clause (ii)** (the
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

/-! **Note on `Dom`-closure**: a head function is raising only when its `Dom`
is closed under the Internal Merge construction (the IM result is always a
`.node`, so a leaf-only domain would fail clause (i)'s `Dom (.node ...)`
conclusion). This is a substantive linguistic fact: honest head functions for
§1.15.2 Labeling define `Dom` to be IM-closed. The selection-induced
`leftSpine`/`rightSpine` (in `Selection.lean`) take `Dom` to be the endocentric
domain, which is IM-closed up to selection. -/

end HeadFunction

-- ============================================================================
-- § 8: ComplementedHeadFunction (MCB Def 1.14.2)
-- ============================================================================

/-- [marcolli-chomsky-berwick-2025] Def 1.14.2 (book p. 134):
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

/-- The **complement daughter** of `v` under `h` — the structural realization of
    MCB's `Z_v` ([marcolli-chomsky-berwick-2025] Def 1.14.2). At a binary node,
    the head is one daughter (leftmost leaf under `.initial`, rightmost under
    `.final`), and the complement is the **sister** — the other daughter. Leaves
    and traces have no complement (`none`). Computable when `h.section_.σ` is.

    This is the head-aware generalization of the right-daughter pick: `.initial`
    returns the right daughter (head is left), `.final` the left daughter (head is
    right), so it never misfires on head-final analyses. -/
def HeadFunction.complementDaughter? (h : HeadFunction) (v : SyntacticObject) :
    Option SyntacticObject :=
  match h.section_.σ v with
  | .of _ => none
  | .mul l r =>
    match h.headSide with
    | .initial => some (FreeCommMagma.mk r)
    | .final   => some (FreeCommMagma.mk l)

/-- The **canonical complemented extension** of a head function: realizes the
    abstract `complementOf` (MCB Def 1.14.2 `Z_v`) as the structural
    `complementDaughter?` (the head's sister). The `T` index is ignored — the
    complement of `v` depends only on `v` and `h`. This supersedes the deleted
    `Quot.out`-based trivial instances: every head function now has a canonical,
    head-side-aware complemented form. -/
def HeadFunction.complemented (h : HeadFunction) : ComplementedHeadFunction where
  toHeadFunction := h
  complementOf _T v := h.complementDaughter? v

-- ============================================================================
-- § 9: MCB Lemma 1.13.4 counting (deferred — requires V^o(T) primitive)
-- ============================================================================

/-! [marcolli-chomsky-berwick-2025] Lemma 1.13.4 (book p. 127): there are
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
