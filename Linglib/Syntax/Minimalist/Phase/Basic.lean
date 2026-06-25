import Linglib.Syntax.Minimalist.HeadFunction

/-!
# Phase Theory — MCB §1.14 substrate
[marcolli-chomsky-berwick-2025] §1.14

The head-function-derived foundation for Phase Theory: the `(h, T, ℓ)`-indexed
primitives (`maximalProjection`, `phaseComplementZ`, `phaseInterior`, `phaseEdge`,
`inaccessibleTerms`, …) that the bundled `Phase` API (`Syntax/Minimalist/Phase.lean`)
and the phase coproduct Δ^c_Φ (`Phase/Coproduct.lean`) are built on. Everything is
*derived* from the **vertex-keyed head function** `headAtVertex` (`HeadFunction.lean`),
not stipulated.

## What MCB §1.14 says

Phase Theory is *defined via the head function*, not stipulated. Given
a head function `h_T` on T, **Lemma 1.14.1** partitions the vertices of T
into projection paths γ_ℓ — one per leaf ℓ — where γ_ℓ is the path
from ℓ up to its **maximal projection** vertex v_ℓ (the highest vertex
w with h_T(w) = ℓ). **Definition 1.14.3** then identifies the **phases**
Φ_ℓ ⊂ T as the accessible terms inside v_ℓ, partitioning the syntactic
object.

The **inaccessibility set** Y_ℓ (eq 1.14.5) is then the set of
accessible terms in the *interior* of any *lower* phase. The **phase
coproduct** Δ^c_Φ (Definition 1.14.5) is the algebraic operator that
extracts only the *accessible* (= non-inaccessible) terms from T —
this is the algebraic implementation of the Phase Impenetrability
Condition. Lemma 1.14.6 proves Δ^c_Φ is well-defined and coassociative.

## Encoding (post Phase 3.B.1 refoundation)

- All vertex-relative head queries route through `HeadFunction.headAtVertex h T w`,
  the substrate primitive landed in Phase 3.A. The T parameter is the
  containing tree (per MCB Def 1.13.3); v is a vertex of T (per the
  `v ∈ T.subtrees` consumer-side hypothesis).
- The body of `headAtVertex h T v` currently descends into v's own planar
  representative (`h.section_.σ v`) rather than searching for v inside
  `h.section_.σ T`. These agree IFF the section is **locally coherent**
  on T (i.e., `h.section_.σ (a*b) ∈ {(h.section_.σ a) * (h.section_.σ b),
  (h.section_.σ b) * (h.section_.σ a)}`). All theorems below are stated
  modulo this coherence hypothesis where required.

## What this file does

- **§1**: Lemma 1.14.1 substrate — `projectionPath`, `maximalProjection`,
  the chain-on-γ theorem (statement; proof requires §1.13.3 coherence).
- **§2**: `phaseHeadLeaves` (L_Φ(T) of Def 1.14.3 eq 1.14.1).
- **§3**: `phaseComplementZ` (the head's complement Z_ℓ via `complementInPlanar`,
  Def 1.14.2 / Def 1.14.3 step 3), `phase` (Φ_ℓ, eq 1.14.2), `phaseInterior`
  (Φ°_ℓ = the complement, eq 1.14.3), `phaseEdge` (∂Φ_ℓ, eq 1.14.4).
- **§4**: `inaccessibleTerms` (Υ_ℓ, eq 1.14.5), `inaccessibleTerms_strong`
  (Remark 1.14.4), and `phaseAccessibleAt` (Φ_ℓ ∖ Υ_ℓ).

## Notes

- The **interior is the complement** (MCB Def 1.14.3, "Z is the interior of the
  phase"), via `phaseComplementZ` = the head's sister at its mother node. This
  supersedes the earlier `T_{v_ℓ}` over-approximation (now `phase`, eq 1.14.2).
- The **algebraic phase coproduct** Δ^c_Φ (Def 1.14.5 eq 1.14.6) + coassociativity
  (Lemma 1.14.6) live downstream in `Merge/PhaseCoproduct.lean`.
- `ComplementedHeadFunction` (Def 1.14.2) is in `HeadFunction.lean`; its canonical
  structural realization is `HeadFunction.complementDaughter?`/`.complemented`.
-/

namespace Minimalist.Phase

open Minimalist (HeadFunction ComplementedHeadFunction SyntacticObject LIToken)

-- ============================================================================
-- § 1: Maximal Projection Vertex (Lemma 1.14.1)
-- ============================================================================

/-- The projection path γ_ℓ of leaf ℓ in T under head function h
    ([marcolli-chomsky-berwick-2025] Lemma 1.14.1): the multiset of
    vertices `w ∈ V(T)` such that `headAtVertex h T w = ℓ`.

    Per Lemma 1.14.1, this multiset forms a path in T from ℓ up to the
    maximal projection vertex v_ℓ. The path is **trivial** (contains
    only ℓ itself) when ℓ is not the head of any internal vertex of T. -/
noncomputable def projectionPath (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Multiset SyntacticObject :=
  T.subtrees.filter (fun w => decide (h.headAtVertex T w = ℓ))

/-- Helper: subtree membership gives equality OR containment.
    Direct from `Minimalist.isTermOf_iff_mem_subtrees`. -/
private theorem mem_subtrees_imp_eq_or_contains
    {y z : SyntacticObject} (h : z ∈ y.subtrees) :
    z = y ∨ Minimalist.contains y z := by
  rcases (Minimalist.isTermOf_iff_mem_subtrees y z).mpr h with heq | hcontains
  · exact Or.inl heq
  · exact Or.inr hcontains

/-- Auxiliary version of `projectionPath_chain` parameterized by an outer
    induction on T. Both `headAtVertex T w = ℓ` and `w ∈ T.subtrees` are
    surfaced as separate hypotheses (since `headAtVertex` doesn't depend on T,
    we can apply IH cleanly to subtrees). -/
private theorem projectionPath_chain_aux (h : HeadFunction) :
    ∀ T : SyntacticObject, h.LocallyCoherent T →
      (leafTokensPlanar (h.section_.σ T)).Nodup →
      ∀ (ℓ : LIToken) (w₁ w₂ : SyntacticObject),
        w₁ ∈ T.subtrees → w₂ ∈ T.subtrees →
        h.headAtVertex T w₁ = ℓ → h.headAtVertex T w₂ = ℓ →
        Minimalist.contains w₁ w₂ ∨ Minimalist.contains w₂ w₁ ∨ w₁ = w₂ := by
  intro T
  induction T with
  | leaf tok =>
    intro _ _ ℓ w₁ w₂ hw₁ hw₂ _ _
    rw [SyntacticObject.subtrees_leaf, Multiset.mem_singleton] at hw₁ hw₂
    subst hw₁; subst hw₂; exact Or.inr (Or.inr rfl)
  | trace n =>
    intro _ _ ℓ w₁ w₂ hw₁ hw₂ _ _
    rw [SyntacticObject.subtrees_trace, Multiset.mem_singleton] at hw₁ hw₂
    subst hw₁; subst hw₂; exact Or.inr (Or.inr rfl)
  | mul a b iha ihb =>
    intro hCoh hNodup ℓ w₁ w₂ hw₁ hw₂ hℓ₁ hℓ₂
    have ha_in_ab : a ∈ (a * b).subtrees := by
      rw [SyntacticObject.subtrees_mul]
      exact Multiset.mem_cons_of_mem
        (Multiset.mem_add.mpr (Or.inl (self_mem_subtrees a)))
    have hb_in_ab : b ∈ (a * b).subtrees := by
      rw [SyntacticObject.subtrees_mul]
      exact Multiset.mem_cons_of_mem
        (Multiset.mem_add.mpr (Or.inr (self_mem_subtrees b)))
    have hCoh_a : h.LocallyCoherent a := hCoh.descent ha_in_ab
    have hCoh_b : h.LocallyCoherent b := hCoh.descent hb_in_ab
    have hN_a : (leafTokensPlanar (h.section_.σ a)).Nodup :=
      σ_leafTokensPlanar_nodup_subtree h _ hCoh hNodup ha_in_ab
    have hN_b : (leafTokensPlanar (h.section_.σ b)).Nodup :=
      σ_leafTokensPlanar_nodup_subtree h _ hCoh hNodup hb_in_ab
    -- Useful: (a*b) immediately contains a and b
    have hab_imm_a : Minimalist.immediatelyContains (a * b) a :=
      (immediatelyContains_mul _ _ _).mpr (Or.inl rfl)
    have hab_imm_b : Minimalist.immediatelyContains (a * b) b :=
      (immediatelyContains_mul _ _ _).mpr (Or.inr rfl)
    -- For any w' ∈ a.subtrees, a*b contains w' (or w' = a, contained immediately)
    have ab_contains_a_subtree : ∀ {w' : SyntacticObject}, w' ∈ a.subtrees →
        Minimalist.contains (a * b) w' := by
      intro w' hw'
      rcases mem_subtrees_imp_eq_or_contains hw' with rfl | hca
      · exact Minimalist.contains.imm _ _ hab_imm_a
      · exact Minimalist.contains.trans _ _ a hab_imm_a hca
    have ab_contains_b_subtree : ∀ {w' : SyntacticObject}, w' ∈ b.subtrees →
        Minimalist.contains (a * b) w' := by
      intro w' hw'
      rcases mem_subtrees_imp_eq_or_contains hw' with rfl | hcb
      · exact Minimalist.contains.imm _ _ hab_imm_b
      · exact Minimalist.contains.trans _ _ b hab_imm_b hcb
    -- Decompose w₁, w₂ ∈ (a*b).subtrees
    rw [SyntacticObject.subtrees_mul] at hw₁ hw₂
    rcases Multiset.mem_cons.mp hw₁ with h1eq | h1sub
    · -- w₁ = a*b
      subst h1eq
      rcases Multiset.mem_cons.mp hw₂ with h2eq | h2sub
      · -- w₂ = a*b
        subst h2eq; exact Or.inr (Or.inr rfl)
      · -- w₂ ∈ a.subtrees + b.subtrees: contains (a*b) w₂
        left
        rcases Multiset.mem_add.mp h2sub with h2a | h2b
        · exact ab_contains_a_subtree h2a
        · exact ab_contains_b_subtree h2b
    · rcases Multiset.mem_cons.mp hw₂ with h2eq | h2sub
      · -- w₂ = a*b: symmetric
        subst h2eq
        right; left
        rcases Multiset.mem_add.mp h1sub with h1a | h1b
        · exact ab_contains_a_subtree h1a
        · exact ab_contains_b_subtree h1b
      · -- Both w₁, w₂ in a.subtrees + b.subtrees
        rcases Multiset.mem_add.mp h1sub with h1a | h1b
        all_goals rcases Multiset.mem_add.mp h2sub with h2a | h2b
        · -- Both in a.subtrees: apply iha
          exact iha hCoh_a hN_a ℓ w₁ w₂ h1a h2a hℓ₁ hℓ₂
        · -- w₁ in a.subtrees, w₂ in b.subtrees: contradiction via disjointness
          exfalso
          have hℓ_in_w₁ : ℓ ∈ leafTokensPlanar (h.section_.σ w₁) := by
            unfold HeadFunction.headAtVertex at hℓ₁
            cases h_side : h.headSide
            · rw [h_side] at hℓ₁; rw [← hℓ₁]
              exact leftmostLeafPlanar_mem_leafTokens _
            · rw [h_side] at hℓ₁; rw [← hℓ₁]
              exact rightmostLeafPlanar_mem_leafTokens _
          have hℓ_in_w₂ : ℓ ∈ leafTokensPlanar (h.section_.σ w₂) := by
            unfold HeadFunction.headAtVertex at hℓ₂
            cases h_side : h.headSide
            · rw [h_side] at hℓ₂; rw [← hℓ₂]
              exact leftmostLeafPlanar_mem_leafTokens _
            · rw [h_side] at hℓ₂; rw [← hℓ₂]
              exact rightmostLeafPlanar_mem_leafTokens _
          have hℓ_a : ℓ ∈ leafTokensPlanar (h.section_.σ a) :=
            Multiset.mem_of_le (σ_leafMultiset_le_root h a hCoh_a w₁ h1a) hℓ_in_w₁
          have hℓ_b : ℓ ∈ leafTokensPlanar (h.section_.σ b) :=
            Multiset.mem_of_le (σ_leafMultiset_le_root h b hCoh_b w₂ h2b) hℓ_in_w₂
          exact σ_leafTokens_disjoint_at_mul h _ hCoh hNodup
            (by rw [SyntacticObject.subtrees_mul]; exact Multiset.mem_cons_self _ _)
            hℓ_a hℓ_b
        · -- w₁ in b.subtrees, w₂ in a.subtrees: symmetric contradiction
          exfalso
          have hℓ_in_w₁ : ℓ ∈ leafTokensPlanar (h.section_.σ w₁) := by
            unfold HeadFunction.headAtVertex at hℓ₁
            cases h_side : h.headSide
            · rw [h_side] at hℓ₁; rw [← hℓ₁]
              exact leftmostLeafPlanar_mem_leafTokens _
            · rw [h_side] at hℓ₁; rw [← hℓ₁]
              exact rightmostLeafPlanar_mem_leafTokens _
          have hℓ_in_w₂ : ℓ ∈ leafTokensPlanar (h.section_.σ w₂) := by
            unfold HeadFunction.headAtVertex at hℓ₂
            cases h_side : h.headSide
            · rw [h_side] at hℓ₂; rw [← hℓ₂]
              exact leftmostLeafPlanar_mem_leafTokens _
            · rw [h_side] at hℓ₂; rw [← hℓ₂]
              exact rightmostLeafPlanar_mem_leafTokens _
          have hℓ_b : ℓ ∈ leafTokensPlanar (h.section_.σ b) :=
            Multiset.mem_of_le (σ_leafMultiset_le_root h b hCoh_b w₁ h1b) hℓ_in_w₁
          have hℓ_a : ℓ ∈ leafTokensPlanar (h.section_.σ a) :=
            Multiset.mem_of_le (σ_leafMultiset_le_root h a hCoh_a w₂ h2a) hℓ_in_w₂
          exact σ_leafTokens_disjoint_at_mul h _ hCoh hNodup
            (by rw [SyntacticObject.subtrees_mul]; exact Multiset.mem_cons_self _ _)
            hℓ_a hℓ_b
        · -- Both w₁, w₂ in b.subtrees: apply ihb
          exact ihb hCoh_b hN_b ℓ w₁ w₂ h1b h2b hℓ₁ hℓ₂

/-- **Lemma 1.14.1 chain property** (Phase 3.D: discharged).
    Public-facing version: decodes `projectionPath` membership into
    `T.subtrees` + `headAtVertex T w = ℓ` and dispatches to the
    inductive helper `projectionPath_chain_aux`. -/
theorem projectionPath_chain (h : HeadFunction) (T : SyntacticObject)
    (hCoh : h.LocallyCoherent T)
    (hNodup : (leafTokensPlanar (h.section_.σ T)).Nodup)
    (ℓ : LIToken) {w₁ w₂ : SyntacticObject}
    (h₁ : w₁ ∈ projectionPath h T ℓ) (h₂ : w₂ ∈ projectionPath h T ℓ) :
    Minimalist.contains w₁ w₂ ∨ Minimalist.contains w₂ w₁ ∨ w₁ = w₂ := by
  unfold projectionPath at h₁ h₂
  rw [Multiset.mem_filter] at h₁ h₂
  obtain ⟨hw₁, hℓ₁⟩ := h₁
  obtain ⟨hw₂, hℓ₂⟩ := h₂
  rw [decide_eq_true_eq] at hℓ₁ hℓ₂
  exact projectionPath_chain_aux h T hCoh hNodup ℓ w₁ w₂ hw₁ hw₂ hℓ₁ hℓ₂

/-- The **maximal projection vertex** v_ℓ of leaf ℓ in T
    ([marcolli-chomsky-berwick-2025] Lemma 1.14.1): the topmost
    vertex on `projectionPath h T ℓ`, ordered by containment.

    Returns `none` if `projectionPath h T ℓ` is empty (ℓ ∉ L(T) under h).
    Otherwise returns the vertex containing all others on γ_ℓ (the unique
    maximal element under containment, well-defined by `projectionPath_chain`).

    Implementation: filter `T.subtrees` to those on γ_ℓ that are NOT
    properly contained in any other γ_ℓ vertex. Returns the first (in
    `Multiset.toList` order) — by `projectionPath_chain` this is unique
    when nonempty. -/
noncomputable def maximalProjection (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Option SyntacticObject :=
  let γ := projectionPath h T ℓ
  let topmost := γ.filter (fun w =>
    decide (∀ w' ∈ γ, w' ≠ w → ¬ Minimalist.contains w' w))
  topmost.toList.head?

/-- A projection path is **non-trivial** (contains at least one
    internal vertex) when its cardinality exceeds 1 — i.e., the leaf has
    ascended at least one level in T. Per Definition 1.14.3, only
    non-trivial projection paths give rise to phases. -/
noncomputable def isNonTrivialProjection (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Bool :=
  decide (1 < (projectionPath h T ℓ).card)

-- ============================================================================
-- § 2: Phase Head Leaves L_Φ(T) (Definition 1.14.3 eq 1.14.1)
-- ============================================================================

/-- The set L(T) of leaves of T as LITokens, under head function `h`.
    Renamed alias for `HeadFunction.leafTokens` matching MCB notation. -/
def leafSet (h : HeadFunction) (T : SyntacticObject) : List LIToken := h.leafTokens T

/-- [marcolli-chomsky-berwick-2025] Definition 1.14.3 (eq 1.14.1):
    L_Φ(T) = the set of leaves ℓ ∈ L(T) such that γ_ℓ contains
    interior (non-leaf) vertices. Each such ℓ is the head of a phase. -/
noncomputable def phaseHeadLeaves (h : HeadFunction) (T : SyntacticObject) : List LIToken :=
  (leafSet h T).filter (fun ℓ => isNonTrivialProjection h T ℓ)

-- ============================================================================
-- § 3: Phase Interior Φ°_ℓ and Edge ∂Φ_ℓ (Definitions 1.14.3, 1.14.4)
-- ============================================================================

/-- Search a planar representative for the **complement** of head leaf `ℓ`: the
    sister of `ℓ` at its mother node — the (unique) node on whose head side `ℓ`
    appears as the direct leaf daughter. `side` says which daughter is the head
    (left for `.initial`, right for `.final`); the complement is the other.
    Returns the complement as a planar `FreeMagma`, or `none` if `ℓ` heads no
    internal node. **Computable** — it walks the fixed planar embedding by
    structural recursion, with no `Multiset`/`Quot` choice. -/
def complementInPlanar (side : ConventionDir) (ℓ : LIToken) :
    FreeMagma (LIToken ⊕ Nat) → Option (FreeMagma (LIToken ⊕ Nat))
  | .of _ => none
  | .mul l r =>
    match side, l, r with
    | .initial, .of (.inl t), _ =>
        if t = ℓ then some r
        else (complementInPlanar side ℓ l) <|> (complementInPlanar side ℓ r)
    | .final, _, .of (.inl t) =>
        if t = ℓ then some l
        else (complementInPlanar side ℓ l) <|> (complementInPlanar side ℓ r)
    | _, _, _ => (complementInPlanar side ℓ l) <|> (complementInPlanar side ℓ r)

/-- The **complement** Z_ℓ of phase head `ℓ` ([marcolli-chomsky-berwick-2025]
    Def 1.14.2, Def 1.14.3 step 3): the head's sister at its mother node — the
    structure `ℓ` first selects. `none` for an empty complement (`ℓ` heads no
    internal node). Head-side-aware, so correct under both head-initial and
    head-final `h`. **Computable** when the section is (e.g. the selection-induced
    `HeadFunction.leftSpine`), since it walks `h.section_.σ T` directly — so
    concrete phase complements `decide`. -/
def phaseComplementZ (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Option SyntacticObject :=
  (complementInPlanar h.headSide ℓ (h.section_.σ T)).map FreeCommMagma.mk

/-- [marcolli-chomsky-berwick-2025] Def 1.14.3 (eq 1.14.2): the **phase** Φ_ℓ =
    {T_v ∈ Acc'(T) | T_v ⊆ T_{v_ℓ}} — all accessible terms within the maximal
    projection `v_ℓ`. This is the *whole* phase; its interior is the complement
    (`phaseInterior`) and its edge is head + specifiers + modifiers (`phaseEdge`). -/
noncomputable def phase (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Multiset SyntacticObject :=
  match maximalProjection h T ℓ with
  | none    => 0
  | some vℓ => T.subtrees.filter (fun Tv => decide (Minimalist.contains vℓ Tv))

/-- [marcolli-chomsky-berwick-2025] Def 1.14.3 (eq 1.14.3): the **interior**
    Φ°_ℓ = {T_v ∈ Acc(T) | T_v ⊆ T_{s_ℓ}} — the complement `Z_ℓ` and all of its
    accessible terms; `∅` when the complement is empty.

    Per MCB ("if H is a phase head with complement Z, then Z is the interior of
    the phase"), the interior **is the complement** — NOT the whole maximal
    projection. The head and any specifiers/modifiers sit at the *edge*. (This
    corrects the earlier `T_{v_ℓ}` over-approximation, which is the *phase* Φ_ℓ
    of eq 1.14.2, now named `phase`.) **Computable** (built on the computable
    `phaseComplementZ` + subtree filter) — so concrete PIC checks `decide`. -/
def phaseInterior (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Multiset SyntacticObject :=
  match phaseComplementZ h T ℓ with
  | none   => 0
  | some Z => T.subtrees.filter (fun Tv => decide (Minimalist.containsOrEq Z Tv))

/-- [marcolli-chomsky-berwick-2025] Def 1.14.3 (eq 1.14.4): the **edge** ∂Φ_ℓ =
    {T_v ∈ Acc'(T) | T_v ⊆ T_{v_ℓ} ∧ T_v ⊄ T_{s_ℓ}} — the phase content not in the
    interior: the head, specifiers, and modifiers. `= Φ_ℓ` when the complement is
    empty (everything is then at the edge). Computed as `phase ∖ interior`. -/
noncomputable def phaseEdge (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Multiset SyntacticObject :=
  let interior := phaseInterior h T ℓ
  (phase h T ℓ).filter (fun Tv => decide (Tv ∉ interior))

-- ============================================================================
-- § 4: Inaccessibility Set Y_ℓ (eq 1.14.5)
-- ============================================================================

/-- The partial order on phases ([marcolli-chomsky-berwick-2025]
    after Definition 1.14.3): Φ_ℓ is a **lower phase** than Φ_ℓ' when
    Φ_ℓ ⊂ Φ_ℓ' as sets of accessible terms. We approximate this by
    interior containment of the maximal projection vertices. -/
noncomputable def isLowerPhaseThan (h : HeadFunction) (T : SyntacticObject)
    (ℓ ℓ' : LIToken) : Bool :=
  match maximalProjection h T ℓ, maximalProjection h T ℓ' with
  | some vℓ, some vℓ' => decide (Minimalist.contains vℓ' vℓ)
  | _, _ => false

/-- [marcolli-chomsky-berwick-2025] eq (1.14.5): the
    **inaccessibility set** Y_ℓ for phase Φ_ℓ:

      Y_ℓ := { T_v ∈ Acc'(T) | T_v ∈ ⋃_{ℓ' < ℓ} Φ°_ℓ' }

    — accessible terms that lie in the interior of any *strictly
    lower* phase. The complement Φ_ℓ ∖ Y_ℓ is the set of terms
    available for computation in phase Φ_ℓ. -/
noncomputable def inaccessibleTerms (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Multiset SyntacticObject :=
  let lowerPhases := (phaseHeadLeaves h T).filter (fun ℓ' => isLowerPhaseThan h T ℓ' ℓ)
  -- Union of interiors of all lower phases (Multiset sum)
  (lowerPhases.map (phaseInterior h T)).foldr (· + ·) 0

/-- [marcolli-chomsky-berwick-2025] Remark 1.14.4: the **more restrictive**
    inaccessibility set — the default `inaccessibleTerms` Υ_ℓ together with the
    head leaves of all strictly-lower phases. MCB's default (eq 1.14.5) counts the
    head in the *edge* (accessible, permitting head movement); the restrictive
    Phase Theory that also bans head movement additionally freezes the lower heads.
    Since the corrected `phaseInterior` (= complement) already excludes the head,
    the head must be added back explicitly for the strong variant. -/
noncomputable def inaccessibleTerms_strong (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Multiset SyntacticObject :=
  let lowerHeads : Multiset SyntacticObject :=
    ((phaseHeadLeaves h T).filter (fun ℓ' => isLowerPhaseThan h T ℓ' ℓ)).map
      (fun ℓ' => SyntacticObject.leaf ℓ')
  inaccessibleTerms h T ℓ + lowerHeads

/-- The **accessible terms in phase Φ_ℓ**: the *phase* content minus the
    inaccessibility set (MCB Def 1.14.5 eq 1.14.6: `Φ_ℓ ∖ Υ_ℓ`). These are the
    terms available for further Merge computation when phase Φ_ℓ is being built or
    extended; this is the set summed over by the algebraic phase coproduct
    Δ^c_Φ (`Merge/PhaseCoproduct.lean`). -/
noncomputable def phaseAccessibleAt (h : HeadFunction) (T : SyntacticObject)
    (ℓ : LIToken) : Multiset SyntacticObject :=
  let inaccessible := inaccessibleTerms h T ℓ
  (phase h T ℓ).filter (fun Tv => decide (Tv ∉ inaccessible))

end Minimalist.Phase
