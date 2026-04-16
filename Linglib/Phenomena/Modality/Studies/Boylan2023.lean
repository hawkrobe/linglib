import Linglib.Theories.Semantics.Modality.Kratzer.Operators
import Linglib.Theories.Semantics.Modality.Kratzer.Flavor

/-!
# Putting *oughts* together
@cite{boylan-2023}

Semantics and Pragmatics 16, Article 5: 1–53.

## Core Proposal

Consistent Agglomeration — when φ and ψ are consistent, ⌜ought φ⌝ and
⌜ought ψ⌝ entail ⌜ought (φ ∧ ψ)⌝ — is valid for deontic but not epistemic
*ought*. Boylan gives a unified semantics that derives this asymmetry from
three independently motivated components:

1. **Existential semantics**: *ought* is an existential quantifier over the
   propositionally best partial answers to a relevance question (PBEST),
   not a universal quantifier over best worlds.

2. **Question-sensitivity**: The ordering only ranks partial answers to a
   contextually supplied relevance question Q, following
   @cite{karttunen-1977}'s partition semantics.

3. **Pairwise consistency definedness**: *ought* is defined only when all
   pairs in PBEST are consistent with the background information.

The deontic/epistemic split arises from a structural difference in orderings:
deontic orderings satisfy an **averaging constraint** (a disjunction cannot be
worse than ALL its disjuncts), while epistemic orderings can violate it
(a disjunction can be more probable than any disjunct).

## Structure

The file is organized top-down: abstract framework first, concrete
applications second.

**§§1–6** establish the formal machinery — proposition-level orderings,
partitions (partial/complete answers), PBEST, pairwise consistency,
*ought*, and ordering assumptions (Assumptions 1–6 from the appendix).

**§7** derives the general structural properties from those assumptions:
- **Fact 1** (`fact1_partial_complete`): Partition disjunction — a partial
  answer and complete answer are either nested or disjoint.
- **Fact 2** (`fact2_unique_deontic_complete`): Under deontic orderings,
  PBEST contains exactly one complete answer.
- **Fact 3** (`fact3_deontic_boxy`): Singleton PBEST reduces Boylan's
  *ought* to Kratzer necessity.
- **Fact 4** (`fact4_no_agglomeration`): Singleton PBEST validates
  Agglomeration.
- **Inheritance** (`inheritance`): φ ⊨ ψ → ⌜ought φ⌝ ⊨ ⌜ought ψ⌝.
- **No dilemma** (`no_dilemma`): Pairwise consistency prevents
  ⌜ought φ⌝ ∧ ⌜ought ¬φ⌝.

**§§8–14** instantiate the framework for concrete scenarios (The Office,
Dessert) and comparisons (conflict account, Kratzer bridge).

## Connection to Existing Infrastructure

- Builds on `Kratzer.Ordering` (`bestWorlds`, `atLeastAsGoodAs`,
  `accessibleWorlds`, `ModalBase`, `OrderingSource`).
- Bridges to `Kratzer.Background` (`isConsistent` ↔ `pairConsistent`).
- Connects to `Kratzer.Flavor` (`EpistemicFlavor`, `DeonticFlavor`).
- Contrasts with the universal-quantifier accounts in `Directive.lean`
  (@cite{von-fintel-iatridou-2008}) and `Rubinstein2014.lean`
  (@cite{rubinstein-2014}), which model weak necessity as ∀ over refined
  best-world sets. Boylan's operator is existential over propositions.
-/

namespace Phenomena.Modality.Studies.Boylan2023

open Semantics.Modality.Kratzer
open Semantics.Attitudes.Intensional (World allWorlds)
open Core.Proposition (BProp)

/-- Computable list of accessible worlds for use in the Boylan framework.
    `accessibleWorlds` returns `Finset World` (noncomputable `.toList`), so
    we filter `allWorlds` directly to get a `List World` that is
    definitionally equal for `decide` proofs. -/
def accessibleWorldsList (f : ModalBase World) (w : World) : List World :=
  allWorlds.filter (λ w' => (f w).all (λ p => p w'))

-- ============================================================================
-- §1. Proposition-Level Ordering
-- ============================================================================

/-! ## Lifting world ordering to propositions

Kratzer's ordering ranks *worlds*. Boylan needs ordering over *propositions*
(subsets of the modal base). We lift the world ordering: a proposition p is
at least as good as q iff every world satisfying q is at-least-as-good-as
some world satisfying p. In practice, Boylan's ordering over partial answers
is supplied by context (probability for epistemics, value for deontics), so
we parameterize directly over a proposition-level ordering. -/

/-- A proposition-level ordering: ranks propositions relative to an
    evaluation world. This abstracts over the source of the ordering
    (probability, normality, deontic value, etc.). -/
abbrev PropOrdering := World → BProp World → BProp World → Bool

-- ============================================================================
-- §2. Partition Framework (Appendix, Assumptions 4–6)
-- ============================================================================

/-! ## Questions as partitions

The relevance question Q restricted to the modal base f(w) partitions the
accessible worlds into cells. Complete answers are individual cells; partial
answers are unions of cells. This is the mathematical foundation for
Boylan's semantics — *ought* quantifies over the best partial answers.

The partition framework corresponds to Assumptions 4 (question-sensitivity),
5 (partition invariance), and 6 (comparability) from the appendix. -/

/-- A partition of accessible worlds into non-empty pairwise-disjoint cells.
    Models Q|f(w) — the relevance question restricted to the modal base. -/
structure BoylanPartition (accessible : List World) where
  cells : List (BProp World)
  /-- Every accessible world belongs to some cell. -/
  cover : ∀ w ∈ accessible, ∃ c ∈ cells, c w = true
  /-- Distinct cells share no accessible world. -/
  disjoint : ∀ c₁ ∈ cells, ∀ c₂ ∈ cells, c₁ ≠ c₂ →
    ∀ w ∈ accessible, ¬(c₁ w = true ∧ c₂ w = true)
  /-- Every cell contains at least one accessible world. -/
  inhabited : ∀ c ∈ cells, ∃ w ∈ accessible, c w = true

/-- A **partial answer** is a union of cells: if p intersects a cell on
    the accessible worlds, it contains the entire cell. -/
def BoylanPartition.isPartialAnswer {acc : List World} (Q : BoylanPartition acc) (p : BProp World) : Prop :=
  ∀ c ∈ Q.cells, (∃ w ∈ acc, c w = true ∧ p w = true) →
    ∀ w ∈ acc, c w = true → p w = true

/-- A **complete answer** is a single cell of the partition. -/
def BoylanPartition.isCompleteAnswer {acc : List World} (Q : BoylanPartition acc) (q : BProp World) : Prop :=
  q ∈ Q.cells

/-- Every non-empty partial answer contains at least one complete cell.
    Since p is a union of cells and is non-empty, some cell's accessible
    worlds are entirely within p. -/
theorem BoylanPartition.partial_contains_cell
    {acc : List World} (Q : BoylanPartition acc) {p : BProp World}
    (hp : Q.isPartialAnswer p) (hne : ∃ w ∈ acc, p w = true) :
    ∃ c ∈ Q.cells, ∀ w ∈ acc, c w = true → p w = true := by
  obtain ⟨v, hva, hpv⟩ := hne
  obtain ⟨c, hc, hcv⟩ := Q.cover v hva
  exact ⟨c, hc, hp c hc ⟨v, hva, hcv, hpv⟩⟩

-- ============================================================================
-- §3. PBEST — Propositionally Best Partial Answers (§4, eq. 70)
-- ============================================================================

/-! ## PBEST

PBEST(w, f, g, Q) = {p ⊆ f(w) : p ≠ ∅ and ¬∃q ⊆ f(w) : q ≺ p}

The set of undominated (best) propositions among the partial answers to Q
that are subsets of the modal base information f(w). We take a list of
candidate propositions (the partial answers to Q restricted to f(w))
and filter to those that are undominated under the ordering. -/

/-- Strict betterness between propositions: p is strictly better than q. -/
def StrictlyBetter (ord : PropOrdering) (w : World) (p q : BProp World) : Prop :=
  ord w p q = true ∧ ¬(ord w q p = true)

/-- PBEST: the propositionally best partial answers.

    Given a list of candidate propositions (partial answers to Q
    restricted to f(w)), returns those that are non-empty on the
    accessible worlds and undominated under the ordering. -/
def PBEST (ord : PropOrdering) (w : World) (candidates : List (BProp World))
    (acc : List World) : List (BProp World) :=
  candidates.filter λ p =>
    acc.any p && !candidates.any (λ q => ord w q p && !(ord w p q))

/-! ### PBEST bridge lemmas -/

theorem PBEST_subset {ord : PropOrdering} {w : World}
    {candidates : List (BProp World)} {acc : List World} {p : BProp World}
    (h : p ∈ PBEST ord w candidates acc) : p ∈ candidates :=
  (List.mem_filter.mp h).1

theorem PBEST_nonempty {ord : PropOrdering} {w : World}
    {candidates : List (BProp World)} {acc : List World} {p : BProp World}
    (h : p ∈ PBEST ord w candidates acc) : ∃ v ∈ acc, p v = true := by
  have := (List.mem_filter.mp h).2
  simp only [Bool.and_eq_true, List.any_eq_true] at this
  exact this.1

theorem PBEST_undom {ord : PropOrdering} {w : World}
    {candidates : List (BProp World)} {acc : List World} {p : BProp World}
    (h : p ∈ PBEST ord w candidates acc) :
    ∀ r ∈ candidates, ¬StrictlyBetter ord w r p := by
  have hcond := (List.mem_filter.mp h).2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
  intro r hr ⟨hrp, hpr⟩
  have : candidates.any (λ q => ord w q p && !(ord w p q)) = true := by
    rw [List.any_eq_true]
    refine ⟨r, hr, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨hrp, by cases h : ord w p r <;> simp_all⟩
  simp [this] at hcond

theorem mem_PBEST {ord : PropOrdering} {w : World}
    {candidates : List (BProp World)} {acc : List World} {p : BProp World}
    (hmem : p ∈ candidates)
    (hne : ∃ v ∈ acc, p v = true)
    (hund : ∀ r ∈ candidates, ¬StrictlyBetter ord w r p) :
    p ∈ PBEST ord w candidates acc := by
  apply List.mem_filter.mpr
  refine ⟨hmem, ?_⟩
  have h1 : acc.any p = true := List.any_eq_true.mpr hne
  have h2 : candidates.any (fun q => ord w q p && !(ord w p q)) = false := by
    match hc : candidates.any (fun q => ord w q p && !(ord w p q)) with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨r, hr, hcond⟩ := List.any_eq_true.mp hc
      have hrp : ord w r p = true := by
        match h : ord w r p with | true => rfl | false => simp [h] at hcond
      have hpr : ¬(ord w p r = true) := by
        match h : ord w p r with | false => simp | true => simp [h] at hcond
      exact hund r hr ⟨hrp, hpr⟩
  simp [h1, h2]

-- ============================================================================
-- §4. Pairwise Consistency (§4.3)
-- ============================================================================

/-! ## Consistency definedness condition

⟦ought φ⟧ is defined only if for all p and q in PBEST(w,f,g,Q),
(p ∩ q) ∩ f(w) ≠ ∅. This is pairwise, not global, consistency.

The key insight: {Alice is in, Bob is in, ..., Not everyone is in} is
pairwise consistent (any two people can both be in) but globally
inconsistent (not everyone can be in while someone is absent). -/

/-- Two propositions are consistent with respect to background information:
    there exists a world satisfying both p, q, and the modal base. -/
def pairConsistent (p q : BProp World) (accessible : List World) : Bool :=
  accessible.any (λ w => p w && q w)

/-- All pairs in a list of propositions are consistent. -/
def pairwiseConsistent (props : List (BProp World)) (accessible : List World) : Bool :=
  props.all λ p => props.all λ q => pairConsistent p q accessible

/-- Definedness condition for *ought*: PBEST is pairwise consistent. -/
def oughtDefined (ord : PropOrdering) (w : World)
    (candidates : List (BProp World)) (accessible : List World) : Bool :=
  pairwiseConsistent (PBEST ord w candidates accessible) accessible

-- ============================================================================
-- §5. The Semantics of *ought* (§4.4, eq. 71)
-- ============================================================================

/-! ## Boylan's *ought*

(a) ⟦ought φ⟧^{w,f,g,Q} is defined only if for all p and q in
    PBEST(w,f,g,Q), p ∩ q is consistent with f(w).

(b) If defined, ⟦ought φ⟧^{w,f,g,Q} iff ∃p ∈ PBEST(w,f,g,Q):
    ∀w' ∈ p: ⟦φ⟧^{w'} = 1 -/

/-- Boylan's *ought*: existential quantifier over PBEST.
    Returns `none` when the definedness condition fails. -/
def ought (ord : PropOrdering) (f : ModalBase World)
    (candidates : List (BProp World))
    (φ : BProp World) (w : World) : Option Bool :=
  let accessible := accessibleWorldsList f w
  let best := PBEST ord w candidates accessible
  if pairwiseConsistent best accessible then
    -- ∃p ∈ PBEST. ∀w' ∈ p. φ(w')
    some (best.any λ p =>
      accessible.filter p |>.all φ)
  else
    none

-- ============================================================================
-- §6. Ordering Assumptions (Appendix, Assumptions 1–2)
-- ============================================================================

/-! ## Ordering constraints

The deontic/epistemic asymmetry arises from structural differences in
orderings. Deontic orderings satisfy an **averaging constraint**: a
disjunction's value lies between its best and worst disjuncts. Epistemic
orderings violate this: P(A ∨ B) can exceed max(P(A), P(B)).

These correspond to Assumptions 1 (Limit) and 2 (Deontic orderings) from
the appendix. -/

/-- The **deontic constraint** on a proposition-level ordering (Assumption 2).

    For every proposition p that contains a complete answer (cell) q ⊆ p
    on the accessible worlds, some complete answer q' ⊆ p is at least as
    good as p. This ensures a complete answer makes it into PBEST under
    deontic orderings.

    Epistemics violate this: a disjunction can be more probable than any
    disjunct (P(A∨B) > max(P(A), P(B)) when A,B overlap). -/
def isDeontic (ord : PropOrdering) (w : World)
    (completeAnswers : List (BProp World)) (acc : List World) : Prop :=
  ∀ p : BProp World,
    (∃ q ∈ completeAnswers, ∀ v ∈ acc, q v = true → p v = true) →
    ∃ q ∈ completeAnswers,
      (∀ v ∈ acc, q v = true → p v = true) ∧ ord w q p = true

/-- Transitivity of the ordering (implicit in Kratzer's framework). -/
def orderingTransitive (ord : PropOrdering) (w : World) : Prop :=
  ∀ a b c : BProp World,
    ord w a b = true → ord w b c = true → ord w a c = true

-- ============================================================================
-- §7. General Structural Properties (Appendix, Facts 1–4; §10–11)
-- ============================================================================

/-! ## Structural properties of Boylan's *ought*

The general properties derived from the framework above. These hold for
all orderings, modal bases, and candidate sets — they are not finite data
checks but structured proofs from the assumptions.

**From the appendix**: Facts 1–4 establish that deontic *ought* reduces
to Kratzer necessity (Facts 2–3) and validates Agglomeration (Fact 4),
while epistemic *ought* can fail Agglomeration (Fact 5, §8 below).

**From §10–11**: Inheritance and No-dilemma hold for all flavors. -/

/-- **Fact 1**: For any partial answer p and complete answer q (cell),
    either q ⊆ p or p ∩ q = ∅ on the accessible worlds.

    **Proof**: q is a cell. If q and p share an accessible world v, then
    since p is a union of cells, all of q's accessible worlds must be in p
    (by `isPartialAnswer` applied to cell q). Otherwise disjoint. -/
theorem fact1_partial_complete {acc : List World} (Q : BoylanPartition acc)
    {p q : BProp World}
    (hp : Q.isPartialAnswer p) (hq : Q.isCompleteAnswer q) :
    (∀ w ∈ acc, q w = true → p w = true) ∨
    (∀ w ∈ acc, ¬(p w = true ∧ q w = true)) := by
  classical
  by_cases h : ∃ w ∈ acc, p w = true ∧ q w = true
  · left; obtain ⟨v, hva, hpv, hqv⟩ := h
    exact hp q hq ⟨v, hva, hqv, hpv⟩
  · right; intro w hw ⟨hpw, hqw⟩; exact h ⟨w, hw, hpw, hqw⟩

/-- Distinct cells of a partition are pairwise inconsistent — they share
    no accessible world. This is the key to uniqueness in Fact 2. -/
theorem BoylanPartition.cells_pairInconsistent
    {acc : List World} (Q : BoylanPartition acc) {q₁ q₂ : BProp World}
    (hq₁ : q₁ ∈ Q.cells) (hq₂ : q₂ ∈ Q.cells) (hne : q₁ ≠ q₂) :
    pairConsistent q₁ q₂ acc = false := by
  cases h : pairConsistent q₁ q₂ acc
  · rfl
  · simp only [pairConsistent, List.any_eq_true, Bool.and_eq_true] at h
    obtain ⟨w, hw, h1, h2⟩ := h
    exact absurd ⟨h1, h2⟩ (Q.disjoint q₁ hq₁ q₂ hq₂ hne w hw)

/-- **Key lemma**: If p is undominated among candidates and q ≽ p
    (at least as good), then q is also undominated — given transitivity.

    **Proof**: Suppose r ≻ q (r strictly better). By transitivity
    r ≽ p (from r ≽ q ≽ p). If also p ≽ r, then by transitivity
    q ≽ r (from q ≽ p ≽ r), contradicting r ≻ q. So ¬(p ≽ r),
    hence r ≻ p, contradicting p's undominatedness. -/
theorem undominated_of_geq
    {ord : PropOrdering} {w : World} {candidates : List (BProp World)}
    (htrans : orderingTransitive ord w)
    {p q : BProp World}
    (hp_undom : ∀ r ∈ candidates, ¬StrictlyBetter ord w r p)
    (hq_geq_p : ord w q p = true) :
    ∀ r ∈ candidates, ¬StrictlyBetter ord w r q := by
  intro r hr ⟨hrq, hqr⟩
  exact hp_undom r hr ⟨htrans r q p hrq hq_geq_p,
    fun hpr => hqr (htrans q p r hq_geq_p hpr)⟩

/-! ### Fact 2 — Unique Deontic Complete Answer

**Proof sketch** (Boylan, p. 46):

*Existence*. PBEST is non-empty (Assumption 1); take p ∈ PBEST. Since p is
a partial answer, some cell q ⊆ p (`partial_contains_cell`). By the deontic
constraint (Assumption 2 / `isDeontic`), some cell q' ⊆ p is at least as good
as p (q' ≽ p). By `undominated_of_geq`, q' is also undominated. Since q' is
non-empty (a cell) and in the candidates, q' ∈ PBEST.

*Uniqueness*. Suppose q₁ ≠ q₂ are both cells in PBEST. By
`cells_pairInconsistent`, `pairConsistent q₁ q₂ acc = false`. But
`pairwiseConsistent` requires all PBEST pairs to be consistent — contradiction.
-/

/-- **Fact 2**: Under a deontic, transitive ordering with pairwise consistency,
    PBEST contains exactly one complete answer. -/
theorem fact2_unique_deontic_complete
    {acc : List World} (Q : BoylanPartition acc)
    {ord : PropOrdering} {w : World} {candidates : List (BProp World)}
    (htrans : orderingTransitive ord w)
    (hcands_pa : ∀ p ∈ candidates, Q.isPartialAnswer p)
    (hcells_in_cands : ∀ c ∈ Q.cells, c ∈ candidates)
    (hdeontic : isDeontic ord w Q.cells acc)
    (hp_exists : ∃ p, p ∈ PBEST ord w candidates acc)
    (hpw : pairwiseConsistent (PBEST ord w candidates acc) acc = true) :
    ∃ q, Q.isCompleteAnswer q ∧ q ∈ PBEST ord w candidates acc ∧
      ∀ q', Q.isCompleteAnswer q' → q' ∈ PBEST ord w candidates acc → q' = q := by
  -- Existence: get a cell into PBEST
  obtain ⟨p, hp⟩ := hp_exists
  obtain ⟨v, hva, hpv⟩ := PBEST_nonempty hp
  obtain ⟨c, hc_cells, hc_sub⟩ :=
    Q.partial_contains_cell (hcands_pa p (PBEST_subset hp)) ⟨v, hva, hpv⟩
  obtain ⟨q, hq_cells, hq_sub, hq_geq⟩ := hdeontic p ⟨c, hc_cells, hc_sub⟩
  have hq_undom := undominated_of_geq htrans (PBEST_undom hp) hq_geq
  obtain ⟨u, hua, hqu⟩ := Q.inhabited q hq_cells
  have hq_pbest := mem_PBEST (hcells_in_cands q hq_cells) ⟨u, hua, hqu⟩ hq_undom
  -- Uniqueness: distinct cells in PBEST violate pairwise consistency
  refine ⟨q, hq_cells, hq_pbest, ?_⟩
  intro q' hq'_cells hq'_pbest
  by_contra hne
  have hinc := Q.cells_pairInconsistent hq_cells hq'_cells (fun h => hne h.symm)
  rw [pairwiseConsistent, List.all_eq_true] at hpw
  have := hpw q hq_pbest
  rw [List.all_eq_true] at this
  have := this q' hq'_pbest
  simp [hinc] at this

/-! ### Fact 3 — Deontic *Ought* Is Boxy (General)

When PBEST = [q] (a singleton containing one complete answer), Boylan's
existential *ought* reduces to universal quantification over q — exactly
Kratzer necessity relativized to the unique best complete answer. -/

/-- **Fact 3**: When PBEST is a singleton {q}, ⌜ought φ⌝ = true iff
    all accessible q-worlds satisfy φ. -/
theorem fact3_deontic_boxy
    {ord : PropOrdering} {f : ModalBase World} {w : World}
    {candidates : List (BProp World)} {q : BProp World}
    (hpbest : PBEST ord w candidates (accessibleWorldsList f w) = [q])
    (hpw : pairwiseConsistent [q] (accessibleWorldsList f w) = true)
    (φ : BProp World) :
    ought ord f candidates φ w =
      some ((accessibleWorldsList f w).filter q |>.all φ) := by
  simp only [ought]
  rw [hpbest, hpw]
  simp

/-- **Fact 4**: Under the hypotheses of Fact 3 (PBEST = [q]),
    Agglomeration holds: ⌜ought φ⌝ ∧ ⌜ought ψ⌝ → ⌜ought (φ ∧ ψ)⌝. -/
theorem fact4_no_agglomeration
    {ord : PropOrdering} {f : ModalBase World} {w : World}
    {candidates : List (BProp World)} {q : BProp World} {φ ψ : BProp World}
    (hpbest : PBEST ord w candidates (accessibleWorldsList f w) = [q])
    (hpw : pairwiseConsistent [q] (accessibleWorldsList f w) = true)
    (hφ : ought ord f candidates φ w = some true)
    (hψ : ought ord f candidates ψ w = some true) :
    ought ord f candidates (fun v => φ v && ψ v) w = some true := by
  rw [fact3_deontic_boxy hpbest hpw] at hφ hψ ⊢
  simp only [Option.some.injEq] at hφ hψ ⊢
  rw [List.all_eq_true] at hφ hψ ⊢
  intro v hv
  simp only [Bool.and_eq_true]
  exact ⟨hφ v hv, hψ v hv⟩

/-! ### Inheritance and No-Dilemma -/

/-- **Inheritance**: If φ entails ψ, then ⌜ought φ⌝ entails ⌜ought ψ⌝.
    This is a general result — not a finite data check — that holds for
    all orderings, modal bases, and candidate sets. Contrastivist accounts
    generally invalidate this (§10). -/
theorem inheritance {ord : PropOrdering} {f : ModalBase World}
    {cands : List (BProp World)} {φ ψ : BProp World} {w : World}
    (hent : ∀ v, φ v = true → ψ v = true)
    (hoφ : ought ord f cands φ w = some true) :
    ought ord f cands ψ w = some true := by
  simp only [ought] at hoφ ⊢
  split at hoφ
  · rename_i hpc
    rw [if_pos hpc]
    simp only [Option.some.injEq] at hoφ ⊢
    rw [List.any_eq_true] at hoφ ⊢
    obtain ⟨p, hpmem, hpall⟩ := hoφ
    exact ⟨p, hpmem, List.all_eq_true.mpr (fun v hv =>
      hent v (List.all_eq_true.mp hpall v hv))⟩
  · simp at hoφ

/-- **No dilemma when defined**: Boylan's ought never simultaneously yields
    ⌜ought φ⌝ = true and ⌜ought ¬φ⌝ = true. If p₁ ∈ PBEST witnesses φ and
    p₂ ∈ PBEST witnesses ¬φ, pairwise consistency gives a world in p₁ ∩ p₂
    that would satisfy both φ and ¬φ. This is the key structural advantage
    over the conflict account, which predicts dilemmas in The Office. -/
theorem no_dilemma {ord : PropOrdering} {f : ModalBase World}
    {cands : List (BProp World)} {φ : BProp World} {w : World}
    (h1 : ought ord f cands φ w = some true)
    (h2 : ought ord f cands (fun v => !φ v) w = some true) : False := by
  simp only [ought] at h1 h2
  split at h1
  · rename_i hpc
    split at h2
    · simp only [Option.some.injEq] at h1 h2
      rw [List.any_eq_true] at h1 h2
      obtain ⟨p₁, hp₁, ha₁⟩ := h1
      obtain ⟨p₂, hp₂, ha₂⟩ := h2
      rw [pairwiseConsistent, List.all_eq_true] at hpc
      have h₁₂ := hpc p₁ hp₁
      rw [List.all_eq_true] at h₁₂
      simp only [pairConsistent, List.any_eq_true] at h₁₂
      obtain ⟨v, hv, hboth⟩ := h₁₂ p₂ hp₂
      simp only [Bool.and_eq_true] at hboth
      rw [List.all_eq_true] at ha₁ ha₂
      have hfv := ha₁ v (List.mem_filter.mpr ⟨hv, hboth.1⟩)
      have hnfv := ha₂ v (List.mem_filter.mpr ⟨hv, hboth.2⟩)
      simp [hfv] at hnfv
    · rename_i hnpc; exact absurd hpc hnpc
  · simp at h1

-- ============================================================================
-- §8. The Office — Epistemic Agglomeration Failure (§1.2, §8.1)
-- ============================================================================

/-! ## The Office

26 workers (Alice, Bob, ..., Zadie) work on separate floors. On average
they each take a sick day once a month, so statistically it is rare that
all 26 are present on any given day.

For each worker x: "x should be in the office today" is true.
But "Everyone should be in the office today" is false.

We model this with 4 worlds (the minimum needed to demonstrate the
structure): 3 workers, where exactly one is absent in each non-ideal world.

- w0: all present (low probability)
- w1: Alice absent
- w2: Bob absent
- w3: Carol absent -/

section Office

/-- Who is present at work in each world. -/
def aliceIn : BProp World := λ w => w != .w1
def bobIn   : BProp World := λ w => w != .w2
def carolIn : BProp World := λ w => w != .w3

/-- Everyone is in the office. -/
def everyoneIn : BProp World := λ w => aliceIn w && bobIn w && carolIn w

/-- Epistemic modal base: all worlds epistemically accessible. -/
def officeBase : ModalBase World := λ _ => []

/-- Epistemic ordering for The Office: probability-based.
    Propositions true in more worlds are ranked higher.
    w1, w2, w3 are each roughly equally likely; w0 (all present) is rare.

    Here we model this with a simple ordering: p is at least as good as q
    iff p is true in at least as many worlds as q. -/
def officeOrdering : PropOrdering := λ _ p q =>
  let pCount := allWorlds.filter p |>.length
  let qCount := allWorlds.filter q |>.length
  decide (pCount >= qCount)

/-- The partial answers to the relevance question include each
    individual-in proposition and the not-everyone-in proposition.
    These are the propositions whose truth depends only on which
    workers are present.

    In the full 26-worker model, the best propositions are
    {Alice is in, Bob is in, ..., Zadie is in, Not everyone is in}.
    In our 4-world model: -/
def officeCandidates : List (BProp World) :=
  [aliceIn, bobIn, carolIn, everyoneIn, λ w => !everyoneIn w]

/-- PBEST contains exactly 4 propositions (the 3 individual-in props
    and not-everyone-in; everyoneIn is dominated). -/
theorem office_pbest_length :
    (PBEST officeOrdering .w0 officeCandidates (accessibleWorldsList officeBase .w0)).length = 4 := by
  decide

/-- The best propositions are pairwise consistent: any two workers can
    both be in (pairwise but not globally). -/
theorem office_pairwise_consistent :
    pairwiseConsistent (PBEST officeOrdering .w0 officeCandidates
      (accessibleWorldsList officeBase .w0))
      (accessibleWorldsList officeBase .w0) = true := by
  decide

/-- *ought* is defined in The Office (pairwise consistency holds). -/
theorem office_ought_defined :
    oughtDefined officeOrdering .w0 officeCandidates
      (accessibleWorldsList officeBase .w0) = true := by
  decide

/-- "Alice should be in the office" is true: there is a best proposition
    (namely aliceIn) such that Alice is in at every world in it. -/
theorem alice_should_be_in :
    ought officeOrdering officeBase officeCandidates aliceIn .w0 = some true := by
  decide

/-- "Bob should be in the office" is true. -/
theorem bob_should_be_in :
    ought officeOrdering officeBase officeCandidates bobIn .w0 = some true := by
  decide

/-- "Everyone should be in the office" is FALSE: no best proposition
    entails that everyone is in. This is Agglomeration failure. -/
theorem not_everyone_should_be_in :
    ought officeOrdering officeBase officeCandidates everyoneIn .w0 = some false := by
  decide

/-- **Fact 5 (Epistemic Agglomeration Failure)**: There exist parameters
    such that ⟦ought φ⟧ = 1 and ⟦ought ψ⟧ = 1 but ⟦ought (φ ∧ ψ)⟧ = 0,
    witnessed by The Office. -/
theorem epistemic_agglomeration_failure :
    ∃ (ord : PropOrdering) (f : ModalBase World)
      (cands : List (BProp World)) (φ ψ : BProp World) (w : World),
      ought ord f cands φ w = some true ∧
      ought ord f cands ψ w = some true ∧
      ought ord f cands (λ v => φ v && ψ v) w = some false :=
  ⟨officeOrdering, officeBase, officeCandidates, aliceIn, bobIn, .w0,
   by decide, by decide, by decide⟩

end Office

-- ============================================================================
-- §9. Dessert — Deontic Indifference (§5.2, §8.2)
-- ============================================================================

/-! ## Dessert

Three dessert options: cannoli, cheesecake, and apple pie. Pie and cannoli
are tastiest. One can order as many as one likes, but having more than one
causes illness.

The relevance question *how good will the action I perform be?* lumps
equally-good options together. With this question, "I ought to have pie
or cannoli" is true, but "I ought to have pie" and "I ought to have cannoli"
are each false — Boylan's Indifference prediction.

We model this with 4 worlds:
- w0: just pie
- w1: just cannoli
- w2: just cheesecake (less tasty)
- w3: nothing / more than one (illness) -/

section Dessert

/-- Propositions for each dessert outcome. -/
def justPie     : BProp World := λ w => w == .w0
def justCannoli : BProp World := λ w => w == .w1
def justCake    : BProp World := λ w => w == .w2
def noGood      : BProp World := λ w => w == .w3

/-- "I have pie or cannoli" — the disjunctive ought. -/
def pieOrCannoli : BProp World := λ w => justPie w || justCannoli w

/-- Deontic ordering: tracks preferences.
    pie ≈ cannoli > cheesecake > nothing.

    A proposition is at least as good as another iff its worst outcome
    is at least as good as the other's worst. We implement this as:
    value = minimum world index among satisfying worlds (lower = better). -/
def dessertValue : World → Nat
  | .w0 => 3  -- pie: best
  | .w1 => 3  -- cannoli: equally best
  | .w2 => 2  -- cheesecake: second
  | .w3 => 0  -- illness/nothing: worst

/-- Worst value among worlds satisfying a proposition. -/
def worstValue (p : BProp World) : Nat :=
  let satisfying := allWorlds.filter p |>.map dessertValue
  satisfying.foldl min 100  -- 100 as sentinel for empty

/-- Deontic ordering based on worst-case value (conservative). -/
def dessertOrdering : PropOrdering := λ _ p q =>
  decide (worstValue p >= worstValue q)

/-- Deontic modal base: all worlds accessible. -/
def dessertBase : ModalBase World := λ _ => []

/-- Candidates for the *how good?* relevance question:
    actions of equal quality are lumped together.
    - {pie or cannoli} (best tier)
    - {cheesecake} (second tier)
    - {nothing/illness} (worst tier) -/
def dessertCandidatesHowGood : List (BProp World) :=
  [pieOrCannoli, justCake, noGood]

/-- "I ought to have pie or cannoli" is true under *how good?*. -/
theorem ought_pie_or_cannoli :
    ought dessertOrdering dessertBase dessertCandidatesHowGood
      pieOrCannoli .w0 = some true := by
  decide

/-- "I ought to have (just) pie" is FALSE: no single best proposition
    in the *how good?* partition entails just pie. -/
theorem not_ought_just_pie :
    ought dessertOrdering dessertBase dessertCandidatesHowGood
      justPie .w0 = some false := by
  decide

/-- "I ought to have (just) cannoli" is FALSE. -/
theorem not_ought_just_cannoli :
    ought dessertOrdering dessertBase dessertCandidatesHowGood
      justCannoli .w0 = some false := by
  decide

/-- **Indifference**: When multiple incompatible options are equally best,
    the strongest true *ought*-claim is disjunctive. -/
theorem dessert_indifference :
    ought dessertOrdering dessertBase dessertCandidatesHowGood
      pieOrCannoli .w0 = some true ∧
    ought dessertOrdering dessertBase dessertCandidatesHowGood
      justPie .w0 = some false ∧
    ought dessertOrdering dessertBase dessertCandidatesHowGood
      justCannoli .w0 = some false :=
  ⟨by decide, by decide, by decide⟩

end Dessert

-- ============================================================================
-- §10. Deontic *ought* Is a Box (§7, Fact 3)
-- ============================================================================

/-! ## Deontic *ought* reduces to Kratzer necessity

When the ordering is deontic and PBEST is pairwise consistent, there is a
unique best complete answer to the relevance question. *Ought* φ is then
true iff φ holds throughout that unique best complete answer — exactly
the truth conditions of classical Kratzer necessity.

We demonstrate this for the Dessert scenario: with the fine-grained
*what will I do?* question, the deontic ordering yields a single best
proposition, and *ought* agrees with Kratzer `necessity`. -/

section DeonticBox

/-- Candidates for the *what will I do?* question: each action is its
    own complete answer. -/
def dessertCandidatesWhat : List (BProp World) :=
  [justPie, justCannoli, justCake, noGood]

/-- Under *what will I do?* with deontic ordering, PBEST contains
    two equally-best options (pie and cannoli are tied). -/
theorem dessert_what_pbest_length :
    (PBEST dessertOrdering .w0 dessertCandidatesWhat
      (accessibleWorldsList dessertBase .w0)).length = 2 := by
  decide

/-- But these are inconsistent (no world has both just-pie and just-cannoli),
    so *ought* is UNDEFINED with the *what will I do?* question. This is why
    the deontic case forces the coarser *how good?* question. -/
theorem dessert_what_undefined :
    ought dessertOrdering dessertBase dessertCandidatesWhat
      justPie .w0 = none := by
  decide

/-- Modified dessert values where pie is uniquely best.
    Used to show Boylan's *ought* agrees with Kratzer necessity when
    there is a unique best option (§7, Fact 3). -/
def dessertValueStrict : World → Nat
  | .w0 => 4  -- pie: uniquely best
  | .w1 => 3  -- cannoli: second
  | .w2 => 2  -- cheesecake: third
  | .w3 => 0  -- nothing: worst

def worstValueStrict (p : BProp World) : Nat :=
  let satisfying := allWorlds.filter p |>.map dessertValueStrict
  satisfying.foldl min 100

def dessertStrictOrd : PropOrdering := λ _ p q =>
  decide (worstValueStrict p >= worstValueStrict q)

def dessertStrictCandidates : List (BProp World) :=
  [justPie, justCannoli, justCake, noGood]

/-- With a unique best option, PBEST is a singleton. -/
theorem strict_pbest_singleton :
    (PBEST dessertStrictOrd .w0 dessertStrictCandidates
      (accessibleWorldsList dessertBase .w0)).length = 1 := by
  decide

/-- **Fact 3 (concrete)**: When PBEST is a singleton {p},
    ought φ = true iff ∀w' ∈ p. φ(w') — matching Kratzer necessity
    relativized to the unique best proposition. -/
theorem deontic_ought_is_box :
    ought dessertStrictOrd dessertBase dessertStrictCandidates justPie .w0
      = some true ∧
    ought dessertStrictOrd dessertBase dessertStrictCandidates
      (λ w => !justPie w) .w0
      = some false :=
  ⟨by decide, by decide⟩

end DeonticBox

-- ============================================================================
-- §11. No Deontic Agglomeration Failure (§8.3, Fact 4)
-- ============================================================================

/-! ## Deontic Agglomeration holds

When PBEST is a singleton (the deontic case with a unique best complete
answer), Agglomeration holds trivially: if the unique best proposition
entails both φ and ψ, it entails φ ∧ ψ.

We verify this for the strict dessert scenario. -/

section DeonticAgglomeration

/-- "I ought to have pie" and "I ought not to have cannoli" — both true. -/
def notCannoli : BProp World := λ w => !justCannoli w

theorem strict_ought_pie :
    ought dessertStrictOrd dessertBase dessertStrictCandidates
      justPie .w0 = some true := by
  decide

theorem strict_ought_not_cannoli :
    ought dessertStrictOrd dessertBase dessertStrictCandidates
      notCannoli .w0 = some true := by
  decide

/-- **Fact 4 (concrete)**: The conjunction of two true deontic
    *ought*-claims is also true. -/
theorem no_deontic_agglomeration_failure :
    ought dessertStrictOrd dessertBase dessertStrictCandidates
      (λ w => justPie w && notCannoli w) .w0 = some true := by
  decide

end DeonticAgglomeration

-- ============================================================================
-- §12. Bridge to Kratzer Necessity
-- ============================================================================

/-! ## Connecting Boylan to Kratzer

When Boylan's *ought* is defined and the ordering is deontic (unique best
complete answer), it agrees with Kratzer's `necessity` operator for the
same modal base and ordering source. This is the structural connection
that justifies calling deontic *ought* "a box after all" (§7). -/

/-- The classic Kratzer semantics: ought is a universal quantifier
    over best worlds. Boylan argues this is correct for deontics but
    not epistemics. -/
def classicOught (f : ModalBase World) (g : OrderingSource World) (φ : BProp World) (w : World) : Prop :=
  necessity f g φ w

/-- **The classic semantics cannot distinguish the epistemic pattern.**

    Kratzer necessity is Agglomeration-valid by construction: if □φ and □ψ
    then □(φ∧ψ). So any ordering that makes "Alice should be in" true
    also makes "Everyone should be in" true. The classic semantics cannot
    get {Alice-true, Bob-true, Carol-true, Everyone-false} for ANY choice
    of modal base and ordering. -/
theorem kratzer_agglomerates :
    ∀ (f : ModalBase World) (g : OrderingSource World) (w : World),
      necessity f g aliceIn w →
      necessity f g bobIn w →
      necessity f g carolIn w →
      necessity f g everyoneIn w := by
  intro f g w ha hb hc
  rw [necessity_iff_all] at *
  intro w' hw'
  simp only [everyoneIn, Bool.and_eq_true]
  exact ⟨⟨ha w' hw', hb w' hw'⟩, hc w' hw'⟩

/-- Boylan gets the right pattern: all three individual *ought*s true,
    conjunction false. -/
theorem boylan_correct_office :
    ought officeOrdering officeBase officeCandidates aliceIn .w0 = some true ∧
    ought officeOrdering officeBase officeCandidates bobIn .w0 = some true ∧
    ought officeOrdering officeBase officeCandidates carolIn .w0 = some true ∧
    ought officeOrdering officeBase officeCandidates everyoneIn .w0 = some false :=
  ⟨by decide, by decide, by decide, by decide⟩

-- ============================================================================
-- §13. Conflict Account Counterexample (§3.3)
-- ============================================================================

/-! ## The conflict account wrongly predicts dilemmas

The conflict account (@cite{von-fintel-2012}, @cite{horty-2012}) says
⟦ought φ⟧ = 1 iff some maximally consistent subset of the best propositions
entails φ. In The Office, this predicts epistemic dilemmas: for each worker,
there is an MCS entailing their absence. Boylan argues this is wrong — The
Office does not involve dilemmas.

We formalize the conflict account's prediction and show it diverges from
Boylan's. -/

/-- A subset of propositions: represented as a Boolean mask on the list. -/
def subsetWorlds (props : List (BProp World)) (mask : List Bool)
    (accessible : List World) : List World :=
  let selected := (props.zip mask).filterMap λ ⟨p, b⟩ => if b then some p else none
  accessible.filter λ w => selected.all (· w)

/-- Whether a mask selects a consistent subset (non-empty intersection). -/
def maskConsistent (props : List (BProp World)) (mask : List Bool)
    (accessible : List World) : Bool :=
  !(subsetWorlds props mask accessible).isEmpty

/-- Whether a consistent subset is maximal: no strictly larger consistent
    subset exists (adding any excluded proposition breaks consistency). -/
def maskMaximal (props : List (BProp World)) (mask : List Bool)
    (accessible : List World) : Bool :=
  maskConsistent props mask accessible &&
  -- For each excluded proposition, adding it would be inconsistent
  (List.range mask.length).all λ i =>
    match mask[i]? with
    | some false =>
      let mask' := mask.set i true
      !maskConsistent props mask' accessible
    | _ => true

/-- Generate all Boolean masks of a given length. -/
def allMasks : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allMasks n).flatMap λ m => [true :: m, false :: m]

/-- The conflict account (eq. 61): ⟦ought φ⟧ = 1 iff for some
    maximally consistent subset S of g(w), ∀w' ∈ ∩S ∩ f(w): φ(w'). -/
def conflictOught (bestProps : List (BProp World)) (accessible : List World)
    (φ : BProp World) : Bool :=
  (allMasks bestProps.length).any λ mask =>
    maskMaximal bestProps mask accessible &&
    (subsetWorlds bestProps mask accessible).all φ

/-- In The Office, the conflict account yields epistemic dilemmas.
    The best propositions are {Alice in, Bob in, Carol in, ¬everyone in}.
    MCS {Bob in, Carol in, ¬everyone in} entails Alice is absent — so the
    conflict account predicts "Alice should NOT be in" is true.

    Boylan's semantics avoids this: *ought* never produces dilemmas when
    PBEST is pairwise consistent. -/
def officeBestConflict : List (BProp World) :=
  [aliceIn, bobIn, carolIn, λ w => !everyoneIn w]

theorem conflict_predicts_alice_absent :
    conflictOught officeBestConflict
      (accessibleWorldsList officeBase .w0) (λ w => !aliceIn w) = true := by
  decide

theorem boylan_no_alice_absent :
    ought officeOrdering officeBase officeCandidates (λ w => !aliceIn w) .w0
      = some false := by
  decide

/-- The conflict account also predicts a full dilemma: both "Alice should
    be in" AND "Alice should not be in" come out true simultaneously.
    Boylan's semantics avoids this entirely (see `no_dilemma` above). -/
theorem conflict_dilemma :
    conflictOught officeBestConflict
      (accessibleWorldsList officeBase .w0) aliceIn = true ∧
    conflictOught officeBestConflict
      (accessibleWorldsList officeBase .w0) (λ w => !aliceIn w) = true :=
  ⟨by decide, by decide⟩

-- ============================================================================
-- §14. Bridges to Kratzer Infrastructure
-- ============================================================================

/-! ## Connecting to Kratzer's framework

Boylan's apparatus extends Kratzer with proposition-level ordering and
pairwise consistency. We bridge back by showing:
1. `pairConsistent` agrees with Kratzer's `isConsistent` (Background.lean)
2. The Office and Dessert scenarios can be typed via `EpistemicFlavor`
   and `DeonticFlavor` (Flavor.lean) -/

/-- Boylan's pairwise consistency agrees with Kratzer's proposition
    consistency when all worlds are accessible (Background.lean, p. 31). -/
theorem pairConsistent_eq_isConsistent (p q : BProp World) :
    pairConsistent p q allWorlds = isConsistent [p, q] := by
  unfold pairConsistent isConsistent propIntersection
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
  constructor
  · intro ⟨w, _, hw⟩
    exact Finset.ne_empty_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩)
  · intro h
    obtain ⟨w, hw⟩ := Finset.nonempty_of_ne_empty h
    exact ⟨w, Core.Proposition.FiniteWorlds.complete w,
      (Finset.mem_filter.mp hw).2⟩

/-- The Office as an epistemic scenario via `Kratzer.Flavor`. -/
def officeEpistemic : EpistemicFlavor World where
  evidence := officeBase

/-- Dessert as a deontic scenario via `Kratzer.Flavor`. -/
def dessertDeontic : DeonticFlavor World where
  circumstances := dessertBase
  norms := fun _ => []

/-- The epistemic flavor's modal base matches The Office. -/
theorem office_base_from_flavor :
    officeEpistemic.toKratzerParams.base = officeBase := rfl

/-- The deontic flavor's modal base matches Dessert. -/
theorem dessert_base_from_flavor :
    dessertDeontic.toKratzerParams.base = dessertBase := rfl

end Phenomena.Modality.Studies.Boylan2023
