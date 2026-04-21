/-
# Domain Widening: *just* as addressing the widest answerable question

Formalizes @cite{deo-thomas-2025}: *just* signals that the speaker addresses the
**widest answerable construal** of an underspecified question (UQ). The 9 flavors
arise from how the widest construal is determined by Quality and Relevance.

## Core claim

*Just* has a SINGLE lexical entry. The apparent polysemy follows from
the interaction of domain widening with different alternative sources and Gricean
maxim failures. *Only* shares the exhaustification semantics but requires Roothian
alternatives, explaining why it substitutes in only 2 of the 9 flavors.

-/

import Linglib.Core.Question.QUD
import Linglib.Core.Question.PrecisionProjection
import Linglib.Core.Question.Basic
import Linglib.Core.Question.Granularity
import Linglib.Core.Mood.PartitionAsInquiry
import Linglib.Phenomena.Focus.Exclusives
import Linglib.Theories.Semantics.Questions.Denotation.Inquisitive
import Linglib.Theories.Semantics.Degree.Granularity

namespace DeoThomas2025

open Phenomena.Focus.Exclusives
open Core (Question)

-- ============================================================================
-- A. Alternative Source
-- ============================================================================

/-- Where the alternatives for *just* come from.
    Roothian alternatives are the standard focus-semantic alternatives;
    the other sources are what distinguish *just* from *only*. -/
inductive AlternativeSource where
  | roothian     -- Standard focus alternatives (shared with *only*)
  | granularity  -- Precision / scale granularity levels
  | causal       -- Causal explanations
  | elaboration  -- Elaboration / specification alternatives
  | normative    -- Norm-based expectations
  deriving Repr, DecidableEq

/-- Map each flavor of *just* to its alternative source. -/
def associatedSource : JustFlavor → AlternativeSource
  | .complementExclusion   => .roothian
  | .rankOrder             => .roothian
  | .emphatic              => .granularity
  | .precisifyingEquality  => .granularity
  | .precisifyingProximity => .granularity
  | .minimalSufficiency    => .causal
  | .unexplanatory         => .causal
  | .unelaboratory         => .elaboration
  | .counterexpectational  => .normative

-- ============================================================================
-- B. Discourse Context
-- ============================================================================

/-- A discourse context provides construals of an underspecified question (UQ)
    together with Quality and Relevance filters.

    Construals are `Question`s (sets of alternative propositions), matching the
    paper's definition (30)-(31): questions are sets of propositions that cover
    the common ground. This is more faithful than using partitions (`QUD`),
    since the paper explicitly notes that granularity-based construals generally
    cannot be ordered by question entailment (fn. 20).

    `W` is the world type. -/
structure DiscourseContext (W : Type*) where
  /-- The available construals of UQ_c -/
  construals : List (Question W)
  /-- Does the speaker have sufficient evidence to answer this question? -/
  quality : Question W → Bool
  /-- Is this question relevant to the current discourse? -/
  relevance : Question W → Bool
  /-- There must be at least one construal -/
  nonempty : construals ≠ []

variable {W : Type*}

/-- A question is answerable iff it passes both Quality and Relevance (34). -/
def answerable (ctx : DiscourseContext W) (q : Question W) : Bool :=
  ctx.quality q && ctx.relevance q

-- ============================================================================
-- C. Widest Answerable Question
-- ============================================================================

/-- OPT_c(Q) (@cite{deo-thomas-2025} (35)): the optimal question in a set
    of construals.

    `q` is the widest answerable construal: it is answerable, it is in the
    construal set, and no strictly wider answerable construal exists.

    Width is measured by `Core.Question.widerThan` ((32)), the paper's comparison
    of question inquisitivity — explicitly weaker than G&S question entailment
    (fn. 20), because granularity-based construals generally cannot be ordered
    by entailment strength. -/
def isWidestAnswerable (ctx : DiscourseContext W) (q : Question W) : Prop :=
  q ∈ ctx.construals ∧
  answerable ctx q = true ∧
  ∀ q' ∈ ctx.construals, answerable ctx q' = true → ¬ q'.widerThan q

/-- Classify a discourse context by WHY the widest answerable construal
    is optimal. Connects to `Phenomena.Focus.Exclusives.ContextType`.

    - (37a) answerable: all construals are answerable → CQ = widest overall
    - (37b) qualityFail: some construal fails Quality (speaker lacks evidence)
    - (37c) relevanceFail: some construal fails Relevance (not discourse-relevant) -/
def classifyContext (ctx : DiscourseContext W) : ContextType :=
  if ctx.construals.all (λ q => answerable ctx q) then
    .answerable
  else if ctx.construals.any (λ q => !ctx.quality q) then
    .qualityFail
  else
    .relevanceFail

-- ============================================================================
-- D. Core theorems
-- ============================================================================

-- Theorem 1: *only* substitutes iff the alternative source is Roothian

/-- *Only* can replace *just* exactly when the alternatives are Roothian
    (complement-exclusion and rank-order). Verified against all empirical data. -/
theorem only_substitutes_iff_roothian :
    ∀ d ∈ allJustData,
      d.onlyOk = true ↔ associatedSource d.flavor = .roothian := by
  intro d hd
  simp [allJustData] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                   rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [associatedSource, complementExclusion_vacation, rankOrder_intern,
          emphatic_amazing, emphatic_enormous,
          precisifying_eq_full, precisifying_prox_older, precisifying_temporal,
          minSuff_cat, minSuff_gpa,
          unexplanatory_lamp, unexplanatory_mangoes,
          unelaboratory_dog, unelaboratory_proton, unelaboratory_mad,
          counterexp_texting, counterexp_wafer]

-- Theorem 2: Context type determines flavor family

/-- Quality-failure contexts yield only causal-alternative flavors
    (unexplanatory, minimal sufficiency). -/
theorem quality_fail_implies_causal :
    ∀ d ∈ allJustData,
      d.contextType = .qualityFail →
        associatedSource d.flavor = .causal := by
  intro d hd hctx
  simp [allJustData] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                   rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [associatedSource, complementExclusion_vacation, rankOrder_intern,
              emphatic_amazing, emphatic_enormous,
              precisifying_eq_full, precisifying_prox_older, precisifying_temporal,
              minSuff_cat, minSuff_gpa,
              unexplanatory_lamp, unexplanatory_mangoes,
              unelaboratory_dog, unelaboratory_proton, unelaboratory_mad,
              counterexp_texting, counterexp_wafer]

/-- Relevance-failure contexts yield only elaboration-alternative flavors
    (unelaboratory). -/
theorem relevance_fail_implies_elaboration :
    ∀ d ∈ allJustData,
      d.contextType = .relevanceFail →
        associatedSource d.flavor = .elaboration := by
  intro d hd hctx
  simp [allJustData] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                   rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [associatedSource, complementExclusion_vacation, rankOrder_intern,
              emphatic_amazing, emphatic_enormous,
              precisifying_eq_full, precisifying_prox_older, precisifying_temporal,
              minSuff_cat, minSuff_gpa,
              unexplanatory_lamp, unexplanatory_mangoes,
              unelaboratory_dog, unelaboratory_proton, unelaboratory_mad,
              counterexp_texting, counterexp_wafer]

-- Theorem 3: *only* requires shared CQ (Roothian alternatives)

/-- *only* is felicitous only with Roothian alternatives (shared CQ).
    *just* is felicitous regardless of alternative source.
    This is WHY they diverge: *only* exhaustifies over shared alternatives,
    *just* widens the question. -/
theorem only_requires_shared_cq :
    ∀ d ∈ allJustData,
      d.onlyOk = true →
        associatedSource d.flavor = .roothian := by
  intro d hd honlyOk
  exact (only_substitutes_iff_roothian d hd).mp honlyOk

-- Theorem 4: Every flavor appears in the data

/-- All 9 `JustFlavor` constructors are attested in the empirical data. -/
theorem all_flavors_attested :
    (allJustData.any (λ d => d.flavor == .complementExclusion)) = true ∧
    (allJustData.any (λ d => d.flavor == .rankOrder)) = true ∧
    (allJustData.any (λ d => d.flavor == .emphatic)) = true ∧
    (allJustData.any (λ d => d.flavor == .precisifyingEquality)) = true ∧
    (allJustData.any (λ d => d.flavor == .precisifyingProximity)) = true ∧
    (allJustData.any (λ d => d.flavor == .minimalSufficiency)) = true ∧
    (allJustData.any (λ d => d.flavor == .unexplanatory)) = true ∧
    (allJustData.any (λ d => d.flavor == .unelaboratory)) = true ∧
    (allJustData.any (λ d => d.flavor == .counterexpectational)) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- E. WXDY bridge (@cite{kay-fillmore-1999})
-- ============================================================================

/-- WXDY's incredulity arises from a normative expectation violation:
the situation violates what the speaker considers normal/appropriate.
This is the same alternative source as counterexpectational *just*
("He's just texting during the lecture!").

- WXDY: "What's this fly doing in my soup?" — violates dining norms
- *just*: "He's just texting during the lecture!" — violates classroom norms -/
def wxdyAlternativeSource : AlternativeSource := .normative

/-- WXDY's incongruity and counterexpectational *just* share the same
    alternative source: both involve normative expectations being violated. -/
theorem wxdy_incongruity_is_counterexpectational :
    wxdyAlternativeSource = associatedSource .counterexpectational := rfl

-- ============================================================================
-- F. Granularity-Width Bridge (Figure 1)
-- ============================================================================

/-! ### Partition refinement implies question width

The paper's central formal insight: finer granularity produces wider questions.
At the partition level, "finer" is `QUD.refines` (every fine cell ⊆ some coarse
cell), equivalently `q.toSetoid ≤ q'.toSetoid` in mathlib's `Setoid` lattice.
At the issue level, "wider" is `Core.Question.widerThan` (@cite{deo-thomas-2025}
(32): same `info`, no coarse answer ⊊ fine answer, some fine answer ⊊ coarse
answer). The bridge: `toIssue := Core.Question.fromSetoid ∘ QUD.toSetoid`
preserves this relationship.

The proof is an order-theoretic one-liner over `Setoid`: every alternative
of `Core.Question.fromSetoid r` is either `∅` or an equivalence class of `r`
(`alt_fromSetoid_subset_classes`), and the q-class of `w₀` is contained in
the q'-class of `w₀` by refinement, with `v₀` witnessing strict containment.
This replaces a 100-line Bool/List proof that managed indices into
`worlds : List W` and case-split on `properlyContains`. -/

open Semantics.Questions.Inquisitive (toIssue)

/-- Strict partition refinement implies issue width.

    If `q` (strictly) refines `q'` (`q` is the finer partition), then
    `toIssue q` is wider than `toIssue q'` as `Core.Question`s.

    The strictness witnesses `w₀, v₀ : W` share a coarse cell
    (`q'.sameAnswer w₀ v₀ = true`) but not a fine cell
    (`q.sameAnswer w₀ v₀ = false`); they witness condition (c).

    The proof establishes the three conditions of `Core.Question.widerThan`:
    - (a) Same `info`: both `fromSetoid`-derived issues have `info = univ`.
    - (b) No q'-alternative is properly contained in any q-alternative:
      alternatives are classes (or `∅`); under refinement, classes only
      widen as we go from the finer to the coarser setoid, so the
      reverse containment is impossible.
    - (c) Some q-alternative properly contained in some q'-alternative:
      witnessed by the q-class and q'-class of `w₀`, with `v₀` showing
      the inclusion is strict. -/
theorem refinement_implies_wider {W : Type*}
    (q q' : QUD W)
    (hRefines : QUD.refines q q')
    (w₀ v₀ : W)
    (hCoarse : q'.sameAnswer w₀ v₀ = true)
    (hFine : q.sameAnswer w₀ v₀ = false) :
    (toIssue q).widerThan (toIssue q') := by
  -- Refinement reads as `q.toSetoid ≤ q'.toSetoid` in mathlib's lattice
  have hle : ∀ {x y : W}, q.toSetoid x y → q'.toSetoid x y :=
    fun {x y} hxy => QUD.r_of_sameAnswer (hRefines x y (QUD.sameAnswer_of_r hxy))
  -- The q-class and q'-class of w₀
  let C₁ : Set W := {x | q.toSetoid x w₀}
  let C₂ : Set W := {x | q'.toSetoid x w₀}
  have hC₁_class : C₁ ∈ q.toSetoid.classes := Setoid.mem_classes q.toSetoid w₀
  have hC₂_class : C₂ ∈ q'.toSetoid.classes := Setoid.mem_classes q'.toSetoid w₀
  have hC₁_alt : C₁ ∈ Core.Question.alt (Core.Question.fromSetoid q.toSetoid) :=
    Core.Question.class_mem_alt_fromSetoid _ hC₁_class
  have hC₂_alt : C₂ ∈ Core.Question.alt (Core.Question.fromSetoid q'.toSetoid) :=
    Core.Question.class_mem_alt_fromSetoid _ hC₂_class
  refine ⟨?_, ?_, ?_⟩
  -- (a) Same info: both reduce to Set.univ
  · simp only [toIssue, Core.Question.info_fromSetoid]
  -- (b) No q'-alternative properly contained in any q-alternative
  · intro p₂ hp₂ p₁ hp₁ hssub
    rcases Core.Question.alt_fromSetoid_subset_classes _ hp₂ with hp₂_empty | hp₂_class
    · -- p₂ = ∅ but the q'-class of w₀ contains w₀, so ∅ ∉ alt — contradiction
      have hC₂_props : C₂ ∈ (Core.Question.fromSetoid q'.toSetoid).props :=
        Or.inr ⟨C₂, hC₂_class, subset_rfl⟩
      have hp_sub : p₂ ⊆ C₂ := by rw [hp₂_empty]; exact Set.empty_subset _
      have heq : p₂ = C₂ := hp₂.2 C₂ hC₂_props hp_sub
      have hw₀_in : w₀ ∈ p₂ := by rw [heq]; exact Setoid.refl' q'.toSetoid w₀
      rw [hp₂_empty] at hw₀_in
      exact hw₀_in.elim
    · rcases Core.Question.alt_fromSetoid_subset_classes _ hp₁ with hp₁_empty | hp₁_class
      · -- p₁ = ∅, so p₂ ⊊ ∅: p₂ ⊆ ∅ AND ¬ ∅ ⊆ p₂. The latter is vacuously false.
        rw [hp₁_empty] at hssub
        exact hssub.2 (Set.empty_subset _)
      · -- Both classes; refinement forces p₁ ⊆ p₂, contradicting p₂ ⊊ p₁
        obtain ⟨w, hp₂_eq⟩ := hp₂_class
        obtain ⟨v, hp₁_eq⟩ := hp₁_class
        -- p₂ = {x | q'.toSetoid x w}, p₁ = {x | q.toSetoid x v}
        have hsub : p₁ ⊆ p₂ := by
          rw [hp₁_eq, hp₂_eq]
          intro x (hxv : q.toSetoid x v)
          have hxv' : q'.toSetoid x v := hle hxv
          -- w ∈ p₂ (refl), so w ∈ p₁ (by ⊆); thus q.toSetoid w v
          have hw_in_p₂ : w ∈ p₂ := by
            rw [hp₂_eq]; exact Setoid.refl' q'.toSetoid w
          have hw_in_p₁ : w ∈ p₁ := hssub.1 hw_in_p₂
          have hwv_q : q.toSetoid w v := by rw [hp₁_eq] at hw_in_p₁; exact hw_in_p₁
          have hwv_q' : q'.toSetoid w v := hle hwv_q
          have hvw : q'.toSetoid v w := Setoid.symm' q'.toSetoid hwv_q'
          exact Setoid.trans' q'.toSetoid hxv' hvw
        exact hssub.2 hsub
  -- (c) C₁ ⊊ C₂: the q-class of w₀ is properly contained in the q'-class
  · refine ⟨C₁, hC₁_alt, C₂, hC₂_alt, ?_, ?_⟩
    · intro x (hx : q.toSetoid x w₀); exact hle hx
    · intro hCsub
      -- v₀ ∈ C₂ (from hCoarse + symm) but v₀ ∉ C₁ (from hFine)
      have hv₀_C₂ : v₀ ∈ C₂ := by
        change q'.toSetoid v₀ w₀
        exact Setoid.symm' q'.toSetoid (QUD.r_of_sameAnswer hCoarse)
      have hv₀_C₁ : v₀ ∈ C₁ := hCsub hv₀_C₂
      have hv₀_q : q.sameAnswer v₀ w₀ = true := QUD.sameAnswer_of_r hv₀_C₁
      rw [q.symm v₀ w₀] at hv₀_q
      rw [hv₀_q] at hFine
      exact absurd hFine (by decide)

-- ============================================================================
-- G. Granularity–Question Composition (§3.1.2 + §3.2)
-- ============================================================================

/-! ### The full chain: finer granularity → wider question

Composes the two independently proved steps:
1. `finer_granularity_refines` (from `Theories.Semantics.Degree.Granularity`):
   if ε₁ ∣ ε₂, the ε₁-partition refines the ε₂-partition
2. `refinement_implies_wider` (proved above):
   strict partition refinement → issue width

This is the formal content of the lexical entry (36): *just* selects
the widest answerable construal, which — when alternatives vary by
granularity — is the finest one the speaker can answer. -/

open Semantics.Degree.Granularity (granQUD finer_granularity_refines)

/-- The complete granularity–width chain (@cite{deo-thomas-2025} §3.1.2–3.2).

    If ε₁ divides ε₂ (finer grain) and there exist worlds that share a
    coarse cell but not a fine cell, then the fine-grained question is
    strictly wider than the coarse-grained question.

    This is the general version of Figure 1: any uniform-grain-width
    scale satisfies the width relation when grain widths are divisible. -/
theorem finer_granularity_implies_wider (n ε₁ ε₂ : Nat)
    (hdvd : ε₁ ∣ ε₂)
    (w₀ v₀ : Fin n)
    (hCoarse : (granQUD n ε₂).sameAnswer w₀ v₀ = true)
    (hFine : (granQUD n ε₁).sameAnswer w₀ v₀ = false) :
    (toIssue (granQUD n ε₁)).widerThan (toIssue (granQUD n ε₂)) :=
  refinement_implies_wider _ _
    (finer_granularity_refines n ε₁ ε₂ hdvd)
    w₀ v₀ hCoarse hFine

-- ============================================================================
-- H. Concrete Verification: Figure 1
-- ============================================================================

/-- The 8-point age scale from Figure 1 (@cite{deo-thomas-2025}). -/
def fig1Worlds : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- Coarse granularity: 2 cells of 4 (e.g., "younger half" vs "older half").
    Worlds 0–3 share one answer, worlds 4–7 share another. -/
def coarseQ : QUD (Fin 8) := QUD.ofProject (λ w => w.val / 4)

/-- Fine granularity: 4 cells of 2 (e.g., {0,1}, {2,3}, {4,5}, {6,7}).
    Each pair of adjacent worlds shares an answer. -/
def fineQ : QUD (Fin 8) := QUD.ofProject (λ w => w.val / 2)

/-- Figure 1's partitions are instances of the general `granQUD`. -/
theorem coarseQ_is_granQUD : coarseQ = granQUD 8 4 := rfl
theorem fineQ_is_granQUD : fineQ = granQUD 8 2 := rfl

/-- Fine strictly refines coarse: knowing the fine answer determines the
    coarse answer, but not vice versa (0 and 2 share a coarse cell but
    not a fine cell). -/
theorem fig1_strict_refinement :
    QUD.refines fineQ coarseQ ∧ ¬QUD.refines coarseQ fineQ := by
  constructor
  · rw [coarseQ_is_granQUD, fineQ_is_granQUD]
    exact finer_granularity_refines 8 2 4 ⟨2, rfl⟩
  · intro h
    exact absurd (h 0 2 (by native_decide)) (by native_decide)

/-- Figure 1 via the general granularity–width theorem.
    The fine 4-cell partition produces a wider issue than
    the coarse 2-cell partition over the 8-point domain.

    Witnessed by worlds 0 and 2: they share a coarse cell (0/4 = 2/4 = 0)
    but not a fine cell (0/2 = 0 ≠ 2/2 = 1). -/
theorem fig1_finer_is_wider :
    (toIssue fineQ).widerThan (toIssue coarseQ) := by
  rw [coarseQ_is_granQUD, fineQ_is_granQUD]
  exact finer_granularity_implies_wider 8 2 4 ⟨2, rfl⟩
    0 2
    (by native_decide) (by native_decide)

end DeoThomas2025
