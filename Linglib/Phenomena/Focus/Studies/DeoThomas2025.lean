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

import Linglib.Core.QUD.Basic
import Linglib.Core.QUD.PrecisionProjection
import Linglib.Core.QUD.Relevance
import Linglib.Core.Inquisitive
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy
import Linglib.Phenomena.Focus.Exclusives
import Linglib.Theories.Semantics.Questions.Denotation.Inquisitive
import Linglib.Theories.Semantics.Degree.Granularity

namespace DeoThomas2025

open Phenomena.Focus.Exclusives
open Discourse (Issue)

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

    Construals are `Issue`s (sets of alternative propositions), matching the
    paper's definition (30)-(31): questions are sets of propositions that cover
    the common ground. This is more faithful than using partitions (`QUD`),
    since the paper explicitly notes that granularity-based construals generally
    cannot be ordered by question entailment (fn. 20).

    `W` is the world type. -/
structure DiscourseContext (W : Type*) where
  /-- The available construals of UQ_c -/
  construals : List (Issue W)
  /-- Does the speaker have sufficient evidence to answer this question? -/
  quality : Issue W → Bool
  /-- Is this question relevant to the current discourse? -/
  relevance : Issue W → Bool
  /-- There must be at least one construal -/
  nonempty : construals ≠ []

variable {W : Type*}

/-- A question is answerable iff it passes both Quality and Relevance (34). -/
def answerable (ctx : DiscourseContext W) (q : Issue W) : Bool :=
  ctx.quality q && ctx.relevance q

-- ============================================================================
-- C. Widest Answerable Question
-- ============================================================================

/-- OPT_c(Q) (@cite{deo-thomas-2025} (35)): the optimal question in a set
    of construals.

    `q` is the widest answerable construal: it is answerable, it is in the
    construal set, and no strictly wider answerable construal exists.

    Width is measured by `Issue.widerThan` ((32)), the paper's comparison of
    question inquisitivity — explicitly weaker than G&S question entailment
    (fn. 20), because granularity-based construals generally cannot be ordered
    by entailment strength. -/
def isWidestAnswerable (ctx : DiscourseContext W) (q : Issue W)
    (worlds : List W) : Prop :=
  q ∈ ctx.construals ∧
  answerable ctx q = true ∧
  ∀ q' ∈ ctx.construals, answerable ctx q' = true →
    q'.widerThan q worlds = true → False

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
cell). At the issue level, "wider" is `Issue.widerThan` (@cite{deo-thomas-2025}
(32): same cover, no coarse answer ⊂ fine answer, some fine answer ⊂ coarse
answer). The bridge: `toIssue` preserves this relationship. -/

open Semantics.Questions.Inquisitive (toIssue)

/-- Fine cell membership implies coarse cell membership when `q` refines `q'`.
    Connects through an intermediate world `w₀` that belongs to both cells:
    `q.sameAnswer s w = true → q'.sameAnswer r w = true` via the chain
    w →_q s →_q w₀ →_{q'} r (symmetry + transitivity + refinement). -/
private theorem cell_containment {W : Type*} (q q' : QUD W)
    (s r w₀ : W) (hRefines : QUD.refines q q')
    (hsw₀ : q.sameAnswer s w₀ = true) (hrw₀ : q'.sameAnswer r w₀ = true)
    (w : W) (hsw : q.sameAnswer s w = true) : q'.sameAnswer r w = true := by
  have hws : q.sameAnswer w s = true := by rw [q.symm w s]; exact hsw
  have hww₀ : q.sameAnswer w w₀ = true := q.trans w s w₀ hws hsw₀
  have hw₀r : q'.sameAnswer w₀ r = true := by rw [q'.symm w₀ r]; exact hrw₀
  have hwr : q'.sameAnswer w r = true :=
    q'.trans w w₀ r (hRefines w w₀ hww₀) hw₀r
  rw [q'.symm r w]; exact hwr

/-- Strict partition refinement implies issue width.

    If `q` strictly refines `q'` (finer partition), then converting both to
    issues via `toIssue` yields `q`-issue wider than `q'`-issue.

    The strictness witnesses `w₀, v₀` must be in `worlds`: they share a
    coarse cell (`q'.sameAnswer w₀ v₀ = true`) but not a fine cell
    (`q.sameAnswer w₀ v₀ = false`), providing the element that separates
    a coarse cell from the fine cell it properly contains.

    The proof establishes the three conditions of width (32):
    - (a) Same cover: both partitions cover `worlds` identically
      (`QUD.toCells_covers`)
    - (b) No coarse answer ⊂ fine answer: if coarse ⊆ fine, then fine ⊆ coarse
      too (by `cell_containment`), so proper containment is impossible
    - (c) Some fine answer ⊂ coarse answer: the fine cell of `w₀` is properly
      contained in its coarse cell, witnessed by `v₀` -/
theorem refinement_implies_wider {W : Type*}
    (q q' : QUD W) (worlds : List W)
    (hRefines : QUD.refines q q')
    (w₀ v₀ : W) (hw₀ : w₀ ∈ worlds) (hv₀ : v₀ ∈ worlds)
    (hCoarse : q'.sameAnswer w₀ v₀ = true)
    (hFine : q.sameAnswer w₀ v₀ = false) :
    (toIssue q worlds).widerThan (toIssue q' worlds) worlds = true := by
  simp only [Semantics.Questions.Inquisitive.toIssue,
             Semantics.Questions.Inquisitive.issueOfPartition,
             Discourse.Issue.widerThan, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  -- (a) Same cover: every w ∈ worlds is in some cell of each partition
  · rw [List.all_eq_true]
    intro w hw
    simp only [Discourse.Issue.infoContent]
    obtain ⟨c₁, hc₁, h₁⟩ := QUD.toCells_covers q worlds w hw
    obtain ⟨c₂, hc₂, h₂⟩ := QUD.toCells_covers q' worlds w hw
    have h1 : (q.toCells worlds).any (fun alt => alt w) = true := by
      rw [List.any_eq_true]; exact ⟨c₁, hc₁, h₁⟩
    have h2 : (q'.toCells worlds).any (fun alt => alt w) = true := by
      rw [List.any_eq_true]; exact ⟨c₂, hc₂, h₂⟩
    simp [h1, h2]
  -- (b) No coarse cell properly contained in any fine cell
  · rw [List.all_eq_true]
    intro p2 hp2
    obtain ⟨r, hr, hr_eq⟩ := QUD.toCells_exists_rep q' worlds p2 hp2
    -- Case split: if any fine cell properly contains p2, derive contradiction
    by_cases hany : (q.toCells worlds).any
        (fun p1 => Discourse.properlyContains p1 p2 worlds) = true
    · exfalso
      obtain ⟨p1, hp1, hpc⟩ := List.any_eq_true.mp hany
      obtain ⟨s, _, hs_eq⟩ := QUD.toCells_exists_rep q worlds p1 hp1
      simp only [Discourse.properlyContains, Bool.and_eq_true,
                 List.all_eq_true, List.any_eq_true] at hpc
      obtain ⟨hsub, w₁, hw₁, hdiff⟩ := hpc
      -- p2 r = true (refl), so from p2 ⊆ p1, p1 r = true
      have hp2r : p2 r = true := by rw [hr_eq]; exact q'.refl r
      have hsub_r := hsub r hr
      rw [hp2r] at hsub_r; simp at hsub_r
      -- q.sameAnswer s r = true
      have hsr : q.sameAnswer s r = true := by rw [← hs_eq]; exact hsub_r
      -- p1 w₁ = true and !p2 w₁ = true (from the difference witness)
      have hp1w₁ : p1 w₁ = true := by
        revert hdiff; cases p1 w₁ <;> simp
      have hp2w₁_neg : !p2 w₁ = true := by
        revert hdiff; cases p1 w₁ <;> cases p2 w₁ <;> simp
      have hsw₁ : q.sameAnswer s w₁ = true := by rw [← hs_eq]; exact hp1w₁
      -- By cell_containment, p1 ⊆ p2 — so p2 w₁ = true, contradicting hp2w₁_neg
      have : q'.sameAnswer r w₁ = true :=
        cell_containment q q' s r r hRefines hsr (q'.refl r) w₁ hsw₁
      have hp2w₁ : p2 w₁ = true := by rw [hr_eq]; exact this
      rw [hp2w₁] at hp2w₁_neg; simp at hp2w₁_neg
    · -- The any is false, so !false = true
      cases h : (q.toCells worlds).any
          (fun p1 => Discourse.properlyContains p1 p2 worlds) <;> simp_all
  -- (c) Some fine cell properly contained in coarse cell
  · obtain ⟨cf, hcf, hcf_w₀⟩ := QUD.toCells_covers q worlds w₀ hw₀
    obtain ⟨cc, hcc, hcc_w₀⟩ := QUD.toCells_covers q' worlds w₀ hw₀
    obtain ⟨sf, _, hsf_eq⟩ := QUD.toCells_exists_rep q worlds cf hcf
    obtain ⟨rc, _, hrc_eq⟩ := QUD.toCells_exists_rep q' worlds cc hcc
    have hsfw₀ : q.sameAnswer sf w₀ = true := by rw [← hsf_eq]; exact hcf_w₀
    have hrcw₀ : q'.sameAnswer rc w₀ = true := by rw [← hrc_eq]; exact hcc_w₀
    rw [List.any_eq_true]
    refine ⟨cf, hcf, List.any_eq_true.mpr ⟨cc, hcc, ?_⟩⟩
    -- properlyContains cc cf worlds = true (coarse properly contains fine)
    simp only [Discourse.properlyContains, Bool.and_eq_true]
    constructor
    · -- cf ⊆ cc over worlds
      rw [List.all_eq_true]; intro w hw
      by_cases hcfw : cf w = true
      · -- cf w = true → cc w = true (by cell_containment through w₀)
        have hsfw : q.sameAnswer sf w = true := by rw [← hsf_eq]; exact hcfw
        have hccw : cc w = true := by
          rw [hrc_eq]; exact cell_containment q q' sf rc w₀ hRefines hsfw₀ hrcw₀ w hsfw
        simp [hcfw, hccw]
      · -- cf w ≠ true → cf w = false
        have hcfw_false : cf w = false := by
          cases h : cf w with
          | true => exfalso; exact absurd h hcfw
          | false => rfl
        simp [hcfw_false]
    · -- cc \ cf ≠ ∅: v₀ is in cc but not cf
      rw [List.any_eq_true]
      refine ⟨v₀, hv₀, ?_⟩
      simp only [Bool.and_eq_true]
      constructor
      · -- cc v₀ = true (coarse cell of w₀ contains v₀, since w₀ and v₀ share a coarse cell)
        rw [hrc_eq]; exact q'.trans rc w₀ v₀ hrcw₀ hCoarse
      · -- !cf v₀ = true (v₀ is NOT in the fine cell of w₀)
        have hsfv₀ : q.sameAnswer sf v₀ = false := by
          by_contra h
          have hsfv₀_true : q.sameAnswer sf v₀ = true := by
            cases hval : q.sameAnswer sf v₀ with
            | true => rfl
            | false => exfalso; exact absurd hval h
          have hw₀sf : q.sameAnswer w₀ sf = true := by rw [q.symm w₀ sf]; exact hsfw₀
          have : q.sameAnswer w₀ v₀ = true := q.trans w₀ sf v₀ hw₀sf hsfv₀_true
          rw [this] at hFine; exact absurd hFine (by decide)
        have : cf v₀ = false := by rw [hsf_eq]; exact hsfv₀
        simp [this]

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
    (worlds : List (Fin n))
    (w₀ v₀ : Fin n) (hw₀ : w₀ ∈ worlds) (hv₀ : v₀ ∈ worlds)
    (hCoarse : (granQUD n ε₂).sameAnswer w₀ v₀ = true)
    (hFine : (granQUD n ε₁).sameAnswer w₀ v₀ = false) :
    (toIssue (granQUD n ε₁) worlds).widerThan
      (toIssue (granQUD n ε₂) worlds) worlds = true :=
  refinement_implies_wider _ _ worlds
    (finer_granularity_refines n ε₁ ε₂ hdvd)
    w₀ v₀ hw₀ hv₀ hCoarse hFine

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
    (toIssue fineQ fig1Worlds).widerThan
      (toIssue coarseQ fig1Worlds) fig1Worlds = true := by
  rw [coarseQ_is_granQUD, fineQ_is_granQUD]
  exact finer_granularity_implies_wider 8 2 4 ⟨2, rfl⟩
    fig1Worlds 0 2
    (by simp [fig1Worlds]) (by simp [fig1Worlds])
    (by native_decide) (by native_decide)

end DeoThomas2025
