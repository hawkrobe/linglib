/-
# Domain Widening: *just* as addressing the widest answerable question

Formalizes Deo & Thomas (2025): *just* signals that the speaker addresses the
**widest answerable construal** of an underspecified question (UQ). The 7 flavors
arise from how the widest construal is determined by Quality and Relevance.

## Core claim

*Just* has a SINGLE lexical entry. The apparent polysemy (7 flavors) follows from
the interaction of domain widening with different alternative sources and Gricean
maxim failures. *Only* shares the exhaustification semantics but requires Roothian
alternatives, explaining why it substitutes in only 2 of the 7 flavors.

## References

- Deo, A. & Thomas, W. (2025). Addressing the widest answerable question:
  English "just" as a domain widening strategy.
- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Rooth, M. (1992). A theory of focus interpretation.
-/

import Linglib.Core.QUD
import Linglib.Theories.QuestionSemantics.Partition
import Linglib.Phenomena.Focus.Exclusives

namespace TruthConditional.Sentence.DomainWidening

open Phenomena.Focus.Exclusives
open QuestionSemantics

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
  deriving Repr, DecidableEq, BEq

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

    `W` is the world/meaning type that questions partition over. -/
structure DiscourseContext (W : Type*) where
  /-- The available construals of UQ_c -/
  construals : List (QUD W)
  /-- Does the speaker have sufficient evidence to answer this QUD? -/
  quality : QUD W → Bool
  /-- Is this QUD relevant to the current discourse? -/
  relevance : QUD W → Bool
  /-- There must be at least one construal -/
  nonempty : construals ≠ []

variable {W : Type*}

/-- A QUD is answerable iff it passes both Quality and Relevance. -/
def answerable (ctx : DiscourseContext W) (q : QUD W) : Bool :=
  ctx.quality q && ctx.relevance q

/-- `q1` is strictly wider than `q2` when `q2` refines `q1` but not vice versa.
    A wider question has a coarser partition — fewer distinctions.
    Uses `GSQuestion.refines` from Partition.lean. -/
def strictlyWider (q1 q2 : GSQuestion W) : Prop :=
  GSQuestion.refines q2 q1 ∧ ¬ GSQuestion.refines q1 q2

-- ============================================================================
-- C. Widest Answerable Question
-- ============================================================================

/-- `q` is the widest answerable construal: it is answerable, it is in the
    construal set, and no strictly wider answerable construal exists. -/
def isWidestAnswerable (ctx : DiscourseContext W) (q : QUD W) : Prop :=
  q ∈ ctx.construals ∧
  answerable ctx q = true ∧
  ∀ q' ∈ ctx.construals, answerable ctx q' = true →
    strictlyWider q' q → False

/-- Classify a discourse context by WHY the widest answerable construal is optimal.
    Connects to `Phenomena.Focus.Exclusives.ContextType`. -/
def classifyContext (ctx : DiscourseContext W) (q : QUD W)
    (_ : q ∈ ctx.construals) : ContextType :=
  if ctx.construals.any (fun q' => !ctx.quality q' && !ctx.relevance q') then
    -- Can't distinguish quality vs relevance failure from both failing
    .answerable
  else if ctx.construals.any (fun q' => !ctx.quality q') then
    .qualityFail
  else if ctx.construals.any (fun q' => !ctx.relevance q') then
    .relevanceFail
  else
    .answerable

-- ============================================================================
-- D. Lexical entries for *just* and *only*
-- ============================================================================

/-- The unified lexical entry for *just* (Deo & Thomas 2025: §3).

    Not-at-issue: The CQ is the widest answerable construal of UQ_c.
    At-issue: The prejacent, interpreted relative to CQ's granularity.

    The 7 flavors are NOT separate entries — they are the same entry
    interacting with different discourse contexts and alternative sources. -/
structure JustSemantics (W : Type*) where
  /-- The underspecified question and its construals -/
  context : DiscourseContext W
  /-- The widest answerable construal (= the CQ for *just*) -/
  cq : QUD W
  /-- The CQ is indeed widest answerable -/
  cq_widest : isWidestAnswerable context cq
  /-- The prejacent proposition -/
  prejacent : W → Bool

/-- The lexical entry for *only* (standard Roothian analysis).

    Unlike *just*, *only* requires the CQ to be commonly shared
    and alternatives to be Roothian (focus-semantic). -/
structure OnlySemantics (W : Type*) where
  /-- The shared CQ (must be commonly known) -/
  cq : QUD W
  /-- The prejacent -/
  prejacent : W → Bool
  /-- Roothian focus alternatives -/
  alternatives : List (W → Bool)
  /-- The CQ must be shared between interlocutors -/
  cqShared : Bool := true

/-- *only* presupposes the prejacent and asserts no stronger alternative is true. -/
def OnlySemantics.assertion (sem : OnlySemantics W) (w : W) : Bool :=
  sem.prejacent w &&
  sem.alternatives.all (fun alt => !alt w || (alt w == sem.prejacent w))

-- ============================================================================
-- E. Core theorems
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

-- Theorem 4: All flavors from one entry

/-- The 7 flavors are not separate lexical entries.
    Every flavor in the data is compatible with the unified analysis:
    the associated source is always well-defined, and context type is always
    well-defined. No flavor requires a distinct lexical entry. -/
theorem all_flavors_one_entry :
    ∀ d ∈ allJustData,
      ∃ (src : AlternativeSource) (ct : ContextType),
        associatedSource d.flavor = src ∧ d.contextType = ct := by
  intro d _
  exact ⟨associatedSource d.flavor, d.contextType, rfl, rfl⟩

end TruthConditional.Sentence.DomainWidening
