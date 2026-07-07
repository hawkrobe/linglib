/-
# Domain Widening: *just* as addressing the widest answerable question

Formalizes [deo-thomas-2025]: *just* signals that the speaker addresses the
**widest answerable construal** of an underspecified question (UQ). The 9 flavors
arise from how the widest construal is determined by Quality and Relevance.

## Core claim

*Just* has a SINGLE lexical entry. The apparent polysemy follows from
the interaction of domain widening with different alternative sources and Gricean
maxim failures. *Only* shares the exhaustification semantics but requires Roothian
alternatives, explaining why it substitutes in only 2 of the 9 flavors.

## Main declarations

- `JustFlavor`, `ContextType`: the paper's §2 taxonomy
- `flavorOf`, `contextTypeOf`: adapters over `Data/Examples/DeoThomas2025.json`
- `only_substitutes_iff_roothian` and friends: the §2 generalizations,
  quantified over the example rows
- `justFlavorFromConstruction`: the [thomas-deo-2020] construction → flavor
  bridge
- `refinement_implies_wider`, `finer_granularity_implies_wider`: finer
  granularity yields wider questions (§3.1.2–3.2, Figure 1)

-/

import Linglib.Semantics.Questions.Partition.QUD
import Linglib.Semantics.Questions.PrecisionProjection
import Linglib.Semantics.Questions.Basic
import Linglib.Semantics.Questions.Granularity
import Linglib.Semantics.Mood.PartitionAsInquiry
import Linglib.Semantics.Degree.Granularity
import Linglib.Semantics.Degree.Defs
import Linglib.Data.Examples.DeoThomas2025
import Linglib.Studies.ThomasDeo2020

namespace DeoThomas2025

open Data.Examples (LinguisticExample)

-- ============================================================================
-- A. The §2 Taxonomy
-- ============================================================================

/-- The interpretive flavors of *just* ([deo-thomas-2025]: §2).
    Nine constructors covering the paper's 7 major categories, with
    precisifying split into equality/proximity (§2.3.1-2) and complement
    exclusion separated from rank order (§2.1). -/
inductive JustFlavor where
  | complementExclusion  -- "She just went to Spain and Portugal" → nowhere else
  | rankOrder            -- "She is just an intern" → nothing higher on scale
  | emphatic             -- "The food was just amazing!" → exceeds expectations
  | precisifyingEquality -- "The tank is just full" → exactly (= paraphrase)
  | precisifyingProximity -- "Fafen is just older than Siri" → barely (≈ slightly)
  | minimalSufficiency   -- "Just a 3.5 GPA is sufficient" → nothing less needed
  | unexplanatory        -- "The lamp just broke" → no identifiable cause
  | unelaboratory        -- "Fido is just a dog" → no further elaboration needed
  | counterexpectational -- "She just ate the communion wafer!" → norm violation
  deriving Repr, DecidableEq

/-- Why the widest answerable construal is optimal at context
    ([deo-thomas-2025] (37)). -/
inductive ContextType where
  | answerable  -- (37a): widest construal is answerable (Quality + Relevance)
  | qualityFail -- (37b): wider construals fail Quality (speaker lacks evidence)
  | relevanceFail -- (37c): wider construals fail Relevance (not discourse-relevant)
  deriving Repr, DecidableEq

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
-- B. Row Adapters (Data/Examples/DeoThomas2025.json)
-- ============================================================================

/-- A row's `flavor` feature as a `JustFlavor`. -/
def flavorOf (row : LinguisticExample) : Option JustFlavor :=
  match row.feature? "flavor" with
  | some "complementExclusion"   => some .complementExclusion
  | some "rankOrder"             => some .rankOrder
  | some "emphatic"              => some .emphatic
  | some "precisifyingEquality"  => some .precisifyingEquality
  | some "precisifyingProximity" => some .precisifyingProximity
  | some "minimalSufficiency"    => some .minimalSufficiency
  | some "unexplanatory"         => some .unexplanatory
  | some "unelaboratory"         => some .unelaboratory
  | some "counterexpectational"  => some .counterexpectational
  | _ => none

/-- A row's `context_type` feature as a `ContextType`. -/
def contextTypeOf (row : LinguisticExample) : Option ContextType :=
  match row.feature? "context_type" with
  | some "answerable"    => some .answerable
  | some "qualityFail"   => some .qualityFail
  | some "relevanceFail" => some .relevanceFail
  | _ => none

/-- Whether the row's `#only` substitution test succeeds. -/
def onlyOkOf (row : LinguisticExample) : Bool :=
  row.feature? "only_ok" == some "true"

-- ============================================================================
-- C. Discourse Context
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

/-- OPT_c(Q) ([deo-thomas-2025] (35)): the optimal question in a set
    of construals.

    `q` is the widest answerable construal: it is answerable, it is in the
    construal set, and no strictly wider answerable construal exists.

    Width is measured by `Question.widerThan` ((32)), the paper's comparison
    of question inquisitivity — explicitly weaker than G&S question entailment
    (fn. 20), because granularity-based construals generally cannot be ordered
    by entailment strength. -/
def isWidestAnswerable (ctx : DiscourseContext W) (q : Question W) : Prop :=
  q ∈ ctx.construals ∧
  answerable ctx q = true ∧
  ∀ q' ∈ ctx.construals, answerable ctx q' = true → ¬ q'.widerThan q

/-- Classify a discourse context by WHY the widest answerable construal
    is optimal ([deo-thomas-2025] (37)).

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
-- D. The §2 Generalizations over the Example Rows
-- ============================================================================

/-- *Only* can substitute for *just* exactly in the complement-exclusion
    and rank-order uses. -/
theorem only_substitutes_iff_exclusive :
    ∀ row ∈ Examples.all,
      onlyOkOf row = true ↔
        (flavorOf row = some .complementExclusion ∨
         flavorOf row = some .rankOrder) := by
  decide

/-- *Only* can replace *just* exactly when the alternatives are Roothian. -/
theorem only_substitutes_iff_roothian :
    ∀ row ∈ Examples.all,
      onlyOkOf row = true ↔
        (flavorOf row).map associatedSource = some .roothian := by
  decide

/-- Unexplanatory uses arise when wider construals fail Quality (37b). -/
theorem unexplanatory_is_quality_fail :
    ∀ row ∈ Examples.all,
      flavorOf row = some .unexplanatory →
        contextTypeOf row = some .qualityFail := by
  decide

/-- Unelaboratory uses arise when wider construals fail Relevance (37c). -/
theorem unelaboratory_is_relevance_fail :
    ∀ row ∈ Examples.all,
      flavorOf row = some .unelaboratory →
        contextTypeOf row = some .relevanceFail := by
  decide

/-- All other uses — complement exclusion, rank order, emphatic,
    precisifying, minimal sufficiency, counterexpectational — arise when
    the widest construal IS answerable (37a). -/
theorem standard_uses_are_answerable :
    ∀ row ∈ Examples.all,
      contextTypeOf row = some .answerable ↔
        (flavorOf row ≠ some .unexplanatory ∧
         flavorOf row ≠ some .unelaboratory) := by
  decide

/-- Quality-failure contexts yield only causal-alternative flavors. -/
theorem quality_fail_implies_causal :
    ∀ row ∈ Examples.all,
      contextTypeOf row = some .qualityFail →
        (flavorOf row).map associatedSource = some .causal := by
  decide

/-- Relevance-failure contexts yield only elaboration-alternative flavors. -/
theorem relevance_fail_implies_elaboration :
    ∀ row ∈ Examples.all,
      contextTypeOf row = some .relevanceFail →
        (flavorOf row).map associatedSource = some .elaboration := by
  decide

/-- *only* is felicitous only with Roothian alternatives (shared CQ).
    *just* is felicitous regardless of alternative source.
    This is WHY they diverge: *only* exhaustifies over shared alternatives,
    *just* widens the question. -/
theorem only_requires_shared_cq :
    ∀ row ∈ Examples.all,
      onlyOkOf row = true →
        (flavorOf row).map associatedSource = some .roothian :=
  fun row hrow h => (only_substitutes_iff_roothian row hrow).mp h

/-- All 9 `JustFlavor` constructors are attested in the example rows. -/
theorem all_flavors_attested :
    ∀ f : JustFlavor, Examples.all.any (flavorOf · == some f) = true := by
  intro f
  cases f <;> decide

-- ============================================================================
-- E. Construction → Flavor Bridge ([thomas-deo-2020])
-- ============================================================================

open Degree (AdjectivalConstruction)

/-- Derive *just* flavor from adjectival construction type.
    [thomas-deo-2020] predict:
    - comparative + just → precisifying proximity (barely)
    - equative + just → precisifying equality (exactly) -/
def justFlavorFromConstruction : AdjectivalConstruction → JustFlavor
  | .comparative => .precisifyingProximity
  | .equative => .precisifyingEquality
  | _ => .complementExclusion

/-- "Fafen is just older than Siri" — comparative + just = proximity. -/
theorem comparative_yields_proximity :
    flavorOf Examples.precisifying_prox_older =
      some (justFlavorFromConstruction .comparative) := by
  decide

/-- Equative + just = equality ("just as tall as" ≈ "exactly as tall as").
    Note: `precisifying_eq_full` ("just full") achieves equality via a
    closed-scale endpoint standard, not via equative morphology. The
    shared flavor (`.precisifyingEquality`) reflects parallel pragmatic
    effects through different compositional routes. -/
theorem equative_yields_equality :
    flavorOf Examples.precisifying_eq_full =
      some (justFlavorFromConstruction .equative) := by
  decide

/-- Every equative datum of [thomas-deo-2020] §3 receives the flavor of
    the 2025 corpus's equality row. -/
theorem equative_data_match_corpus :
    ∀ d ∈ ThomasDeo2020.allGranularityData,
      d.construction = .equative →
        some (justFlavorFromConstruction d.construction) =
          flavorOf Examples.precisifying_eq_full := by
  decide

/-- Every comparative datum of [thomas-deo-2020] §3 receives the flavor of
    the 2025 corpus's proximity row. -/
theorem comparative_data_match_corpus :
    ∀ d ∈ ThomasDeo2020.allGranularityData,
      d.construction = .comparative →
        some (justFlavorFromConstruction d.construction) =
          flavorOf Examples.precisifying_prox_older := by
  decide

-- ============================================================================
-- F. WXDY bridge ([kay-fillmore-1999])
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
-- G. Granularity-Width Bridge (Figure 1)
-- ============================================================================

/-! ### Partition refinement implies question width

The paper's central formal insight: finer granularity produces wider questions.
At the partition level, "finer" is `QUD.refines` (every fine cell ⊆ some coarse
cell), equivalently `q.toSetoid ≤ q'.toSetoid` in mathlib's `Setoid` lattice.
At the issue level, "wider" is `Question.widerThan` ([deo-thomas-2025]
(32): same `info`, no coarse answer ⊊ fine answer, some fine answer ⊊ coarse
answer). The bridge: `toIssue := Question.fromSetoid ∘ QUD.toSetoid`
preserves this relationship.

The proof is an order-theoretic one-liner over `Setoid`: every alternative
of `Question.fromSetoid r` is either `∅` or an equivalence class of `r`
(`alt_fromSetoid_subset_classes`), and the q-class of `w₀` is contained in
the q'-class of `w₀` by refinement, with `v₀` witnessing strict containment.
This replaces a 100-line Bool/List proof that managed indices into
`worlds : List W` and case-split on `properlyContains`. -/

/-- A `QUD` partitions a meaning space via an equivalence relation; via
    `QUD.toSetoid` and `Question.fromSetoid`, every QUD induces an
    inquisitive content whose alternatives are exactly the QUD's
    equivalence classes. The bridge is one-way: not every `Question`
    arises from a `QUD` (mention-some, intermediate-exhaustive, and
    conditional-question alternatives are non-disjoint or non-exhaustive
    and so are not representable as the cells of any equivalence
    relation — [theiler-etal-2018]). -/
def toIssue {W : Type*} (q : QUD W) : Question W :=
  Question.fromSetoid q.toSetoid

/-- Strict partition refinement implies issue width.

    If `q` (strictly) refines `q'` (`q` is the finer partition), then
    `toIssue q` is wider than `toIssue q'` as `Question`s.

    The strictness witnesses `w₀, v₀ : W` share a coarse cell
    (`q'.r w₀ v₀`) but not a fine cell
    (`¬ q.r w₀ v₀`); they witness condition (c).

    The proof establishes the three conditions of `Question.widerThan`:
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
    (hCoarse : q'.r w₀ v₀)
    (hFine : ¬ q.r w₀ v₀) :
    (toIssue q).widerThan (toIssue q') := by
  -- Refinement reads as `q.toSetoid ≤ q'.toSetoid` in mathlib's lattice
  have hle : ∀ {x y : W}, q.toSetoid x y → q'.toSetoid x y :=
    fun {x y} hxy => QUD.r_of_sameAnswer (hRefines x y (QUD.sameAnswer_of_r hxy))
  -- The q-class and q'-class of w₀
  let C₁ : Set W := {x | q.toSetoid x w₀}
  let C₂ : Set W := {x | q'.toSetoid x w₀}
  have hC₁_class : C₁ ∈ q.toSetoid.classes := Setoid.mem_classes q.toSetoid w₀
  have hC₂_class : C₂ ∈ q'.toSetoid.classes := Setoid.mem_classes q'.toSetoid w₀
  have hC₁_alt : C₁ ∈ Question.alt (Question.fromSetoid q.toSetoid) :=
    Question.class_mem_alt_fromSetoid _ hC₁_class
  have hC₂_alt : C₂ ∈ Question.alt (Question.fromSetoid q'.toSetoid) :=
    Question.class_mem_alt_fromSetoid _ hC₂_class
  refine ⟨?_, ?_, ?_⟩
  -- (a) Same info: both reduce to Set.univ
  · simp only [toIssue, Question.info_fromSetoid]
  -- (b) No q'-alternative properly contained in any q-alternative
  · intro p₂ hp₂ p₁ hp₁ hssub
    rcases Question.alt_fromSetoid_subset_classes _ hp₂ with hp₂_empty | hp₂_class
    · -- p₂ = ∅ but the q'-class of w₀ contains w₀, so ∅ ∉ alt — contradiction
      have hC₂_props : C₂ ∈ (Question.fromSetoid q'.toSetoid).props :=
        Or.inr ⟨C₂, hC₂_class, subset_rfl⟩
      have hp_sub : p₂ ⊆ C₂ := by rw [hp₂_empty]; exact Set.empty_subset _
      have heq : p₂ = C₂ := hp₂.2 C₂ hC₂_props hp_sub
      have hw₀_in : w₀ ∈ p₂ := by rw [heq]; exact Setoid.refl' q'.toSetoid w₀
      rw [hp₂_empty] at hw₀_in
      exact hw₀_in.elim
    · rcases Question.alt_fromSetoid_subset_classes _ hp₁ with hp₁_empty | hp₁_class
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
        exact Setoid.symm' q'.toSetoid hCoarse
      have hv₀_C₁ : v₀ ∈ C₁ := hCsub hv₀_C₂
      -- hv₀_C₁ : q.toSetoid v₀ w₀, want: q.r w₀ v₀
      exact hFine (q.iseqv.symm hv₀_C₁)

-- ============================================================================
-- H. Granularity–Question Composition (§3.1.2 + §3.2)
-- ============================================================================

/-! ### The full chain: finer granularity → wider question

Composes the two independently proved steps:
1. `finer_granularity_refines` (from `Degree.Granularity`):
   if ε₁ ∣ ε₂, the ε₁-partition refines the ε₂-partition
2. `refinement_implies_wider` (proved above):
   strict partition refinement → issue width

This is the formal content of the lexical entry (36): *just* selects
the widest answerable construal, which — when alternatives vary by
granularity — is the finest one the speaker can answer. -/

open Degree.Granularity (granQUD finer_granularity_refines)

/-- The complete granularity–width chain ([deo-thomas-2025] §3.1.2–3.2).

    If ε₁ divides ε₂ (finer grain) and there exist worlds that share a
    coarse cell but not a fine cell, then the fine-grained question is
    strictly wider than the coarse-grained question.

    This is the general version of Figure 1: any uniform-grain-width
    scale satisfies the width relation when grain widths are divisible. -/
theorem finer_granularity_implies_wider (n ε₁ ε₂ : Nat)
    (hdvd : ε₁ ∣ ε₂)
    (w₀ v₀ : Fin n)
    (hCoarse : (granQUD n ε₂).r w₀ v₀)
    (hFine : ¬ (granQUD n ε₁).r w₀ v₀) :
    (toIssue (granQUD n ε₁)).widerThan (toIssue (granQUD n ε₂)) :=
  refinement_implies_wider _ _
    (finer_granularity_refines n ε₁ ε₂ hdvd)
    w₀ v₀ hCoarse hFine

-- ============================================================================
-- I. Concrete Verification: Figure 1
-- ============================================================================

/-- The 8-point age scale from Figure 1 ([deo-thomas-2025]). -/
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
