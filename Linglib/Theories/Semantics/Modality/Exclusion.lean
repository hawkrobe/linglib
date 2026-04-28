import Linglib.Core.Context.Tower
import Linglib.Core.Context.Shifts
import Linglib.Core.Context.Rich
import Linglib.Core.Modality.HistoricalAlternatives
import Linglib.Theories.Semantics.Tense.Counterfactual.Defs
import Linglib.Theories.Semantics.Mood.Basic
import Linglib.Theories.Semantics.Reference.Kaplan
import Linglib.Theories.Semantics.Tense.ConditionalShift

/-!
# Exclusion features and X/O-marking strategies

@cite{iatridou-2000} @cite{condoravdi-2002} @cite{deal-2020}
@cite{anderson-1951} @cite{schlenker-2004} @cite{von-fintel-iatridou-2023}

Framework primitives for the **Exclusion Feature** analysis of past
morphology (@cite{iatridou-2000}) and the **X-marking / O-marking**
typology of counterfactuality (@cite{von-fintel-iatridou-2023}).

This file provides the *framework primitives* — types, predicates, and
bridge theorems usable by any study of counterfactuals or
crosslinguistic conditional morphology. Paper-specific typologies and
empirical claims live in the corresponding `Studies/` files:

- `Phenomena/Conditionals/Studies/Iatridou2000.lean` —
  `IatridouPredType` / `CounterfactualType` / `classifyCounterfactual`
  (FLV/PresCF/PastCF taxonomy)
- `Phenomena/Conditionals/Studies/Mizuno2024.lean` —
  Anderson-conditional empirical observations (English X-marking,
  Japanese O-marking, FLV correlation)

## Core claims

Past morphology encodes **exclusion**:
- **Temporal**: T(topic) ≠ T(speaker)
- **Modal**: w(topic) ≠ w(speaker)

This maps onto the `ContextTower`'s `origin` / `innermost` distinction:
`ExclF dim tower` holds iff the relevant coordinate of `tower.innermost`
differs from that of `tower.origin`.

The **X-marking / O-marking** distinction (per
@cite{von-fintel-iatridou-2023}) is the typological label for whether
a language uses counterfactual morphology (X-marking, produces ExclF)
or some other strategy (O-marking, e.g., Japanese Historical Present)
to grammatically distinguish live from non-live possibilities.

## Bicontextual semantics

@cite{schlenker-2004} distinguishes the **Context of Thought** θ
(speech-act context, anchors temporal indexicals) from the **Context of
Utterance** v (can be shifted by HP). The `ContextTower` implements
this distinction: `tower.origin` = θ, `tower.innermost` = v. The
`origin_stable` theorem captures Schlenker's claim that θ-anchored
indexicals are unaffected by HP/CF shifts.
-/

namespace Semantics.Modality.Exclusion

open Core.Context (KContext ContextTower ContextShift RichContext
  hpShift xMarkingShift DomainExpanding temporalShift)
open Semantics.Tense.Counterfactual (PastMorphologyUse CounterfactualDistance)
open Core.Modality.HistoricalAlternatives (WorldHistory historicalBase)
open Semantics.Mood (subjShift)
open Semantics.Reference.Kaplan (opActually_access opActually_shift_invariant)
open Semantics.Tense.ConditionalShift (domainRestrictedConditional
  trivialConsequent nonTrivialConsequent
  trivial_domainRestricted expansion_resolves_triviality
  nontrivial_conditional_excludes)

-- ════════════════════════════════════════════════════════════════
-- § ExclF: The Exclusion Feature (@cite{iatridou-2000})
-- ════════════════════════════════════════════════════════════════

/-- The two dimensions along which past morphology can exclude.

@cite{iatridou-2000}'s key insight: past morphology has a single
semantic contribution (exclusion) that applies to different dimensions.
The temporal/modal ambiguity of "past" is not lexical ambiguity — it
is the same feature targeting different coordinates. -/
inductive ExclDimension where
  /-- Temporal: T(topic) ≠ T(speaker) -/
  | temporal
  /-- Modal: w(topic) ≠ w(speaker) -/
  | modal
  deriving DecidableEq, Repr

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*}

/-- The Exclusion Feature: past morphology signals that the topic
coordinate differs from the speaker coordinate on the given dimension.

This is a predicate over context towers: `ExclF dim tower` holds iff
the relevant coordinate of the innermost context (topic) differs from
the origin context (speaker). -/
def ExclF (dim : ExclDimension) (tower : ContextTower (KContext W E P T)) : Prop :=
  match dim with
  | .temporal => tower.innermost.time ≠ tower.origin.time
  | .modal    => tower.innermost.world ≠ tower.origin.world

/-- ExclF temporal unfolds to time inequality. -/
theorem exclF_temporal_iff (tower : ContextTower (KContext W E P T)) :
    ExclF .temporal tower ↔ tower.innermost.time ≠ tower.origin.time :=
  Iff.rfl

/-- ExclF modal unfolds to world inequality. -/
theorem exclF_modal_iff (tower : ContextTower (KContext W E P T)) :
    ExclF .modal tower ↔ tower.innermost.world ≠ tower.origin.world :=
  Iff.rfl

-- ════════════════════════════════════════════════════════════════
-- § ExclF–Deal Bridge
-- ════════════════════════════════════════════════════════════════

/-- Map ExclDimension to @cite{deal-2020}'s `PastMorphologyUse`.

This connects @cite{iatridou-2000}'s exclusion analysis to
@cite{deal-2020}'s tense typology: temporal exclusion corresponds to
temporal tense, modal exclusion corresponds to counterfactual tense. -/
def ExclDimension.toDealUse : ExclDimension → PastMorphologyUse
  | .temporal => .temporal
  | .modal    => .counterfactual

theorem exclF_temporal_is_deal_temporal :
    ExclDimension.toDealUse .temporal = .temporal := rfl

theorem exclF_modal_is_deal_cf :
    ExclDimension.toDealUse .modal = .counterfactual := rfl

-- ════════════════════════════════════════════════════════════════
-- § ExclF–Tower Bridge: Shifts produce ExclF
-- ════════════════════════════════════════════════════════════════

/-- `subjShift` changes world → produces modal ExclF.

When a subjunctive clause introduces a new world that differs from the
origin, the resulting tower has modal ExclF. This is the tower-level
formalization of @cite{iatridou-2000}'s claim that counterfactual
morphology signals world exclusion. -/
theorem subjShift_produces_modal_exclF (c : KContext W E P T) (w' : W) (t' : T)
    (h : w' ≠ c.world) :
    ExclF .modal ((ContextTower.root c).push (subjShift w' t')) :=
  h

/-- `temporalShift` changes time → produces temporal ExclF.

When an embedding shifts the evaluation time away from the speech time,
the resulting tower has temporal ExclF. This is ordinary temporal past. -/
theorem temporalShift_produces_temporal_exclF (c : KContext W E P T) (t' : T)
    (h : t' ≠ c.time) :
    ExclF .temporal ((ContextTower.root c).push (temporalShift t')) :=
  h

/-- Two shifts → both ExclFs (the PastCF configuration). -/
theorem two_shifts_two_exclFs (c : KContext W E P T) (w' : W) (t' t'' : T)
    (hw : w' ≠ c.world) (ht : t'' ≠ c.time) :
    let tower := ((ContextTower.root c).push (subjShift w' t')).push (temporalShift t'')
    ExclF .modal tower ∧ ExclF .temporal tower :=
  ⟨hw, ht⟩

-- ════════════════════════════════════════════════════════════════
-- § Root tower has no ExclF
-- ════════════════════════════════════════════════════════════════

theorem root_no_temporal_exclF (c : KContext W E P T) :
    ¬ ExclF .temporal (ContextTower.root c) :=
  fun h => h rfl

theorem root_no_modal_exclF (c : KContext W E P T) :
    ¬ ExclF .modal (ContextTower.root c) :=
  fun h => h rfl

-- ════════════════════════════════════════════════════════════════
-- § X-marking on RichContext (Kratzer ∗-revision bridge)
-- ════════════════════════════════════════════════════════════════

/-- X-marking shift produces modal ExclF on `RichContext` towers.

`xMarkingShift` (from `Core.Context.Rich`) changes both world and
time. When the counterfactual world differs from the origin, the
resulting tower has modal ExclF.

**Kratzer-level counterpart**: in @cite{kratzer-2012}'s modal
semantics, the same X-marking operation corresponds to ∗-revision of
the modal base (`Semantics.Modality.Kratzer.XMarking.IsStarRevision`):
the `expandedDomain` parameter here maps to the widened accessible
world set ∩f'(w) ⊇ ∩f(w). See @cite{ferreira-2023} for the full 2×2
square of necessities generated by X-marking on both modal base (Xf)
and ordering source (Xg). -/
theorem xMarking_produces_modal_exclF
    (rc : RichContext W E P T)
    (pastTime : T) (cfWorld : W) (expandedDomain : Set W)
    (h : cfWorld ≠ rc.base.world) :
    ((xMarkingShift (E := E) (P := P) pastTime cfWorld expandedDomain).apply rc
      ).base.world ≠ rc.base.world :=
  h

-- ════════════════════════════════════════════════════════════════
-- § X-marking / O-marking typology (@cite{von-fintel-iatridou-2023})
-- ════════════════════════════════════════════════════════════════

/-- The two crosslinguistic strategies for grammatically distinguishing
live from non-live possibilities (@cite{von-fintel-iatridou-2023}'s
typological label).

Used by @cite{mizuno-2024} to characterize how different languages
express Anderson conditionals: English uses X-marking (counterfactual
morphology), Japanese uses O-marking (Non-Past + Historical Present). -/
inductive MarkingStrategy where
  /-- X-marking: counterfactual morphology expands the domain from D
      to D⁺. "Actually" in the consequent recovers the actual world via
      Kaplanian origin access.
      English: "If Jones *had taken* arsenic, he *would have shown*
      exactly the symptoms he is *actually* showing." -/
  | xMarking
  /-- O-marking: Non-Past morphology triggers a perspectival shift
      analogous to the Historical Present (@cite{schlenker-2004}). The
      backward time shift expands the domain under branching time,
      avoiding triviality without counterfactual morphology. The actual
      world is directly accessible (no world shift, so no need for
      "actually").
      Japanese: "Jones-si-ga... nom-*eba*,... mise-*ru* (hazuda)." -/
  | oMarking
  deriving DecidableEq, Repr

/-- X-marking strategy uses counterfactual morphology; O-marking does
    not. The single primitive property of marking strategies; all
    others (`producesExclF`, `requiresActuallyOperator`) derive from
    it. -/
def MarkingStrategy.hasXMarking : MarkingStrategy → Bool
  | .xMarking => true
  | .oMarking => false

/-- X-marking produces ExclF; O-marking does not.

X-marking is counterfactual morphology: `subjShift` changes the
evaluation world, creating modal ExclF. O-marking leaves the tower at
the root, so no ExclF arises. Definitionally equal to `hasXMarking`. -/
abbrev MarkingStrategy.producesExclF (s : MarkingStrategy) : Bool :=
  s.hasXMarking

/-- X-marking requires "actually" to recover the actual world; O-marking
does not. When X-marking produces ExclF, the actual world is excluded
from the shifted evaluation; "actually" (Kaplanian origin access)
reaches back through the shift. With O-marking, the evaluation world
IS the actual world. Definitionally equal to `hasXMarking`. -/
abbrev MarkingStrategy.requiresActuallyOperator (s : MarkingStrategy) : Bool :=
  s.hasXMarking

/-- Map marking strategies to the `ExclDimension` they produce. -/
def MarkingStrategy.exclDimension : MarkingStrategy → Option ExclDimension
  | .xMarking => some .modal
  | .oMarking => none

/-- Map marking strategies to @cite{deal-2020}'s `PastMorphologyUse`. -/
def MarkingStrategy.toDealUse : MarkingStrategy → PastMorphologyUse
  | .xMarking => .counterfactual
  | .oMarking => .temporal

theorem xMarking_exclDimension :
    MarkingStrategy.xMarking.exclDimension = some .modal := rfl

theorem oMarking_no_exclDimension :
    MarkingStrategy.oMarking.exclDimension = none := rfl

theorem xMarking_is_deal_counterfactual :
    MarkingStrategy.xMarking.toDealUse = .counterfactual := rfl

theorem oMarking_is_deal_temporal :
    MarkingStrategy.oMarking.toDealUse = .temporal := rfl

theorem xMarking_excl_deal_consistent :
    (MarkingStrategy.xMarking.exclDimension.map ExclDimension.toDealUse) =
    some MarkingStrategy.xMarking.toDealUse := rfl

-- ════════════════════════════════════════════════════════════════
-- § Tower-level X/O-marking theorems
-- ════════════════════════════════════════════════════════════════

/-- X-marking produces modal ExclF: subjunctive shift changes the
world, creating world exclusion. Wraps `subjShift_produces_modal_exclF`. -/
theorem xMarking_produces_exclF (c : KContext W E P T) (w' : W) (t' : T)
    (h : w' ≠ c.world) :
    ExclF .modal ((ContextTower.root c).push (subjShift w' t')) :=
  subjShift_produces_modal_exclF c w' t' h

/-- "Actually" recovers the origin world even after a tower shift.

In an X-marked Anderson conditional, the CF morphology pushes the
tower (shifting the evaluation world). But "actually" — being a
Kaplanian indexical with `depth = .origin` — resolves to the
speech-act world regardless. Wraps `opActually_shift_invariant`. -/
theorem actually_recovers_origin_after_shift
    (t : ContextTower (KContext W E P T)) (σ : ContextShift (KContext W E P T)) :
    opActually_access.resolve (t.push σ) = opActually_access.resolve t :=
  opActually_shift_invariant t σ

/-- O-marking has no modal ExclF: without CF morphology, the tower
stays at the root. Wraps `root_no_modal_exclF`. -/
theorem oMarking_no_exclF (c : KContext W E P T) :
    ¬ ExclF .modal (ContextTower.root c) :=
  root_no_modal_exclF c

-- ════════════════════════════════════════════════════════════════
-- § Domain expansion (the Anderson-conditional triviality fix)
-- ════════════════════════════════════════════════════════════════

/-- Both X-marking and O-marking avoid the triviality problem by
expanding the domain. General pattern: if a domain expansion produces
a world where the consequent fails, the conditional is non-trivial.

- X-marking achieves this via `xMarkingShift` (CF morphology → D⁺)
- O-marking achieves this via `hpShift` (HP → backward time → D⁺)

Wraps `ConditionalShift.expansion_resolves_triviality`. -/
theorem domain_expansion_avoids_triviality
    (smallDomain expandedDomain : Set W)
    (consequent : W → Prop)
    (h_subset : smallDomain ⊆ expandedDomain)
    (h_trivial : trivialConsequent smallDomain consequent)
    (w : W) (hw : w ∈ expandedDomain) (hw_fails : ¬ consequent w) :
    nonTrivialConsequent expandedDomain consequent :=
  expansion_resolves_triviality smallDomain expandedDomain consequent
    h_subset h_trivial w hw hw_fails

/-- End-to-end O-marking domain expansion: backwards-closed history +
backward time shift → the HP-shifted domain contains the original.

Connects three layers:
1. `BranchingTime.WorldHistory.backwardsClosed` (semantic property)
2. `ConditionalShift.history_monotone_set` (set-level monotonicity)
3. `hpShift` installs the expanded domain -/
theorem oMarking_hpShift_expanding
    {W : Type*} {T : Type*} [Preorder T]
    (history : WorldHistory W T) (h_bc : history.backwardsClosed)
    (w₀ : W) (t₀ t' : T) (h_earlier : t' ≤ t₀)
    (D : Set W) (h_domain : D ⊆ history ⟨w₀, t₀⟩) :
    D ⊆ history ⟨w₀, t'⟩ :=
  Set.Subset.trans h_domain
    (Semantics.Tense.ConditionalShift.history_monotone_set
      history h_bc ⟨w₀, t₀⟩ t' h_earlier)

/-- The O-marking triviality problem: without domain expansion, the
Anderson conditional is vacuously true. The `domainRestrictedConditional`
over the non-expanded domain `D` is trivially satisfied because the
consequent (an observed fact) holds at every world in `D`. -/
theorem oMarking_trivial
    (domain : Set W) (antecedent consequent : W → Prop)
    (h_trivial : trivialConsequent domain consequent) :
    domainRestrictedConditional domain antecedent consequent :=
  trivial_domainRestricted domain antecedent consequent h_trivial

/-- The X/O-marking payoff: when domain expansion makes the consequent
non-trivial, the antecedent of a true conditional must exclude at
least one world in `D⁺`. The Anderson conditional is informative —
the antecedent restriction partitions `D⁺` into consequent-satisfying
worlds (selected by the conditional) and consequent-failing worlds
(excluded by the antecedent). -/
theorem expanded_conditional_informative
    (expandedDomain : Set W) (antecedent consequent : W → Prop)
    (h_nontrivial : nonTrivialConsequent expandedDomain consequent)
    (h_cond : domainRestrictedConditional expandedDomain antecedent consequent) :
    ∃ w ∈ expandedDomain, ¬ antecedent w :=
  nontrivial_conditional_excludes expandedDomain antecedent consequent
    h_nontrivial h_cond

-- ════════════════════════════════════════════════════════════════
-- § Bicontextual semantics (@cite{schlenker-2004})
-- ════════════════════════════════════════════════════════════════

/-- In O-marking (HP) strategy, temporal indexicals still evaluate
against the speech-act context (θ = origin), not the shifted context
(v = innermost).

This explains why Japanese *sakuya* 'last night' in the antecedent of
an HP-shifted O-marked conditional evaluates against the utterance
time, paralleling the behavior of *seventy-eight years ago* in
@cite{schlenker-2004}'s HP example. -/
theorem oMarking_indexicals_at_origin
    (ap : Core.Context.AccessPattern (KContext W E P T) W)
    (hd : ap.depth = .origin)
    (t : ContextTower (KContext W E P T)) (σ : ContextShift (KContext W E P T)) :
    ap.resolve (t.push σ) = ap.resolve t :=
  Core.Context.AccessPattern.origin_stable ap hd t σ

end Semantics.Modality.Exclusion
