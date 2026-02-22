import Linglib.Core.Context.Tower
import Linglib.Core.Context.Shifts
import Linglib.Core.Context.Rich
import Linglib.Theories.Semantics.Tense.BranchingTime
import Linglib.Theories.Semantics.Tense.Deal
import Linglib.Theories.Semantics.Mood.Basic
import Linglib.Theories.Semantics.Lexical.Verb.Aspect

/-!
# Iatridou (2000): The Grammatical Ingredients of Counterfactuality
@cite{iatridou-2000}

Formalizes the core contribution of Iatridou (2000): the **Exclusion Feature**
(ExclF), a single semantic predicate that unifies temporal past and
counterfactual past. Past morphology signals exclusion of the topic situation's
coordinate from the speaker's coordinate — on the temporal dimension for genuine
past, on the modal dimension for counterfactuals.

## Core Claim

Past morphology encodes exclusion:
- **Temporal**: T(topic) ≠ T(speaker)
- **Modal**: w(topic) ≠ w(speaker)

This maps directly onto the ContextTower's `origin` / `innermost` distinction:
`ExclF dim tower` holds iff the relevant coordinate of `tower.innermost` differs
from that of `tower.origin`.

## Counterfactual Typology

Three counterfactual types arise from the number of ExclFs and predicate type:
- **FLV** (Future Less Vivid): 1 modal ExclF + telic predicate
- **PresCF** (Present Counterfactual): 1 modal ExclF + ILP/stative predicate
- **PastCF** (Past Counterfactual): 2 ExclFs (modal + temporal)

## Tower Integration

ExclF stress-tests the tower because:
- `ExclF` is literally `origin ≠ innermost` on a coordinate
- `subjShift` produces modal ExclF when `newWorld ≠ origin.world`
- `temporalShift` produces temporal ExclF when `newTime ≠ origin.time`
- PastCF requires tower depth ≥ 2 (two mood-labeled shifts)

## References

- Iatridou, S. (2000). The grammatical ingredients of counterfactuality.
  *Linguistic Inquiry* 31(2): 231–270.
- Deal, A. R. (2020). Counterfactuals and the Upper Limit Constraint.
- Condoravdi, M. (2002). Temporal interpretation of modals.
-/

namespace Semantics.Conditionals.Iatridou

open Core.Context (KContext ContextTower ContextShift temporalShift)
open Semantics.Tense.Deal (PastMorphologyUse CounterfactualDistance)
open Semantics.Tense.BranchingTime (WorldHistory historicalBase)
open Semantics.Mood (subjShift)
open Semantics.Lexical.Verb.Aspect (VendlerClass)

-- ════════════════════════════════════════════════════════════════
-- § ExclF: The Exclusion Feature
-- ════════════════════════════════════════════════════════════════

/-- The two dimensions along which past morphology can exclude.

Iatridou's key insight: past morphology has a single semantic contribution
(exclusion) that applies to different dimensions. The temporal/modal ambiguity
of "past" is not lexical ambiguity — it is the same feature targeting
different coordinates. -/
inductive ExclDimension where
  /-- Temporal: T(topic) ≠ T(speaker) -/
  | temporal
  /-- Modal: w(topic) ≠ w(speaker) -/
  | modal
  deriving DecidableEq, Repr, BEq

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*}

/-- The Exclusion Feature: past morphology signals that the topic coordinate
differs from the speaker coordinate on the given dimension.

This is a predicate over context towers: `ExclF dim tower` holds iff the
relevant coordinate of the innermost context (topic) differs from the
origin context (speaker). -/
def ExclF (dim : ExclDimension) (tower : ContextTower (KContext W E P T)) : Prop :=
  match dim with
  | .temporal => tower.innermost.time ≠ tower.origin.time
  | .modal    => tower.innermost.world ≠ tower.origin.world

-- ════════════════════════════════════════════════════════════════
-- § ExclF Definitional Unfolds
-- ════════════════════════════════════════════════════════════════

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

/-- Map ExclDimension to Deal's PastMorphologyUse.

This connects Iatridou's exclusion analysis to Deal's tense typology:
temporal exclusion corresponds to temporal tense, modal exclusion
corresponds to counterfactual tense. -/
def ExclDimension.toDealUse : ExclDimension → PastMorphologyUse
  | .temporal => .temporal
  | .modal    => .counterfactual

/-- Temporal ExclF maps to Deal's temporal use. -/
theorem exclF_temporal_is_deal_temporal :
    ExclDimension.toDealUse .temporal = .temporal := rfl

/-- Modal ExclF maps to Deal's counterfactual use. -/
theorem exclF_modal_is_deal_cf :
    ExclDimension.toDealUse .modal = .counterfactual := rfl

-- ════════════════════════════════════════════════════════════════
-- § ExclF–Tower Bridge: Shifts Produce ExclF
-- ════════════════════════════════════════════════════════════════

/-- `subjShift` changes world → produces modal ExclF.

When a subjunctive clause introduces a new world that differs from the
origin, the resulting tower has modal ExclF. This is the tower-level
formalization of Iatridou's claim that counterfactual morphology signals
world exclusion. -/
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

/-- Two shifts → both ExclFs.

PastCF requires two layers of past morphology: one modal ExclF (from
subjunctive/counterfactual world shift) and one temporal ExclF (from
the additional past morpheme). This produces a tower of depth ≥ 2 with
both ExclFs active. -/
theorem two_shifts_two_exclFs (c : KContext W E P T) (w' : W) (t' t'' : T)
    (hw : w' ≠ c.world) (ht : t'' ≠ c.time) :
    let tower := ((ContextTower.root c).push (subjShift w' t')).push (temporalShift t'')
    ExclF .modal tower ∧ ExclF .temporal tower :=
  ⟨hw, ht⟩

-- ════════════════════════════════════════════════════════════════
-- § Predicate-Type Gating
-- ════════════════════════════════════════════════════════════════

/-- Iatridou's predicate classification for counterfactual gating.

The distinction between FLV and PresCF (both with 1 modal ExclF) depends
on the predicate type:
- ILPs and statives yield PresCF ("If he knew French, ...")
- Telic predicates yield FLV ("If he were to leave tomorrow, ...") -/
inductive IatridouPredType where
  /-- Individual-Level Predicate: "be tall", "know French" -/
  | ilp
  /-- Stage-Level stative: "be sick", "be available" -/
  | stative
  /-- Telic predicate: "arrive", "build a house" -/
  | telic
  deriving DecidableEq, Repr, BEq

/-- Map Vendler classes to Iatridou's predicate classification.

States and activities map to stative (both are atelic/non-dynamic enough
for PresCF interpretation). Achievements and accomplishments map to telic
(both have endpoints, triggering FLV interpretation). -/
def VendlerClass.toIatridou : VendlerClass → IatridouPredType
  | .state | .activity => .stative
  | .achievement | .accomplishment => .telic

-- ════════════════════════════════════════════════════════════════
-- § Three Conditional Types
-- ════════════════════════════════════════════════════════════════

/-- Iatridou's three counterfactual conditional types, distinguished by
the number of ExclFs and predicate type. -/
inductive CounterfactualType where
  /-- Future Less Vivid: 1 ExclF modal + telic predicate -/
  | flv
  /-- Present Counterfactual: 1 ExclF modal + ILP/stative -/
  | presCF
  /-- Past Counterfactual: 2 ExclFs (modal + temporal) -/
  | pastCF
  deriving DecidableEq, Repr, BEq

/-- The number of ExclFs required for each counterfactual type.

FLV and PresCF require 1 ExclF (modal only); PastCF requires 2
(modal + temporal). This corresponds to the number of past morpheme
layers observed cross-linguistically. -/
def CounterfactualType.exclFCount : CounterfactualType → Nat
  | .flv | .presCF => 1
  | .pastCF => 2

/-- Classify a counterfactual from its ExclF configuration and predicate type.

Returns `none` if there is no modal ExclF (a non-counterfactual sentence). -/
def classifyCounterfactual (modalExcl temporalExcl : Bool)
    (predType : IatridouPredType) : Option CounterfactualType :=
  match modalExcl, temporalExcl with
  | true, true => some .pastCF
  | true, false => match predType with
    | .telic => some .flv
    | .ilp | .stative => some .presCF
  | false, _ => none

-- ════════════════════════════════════════════════════════════════
-- § Gating Theorems
-- ════════════════════════════════════════════════════════════════

/-- Telic predicate + 1 modal ExclF = FLV. -/
theorem telic_one_exclF_is_flv :
    classifyCounterfactual true false .telic = some .flv := rfl

/-- ILP + 1 modal ExclF = PresCF. -/
theorem ilp_one_exclF_is_presCF :
    classifyCounterfactual true false .ilp = some .presCF := rfl

/-- Stative + 1 modal ExclF = PresCF. -/
theorem stative_one_exclF_is_presCF :
    classifyCounterfactual true false .stative = some .presCF := rfl

/-- Two ExclFs = PastCF regardless of predicate type. -/
theorem two_exclFs_is_pastCF (pred : IatridouPredType) :
    classifyCounterfactual true true pred = some .pastCF := by
  cases pred <;> rfl

/-- No modal ExclF = not a counterfactual. -/
theorem no_modal_not_cf (temporalExcl : Bool) (pred : IatridouPredType) :
    classifyCounterfactual false temporalExcl pred = none := by
  cases temporalExcl <;> rfl

-- ════════════════════════════════════════════════════════════════
-- § Root Tower Has No ExclF
-- ════════════════════════════════════════════════════════════════

/-- A root tower (no shifts) has no temporal ExclF. -/
theorem root_no_temporal_exclF (c : KContext W E P T) :
    ¬ ExclF .temporal (ContextTower.root c) :=
  fun h => h rfl

/-- A root tower (no shifts) has no modal ExclF. -/
theorem root_no_modal_exclF (c : KContext W E P T) :
    ¬ ExclF .modal (ContextTower.root c) :=
  fun h => h rfl

-- ════════════════════════════════════════════════════════════════
-- § Fake Imp / Subjunctive Generalization
-- ════════════════════════════════════════════════════════════════

/-- Iatridou's subjunctive generalization (42): "A CF can contain a
subjunctive morpheme only if that subjunctive morpheme has a past tense
form" (Iatridou 2000, p.247).

Strictly, the paper states this as a one-directional conditional
(requires → has). We encode the biconditional because all languages
in our data satisfy both directions: English and Greek lack past
subjunctive and don't require subjunctive in CFs; Italian has past
subjunctive and requires it. -/
def iatridouSubjGeneralization (hasPastSubj requiresSubj : Bool) : Prop :=
  requiresSubj = hasPastSubj

-- ════════════════════════════════════════════════════════════════
-- § XMarking Bridge
-- ════════════════════════════════════════════════════════════════

/-- X-marking shift produces modal ExclF on RichContext towers.

The `xMarkingShift` (from Rich.lean) changes both world and time. When
the counterfactual world differs from the origin, the resulting tower
has modal ExclF. -/
theorem xMarking_produces_modal_exclF
    (rc : Core.Context.RichContext W E P T)
    (pastTime : T) (cfWorld : W) (expandedDomain : Set W)
    (h : cfWorld ≠ rc.base.world) :
    ((Core.Context.xMarkingShift (E := E) (P := P) pastTime cfWorld expandedDomain).apply rc
      ).base.world ≠ rc.base.world :=
  h

-- ════════════════════════════════════════════════════════════════
-- § Depth Counting
-- ════════════════════════════════════════════════════════════════

/-- PastCF tower has depth 2.

A tower built with two mood shifts (for PastCF) has depth 2,
corresponding to the two past morpheme layers observed cross-linguistically. -/
theorem pastCF_tower_depth (c : KContext W E P T) (w' : W) (t' t'' : T) :
    (((ContextTower.root c).push (subjShift w' t')).push (temporalShift t'')
      ).depth = 2 := by
  simp [ContextTower.push, ContextTower.depth, ContextTower.root]

end Semantics.Conditionals.Iatridou
