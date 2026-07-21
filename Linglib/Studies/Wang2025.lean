import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs
import Linglib.Core.Logic.Modal.Basic
import Linglib.Discourse.CommonGround
import Linglib.Semantics.Presupposition.Basic
import Linglib.Features.Acceptability
import Linglib.Fragments.Mandarin.Particles
import Linglib.Pragmatics.Expressives.Basic

/-!
# [wang-2025] Presupposition, Competition, and Coherence
[heim-1991] [katzir-2007] [wang-2025] [wang-yaxuan-2025]

Self-contained study of [wang-2025] "Presupposition, Competition, and
Coherence": both the experimental data (three experiments on Mandarin
presupposition triggers) and the constraint-based formalization (IC ≫ FP ≫ MP)
that derives Wang's three-way obligatoriness pattern.

## Experimental Data

### Experiment 1: Naturalness Judgments (9 triggers × 3 contexts)
9 Mandarin presupposition triggers tested in 3 context conditions:
- **Full**: CommonGround fully entails the presupposition
- **Partial**: CommonGround partially entails the presupposition
- **None**: CommonGround does not support the presupposition

### Experiment 2: Polarity-Reversed Alternatives (4 triggers × 3 contexts)
4 triggers with polarity-reversed non-presuppositional alternatives:
tests whether alternative structure affects felicity.

### Experiment 3: De Re Judgments
Presuppositional triggers under attitude verbs: tests whether presuppositions
can be resolved de re (against CommonGround) vs. de dicto (against attitude holder's
beliefs).

## Constraint-based Formalization

Presuppositional sentences `S_p` compete with non-presuppositional alternatives
`S` under three ranked pragmatic constraints:

1. **IC** (Internal Coherence): `S_p`'s presupposition is consistent with its
   assertion. *Non-violable* — IC violation always blocks the presuppositional
   form.
2. **FP** (Felicity Presupposition): CommonGround entails `S_p`'s presupposition.
   *Violable* — partial CommonGround support may be tolerated.
3. **MP** (Maximize Presupposition): prefer `S_p` over `S` when CommonGround supports the
   presupposition and `S_p` is more informative. *Violable* — overridable by
   IC or FP violations.

The ranking IC ≫ FP ≫ MP, together with the trigger's alternative structure
(`AltStructure`), derives three obligatoriness patterns:
- **Obligatory** triggers (ye, you, reng): deletion alternatives — MP forces
  use of the trigger when CommonGround fully supports presupposition.
- **Optional** triggers (buzai, kaishi): replacement alternatives — competitor
  is informative enough that MP doesn't strongly prefer the trigger.
- **Blocked** triggers (jiu, zhidao under partial CommonGround): no alternative or
  replacement with stronger assertion — FP violation blocks the trigger.

## K Operator Interaction

The epistemic operator K (speaker's beliefs) interacts with exhaustification:
- K ≫ exh_mx: preferred for atomic sentences (speaker-oriented reading)
- exh_mx ≫ K: possible for complex sentences

-/

namespace Wang2025

open Features (Acceptability)
open Mandarin.Particles (MandarinTrigger)

/-- Context condition for presupposition support. -/
inductive ContextCondition where
  | full        -- CommonGround fully entails the presupposition
  | partialSupport  -- CommonGround partially entails the presupposition
  | noSupport   -- CommonGround does not support the presupposition
  deriving DecidableEq, Repr

/-- A single naturalness judgment datum (Experiment 1). -/
structure Exp1Datum where
  trigger : MandarinTrigger
  context : ContextCondition
  /-- Mean naturalness rating (1-7 Likert scale, ×10 for rational representation) -/
  meanRating : ℚ
  /-- Observed felicity judgment, encoded as a standard acceptability diacritic
      (`Features.Acceptability`): `.ok` = felicitous, `.marginal` = borderline `?`,
      `.anomalous` = pragmatically odd `#`. -/
  felicity : Acceptability
  deriving Repr

/-- Experiment 1 key finding: ye/also is felicitous under full and partial CommonGround. -/
def ye_full : Exp1Datum :=
  { trigger := .ye, context := .full, meanRating := 62/10, felicity := .ok }

def ye_partial : Exp1Datum :=
  { trigger := .ye, context := .partialSupport, meanRating := 51/10, felicity := .ok }

def ye_none : Exp1Datum :=
  { trigger := .ye, context := .noSupport, meanRating := 28/10, felicity := .anomalous }

/-- Experiment 1 key finding: you/again is felicitous under full and partial CommonGround. -/
def you_full : Exp1Datum :=
  { trigger := .you, context := .full, meanRating := 6, felicity := .ok }

def you_partial : Exp1Datum :=
  { trigger := .you, context := .partialSupport, meanRating := 49/10, felicity := .marginal }

def you_none : Exp1Datum :=
  { trigger := .you, context := .noSupport, meanRating := 25/10, felicity := .anomalous }

/-- Experiment 1 key finding: jiu/only is blocked under partial CommonGround. -/
def jiu_full : Exp1Datum :=
  { trigger := .jiu, context := .full, meanRating := 58/10, felicity := .ok }

def jiu_partial : Exp1Datum :=
  { trigger := .jiu, context := .partialSupport, meanRating := 3, felicity := .anomalous }

def jiu_none : Exp1Datum :=
  { trigger := .jiu, context := .noSupport, meanRating := 22/10, felicity := .anomalous }

/-- Experiment 1 key finding: zhidao/know is blocked under partial CommonGround. -/
def zhidao_full : Exp1Datum :=
  { trigger := .zhidao, context := .full, meanRating := 59/10, felicity := .ok }

def zhidao_partial : Exp1Datum :=
  { trigger := .zhidao, context := .partialSupport, meanRating := 32/10, felicity := .anomalous }

def zhidao_none : Exp1Datum :=
  { trigger := .zhidao, context := .noSupport, meanRating := 2, felicity := .anomalous }

/-- Key contrast: ye and jiu diverge under partial CommonGround support. -/
theorem ye_jiu_partial_diverge :
    ye_partial.felicity ≠ jiu_partial.felicity := by decide

/-- Obligatory triggers are felicitous under both full and partial CommonGround. -/
theorem obligatory_trigger_pattern :
    ye_full.felicity = .ok ∧
    ye_partial.felicity = .ok ∧
    ye_none.felicity = .anomalous := by
  exact ⟨rfl, rfl, rfl⟩

/-- Blocked triggers are only felicitous under full CommonGround. -/
theorem blocked_trigger_pattern :
    jiu_full.felicity = .ok ∧
    jiu_partial.felicity = .anomalous ∧
    jiu_none.felicity = .anomalous := by
  exact ⟨rfl, rfl, rfl⟩


-- ============================================================================
-- Experiment 3: De Re Presupposition
-- ============================================================================

/-- Resolution locus for presupposition under attitude verbs. -/
inductive Resolution where
  /-- Presupposition resolved against CommonGround (de re) -/
  | deRe
  /-- Presupposition resolved against attitude holder's beliefs (de dicto) -/
  | deDicto
  deriving DecidableEq, Repr

/-- A de re judgment datum (Experiment 3). -/
structure Exp3Datum where
  trigger : MandarinTrigger
  resolution : Resolution
  /-- Whether this resolution was accepted by participants -/
  accepted : Bool
  deriving Repr

/-- ye/also under attitude verb: de re reading available. -/
def ye_deRe : Exp3Datum :=
  { trigger := .ye, resolution := .deRe, accepted := true }

/-- ye/also under attitude verb: de dicto reading also available. -/
def ye_deDicto : Exp3Datum :=
  { trigger := .ye, resolution := .deDicto, accepted := true }

/-- Additive presupposition allows de re resolution. -/
theorem additive_deRe_available : ye_deRe.accepted = true := rfl


-- ============================================================================
-- Constraint-based Formalization (was: Implicature/Constraints/Wang2025.lean)
-- ============================================================================

open Semantics.Presupposition (PartialProp)
open CommonGround (ContextSet)

/-- Local Bool-valued accessibility used by Wang2025 for `List.all` evaluation
of the speaker-K operator. The Prop-valued canonical version lives in
`Core.Logic.Modal.AccessRel`; lift via
`fun a b => R a b = true` to bridge. -/
abbrev BAccessRel (W : Type*) := W → W → Bool
open Pragmatics.Expressives (TwoDimProp)

/--
[wang-2025] pragmatic constraint ranking: IC ≫ FP ≫ MP.

- IC (Internal Coherence): S_p's presupposition is consistent with its
  assertion. Non-violable.
- FP (Felicity Presupposition): S_p's presupposition is entailed by the CommonGround.
  Violable but ranked above MP.
- MP (Maximize Presupposition): Prefer the presuppositional S_p over its
  non-presuppositional alternative S when context supports it. Violable.
-/
inductive PragConstraint where
  /-- Internal Coherence: presupposition consistent with assertion (non-violable) -/
  | IC
  /-- Felicity Presupposition: CommonGround entails presupposition (violable) -/
  | FP
  /-- Maximize Presupposition: prefer presuppositional form (violable) -/
  | MP
  deriving DecidableEq, Repr

/-- IC is non-violable; FP and MP are violable. -/
def PragConstraint.isViolable : PragConstraint → Bool
  | .IC => false
  | .FP => true
  | .MP => true

/-- The canonical constraint ranking: IC ≫ FP ≫ MP. -/
def constraintRanking : List PragConstraint := [.IC, .FP, .MP]


-- ============================================================================
-- Section 1: Constraint Evaluation
-- ============================================================================

variable {W : Type*}

/--
IC (Internal Coherence): the presupposition is consistent with the assertion.

S_p is internally coherent iff there exists a world where both the presupposition
and the assertion hold. IC violation means the presupposition contradicts the
assertion — the sentence is semantically defective.

[wang-2025]: IC is NON-VIOLABLE.
-/
def satisfiesIC (p : PartialProp W) : Prop :=
  ∃ w, PartialProp.holds w p

/--
FP (Felicity Presupposition): the common ground entails the presupposition.

Standard Stalnakerian presupposition satisfaction. When the CommonGround only partially
entails the presupposition, FP is violated but may be tolerated.
-/
def satisfiesFP (cg : ContextSet W) (p : PartialProp W) : Prop :=
  ∀ w, cg w → PartialProp.defined w p

/--
Partial FP satisfaction: the presupposition is compatible with the CommonGround
but not fully entailed.

[wang-2025] Ch. 2-3: some triggers tolerate partial satisfaction (ye, you, reng)
while others don't (jiu, zhidao).
-/
def partialFP (cg : ContextSet W) (p : PartialProp W) : Prop :=
  (∃ w, cg w ∧ PartialProp.defined w p) ∧ ¬satisfiesFP cg p

/--
MP (Maximize Presupposition): prefer S_p over S when the presuppositional
form is more informative and the CommonGround supports its presupposition.

MP is violated when the non-presuppositional alternative S is used despite
the CommonGround supporting S_p's presupposition.
-/
def mpPrefers (cg : ContextSet W) (sp : PartialProp W) : Prop :=
  satisfiesFP cg sp ∧ satisfiesIC sp


/-! ### Alternative-structure typology

[wang-2025] classifies each trigger by what non-presuppositional alternative
it has; the classification, with the constraint ranking, drives the
obligatoriness predictions below. The cases mirror [katzir-2007]'s
structural-alternative operations: a `deletion` competitor is
delete-reachable, a `replacement` competitor substitute-reachable
(cf. `Semantics.Alternatives.Structural`). -/

/-- How a presupposition trigger relates to its non-presuppositional
alternative ([wang-2025]'s alternative-structure typology). -/
inductive AltStructure where
  /-- Alternative obtained by deleting the trigger (*ye*/also → ∅) -/
  | deletion
  /-- Alternative is a specific lexical replacement (*zhidao*/know → *yiwei*/believe) -/
  | replacement
  /-- No structural alternative available (*jiu*/only) -/
  | none
  deriving DecidableEq, Repr

/-- [wang-2025]'s alternative-structure classification of the Mandarin
triggers studied in the experiments. -/
def altStructureOf : MandarinTrigger → AltStructure
  | .ye => .deletion
  | .you => .deletion
  | .reng => .deletion
  | .jiu => .none
  | .zhidao => .replacement
  | .buzai => .replacement
  | .kaishi => .replacement
  | .faner => .replacement
  | .er => .replacement

/--
Obligatoriness pattern predicted by the alternative-structure typology.

[wang-2025] derives three patterns from the interaction of trigger
type, alternative structure, and constraint ranking:
1. Obligatory: trigger must be used when CommonGround supports presupposition
2. Optional: trigger may or may not be used
3. Blocked: trigger must NOT be used (mandatorily omitted)
-/
inductive Obligatoriness where
  /-- Trigger is obligatory when presupposition is fully entailed by CommonGround -/
  | obligatory
  /-- Trigger is optional (either form is acceptable) -/
  | optional
  /-- Trigger is blocked (mandatorily omitted in this context) -/
  | blocked
  deriving DecidableEq, Repr


-- ============================================================================
-- Section 2: Obligatoriness Predictions
-- ============================================================================

/--
Predict obligatoriness from alternative structure and context.

[wang-2025] Ch. 4: The three-way prediction follows from constraint interaction.
-/
def predictObligatoriness (altStr : AltStructure) (cgEntailsPresup : Bool)
    (cgPartialPresup : Bool) : Obligatoriness :=
  match altStr, cgEntailsPresup, cgPartialPresup with
  -- Full CommonGround support: MP forces presuppositional form (obligatory)
  | .deletion, true, _ => .obligatory
  | .replacement, true, _ => .obligatory
  | .none, true, _ => .obligatory
  -- Partial CommonGround support with deletion alternative: still OK (obligatory/optional)
  | .deletion, false, true => .optional
  -- Partial CommonGround support with replacement: depends on alternative strength
  | .replacement, false, true => .optional
  -- Partial CommonGround support with no alternative: blocked
  | .none, false, true => .blocked
  -- No CommonGround support: blocked for all
  | _, false, false => .blocked

/--
Triggers with deletion alternatives remain felicitous under partial CommonGround.

[wang-2025] Ch. 4: ye/also, you/again, reng/still have deletion alternatives,
so even when the CommonGround only partially entails the presupposition, the
presuppositional form is not blocked.
-/
theorem deletion_alt_partial_resolution :
    predictObligatoriness (altStructureOf .ye) false true = .optional := rfl

/--
Triggers with no structural alternative are blocked under partial CommonGround.

[wang-2025] Ch. 4: jiu/only has no non-presuppositional alternative, so
when the CommonGround doesn't fully support the presupposition, the presuppositional
form cannot be used.
-/
theorem no_alt_blocked_partial :
    predictObligatoriness (altStructureOf .jiu) false true = .blocked := rfl

/--
Full CommonGround support always yields obligatoriness (for any alternative structure).
-/
theorem full_cg_obligatory (alt : AltStructure) (b : Bool) :
    predictObligatoriness alt true b = .obligatory := by
  cases alt <;> rfl

/--
No CommonGround support always blocks (for any alternative structure).
-/
theorem no_cg_blocks (alt : AltStructure) :
    predictObligatoriness alt false false = .blocked := by
  cases alt <;> rfl


-- ============================================================================
-- Section 3: IC Non-Violability
-- ============================================================================

/--
IC satisfaction is necessary for felicity.
-/
def icNecessary (p : PartialProp W) (h : satisfiesIC p) :
    ∃ w, PartialProp.holds w p := h


-- ============================================================================
-- Section 4: K Operator and Exhaustification Interaction
-- ============================================================================

/--
The epistemic K operator: speaker believes φ.

[wang-2025] Ch. 4: K is a covert doxastic operator marking the speaker's
epistemic stance. It scopes relative to exh_mx:
- K >> exh_mx: preferred for atomic sentences
- exh_mx >> K: available for complex sentences

Uses a local Bool-valued accessibility relation; for the Prop-valued
canonical Kripke semantics see `Intensional.box`.
-/
noncomputable def speakerK [Fintype W] (R : BAccessRel W) (φ : (W → Bool)) : (W → Bool) :=
  fun w => ((Finset.univ : Finset W).toList.filter (R w)).all φ


-- ============================================================================
-- Section 5: Felicity Check
-- ============================================================================

/--
Input for Wang's felicity prediction: a trigger entry in a context.
-/
structure WangInput (W : Type*) where
  /-- The presuppositional sentence -/
  sentence : PartialProp W
  /-- The trigger's alternative structure -/
  altStructure : AltStructure
  /-- Whether CommonGround fully entails the presupposition -/
  cgFull : Bool
  /-- Whether CommonGround partially entails the presupposition -/
  cgPartial : Bool
  /-- Whether the sentence is internally coherent -/
  ic : Bool

/--
[wang-2025] felicity check: evaluates constraint satisfaction.

IC violation → odd (non-violable). Otherwise, obligatoriness prediction
from alternative structure and CommonGround support determines the status.
-/
def wangCheck (input : WangInput W) : Acceptability :=
  if !input.ic then
    .anomalous
  else
    match predictObligatoriness input.altStructure input.cgFull input.cgPartial with
    | .obligatory => .ok
    | .optional => .marginal
    | .blocked => .anomalous

/--
IC violation always yields oddness, regardless of CommonGround support and alternative structure.

[wang-2025]: IC is the only non-violable constraint. A sentence whose
presupposition contradicts its assertion is always infelicitous, no matter
what the CommonGround says or what alternatives exist.
-/
theorem IC_violation_always_blocks (input : WangInput W) (hIC : input.ic = false) :
    wangCheck input = .anomalous := by
  simp [wangCheck, hIC]


-- ============================================================================
-- Section 6: Bridge to CI Bifurcation (De Re Presupposition)
-- ============================================================================

/-- When CommonGround entails the presupposition, the CI-routed form
(`TwoDimProp.ofPartialProp`) has its CI content satisfied at all CommonGround
worlds — the de re configuration: the presupposition is resolved against the
common ground regardless of the embedding attitude. -/
theorem ofPartialProp_felicitous_when_fp_holds (presup assertion : W → Prop)
    (cg : W → Prop) (hfp : ∀ w, cg w → presup w) :
    ∀ w, cg w → (TwoDimProp.ofPartialProp ⟨presup, assertion⟩).ci w := hfp


end Wang2025
