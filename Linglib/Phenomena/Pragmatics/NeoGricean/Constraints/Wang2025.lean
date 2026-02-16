import Linglib.Core.Presupposition
import Linglib.Core.CommonGround
import Linglib.Core.ModalLogic
import Linglib.Core.Interfaces.FelicityCondition
import Linglib.Phenomena.Pragmatics.NeoGricean.Presuppositions
import Linglib.Theories.Semantics.Lexical.Expressives.Basic

/-!
# Alternative Competition for Presupposition Triggers (Wang 2025)

Constraint-based evaluation of presuppositional vs. non-presuppositional alternatives,
following Wang (2025) "Presupposition, Competition, and Coherence" Ch. 4.

## Framework

Presuppositional sentences S_p compete with non-presuppositional alternatives S
under three ranked pragmatic constraints:

1. **IC** (Internal Coherence): S_p's presupposition is consistent with its assertion.
   Non-violable — IC violation always blocks the presuppositional form.

2. **FP** (Felicity Presupposition): CG entails S_p's presupposition.
   Violable — partial CG support may be tolerated.

3. **MP** (Maximize Presupposition): Prefer S_p over S when CG supports the
   presupposition and S_p is more informative.
   Violable — can be overridden by IC or FP violations.

## Key Predictions

The constraint ranking IC >> FP >> MP, together with the trigger's alternative
structure (Table 4.1), derives three obligatoriness patterns:

1. **Obligatory** triggers (ye, you, reng): deletion alternatives — MP forces
   use of trigger when CG fully supports presupposition.
2. **Optional** triggers (buzai, kaishi): replacement alternatives — competitor
   is informative enough that MP doesn't strongly prefer the trigger.
3. **Blocked** triggers (jiu, zhidao under partial CG): no alternative or
   replacement with stronger assertion — FP violation blocks the trigger.

## K Operator Interaction

The epistemic operator K (speaker's beliefs) interacts with exhaustification:
- K >> exh_mx: preferred for atomic sentences (speaker-oriented reading)
- exh_mx >> K: possible for complex sentences

## References

- Wang, S. (2025). Presupposition, Competition, and Coherence. MIT dissertation. Ch. 4.
- Heim, I. (1991). Artikel und Definitheit. In von Stechow & Wunderlich.
- Sauerland, U. (2008). Implicated presuppositions.
- Katzir, R. (2007). Structurally-defined alternatives. L&P 30.
-/

namespace NeoGricean.Constraints.Wang2025

open Core.Presupposition (PrProp)
open Core.CommonGround (ContextSet)
open Core.ModalLogic (AccessRel kripkeEval)
open Core.Proposition (BProp FiniteWorlds)
open Interfaces (FelicityStatus FelicityResult FelicityCondition)
open NeoGricean.Presuppositions (AltStructure PragConstraint Obligatoriness)
open Semantics.Lexical.Expressives (ciLift)


-- ============================================================================
-- Section 1: Constraint Evaluation
-- ============================================================================

variable {W : Type*}

/--
IC (Internal Coherence): the presupposition is consistent with the assertion.

S_p is internally coherent iff there exists a world where both the presupposition
and the assertion hold. IC violation means the presupposition contradicts the
assertion — the sentence is semantically defective.

Wang (2025): IC is NON-VIOLABLE.
-/
def satisfiesIC (p : PrProp W) : Prop :=
  ∃ w, p.presup w = true ∧ p.assertion w = true

/--
FP (Felicity Presupposition): the common ground entails the presupposition.

Standard Stalnakerian presupposition satisfaction. When the CG only partially
entails the presupposition, FP is violated but may be tolerated.
-/
def satisfiesFP (cg : ContextSet W) (p : PrProp W) : Prop :=
  ∀ w, cg w → p.presup w = true

/--
Partial FP satisfaction: the presupposition is compatible with the CG
but not fully entailed.

Wang (2025) Ch. 2-3: some triggers tolerate partial satisfaction (ye, you, reng)
while others don't (jiu, zhidao).
-/
def partialFP (cg : ContextSet W) (p : PrProp W) : Prop :=
  (∃ w, cg w ∧ p.presup w = true) ∧ ¬satisfiesFP cg p

/--
MP (Maximize Presupposition): prefer S_p over S when the presuppositional
form is more informative and the CG supports its presupposition.

MP is violated when the non-presuppositional alternative S is used despite
the CG supporting S_p's presupposition.
-/
def mpPrefers (cg : ContextSet W) (sp : PrProp W) : Prop :=
  satisfiesFP cg sp ∧ satisfiesIC sp


-- ============================================================================
-- Section 2: Obligatoriness Predictions
-- ============================================================================

/--
Predict obligatoriness from alternative structure and context.

Wang (2025) Ch. 4: The three-way prediction follows from constraint interaction.
-/
def predictObligatoriness (altStr : AltStructure) (cgEntailsPresup : Bool)
    (cgPartialPresup : Bool) : Obligatoriness :=
  match altStr, cgEntailsPresup, cgPartialPresup with
  -- Full CG support: MP forces presuppositional form (obligatory)
  | .deletion, true, _ => .obligatory
  | .replacement, true, _ => .obligatory
  | .none, true, _ => .obligatory
  -- Partial CG support with deletion alternative: still OK (obligatory/optional)
  | .deletion, false, true => .optional
  -- Partial CG support with replacement: depends on alternative strength
  | .replacement, false, true => .optional
  -- Partial CG support with no alternative: blocked
  | .none, false, true => .blocked
  -- No CG support: blocked for all
  | _, false, false => .blocked

/--
Triggers with deletion alternatives remain felicitous under partial CG.

Wang (2025) Ch. 4: ye/also, you/again, reng/still have deletion alternatives,
so even when the CG only partially entails the presupposition, the
presuppositional form is not blocked.
-/
theorem deletion_alt_partial_resolution :
    predictObligatoriness .deletion false true = .optional := rfl

/--
Triggers with no structural alternative are blocked under partial CG.

Wang (2025) Ch. 4: jiu/only has no non-presuppositional alternative, so
when the CG doesn't fully support the presupposition, the presuppositional
form cannot be used.
-/
theorem no_alt_blocked_partial :
    predictObligatoriness .none false true = .blocked := rfl

/--
Full CG support always yields obligatoriness (for any alternative structure).
-/
theorem full_cg_obligatory (alt : AltStructure) (b : Bool) :
    predictObligatoriness alt true b = .obligatory := by
  cases alt <;> rfl

/--
No CG support always blocks (for any alternative structure).
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
def icNecessary (p : PrProp W) (h : satisfiesIC p) :
    ∃ w, p.presup w = true ∧ p.assertion w = true := h


-- ============================================================================
-- Section 4: K Operator and Exhaustification Interaction
-- ============================================================================

/--
The epistemic K operator: speaker believes φ.

Wang (2025) Ch. 4: K is a covert doxastic operator marking the speaker's
epistemic stance. It scopes relative to exh_mx:
- K >> exh_mx: preferred for atomic sentences
- exh_mx >> K: available for complex sentences

Uses the existing Kripke accessibility relation from Core.ModalLogic.
-/
def speakerK [FiniteWorlds W] (R : AccessRel W) (φ : BProp W) : BProp W :=
  kripkeEval R .necessity φ


-- ============================================================================
-- Section 5: FelicityCondition Instance
-- ============================================================================

/--
Input for Wang's felicity prediction: a trigger entry in a context.
-/
structure WangInput (W : Type*) where
  /-- The presuppositional sentence -/
  sentence : PrProp W
  /-- The trigger's alternative structure -/
  altStructure : AltStructure
  /-- Whether CG fully entails the presupposition -/
  cgFull : Bool
  /-- Whether CG partially entails the presupposition -/
  cgPartial : Bool
  /-- Whether the sentence is internally coherent -/
  ic : Bool

/--
Wang (2025) felicity check: evaluates constraint satisfaction.

IC violation → odd (non-violable). Otherwise, obligatoriness prediction
from alternative structure and CG support determines the status.
-/
def wangCheck (input : WangInput W) : FelicityResult :=
  if !input.ic then
    { status := .odd, source := some .unspecified }
  else
    match predictObligatoriness input.altStructure input.cgFull input.cgPartial with
    | .obligatory => { status := .felicitous }
    | .optional => { status := .borderline }
    | .blocked => { status := .odd, source := some .unspecified }

/--
Wang (2025) as a felicity theory: predicts felicity from constraint evaluation.
-/
instance : FelicityCondition (WangInput W) where
  name := "Wang (2025) Alternative Competition"
  check := wangCheck

/--
IC violation always yields oddness, regardless of CG support and alternative structure.

Wang (2025): IC is the only non-violable constraint. A sentence whose
presupposition contradicts its assertion is always infelicitous, no matter
what the CG says or what alternatives exist.
-/
theorem IC_violation_always_blocks (input : WangInput W) (hIC : input.ic = false) :
    (wangCheck input).status = .odd := by
  simp [wangCheck, hIC]


-- ============================================================================
-- Section 6: Bridge to CI Bifurcation (De Re Presupposition)
-- ============================================================================

/--
When IC is satisfied and CG entails the presupposition, the CI-lifted
form yields a felicitous two-dimensional meaning where:
- The at-issue content is evaluable (assertion)
- The CI content (presupposition) is satisfied at all CG worlds

This connects the constraint-based analysis to the CI bifurcation approach
for de re presupposition (Wang & Buccola 2025).
-/
theorem ciLift_felicitous_when_fp_holds (p : PrProp W)
    (cg : ContextSet W) (hfp : satisfiesFP cg p) :
    ∀ w, cg w → (ciLift p).ci w = true := by
  intro w hw
  exact hfp w hw


end NeoGricean.Constraints.Wang2025
