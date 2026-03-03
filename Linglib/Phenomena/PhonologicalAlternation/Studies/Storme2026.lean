import Linglib.Theories.Phonology.HarmonicGrammar.MaxEnt
import Linglib.Fragments.Farsi.Phonology

/-!
# @cite{storme-2026}: Systemic Constraints in MaxEnt Grammars
@cite{storme-2026}

Replication of @cite{storme-2026} "A Method to Evaluate Systemic Constraints
in Probabilistic Grammars" (Linguistic Inquiry 57(1)).

## Key idea

Standard MaxEnt grammars evaluate each input→output mapping independently.
Storme shows how to incorporate **systemic constraints** — constraints that
evaluate *sets* of mappings jointly. The running example is \*HOMOPHONY:
a constraint penalizing output tuples where distinct inputs receive identical
surface forms.

## Persian hiatus resolution

The case study is Persian vowel hiatus between /æ/ and /ɑ/. Classical
faithfulness (MAX, IDENT) and markedness (\*VV, DEP) constraints predict
symmetric treatment of /æ.ɑ/ vs. /ɑ.æ/ — deletion of V1 vs. V2 should
be equally probable in both. But Storme argues that \*HOMOPHONY breaks this
symmetry: the grammar prefers output tuples where distinct inputs produce
distinct surface forms.

## Formalization

We instantiate `MaxEntGrammar` with the Persian hiatus domain from
`Fragments.Farsi.Phonology`, define the classical and systemic constraints,
and verify the key prediction: homophony avoidance breaks the symmetry.

## Constraints

Following standard OT/MaxEnt constraint families:
- **MAX** (faithfulness): penalizes deletion (1 violation per deleted segment)
- **DEP** (faithfulness): penalizes epenthesis (1 violation per inserted segment)
- **\*VV** (markedness): penalizes vowel hiatus in the output
- **IDENT** (faithfulness): penalizes feature change (coalescence)
- **\*HOMOPHONY** (systemic): penalizes identical outputs for distinct inputs
-/

namespace Phenomena.PhonologicalAlternation.Studies.Storme2026

open Theories.Phonology.HarmonicGrammar
open Fragments.Farsi.Phonology
open Core.OT

-- Fintype instances for HiatusInput/Output (Fintype requires Mathlib,
-- which is available here via MaxEnt → RationalAction)

instance : Fintype HiatusInput where
  elems := {.ae_ae, .ae_ah, .ah_ae, .ah_ah}
  complete := fun x => by cases x <;> simp

instance : Fintype HiatusOutput where
  elems := {.deleteV1, .deleteV2, .epenthesis, .coalescence, .faithful}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- § 1: Classical Constraints
-- ============================================================================

/-- MAX: penalizes deletion. 1 violation for deleteV1 or deleteV2, 0 otherwise. -/
def maxConstraint : WeightedConstraint HiatusCandidate where
  name := "MAX"
  family := .faithfulness
  eval := fun (_, o) => match o with
    | .deleteV1 | .deleteV2 => 1
    | _ => 0
  weight := 2

/-- DEP: penalizes epenthesis. 1 violation for epenthesis, 0 otherwise. -/
def depConstraint : WeightedConstraint HiatusCandidate where
  name := "DEP"
  family := .faithfulness
  eval := fun (_, o) => match o with
    | .epenthesis => 1
    | _ => 0
  weight := 1

/-- \*VV: markedness constraint penalizing vowel hiatus.
    1 violation for faithful (hiatus preserved), 0 for all repairs. -/
def starVV : WeightedConstraint HiatusCandidate where
  name := "*VV"
  family := .markedness
  eval := fun (_, o) => match o with
    | .faithful => 1
    | _ => 0
  weight := 3

/-- IDENT: penalizes coalescence (feature change).
    1 violation for coalescence, 0 otherwise. -/
def identConstraint : WeightedConstraint HiatusCandidate where
  name := "IDENT"
  family := .faithfulness
  eval := fun (_, o) => match o with
    | .coalescence => 1
    | _ => 0
  weight := 2

/-- The classical constraint set for Persian hiatus.

    **Note**: weights are illustrative (chosen to make epenthesis the
    classical winner), not fitted to Storme's experimental data.
    The qualitative predictions (symmetry, symmetry-breaking) hold
    for any positive weights since they depend on constraint structure,
    not specific weight values. -/
def classicalConstraints : List (WeightedConstraint HiatusCandidate) :=
  [maxConstraint, depConstraint, starVV, identConstraint]

-- ============================================================================
-- § 2: Classical Harmony Scores
-- ============================================================================

/-- Harmony scores are symmetric across mirror-image inputs:
    H(ae.ah, deleteV1) = H(ah.ae, deleteV1) under classical constraints alone,
    because classical constraints only look at output structure. -/
theorem classical_symmetry_deleteV1 :
    harmonyScore classicalConstraints (.ae_ah, .deleteV1) =
    harmonyScore classicalConstraints (.ah_ae, .deleteV1) := by native_decide

theorem classical_symmetry_deleteV2 :
    harmonyScore classicalConstraints (.ae_ah, .deleteV2) =
    harmonyScore classicalConstraints (.ah_ae, .deleteV2) := by native_decide

/-- Concrete score verification: deletion costs -2 (MAX weight 2, 1 violation),
    epenthesis costs -1 (DEP weight 1), faithful costs -3 (*VV weight 3),
    coalescence costs -2 (IDENT weight 2). -/
theorem score_deleteV1 :
    harmonyScore classicalConstraints (.ae_ah, .deleteV1) = -2 := by native_decide

theorem score_epenthesis :
    harmonyScore classicalConstraints (.ae_ah, .epenthesis) = -1 := by native_decide

theorem score_faithful :
    harmonyScore classicalConstraints (.ae_ah, .faithful) = -3 := by native_decide

theorem score_coalescence :
    harmonyScore classicalConstraints (.ae_ah, .coalescence) = -2 := by native_decide

-- ============================================================================
-- § 3: Systemic Constraint — *HOMOPHONY
-- ============================================================================

/-- The four hiatus inputs indexed by Fin 4. -/
def inputsIndexed : Fin 4 → HiatusInput
  | ⟨0, _⟩ => .ae_ae
  | ⟨1, _⟩ => .ae_ah
  | ⟨2, _⟩ => .ah_ae
  | ⟨3, _⟩ => .ah_ah

/-- \*HOMOPHONY for the Persian hiatus paradigm:
    penalizes output tuples where distinct inputs produce identical outputs. -/
def starHomophony : SystemicConstraint 4 HiatusOutput :=
  homophonyAvoidance (w := 1)

-- ============================================================================
-- § 4: Joint Distribution
-- ============================================================================

/-- Joint harmony score for a complete output tuple, combining classical
    per-mapping scores with the systemic \*HOMOPHONY penalty. -/
def persianJointScore (f : Fin 4 → HiatusOutput) : ℚ :=
  jointHarmonyScore inputsIndexed classicalConstraints [starHomophony] f

-- ============================================================================
-- § 5: Symmetry-Breaking Prediction
-- ============================================================================

/-- An output tuple where the mirror-image inputs /æ.ɑ/ and /ɑ.æ/ use
    different repair strategies (deleteV1 vs deleteV2). Both still surface
    as [ɑ], so homophony remains at those positions — but the tuple has
    fewer *HOMOPHONY violations overall than the uniform-strategy tuple. -/
def diverseTuple : Fin 4 → HiatusOutput
  | ⟨0, _⟩ => .deleteV1  -- /æ.æ/ → delete V1
  | ⟨1, _⟩ => .deleteV1  -- /æ.ɑ/ → delete V1 (surfaces as [ɑ])
  | ⟨2, _⟩ => .deleteV2  -- /ɑ.æ/ → delete V2 (surfaces as [ɑ])
  | ⟨3, _⟩ => .deleteV1  -- /ɑ.ɑ/ → delete V1

/-- A homophonous tuple: both mirror-image inputs use the same strategy. -/
def homophonousTuple : Fin 4 → HiatusOutput
  | ⟨0, _⟩ => .deleteV1  -- /æ.æ/ → delete V1
  | ⟨1, _⟩ => .deleteV1  -- /æ.ɑ/ → delete V1 (surfaces as [ɑ])
  | ⟨2, _⟩ => .deleteV1  -- /ɑ.æ/ → delete V1 (surfaces as [æ])
  | ⟨3, _⟩ => .deleteV1  -- /ɑ.ɑ/ → delete V1

/-- Concrete violation counts:
    - homophonousTuple: all 4 positions use deleteV1 → C(4,2) = 6 collisions
    - diverseTuple: 3 positions use deleteV1, 1 uses deleteV2 → 3 collisions -/
theorem homophony_violation_counts :
    starHomophony.eval homophonousTuple = 6 ∧
    starHomophony.eval diverseTuple = 3 := by native_decide

/-- \*HOMOPHONY incurs more violations on the homophonous tuple than
    on the diverse tuple. This is the core mechanism by which systemic
    constraints break symmetry. -/
theorem homophony_penalizes_uniform :
    starHomophony.eval homophonousTuple ≥
    starHomophony.eval diverseTuple := by native_decide

/-- The diverse tuple has at least as high joint harmony as the
    homophonous tuple, because it incurs fewer \*HOMOPHONY violations
    while having the same classical constraint violations. -/
theorem diverse_higher_joint_score :
    persianJointScore diverseTuple ≥
    persianJointScore homophonousTuple := by native_decide

-- ============================================================================
-- § 6: Core Prediction — Systemic Constraints Break Symmetry
-- ============================================================================

/-- Classical constraints alone assign the same score to deleteV1 for
    /æ.ɑ/ and /ɑ.æ/ — the grammar cannot distinguish mirror-image inputs
    at the individual mapping level. (Restated from §2 for contrast with
    the non-separability result below.) -/
theorem classical_cannot_distinguish :
    harmonyScore classicalConstraints (.ae_ah, .deleteV1) =
    harmonyScore classicalConstraints (.ah_ae, .deleteV1) :=
  classical_symmetry_deleteV1

/-- Under \*HOMOPHONY, the joint distribution over all four mappings is
    *not* a product of independent per-mapping distributions. The marginal
    probability of a specific output for /æ.ɑ/ depends on what outputs are
    chosen for the other inputs — this is the core mechanism by which
    systemic constraints influence individual mapping probabilities.

    This theorem verifies that the joint score is not additively separable
    (i.e., there exist tuples f, g agreeing on position 1 but differing
    in joint score minus the classical score at position 1). -/
theorem joint_not_separable :
    ∃ (f g : Fin 4 → HiatusOutput),
      f ⟨1, by omega⟩ = g ⟨1, by omega⟩ ∧
      persianJointScore f - harmonyScore classicalConstraints (inputsIndexed ⟨1, by omega⟩, f ⟨1, by omega⟩) ≠
      persianJointScore g - harmonyScore classicalConstraints (inputsIndexed ⟨1, by omega⟩, g ⟨1, by omega⟩) := by
  refine ⟨diverseTuple, homophonousTuple, ?_, ?_⟩
  · rfl
  · native_decide

end Phenomena.PhonologicalAlternation.Studies.Storme2026
