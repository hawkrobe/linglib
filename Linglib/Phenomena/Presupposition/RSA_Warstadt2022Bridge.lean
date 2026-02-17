import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Phenomena.Presupposition.Studies.Warstadt2022
import Linglib.Core.CommonGround

/-!
# Bridge: RSA Presupposition Accommodation → Warstadt (2022)

Connects RSA presupposition accommodation models to the empirical domain
from `Phenomena.Presupposition.Studies.Warstadt2022`.

## Architecture

The latent variable is a **context** (subset of worlds), representing what
is established in the common ground. L1 jointly infers (world, context)
given the utterance and QUD, following Qing, Goodman & Lassiter (2016).

## Key Predictions

1. **QUD sensitivity**: "not green card" triggers the genus inference
   (Tom is non-US) under the visa QUD but not the free-drink QUD.
2. **Gradience**: species-level negation ("not Olympic sprinter") triggers
   stronger accommodation than genus-level negation ("not runner").

## Connection to Other Models

This model is computationally identical to:
- Qing, Goodman & Lassiter (2016) — the original formulation
- Scontras & Tonhauser (2025) — applied to factives

See `Phenomena.Presupposition.Compare` for the formal comparison.
-/

namespace Phenomena.Presupposition.Warstadt2022Bridge

open Phenomena.Presupposition.Studies.Warstadt2022
open RSA.Eval
open Core.CommonGround


/-! ## Green Card: Context Types -/

/-- A context is a subset of GCWorlds, represented as a Boolean structure.
Each field indicates whether that world is compatible with the context. -/
structure GCContext where
  usCitizen : Bool
  gcHolder : Bool
  nonUS : Bool
  deriving DecidableEq, BEq, Repr, Inhabited

/-- All 2³ = 8 contexts (subsets of GCWorld). -/
def allGCContexts : List GCContext :=
  [false, true].flatMap λ a =>
    [false, true].flatMap λ b =>
      [false, true].map λ c =>
        ⟨a, b, c⟩

theorem allGCContexts_length : allGCContexts.length = 8 := rfl

/-- A world is compatible with a context iff the context includes it. -/
def gcCompatible (c : GCContext) (w : GCWorld) : Bool :=
  match w with
  | .usCitizen => c.usCitizen
  | .gcHolder => c.gcHolder
  | .nonUS => c.nonUS

/-- Context credence: 1 if compatible, 0 otherwise.
Plays the role of `speakerCredence` in the RSA framework. -/
def gcContextCredence (c : GCContext) (w : GCWorld) : ℚ :=
  boolToRat (gcCompatible c w)

/-- Uniform context prior. -/
def gcContextPrior (_c : GCContext) : ℚ := 1 / 8

/-- Coerce a GCContext to a BContextSet. -/
def gcToBContextSet (c : GCContext) : BContextSet GCWorld :=
  λ w => gcCompatible c w

/-- toBContextSet preserves compatibility. -/
theorem gcToBContextSet_compat (c : GCContext) (w : GCWorld) :
    gcToBContextSet c w = gcCompatible c w := rfl


/-! ## Green Card: RSA Computation -/

/-- L1 context posterior: P(C | u, Q).
Returns the accommodation distribution over contexts. -/
def gcAccommodation (u : GCUtterance) (q : GCQUD) (α : ℕ) : List (GCContext × ℚ) :=
  RSA.Eval.projectionL1_context
    allGCUtterances allGCWorlds allGCContexts allGCQUDs
    gcMeaning gcWorldPrior gcContextPrior gcContextCredence gcQUDProject α u q

/-- L1 world posterior: P(w | u, Q). -/
def gcL1World (u : GCUtterance) (q : GCQUD) (α : ℕ) : List (GCWorld × ℚ) :=
  RSA.Eval.projectionL1_world
    allGCUtterances allGCWorlds allGCContexts allGCQUDs
    gcMeaning gcWorldPrior gcContextPrior gcContextCredence gcQUDProject α u q

/-- Genus inference measure: P(non-US ∈ context | u, Q).
Sum of posterior probability over contexts that include the non-US world. -/
def gcGenusInference (u : GCUtterance) (q : GCQUD) (α : ℕ) : ℚ :=
  let dist := gcAccommodation u q α
  dist.foldl (λ acc (c, p) => if c.nonUS then acc + p else acc) 0


/-! ## Family-Genus-Species: Context Types -/

/-- A context is a subset of FGSWorlds. -/
structure FGSContext where
  olympicSprinter : Bool
  runner : Bool
  otherAthlete : Bool
  nonAthlete : Bool
  deriving DecidableEq, BEq, Repr, Inhabited

/-- All 2⁴ = 16 contexts. -/
def allFGSContexts : List FGSContext :=
  [false, true].flatMap λ a =>
    [false, true].flatMap λ b =>
      [false, true].flatMap λ c =>
        [false, true].map λ d =>
          ⟨a, b, c, d⟩

theorem allFGSContexts_length : allFGSContexts.length = 16 := rfl

def fgsCompatible (c : FGSContext) (w : FGSWorld) : Bool :=
  match w with
  | .olympicSprinter => c.olympicSprinter
  | .runner => c.runner
  | .otherAthlete => c.otherAthlete
  | .nonAthlete => c.nonAthlete

def fgsContextCredence (c : FGSContext) (w : FGSWorld) : ℚ :=
  boolToRat (fgsCompatible c w)

def fgsContextPrior (_c : FGSContext) : ℚ := 1 / 16

/-- Single QUD for FGS: max QUD (full world identification). -/
inductive FGSQUD where
  | identity
  deriving DecidableEq, BEq, Repr, Inhabited

def allFGSQUDs : List FGSQUD := [.identity]

/-- Wrap the data file's 2-arg QUD projection for the RSA API. -/
def fgsQUDProjectBridge : FGSQUD → FGSWorld → FGSWorld → Bool
  | .identity, w1, w2 => fgsQUDProject w1 w2


/-! ## Family-Genus-Species: RSA Computation -/

/-- L1 context posterior for FGS. -/
def fgsAccommodation (u : FGSUtterance) (α : ℕ) : List (FGSContext × ℚ) :=
  RSA.Eval.projectionL1_context
    allFGSUtterances allFGSWorlds allFGSContexts allFGSQUDs
    fgsMeaning fgsWorldPrior fgsContextPrior fgsContextCredence
    fgsQUDProjectBridge α u .identity

/-- L1 world posterior for FGS. -/
def fgsL1World (u : FGSUtterance) (α : ℕ) : List (FGSWorld × ℚ) :=
  RSA.Eval.projectionL1_world
    allFGSUtterances allFGSWorlds allFGSContexts allFGSQUDs
    fgsMeaning fgsWorldPrior fgsContextPrior fgsContextCredence
    fgsQUDProjectBridge α u .identity

/-- Athlete inference measure: P(athlete world | u).
Sum of posterior probability over athlete worlds (all except nonAthlete). -/
def fgsAthleteInference (u : FGSUtterance) (α : ℕ) : ℚ :=
  let dist := fgsL1World u α
  dist.foldl (λ acc (w, p) =>
    match w with
    | .nonAthlete => acc
    | _ => acc + p) 0


/-! ## Predictions -/

/-- Main prediction: under visa QUD, "not green card" triggers genus inference.
P(non-US ∈ context | notGreenCard, needVisa) > prior (1/2). -/
def prediction_visa_projects (α : ℕ := 100) : Bool :=
  gcGenusInference .notGreenCard .needVisa α > 1/2

/-- Central prediction: visa QUD triggers stronger genus inference than free-drink QUD. -/
def prediction_qud_sensitivity (α : ℕ := 100) : Bool :=
  gcGenusInference .notGreenCard .needVisa α >
  gcGenusInference .notGreenCard .freeDrink α

/-- Gradience: species negation triggers stronger accommodation than genus negation.
P(athlete | "not O.S.") > P(athlete | "not runner"). -/
def prediction_species_gradience (α : ℕ := 1000) : Bool :=
  fgsAthleteInference .notOlympicSprinter α >
  fgsAthleteInference .notRunner α


/-! ## PrProp Connection -/

/-- The Boolean meaning of "green card" decomposes as presupposition ∧ assertion,
matching the PrProp structure from Core.Presupposition.

The paper's key insight: this presupposition structure is NOT stipulated in the
truth conditions (which are purely Boolean). Instead, the genus inference
EMERGES from RSA reasoning about utterance utility. -/
theorem greenCard_meaning_from_prprop (w : GCWorld) :
    gcMeaning .greenCard w =
    (greenCardPrProp.presup w && greenCardPrProp.assertion w) :=
  gcMeaning_greenCard_eq_prprop w

/-- "not green card" is Boolean negation — no presupposition in the semantics. -/
theorem notGreenCard_is_boolean_negation (w : GCWorld) :
    gcMeaning .notGreenCard w = !gcMeaning .greenCard w :=
  gcMeaning_notGreenCard_eq_neg w


/-! ## Evaluation

Uncomment to verify predictions compute correctly:

```
#eval gcGenusInference .notGreenCard .needVisa 100
#eval gcGenusInference .notGreenCard .freeDrink 100
#eval prediction_qud_sensitivity 100
#eval fgsAthleteInference .notOlympicSprinter 1000
#eval fgsAthleteInference .notRunner 1000
#eval prediction_species_gradience 1000
```
-/

end Phenomena.Presupposition.Warstadt2022Bridge
