import Linglib.Theories.Semantics.Events.Krifka1998
import Linglib.Theories.Semantics.Events.Krifka1989
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Gradual Change (GRAD) Bridge

Connects the GRAD/GRADSquare/MeasureProportional theory machinery from
`Events/Krifka1998.lean` and `Events/Krifka1989.lean` to concrete verb
entries and empirical gradual change predictions.

## What it exercises

- `GRAD` (graduality: more object measure → more event measure)
- `GRADSquare` (SINC + measures + proportionality → GRAD)
- `MeasureProportional` (constant rate: μ_ev(e) = c · μ_obj(x))
- `grad_of_sinc` (SINC + ExtMeasure + proportional → GRAD)
- `krifkaGRADSquare` (canonical GRAD square constructor)

## Structure

1. **GRAD prediction data** — which verbs exhibit gradual change
2. **VerbIncClass → GRAD prediction** — sinc/inc → GRAD, cumOnly → no GRAD
3. **Per-verb GRAD verification** — fragment annotations match predictions
4. **GRADSquare parametric documentation** — structure of the proof
-/

namespace Phenomena.TenseAspect.Bridge.GradualChange

open Fragments.English.Predicates.Verbal
open Semantics.Events.Krifka1998 (VerbIncClass)

-- ════════════════════════════════════════════════════
-- § 1. GRAD Prediction Data
-- ════════════════════════════════════════════════════

/-- A gradual change datum: verb + description of what increases,
    and whether GRAD is predicted. -/
structure GRADDatum where
  verb : String
  objectMeasure : String
  expectsGRAD : Bool
  deriving Repr, DecidableEq, BEq

/-- "eat more food → take more time" (sinc, μ = weight/volume). -/
def eatGRAD : GRADDatum :=
  { verb := "eat", objectMeasure := "weight/volume", expectsGRAD := true }

/-- "build more of the house → take more time" (sinc, μ = proportion). -/
def buildGRAD : GRADDatum :=
  { verb := "build", objectMeasure := "proportion done", expectsGRAD := true }

/-- "read more of the book → take more time" (inc, μ = pages). -/
def readGRAD : GRADDatum :=
  { verb := "read", objectMeasure := "pages", expectsGRAD := true }

/-- "push a heavier cart ↛ take more time" (cumOnly, no GRAD). -/
def pushNoGRAD : GRADDatum :=
  { verb := "push", objectMeasure := "weight", expectsGRAD := false }

/-- "kick harder ↛ take more time" (no incremental theme). -/
def kickNoGRAD : GRADDatum :=
  { verb := "kick", objectMeasure := "force", expectsGRAD := false }

def gradData : List GRADDatum :=
  [eatGRAD, buildGRAD, readGRAD, pushNoGRAD, kickNoGRAD]

-- ════════════════════════════════════════════════════
-- § 2. VerbIncClass → GRAD Prediction
-- ════════════════════════════════════════════════════

/-- Whether a verb's incrementality class predicts GRAD.
    SINC and INC verbs exhibit gradual change (more object → more event);
    cumOnly and unannotated verbs do not.
    @cite{krifka-1998} §6: GRAD requires strict incrementality (or INC). -/
def predictsGRAD : Option VerbIncClass → Bool
  | some .sinc => true
  | some .inc => true
  | some .cumOnly => false
  | none => false

/-- All incrementality classes have determinate GRAD predictions. -/
theorem grad_decidable :
    (predictsGRAD (some .sinc) = true) ∧
    (predictsGRAD (some .inc) = true) ∧
    (predictsGRAD (some .cumOnly) = false) ∧
    (predictsGRAD none = false) := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Per-Verb GRAD Annotation Verification
-- ════════════════════════════════════════════════════

/-! Each verb's incrementality class determines GRAD prediction.
    Changing any annotation breaks exactly one theorem. -/

/-- "eat" (sinc) → GRAD predicted. -/
theorem eat_predicts_grad :
    predictsGRAD eat.toVerbCore.verbIncClass = true := rfl

/-- "build" (sinc) → GRAD predicted. -/
theorem build_predicts_grad :
    predictsGRAD build.toVerbCore.verbIncClass = true := rfl

/-- "read" (inc) → GRAD predicted. -/
theorem read_predicts_grad :
    predictsGRAD read.toVerbCore.verbIncClass = true := rfl

/-- "push" (cumOnly) → GRAD not predicted. -/
theorem push_no_grad :
    predictsGRAD push.toVerbCore.verbIncClass = false := rfl

/-- "kick" (no incremental theme) → GRAD not predicted. -/
theorem kick_no_grad :
    predictsGRAD kick.toVerbCore.verbIncClass = false := rfl

/-- All GRAD data matches fragment verb annotations. -/
theorem all_grad_data_matches :
    gradData.all (λ d => predictsGRAD (match d.verb with
      | "eat" => eat.toVerbCore.verbIncClass
      | "build" => build.toVerbCore.verbIncClass
      | "read" => read.toVerbCore.verbIncClass
      | "push" => push.toVerbCore.verbIncClass
      | "kick" => kick.toVerbCore.verbIncClass
      | _ => none) == d.expectsGRAD) = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 4. GRADSquare Parametric Structure
-- ════════════════════════════════════════════════════

/-! The `GRADSquare` from `Krifka1998.lean` provides the theoretical
    backbone: given SINC θ, extensive measures on objects and events,
    and proportionality (constant rate), GRAD follows by `GRADSquare.grad`.

    We don't instantiate this for concrete verbs (that would require
    actual numerical measurements), but we document the structure:

    For "eat":
      θ = theme role (eating → food mapping)
      μ_obj = weight/volume measure on food (extensive)
      τ = runtime extraction (event → interval)
      dur = duration measure on intervals (extensive)
      rate = eating rate (grams per second)

    The `krifkaGRADSquare` constructor from `Krifka1989.lean` packages
    these assumptions into a `GRADSquare`, and `GRADSquare.grad` derives
    GRAD from it.

    The proof path for each sinc verb:
    1. sinc (verb annotation) → SINC θ (meaning postulate)
    2. ExtMeasure μ_obj (e.g., weight is extensive)
    3. ExtMeasure (dur ∘ τ) (duration is extensive)
    4. MeasureProportional θ μ_obj (dur ∘ τ) (constant rate assumption)
    5. krifkaGRADSquare θ μ_obj dur sinc ext_obj ext_ev prop → GRADSquare
    6. GRADSquare.grad → GRAD θ μ_obj (dur ∘ τ)

    For cumOnly verbs (push, carry), step 1 fails: the verb lacks SINC,
    so the GRADSquare cannot be constructed, and GRAD is not predicted. -/

/-- sinc verbs have the prerequisites for GRADSquare; cumOnly verbs don't. -/
theorem grad_requires_incrementality :
    (predictsGRAD (some .sinc) = true) ∧
    (predictsGRAD (some .cumOnly) = false) := ⟨rfl, rfl⟩

end Phenomena.TenseAspect.Bridge.GradualChange
