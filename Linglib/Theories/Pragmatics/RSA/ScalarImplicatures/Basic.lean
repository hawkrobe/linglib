import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Semantics.Montague.Derivation
import Mathlib.Data.Rat.Defs
import Linglib.Core.Interface

/-!
# RSA Scalar Implicatures from Semantic Derivations

Connects RSA pragmatics to the syntax-semantics pipeline.
Any syntax theory (CCG, HPSG, Minimalism) that produces a `SemDeriv.Derivation`
can feed into RSA for probabilistic scalar implicature derivation.

## Architecture

```
CCG/HPSG/Minimalism → SemDeriv.Derivation → rsaFromDerivation → RSA L1 interpretation
```

## Status

The ℚ-based RSA evaluation infrastructure (RSA.Eval, boolToRat, RSAScenario) has been
removed. The scalar implicature results and RSA ImplicatureTheory instance need to be
re-implemented using the new RSAConfig framework.

## Results (To Be Re-derived)

- `rsa_some_not_all`: RSA derives P(some_not_all | "some") > P(all | "some")
- `rsa_derives_not_all`: Using derivation interface, RSA prefers non-all worlds
-/

namespace RSA.ScalarImplicatures

open Semantics.Montague
open Semantics.Montague.SemDeriv
open Semantics.Montague

/-- World states for scalar implicature reasoning (coarser partition) -/
inductive ScalarWorld where
  | none  -- No one (0)
  | some  -- Some but not all (1 or 2 out of 3)
  | all   -- All (3 out of 3)
  deriving DecidableEq, BEq, Repr, Inhabited

/--
RSA scalar implicature result.

Records the L1 probabilities for different world types,
showing how RSA derives the implicature probabilistically.
-/
structure RSAScalarResult where
  /-- The utterance analyzed -/
  utterance : String
  /-- L1 probability mass on "some but not all" worlds -/
  probSomeNotAll : ℚ
  /-- L1 probability mass on "all" world -/
  probAll : ℚ
  /-- Does the implicature hold? (probSomeNotAll > probAll) -/
  implicatureHolds : Bool
  deriving Repr


/--
Check if a derivation contains a "some" scalar item.
-/
def hasSomeQuantifier {m : Model} (d : Derivation m) : Bool :=
  d.scalarItems.any λ occ =>
    match occ.entry.scaleMembership with
    | some (.quantifier .some_) => true
    | _ => false

/--
Check if a derivation contains an "all/every" scalar item.
-/
def hasAllQuantifier {m : Model} (d : Derivation m) : Bool :=
  d.scalarItems.any λ occ =>
    match occ.entry.scaleMembership with
    | some (.quantifier .all) => true
    | _ => false


end RSA.ScalarImplicatures


/-!
# RSA ImplicatureTheory Instance

Implements the ImplicatureTheory interface for the RSA (Rational Speech Acts)
framework (Goodman & Frank 2016).

## Status

The RSA model currently uses stub values. The ℚ-based RSA evaluation
infrastructure has been removed. The instance needs to be re-implemented
using the new RSAConfig framework.

## References

- Goodman & Frank (2016). Pragmatic Language Interpretation as Probabilistic Inference.
- Frank & Goodman (2012). Predicting Pragmatic Reasoning in Language Games.
- Bergen, Levy & Goodman (2016). Pragmatic reasoning through semantic inference.
-/

namespace RSA

open Interfaces
open RSA.ScalarImplicatures

/-- Marker type for the RSA theory -/
structure RSATheory

/-- RSA's internal representation for implicature analysis.

    Wraps RSAScalarResult with position information. -/
structure RSAStructure where
  /-- The RSA scalar result (probabilities, implicature status) -/
  result : RSAScalarResult
  /-- Position of the scalar item (if any) -/
  scalarPosition : Option Nat
  deriving Repr

-- Parsing

/-- Check if a word is a scalar quantifier -/
def isScalarQuantifier (w : Word) : Bool :=
  w.form == "some" || w.form == "every" || w.form == "all" || w.form == "most"

/-- Find the position of a scalar item in a word list -/
def findScalarPosition (ws : List Word) : Option Nat :=
  ws.findIdx? isScalarQuantifier

/-- Parse words into RSA structure.

    For now, uses stub RSA results.
    TODO: Re-implement using RSAConfig-based computation. -/
def parseToRSA (ws : List Word) : Option RSAStructure :=
  let scalarPos := findScalarPosition ws
  match scalarPos with
  | none => some { result := { utterance := ""
                             , probSomeNotAll := 0
                             , probAll := 0
                             , implicatureHolds := false }
                 , scalarPosition := none }
  | some pos =>
    match ws[pos]? with
    | some w =>
      if Word.form w == "some" then
        -- TODO: Replace with RSAConfig-based L1 computation
        some { result := { utterance := "some"
                         , probSomeNotAll := 2/3
                         , probAll := 1/3
                         , implicatureHolds := true }
             , scalarPosition := some pos }
      else if Word.form w == "every" || Word.form w == "all" then
        -- Top of scale, no implicature
        some { result := { utterance := "all"
                         , probSomeNotAll := 0
                         , probAll := 1  -- High probability
                         , implicatureHolds := false }
             , scalarPosition := some pos }
      else
        -- Other scalar items (most, etc.) - simplified
        some { result := { utterance := Word.form w
                         , probSomeNotAll := 0
                         , probAll := 0
                         , implicatureHolds := false }
             , scalarPosition := some pos }
    | none => none

-- ImplicatureTheory Instance

instance : ImplicatureTheory RSATheory where
  Structure := RSAStructure

  parse := parseToRSA

  implicatureStatus := λ s pos =>
    -- Check if this position has the scalar item
    if s.scalarPosition != some pos then .absent
    else
      -- RSA: implicature holds if P(some_not_all) > P(all)
      if s.result.implicatureHolds then .triggered
      else .absent

  implicatureStrength := λ s pos =>
    -- Convert RSA probabilities to percentage (0-100)
    if s.scalarPosition != some pos then none
    else if s.result.implicatureHolds then
      -- RSA gives ~50% for "some but not all" interpretation
      -- (P(w1) + P(w2) combined)
      some 50
    else
      none

  -- These flags reflect model incompleteness, not theoretical predictions.
  -- A complete RSA model with compositional semantics could potentially
  -- derive DE blocking and task effects. See header comment for details.

  predictsDEBlocking := false  -- Model incomplete: can't represent embedded contexts

  predictsTaskEffect := false  -- Model incomplete: no QUD/attention mechanism

  predictedBaselineRate := 50  -- RSA predicts ~50% for "some but not all"

-- Theorems (Reflecting Model Incompleteness)

/-- Current RSA model doesn't handle DE contexts (model incomplete, not wrong) -/
theorem rsa_de_not_modeled :
    ImplicatureTheory.predictsDEBlocking (T := RSATheory) = false := rfl

/-- Current RSA model doesn't handle task effects (model incomplete) -/
theorem rsa_task_effect_not_modeled :
    ImplicatureTheory.predictsTaskEffect (T := RSATheory) = false := rfl

/-- RSA baseline rate is 50% -/
theorem rsa_baseline_rate :
    ImplicatureTheory.predictedBaselineRate (T := RSATheory) = 50 := rfl

-- Example Derivations

/-- Example: "some" via RSA -/
def someRSA : RSAStructure :=
  { result := { utterance := "some"
              , probSomeNotAll := 2/3
              , probAll := 1/3
              , implicatureHolds := true }
  , scalarPosition := some 0
  }

/-- Example: "all" via RSA -/
def allRSA : RSAStructure :=
  { result := { utterance := "all"
              , probSomeNotAll := 0
              , probAll := 1
              , implicatureHolds := false }
  , scalarPosition := some 0
  }

/-- RSA triggers implicature for "some" -/
theorem rsa_some_triggers :
    ImplicatureTheory.implicatureStatus (T := RSATheory) someRSA 0 =
    .triggered := by sorry  -- TODO: re-derive with RSAConfig

/-- RSA doesn't trigger implicature for "all" (top of scale) -/
theorem rsa_all_no_implicature :
    ImplicatureTheory.implicatureStatus (T := RSATheory) allRSA 0 =
    .absent := by sorry  -- TODO: re-derive with RSAConfig

/-- Wrong position returns absent -/
theorem rsa_wrong_position_absent :
    ImplicatureTheory.implicatureStatus (T := RSATheory) someRSA 1 =
    .absent := by sorry  -- TODO: re-derive with RSAConfig

end RSA
