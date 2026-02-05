/-
# RSA Scalar Implicatures from Semantic Derivations

Connects RSA pragmatics to the syntax-semantics pipeline.
Any syntax theory (CCG, HPSG, Minimalism) that produces a `SemDeriv.Derivation`
can feed into RSA for probabilistic scalar implicature derivation.

## Architecture

```
CCG/HPSG/Minimalism → SemDeriv.Derivation → rsaFromDerivation → RSA L1 interpretation
```

## Results

- `rsa_some_not_all`: RSA derives P(some_not_all | "some") > P(all | "some")
- `rsa_derives_not_all`: Using derivation interface, RSA prefers non-all worlds
-/

import Linglib.Theories.RSA.Domains.Quantities
import Linglib.Theories.RSA.Core.Eval
import Linglib.Theories.Montague.Core.Derivation
import Mathlib.Data.Rat.Defs
import Linglib.Theories.Core.Interfaces.ImplicatureTheory

namespace RSA.ScalarImplicatures

open RSA RSA.Domains.Quantity
open Montague
open Montague.SemDeriv
open Montague.Core


/-
## Connecting Derivations to RSA Worlds

For scalar implicatures with quantifiers, the relevant distinction is:
- `none`: No individuals satisfy the predicate
- `some`: Some but not all satisfy
- `all`: All individuals satisfy

RSA reasons about these worlds probabilistically.
-/

-- Use the standard 3-person domain from Fragments
def threePerson : Domain 3 := standard 3
-- Note: For #eval demonstrations, use threePerson.runL1 etc.

/-- World states for scalar implicature reasoning (coarser partition) -/
inductive ScalarWorld where
  | none  -- No one (0)
  | some  -- Some but not all (1 or 2 out of 3)
  | all   -- All (3 out of 3)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Convert Quantity world to ScalarWorld (coarser partition) -/
def quantityToScalar : Fin 4 → ScalarWorld
  | ⟨0, _⟩ => .none
  | ⟨1, _⟩ => .some
  | ⟨2, _⟩ => .some
  | ⟨3, _⟩ => .all
  | ⟨n+4, h⟩ => absurd h (by omega)


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
Compute RSA result for "some" utterance.

Uses the L1 scores from RSA.Domains.Quantity.l1 to get the distribution over worlds.
-/
def rsaSomeResult : RSAScalarResult :=
  let l1_scores := l1 threePerson .some_
  -- P(some_not_all) = P(w1) + P(w2)
  let p_w1 := RSA.Eval.getScore l1_scores (w1 (n := 3))
  let p_w2 := RSA.Eval.getScore l1_scores (w2 (n := 3))
  let p_some_not_all := p_w1 + p_w2
  -- P(all) = P(w3)
  let p_all := RSA.Eval.getScore l1_scores (wAll (n := 3))
  { utterance := "some"
  , probSomeNotAll := p_some_not_all
  , probAll := p_all
  , implicatureHolds := p_some_not_all > p_all
  }

/--
RSA assigns higher probability to "some but not all" worlds than to "all" world.
This is the RSA counterpart to NeoGricean's categorical "not all" implicature.
-/
theorem rsa_some_not_all :
    rsaSomeResult.implicatureHolds = true := by
  native_decide

/--
P(some_not_all) > P(all) explicitly.
-/
theorem rsa_some_not_all_explicit :
    rsaSomeResult.probSomeNotAll > rsaSomeResult.probAll := by
  native_decide


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

/--
Derive RSA scalar implicature from a semantic derivation.

For derivations with "some", returns the RSA analysis showing
higher probability for "some but not all" worlds.

Syntax-agnostic: works with CCG, HPSG, Minimalism, or any theory
that implements the SemDeriv interface.
-/
def rsaFromDerivation {m : Model} (d : Derivation m) : Option RSAScalarResult :=
  if hasSomeQuantifier d then
    some rsaSomeResult
  else if hasAllQuantifier d then
    -- "all" doesn't generate an implicature (top of scale)
    let l1_scores := l1 threePerson .all
    let p_all := RSA.Eval.getScore l1_scores (wAll (n := 3))
    some { utterance := "all"
         , probSomeNotAll := 0
         , probAll := p_all
         , implicatureHolds := false
         }
  else
    none


/--
"some students sleep" via RSA.
-/
def someStudentsSleep_rsa : Option RSAScalarResult :=
  rsaFromDerivation someStudentsSleep

/--
someStudentsSleep produces a result.
-/
theorem someStudentsSleep_rsa_isSome :
    someStudentsSleep_rsa.isSome = true := by native_decide

/--
RSA derives "not all" from "some students sleep".
-/
theorem rsa_derives_not_all_from_some_students :
    (someStudentsSleep_rsa.get someStudentsSleep_rsa_isSome).implicatureHolds = true := by
  native_decide

/--
"every student sleeps" via RSA.
-/
def everyStudentSleeps_rsa : Option RSAScalarResult :=
  rsaFromDerivation everyStudentSleeps

/--
everyStudentSleeps produces a result.
-/
theorem everyStudentSleeps_rsa_isSome :
    everyStudentSleeps_rsa.isSome = true := by native_decide

/--
"every" has no scalar implicature.

Since "every/all" is at the top of the scale, no stronger alternative exists.
-/
theorem rsa_every_no_implicature :
    (everyStudentSleeps_rsa.get everyStudentSleeps_rsa_isSome).implicatureHolds = false := by
  native_decide


/--
Get L1 probability for a specific world.
-/
def l1ProbForWorld (w : Fin 4) : ℚ :=
  RSA.Eval.getScore (l1 threePerson .some_) w

-- L1 scores for "some" (for reference).
#eval l1 threePerson .some_

/--
w1 > w3 (one vs all).
-/
theorem l1_w1_gt_w3 : l1ProbForWorld (w1 (n := 3)) > l1ProbForWorld (wAll (n := 3)) := by
  native_decide

/--
w2 > w3 (two vs all).
-/
theorem l1_w2_gt_w3 : l1ProbForWorld (w2 (n := 3)) > l1ProbForWorld (wAll (n := 3)) := by
  native_decide

/--
w1 = w2 (symmetry among "some but not all" worlds).
-/
theorem l1_w1_eq_w2 : l1ProbForWorld (w1 (n := 3)) = l1ProbForWorld (w2 (n := 3)) := by
  native_decide


end RSA.ScalarImplicatures


/-
# RSA ImplicatureTheory Instance

Implements the ImplicatureTheory interface for the RSA (Rational Speech Acts)
framework (Goodman & Frank 2016).

The RSA model currently handles:
- Simple sentences with scalar quantifiers ("some students sleep")
- Probabilistic implicature derivation: P(some_not_all) > P(all)

The current RSA formalization is incomplete -- it cannot represent:

1. Embedded contexts: The model uses a toy domain with 4 world states.
   There's no way to represent "No one ate some cookies" or other embeddings.

2. DE blocking: Without compositional semantics over sentence structure,
   context polarity (upward/downward entailing) cannot be modeled.

3. Task effects: The model has no notion of QUD (Question Under Discussion)
   or attention-based mechanisms that could explain task effects.

The `predictsDEBlocking := false` flag means "model incomplete"
not "RSA predicts no blocking". A full RSA model with compositional semantics
could potentially derive DE blocking through:
- Context-sensitive QUDs
- Compositional alternative generation
- Recursive pragmatic reasoning in embedded contexts

A complete RSA model would need:

1. Compositional RSA: RSA over sentence meanings, not just world labels
2. Structured utterance space: Sentences with operators, not just "some"/"all"
3. Context-sensitive literal semantics: L0 changes based on embedding
4. QUD manipulation: Different QUDs for different tasks

See: Bergen et al. (2016), Potts et al. (2016) for RSA extensions.

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

    For now, uses the pre-computed RSA results:
    - "some" → rsaSomeResult (implicature holds)
    - "all"/"every" → no implicature (top of scale) -/
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
        some { result := rsaSomeResult
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
  { result := rsaSomeResult
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
    .triggered := by native_decide

/-- RSA doesn't trigger implicature for "all" (top of scale) -/
theorem rsa_all_no_implicature :
    ImplicatureTheory.implicatureStatus (T := RSATheory) allRSA 0 =
    .absent := by native_decide

/-- Wrong position returns absent -/
theorem rsa_wrong_position_absent :
    ImplicatureTheory.implicatureStatus (T := RSATheory) someRSA 1 =
    .absent := by native_decide

end RSA
