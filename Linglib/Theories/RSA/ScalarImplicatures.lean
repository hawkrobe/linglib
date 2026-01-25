/-
# RSA Scalar Implicatures from Semantic Derivations

Connects RSA pragmatics to the syntax-semantics pipeline.
Any syntax theory (CCG, HPSG, Minimalism) that produces a `SemDeriv.Derivation`
can feed into RSA for probabilistic scalar implicature derivation.

## Architecture

```
CCG/HPSG/Minimalism → SemDeriv.Derivation → rsaFromDerivation → RSA L1 interpretation
```

## Key Results

- `rsa_some_not_all`: RSA derives P(some_not_all | "some") > P(all | "some")
- `rsa_derives_not_all`: Using derivation interface, RSA prefers non-all worlds
-/

import Linglib.Theories.RSA.Basic
import Linglib.Theories.RSA.GoodmanStuhlmuller2013
import Linglib.Theories.Montague.SemDerivation
import Linglib.Core.Frac

namespace RSA.ScalarImplicatures

open RSA RSA.Scalar Frac
open Montague
open Montague.SemDeriv
open Montague.Lexicon

-- ============================================================================
-- PART 1: World Type for Scalar Implicature
-- ============================================================================

/-
## Connecting Derivations to RSA Worlds

For scalar implicatures with quantifiers, the relevant distinction is:
- `none`: No individuals satisfy the predicate
- `some`: Some but not all satisfy
- `all`: All individuals satisfy

RSA reasons about these worlds probabilistically.
-/

/-- World states for scalar implicature reasoning -/
inductive ScalarWorld where
  | none  -- No one (0)
  | some  -- Some but not all (1 or 2 out of 3)
  | all   -- All (3 out of 3)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Convert RSA CookieWorld to ScalarWorld (coarser partition) -/
def cookieToScalar : CookieWorld → ScalarWorld
  | .w0 => .none
  | .w1 => .some
  | .w2 => .some
  | .w3 => .all

-- ============================================================================
-- PART 2: RSA Result Structure
-- ============================================================================

/--
RSA scalar implicature result.

Records the L1 probabilities for different world types,
showing how RSA derives the implicature probabilistically.
-/
structure RSAScalarResult where
  /-- The utterance analyzed -/
  utterance : String
  /-- L1 probability mass on "some but not all" worlds -/
  probSomeNotAll : Frac
  /-- L1 probability mass on "all" world -/
  probAll : Frac
  /-- Does the implicature hold? (probSomeNotAll > probAll) -/
  implicatureHolds : Bool
  deriving Repr

/--
Compute RSA result for "some" utterance.

Uses the L1 scores from RSA.Basic to get the distribution over worlds.
-/
def rsaSomeResult : RSAScalarResult :=
  let l1_scores := L1_scores ScalarDomain .some_
  -- P(some_not_all) = P(w1) + P(w2)
  let p_w1 := getScore l1_scores .w1
  let p_w2 := getScore l1_scores .w2
  let p_some_not_all := Frac.add p_w1 p_w2
  -- P(all) = P(w3)
  let p_all := getScore l1_scores .w3
  { utterance := "some"
  , probSomeNotAll := p_some_not_all
  , probAll := p_all
  , implicatureHolds := p_some_not_all > p_all
  }

/--
**RSA Scalar Implicature Theorem**

RSA assigns higher probability to "some but not all" worlds than to "all" world.
This is the RSA counterpart to NeoGricean's categorical "not all" implicature.
-/
theorem rsa_some_not_all :
    rsaSomeResult.implicatureHolds = true := by
  native_decide

/--
**Theorem: P(some_not_all) > P(all) explicitly**
-/
theorem rsa_some_not_all_explicit :
    rsaSomeResult.probSomeNotAll > rsaSomeResult.probAll := by
  native_decide

-- ============================================================================
-- PART 3: Bridge from SemDeriv.Derivation
-- ============================================================================

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

**Syntax-agnostic**: Works with CCG, HPSG, Minimalism, or any theory
that implements the SemDeriv interface.
-/
def rsaFromDerivation {m : Model} (d : Derivation m) : Option RSAScalarResult :=
  if hasSomeQuantifier d then
    some rsaSomeResult
  else if hasAllQuantifier d then
    -- "all" doesn't generate an implicature (top of scale)
    let l1_scores := L1_scores ScalarDomain .all
    let p_all := getScore l1_scores .w3
    some { utterance := "all"
         , probSomeNotAll := Frac.zero
         , probAll := p_all
         , implicatureHolds := false
         }
  else
    none

-- ============================================================================
-- PART 4: Examples Using Derivations
-- ============================================================================

/--
**Example: "some students sleep" via RSA**
-/
def someStudentsSleep_rsa : Option RSAScalarResult :=
  rsaFromDerivation someStudentsSleep

/--
**Theorem: someStudentsSleep produces a result**
-/
theorem someStudentsSleep_rsa_isSome :
    someStudentsSleep_rsa.isSome = true := by native_decide

/--
**Theorem: RSA derives "not all" from "some students sleep"**
-/
theorem rsa_derives_not_all_from_some_students :
    (someStudentsSleep_rsa.get someStudentsSleep_rsa_isSome).implicatureHolds = true := by
  native_decide

/--
**Example: "every student sleeps" via RSA**
-/
def everyStudentSleeps_rsa : Option RSAScalarResult :=
  rsaFromDerivation everyStudentSleeps

/--
**Theorem: everyStudentSleeps produces a result**
-/
theorem everyStudentSleeps_rsa_isSome :
    everyStudentSleeps_rsa.isSome = true := by native_decide

/--
**Theorem: "every" has no scalar implicature**

Since "every/all" is at the top of the scale, no stronger alternative exists.
-/
theorem rsa_every_no_implicature :
    (everyStudentSleeps_rsa.get everyStudentSleeps_rsa_isSome).implicatureHolds = false := by
  native_decide

-- ============================================================================
-- PART 5: Quantitative Comparison
-- ============================================================================

/--
Get L1 probability for a specific world.
-/
def l1ProbForWorld (w : CookieWorld) : Frac :=
  getScore (L1_scores ScalarDomain .some_) w

-- L1 scores for "some" (for reference).
#eval L1_scores ScalarDomain .some_

/--
**Theorem: w1 > w3 (one vs all)**
-/
theorem l1_w1_gt_w3 : l1ProbForWorld .w1 > l1ProbForWorld .w3 := by
  native_decide

/--
**Theorem: w2 > w3 (two vs all)**
-/
theorem l1_w2_gt_w3 : l1ProbForWorld .w2 > l1ProbForWorld .w3 := by
  native_decide

/--
**Theorem: w1 = w2 (symmetry among "some but not all" worlds)**
-/
theorem l1_w1_eq_w2 : Frac.eq (l1ProbForWorld .w1) (l1ProbForWorld .w2) := by
  native_decide

-- ============================================================================
-- PART 6: Summary
-- ============================================================================

/-
## What This Module Provides

### Types
- `ScalarWorld`: Coarse partition (none/some/all)
- `RSAScalarResult`: RSA analysis result with probabilities

### Key Functions
- `rsaFromDerivation`: Main pipeline function (syntax-agnostic)
- `rsaSomeResult`: RSA analysis for "some" utterance
- `hasSomeQuantifier`: Check for "some" in derivation
- `hasAllQuantifier`: Check for "all" in derivation

### Key Theorems
- `rsa_some_not_all`: RSA implicature holds for "some"
- `rsa_some_not_all_explicit`: P(some_not_all) > P(all) directly
- `rsa_derives_not_all_from_some_students`: Pipeline works end-to-end
- `rsa_every_no_implicature`: Top of scale has no SI
- `l1_w1_gt_w3`, `l1_w2_gt_w3`: Individual world comparisons

### Architecture

```
SemDeriv.Derivation (syntax-agnostic)
        │
        ▼
rsaFromDerivation
        │
        ▼
RSAScalarResult (probabilistic implicature)
        │
        ├── probSomeNotAll: combined probability for "some but not all" worlds
        ├── probAll: probability for "all" world
        └── implicatureHolds: probSomeNotAll > probAll
```

### Connection to NeoGricean

| NeoGricean | RSA |
|------------|-----|
| ¬Bel_S(all) | P_L1(w3) < P_L1(w1) + P_L1(w2) |
| Bel_S(¬all) | P_L1(w1,w2) ≫ P_L1(w3) |
| Categorical "not all" | Probabilistic preference for non-all worlds |
-/

end RSA.ScalarImplicatures
