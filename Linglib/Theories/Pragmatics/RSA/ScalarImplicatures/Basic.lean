import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Semantics.Montague.Lexicon
import Mathlib.Data.Rat.Defs
import Linglib.Core.Interface

/-!
# RSA Scalar Implicatures from Semantic Derivations
@cite{bergen-levy-goodman-2016} @cite{frank-goodman-2012} @cite{goodman-frank-2016}

Connects RSA pragmatics to the syntax-semantics pipeline.
Any syntax theory (CCG, HPSG, Minimalism) that produces a `Derivation`
can feed into RSA for probabilistic scalar implicature derivation.

## Architecture

```
CCG/HPSG/Minimalism → Derivation → rsaFromDerivation → RSA L1 interpretation
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


/-- Check if scalar items include a "some" quantifier. -/
def hasSomeQuantifier {m : Model} (items : List (SemLexEntry m)) : Bool :=
  items.any λ entry =>
    match entry.scaleMembership with
    | some (.quantifier .some_) => true
    | _ => false

/-- Check if scalar items include an "all/every" quantifier. -/
def hasAllQuantifier {m : Model} (items : List (SemLexEntry m)) : Bool :=
  items.any λ entry =>
    match entry.scaleMembership with
    | some (.quantifier .all) => true
    | _ => false


end RSA.ScalarImplicatures


