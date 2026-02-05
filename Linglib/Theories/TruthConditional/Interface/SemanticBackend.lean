/-
# Montague Semantics as a SemanticBackend

Connects Montague semantics to the RSA pragmatics interface via φ agreement function.

## Main definitions

`MontagueSentence`, `ToyWorld`, `evaluate`, `montaguePhi`

## References

Montague (1973), Goodman & Stuhlmüller (2013)
-/

import Linglib.Theories.TruthConditional.Basic

namespace TruthConditional.Interface.SemanticBackend

open TruthConditional

/-- Sentence with its denotation -/
structure MontagueSentence where
  form : String
  meaning : toyModel.interpTy .t

/-- World state -/
inductive ToyWorld where
  | actual
  deriving DecidableEq, Repr

/-- Evaluate a sentence's truth in a world -/
def evaluate (s : MontagueSentence) (w : ToyWorld) : Bool :=
  match w with
  | .actual => s.meaning

/-- Semantic agreement function: 1.0 if true, 0.0 if false -/
def montaguePhi (s : MontagueSentence) (w : ToyWorld) : Float :=
  if evaluate s w then 1.0 else 0.0

open ToyLexicon in
def johnSleepsSent : MontagueSentence :=
  { form := "John sleeps"
  , meaning := apply sleeps_sem john_sem
  }

open ToyLexicon in
def marySleepsSent : MontagueSentence :=
  { form := "Mary sleeps"
  , meaning := apply sleeps_sem mary_sem
  }

open ToyLexicon in
def johnSeesMary : MontagueSentence :=
  { form := "John sees Mary"
  , meaning := apply (apply sees_sem mary_sem) john_sem
  }

theorem john_sleeps_phi : montaguePhi johnSleepsSent .actual = 1.0 := rfl
theorem mary_sleeps_phi : montaguePhi marySleepsSent .actual = 0.0 := rfl
theorem john_sees_mary_phi : montaguePhi johnSeesMary .actual = 1.0 := rfl

end TruthConditional.Interface.SemanticBackend

-- Backward compatibility (original namespace was just Montague)
namespace TruthConditional
  export TruthConditional.Interface.SemanticBackend (MontagueSentence ToyWorld evaluate montaguePhi
    johnSleepsSent marySleepsSent johnSeesMary)
end TruthConditional
