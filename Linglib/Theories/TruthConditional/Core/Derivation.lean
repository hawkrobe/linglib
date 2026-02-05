/-
# Semantic Derivations

Interface between syntax and pragmatics via `SemDeriv` bundles.

## Main definitions

`ScalarOccurrence`, `SemDeriv`, `alternativeMeanings`, `alternativeForms`, `SemanticsProducer`

## References

Montague (1973)
-/

import Linglib.Theories.TruthConditional.Core.Polarity
import Linglib.Theories.TruthConditional.Basic
import Linglib.Theories.TruthConditional.Core.Lexicon
import Linglib.Theories.TruthConditional.Determiner.Quantifier
import Linglib.Core.Scales

namespace TruthConditional.Core.Derivation

open TruthConditional
open TruthConditional.Core
open Core.Scales

/-- Scalar item occurrence in a derivation -/
structure ScalarOccurrence (m : Model) where
  position : Nat
  entry : SemLexEntry m

/-- Semantic derivation: output of compositional interpretation -/
structure SemDeriv (m : Model) where
  surface : List String
  ty : Ty
  meaning : m.interpTy ty
  scalarItems : List (ScalarOccurrence m) := []

abbrev Derivation := SemDeriv

def SemDeriv.sentence {m : Model} (d : SemDeriv m) : String :=
  " ".intercalate d.surface

def SemDeriv.hasScalarItems {m : Model} (d : SemDeriv m) : Bool :=
  !d.scalarItems.isEmpty

open TruthConditional.Core.Polarity (ContextPolarity)

/-- Generate sentential alternatives by replacing scalar items -/
def alternativeMeanings {m : Model} [Determiner.Quantifier.FiniteModel m]
    (d : SemDeriv m)
    (_ctx : ContextPolarity)
    : List (m.interpTy d.ty) :=
  []

/-- Get surface forms of scalar alternatives -/
def alternativeForms {m : Model} (d : SemDeriv m) (ctx : ContextPolarity)
    : List (List String) :=
  d.scalarItems.flatMap λ occ =>
    let alts := match ctx with
      | .upward => occ.entry.strongerAlternatives
      | .downward => []
      | .nonMonotonic => []
    alts.map λ altForm =>
      d.surface.set occ.position altForm

open ToyLexicon
open Determiner.Quantifier

def johnSleeps : SemDeriv toyModel :=
  { surface := ["John", "sleeps"]
  , ty := .t
  , meaning := sleeps_sem john_sem
  , scalarItems := []
  }

def someStudentsSleep : SemDeriv toyModel :=
  { surface := ["some", "students", "sleep"]
  , ty := .t
  , meaning := some_sem toyModel student_sem sleeps_sem
  , scalarItems := [⟨0, some_entry⟩]
  }

def everyStudentSleeps : SemDeriv toyModel :=
  { surface := ["every", "student", "sleeps"]
  , ty := .t
  , meaning := every_sem toyModel student_sem sleeps_sem
  , scalarItems := [⟨0, every_entry⟩]
  }

def someStudentsLaugh : SemDeriv toyModel :=
  { surface := ["some", "students", "laugh"]
  , ty := .t
  , meaning := some_sem toyModel student_sem laughs_sem
  , scalarItems := [⟨0, some_entry⟩]
  }

def everyStudentLaughs : SemDeriv toyModel :=
  { surface := ["every", "student", "laughs"]
  , ty := .t
  , meaning := every_sem toyModel student_sem laughs_sem
  , scalarItems := [⟨0, every_entry⟩]
  }

theorem johnSleeps_no_scalars : johnSleeps.hasScalarItems = false := rfl
theorem someStudentsSleep_has_scalars : someStudentsSleep.hasScalarItems = true := rfl
theorem someStudentsSleep_true : someStudentsSleep.meaning = true := rfl
theorem everyStudentSleeps_false : everyStudentSleeps.meaning = false := rfl
theorem everyStudentLaughs_true : everyStudentLaughs.meaning = true := rfl

/-- Syntax theory that can produce semantic derivations -/
class SemanticsProducer (SynDeriv : Type) (m : Model) where
  toDerivation : SynDeriv → SemDeriv m

end TruthConditional.Core.Derivation

-- Backward compatibility aliases (excluding ContextPolarity which is now in Polarity.lean)
namespace TruthConditional.SemDeriv
  export TruthConditional.Core.Derivation (ScalarOccurrence SemDeriv Derivation
    alternativeMeanings alternativeForms SemanticsProducer
    johnSleeps someStudentsSleep everyStudentSleeps someStudentsLaugh everyStudentLaughs)
end TruthConditional.SemDeriv
