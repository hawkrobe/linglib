/-
# Semantic Derivations

Interface between syntax and pragmatics via `SemDeriv` bundles.

## Main definitions

`ScalarOccurrence`, `SemDeriv`, `alternativeMeanings`, `alternativeForms`, `SemanticsProducer`

## Compositional derivation

The `SemDeriv` instances below derive their meanings from tree interpretation
(`interpTreeG`) rather than hand-assembling function applications. Each
derivation specifies a `Tree` and a `Lexicon`, and the meaning is computed
by the composition engine. Grounding theorems verify that tree interpretation
produces the same values as direct GQ application.

-/

import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Theories.Semantics.Montague.Basic
import Linglib.Theories.Semantics.Montague.Lexicon
import Linglib.Theories.Semantics.Lexical.Determiner.Quantifier
import Linglib.Theories.Semantics.Composition.Tree
import Linglib.Theories.Semantics.Alternatives.Lexical

namespace Semantics.Montague.Derivation

open Semantics.Montague
open Semantics.Montague
open Core.Tree
open Semantics.Composition.Tree
open Semantics.Montague.Variables
open Alternatives

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

open Semantics.Entailment.Polarity (ContextPolarity)

/-- Generate sentential alternatives by replacing scalar items -/
def alternativeMeanings {m : Model} [Semantics.Lexical.Determiner.Quantifier.FiniteModel m]
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

-- ════════════════════════════════════════════════════════════════════
-- § Tree-derived SemDerivs
-- ════════════════════════════════════════════════════════════════════

open ToyLexicon
open Semantics.Lexical.Determiner.Quantifier

/-- Lexicon for derivation trees, derived from `toyLexicon` via `SemLexicon.toLexicon`.
    Bare forms ("sleep", "laugh") are added for plural agreement contexts. -/
def derivLex : Lexicon toyModel :=
  fun word => match word with
  | "sleep" => some ⟨.e ⇒ .t, ToyLexicon.sleeps_sem⟩
  | "laugh" => some ⟨.e ⇒ .t, ToyLexicon.laughs_sem⟩
  | other => toyLexicon.toLexicon other

/-- Default assignment (closed sentences are independent of this choice). -/
def g₀ : Assignment toyModel := λ _ => .john

-- Trees

/-- `[S John sleeps]` — simple FA -/
def tree_johnSleeps : Tree Unit String :=
  .bin (.leaf "John") (.leaf "sleeps")

/-- `[S [DP some students] [1 [S t₁ sleep]]]` — QR -/
def tree_someStudentsSleep : Tree Unit String :=
  .bin
    (.bin (.leaf "some") (.leaf "students"))
    (.binder 1 (.bin (.tr 1) (.leaf "sleep")))

/-- `[S [DP every student] [1 [S t₁ sleeps]]]` — QR -/
def tree_everyStudentSleeps : Tree Unit String :=
  .bin
    (.bin (.leaf "every") (.leaf "student"))
    (.binder 1 (.bin (.tr 1) (.leaf "sleeps")))

/-- `[S [DP some students] [1 [S t₁ laugh]]]` — QR -/
def tree_someStudentsLaugh : Tree Unit String :=
  .bin
    (.bin (.leaf "some") (.leaf "students"))
    (.binder 1 (.bin (.tr 1) (.leaf "laugh")))

/-- `[S [DP every student] [1 [S t₁ laughs]]]` — QR -/
def tree_everyStudentLaughs : Tree Unit String :=
  .bin
    (.bin (.leaf "every") (.leaf "student"))
    (.binder 1 (.bin (.tr 1) (.leaf "laughs")))

-- Derivations: meanings derived from tree interpretation

def johnSleeps : SemDeriv toyModel :=
  { surface := ["John", "sleeps"]
  , ty := .t
  , meaning := (evalTree derivLex g₀ tree_johnSleeps).getD false
  , scalarItems := []
  }

def someStudentsSleep : SemDeriv toyModel :=
  { surface := ["some", "students", "sleep"]
  , ty := .t
  , meaning := (evalTree derivLex g₀ tree_someStudentsSleep).getD false
  , scalarItems := [⟨0, some_entry⟩]
  }

def everyStudentSleeps : SemDeriv toyModel :=
  { surface := ["every", "student", "sleeps"]
  , ty := .t
  , meaning := (evalTree derivLex g₀ tree_everyStudentSleeps).getD false
  , scalarItems := [⟨0, every_entry⟩]
  }

def someStudentsLaugh : SemDeriv toyModel :=
  { surface := ["some", "students", "laugh"]
  , ty := .t
  , meaning := (evalTree derivLex g₀ tree_someStudentsLaugh).getD false
  , scalarItems := [⟨0, some_entry⟩]
  }

def everyStudentLaughs : SemDeriv toyModel :=
  { surface := ["every", "student", "laughs"]
  , ty := .t
  , meaning := (evalTree derivLex g₀ tree_everyStudentLaughs).getD false
  , scalarItems := [⟨0, every_entry⟩]
  }

-- Truth-value verification

theorem johnSleeps_no_scalars : johnSleeps.hasScalarItems = false := rfl
theorem someStudentsSleep_has_scalars : someStudentsSleep.hasScalarItems = true := rfl
theorem someStudentsSleep_true : someStudentsSleep.meaning = true := by
  show (evalTree derivLex g₀ tree_someStudentsSleep).getD false = true; native_decide
theorem everyStudentSleeps_false : everyStudentSleeps.meaning = false := by
  show (evalTree derivLex g₀ tree_everyStudentSleeps).getD false = false; native_decide
theorem everyStudentLaughs_true : everyStudentLaughs.meaning = true := by
  show (evalTree derivLex g₀ tree_everyStudentLaughs).getD false = true; native_decide

-- Grounding: tree interpretation = direct GQ application

theorem johnSleeps_grounding :
    evalTree derivLex g₀ tree_johnSleeps =
    some (sleeps_sem john_sem) := by native_decide

theorem someStudentsSleep_grounding :
    evalTree derivLex g₀ tree_someStudentsSleep =
    some (some_sem toyModel student_sem sleeps_sem) := by native_decide

theorem everyStudentSleeps_grounding :
    evalTree derivLex g₀ tree_everyStudentSleeps =
    some (every_sem toyModel student_sem sleeps_sem) := by native_decide

/-- Syntax theory that can produce semantic derivations -/
class SemanticsProducer (SynDeriv : Type) (m : Model) where
  toDerivation : SynDeriv → SemDeriv m

end Semantics.Montague.Derivation

-- Backward compatibility aliases (excluding ContextPolarity which is now in Polarity.lean)
namespace Semantics.Montague.SemDeriv
  export Semantics.Montague.Derivation (ScalarOccurrence SemDeriv Derivation
    alternativeMeanings alternativeForms SemanticsProducer
    johnSleeps someStudentsSleep everyStudentSleeps someStudentsLaugh everyStudentLaughs)
end Semantics.Montague.SemDeriv
