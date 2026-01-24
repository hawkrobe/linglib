/-
# Semantic Derivations

The interface between syntax and pragmatics. A `Derivation` bundles:
- Surface form (the words)
- Semantic type and meaning
- Scalar item positions (for alternative generation)

## Design Principle

This is what pragmatics needs from syntax. Any syntax theory (CCG, HPSG,
Minimalism) can produce a `Derivation`. Pragmatics imports this module,
not specific syntax theories.

```
Syntax Theory → Derivation → Pragmatics (NeoGricean, RSA)
```
-/

import Linglib.Theories.Montague.Basic
import Linglib.Theories.Montague.Lexicon
import Linglib.Theories.Montague.Quantifiers
import Linglib.Theories.Montague.Scales

namespace Montague.SemDeriv

open Montague
open Montague.Lexicon
open Montague.Scales

-- ============================================================================
-- Scalar Item Position
-- ============================================================================

/--
A scalar item occurrence in a derivation.
Records the position and the lexical entry (which includes scale membership).
-/
structure ScalarOccurrence (m : Model) where
  position : Nat              -- word index in the sentence
  entry : SemLexEntry m       -- the lexical entry (has scale info)

-- ============================================================================
-- Semantic Derivation
-- ============================================================================

/--
A semantic derivation: what pragmatics needs from syntax.

This is the output of any compositional semantic interpretation,
regardless of which syntax theory produced it.
-/
structure Derivation (m : Model) where
  /-- The surface form (list of words) -/
  surface : List String
  /-- The result semantic type -/
  ty : Ty
  /-- The compositionally derived meaning -/
  meaning : m.interpTy ty
  /-- Positions of scalar items (for alternative generation) -/
  scalarItems : List (ScalarOccurrence m) := []

/-- Get the sentence as a string -/
def Derivation.sentence {m : Model} (d : Derivation m) : String :=
  " ".intercalate d.surface

/-- Check if derivation contains scalar items -/
def Derivation.hasScalarItems {m : Model} (d : Derivation m) : Bool :=
  !d.scalarItems.isEmpty

-- ============================================================================
-- Alternative Generation
-- ============================================================================

/--
Context polarity for alternative computation.
In downward-entailing contexts, scales reverse.
-/
inductive ContextPolarity where
  | upward    -- Standard: stronger alternatives
  | downward  -- DE: weaker alternatives (scale reversal)
  deriving DecidableEq, Repr

/--
Generate a sentential alternative by replacing a scalar item.
Returns the alternative meaning (same type as original).

For now, this is a simplified version that just returns the
stronger/weaker alternatives' meanings. A full implementation
would reconstruct the entire derivation with the substituted item.
-/
def alternativeMeanings {m : Model} [Quantifiers.FiniteModel m]
    (d : Derivation m)
    (_ctx : ContextPolarity)
    : List (m.interpTy d.ty) :=
  -- For a proper implementation, we'd need to:
  -- 1. For each scalar item in d.scalarItems
  -- 2. Get its alternatives (stronger in UE, weaker in DE)
  -- 3. Recompute the sentence meaning with substituted item
  -- For now, return empty (placeholder for full implementation)
  []

/--
Get the forms of scalar alternatives (for display/debugging).
-/
def alternativeForms {m : Model} (d : Derivation m) (ctx : ContextPolarity)
    : List (List String) :=
  d.scalarItems.flatMap fun occ =>
    let alts := match ctx with
      | .upward => occ.entry.strongerAlternatives
      | .downward =>
        -- For DE, we'd use weakerAlternatives
        -- For now, just return empty since we don't have that function yet
        []
    alts.map fun altForm =>
      d.surface.set occ.position altForm

-- ============================================================================
-- Toy Model Examples
-- ============================================================================

open ToyLexicon
open Quantifiers

/-- "John sleeps" -/
def johnSleeps : Derivation toyModel :=
  { surface := ["John", "sleeps"]
  , ty := .t
  , meaning := sleeps_sem john_sem
  , scalarItems := []  -- no scalar items
  }

/-- "Some students sleep" (with scalar item) -/
def someStudentsSleep : Derivation toyModel :=
  { surface := ["some", "students", "sleep"]
  , ty := .t
  , meaning := some_sem toyModel student_sem sleeps_sem
  , scalarItems := [⟨0, some_entry⟩]  -- "some" at position 0
  }

/-- "Every student sleeps" (with scalar item) -/
def everyStudentSleeps : Derivation toyModel :=
  { surface := ["every", "student", "sleeps"]
  , ty := .t
  , meaning := every_sem toyModel student_sem sleeps_sem
  , scalarItems := [⟨0, every_entry⟩]  -- "every" at position 0
  }

/-- "Some students laugh" -/
def someStudentsLaugh : Derivation toyModel :=
  { surface := ["some", "students", "laugh"]
  , ty := .t
  , meaning := some_sem toyModel student_sem laughs_sem
  , scalarItems := [⟨0, some_entry⟩]
  }

/-- "Every student laughs" -/
def everyStudentLaughs : Derivation toyModel :=
  { surface := ["every", "student", "laughs"]
  , ty := .t
  , meaning := every_sem toyModel student_sem laughs_sem
  , scalarItems := [⟨0, every_entry⟩]
  }

-- ============================================================================
-- Theorems
-- ============================================================================

/-- "John sleeps" has no scalar items -/
theorem johnSleeps_no_scalars :
    johnSleeps.hasScalarItems = false := rfl

/-- "Some students sleep" has scalar items -/
theorem someStudentsSleep_has_scalars :
    someStudentsSleep.hasScalarItems = true := rfl

/-- "Some students sleep" is true (John is a student and sleeps) -/
theorem someStudentsSleep_true :
    someStudentsSleep.meaning = true := rfl

/-- "Every student sleeps" is false (Mary is a student but doesn't sleep) -/
theorem everyStudentSleeps_false :
    everyStudentSleeps.meaning = false := rfl

/-- "Every student laughs" is true (both John and Mary laugh) -/
theorem everyStudentLaughs_true :
    everyStudentLaughs.meaning = true := rfl

-- ============================================================================
-- Interface for Syntax Theories
-- ============================================================================

/--
A syntax theory that can produce semantic derivations.

Any theory implementing this can feed into pragmatics.
-/
class SemanticsProducer (SynDeriv : Type) (m : Model) where
  /-- Convert a syntactic derivation to a semantic derivation -/
  toDerivation : SynDeriv → Derivation m

/-
## Usage

To make a syntax theory work with pragmatics:

1. Define your derivation type (e.g., `CCG.DerivStep`)
2. Implement `SemanticsProducer`:
   ```lean
   instance : SemanticsProducer CCG.DerivStep toyModel where
     toDerivation d := ...
   ```
3. Pragmatics can then work with any syntax theory uniformly
-/

end Montague.SemDeriv
