import Linglib.Theories.Semantics.Focus.Particles
import Linglib.Core.Semantics.ContentLayer
import Linglib.Core.Discourse.InformationStructure

/-!
# English Focus-Sensitive Particles
@cite{rooth-1992} @cite{karttunen-peters-1979} @cite{francescotti-1995}

Lexical entries for English focus-sensitive particles, typed by
`Semantics.FocusParticles` theory types.
-/

namespace Fragments.English.FocusParticles

open Semantics.FocusParticles (EvenThreshold)
open Core.Semantics.ContentLayer (ContentLayer)
open Core.InformationStructure (FIPApplication)

/-- A focus-sensitive particle lexical entry. -/
structure Entry where
  /-- Surface form -/
  form : String
  /-- Does the particle affect truth conditions? -/
  truthFunctional : Bool
  /-- Which content layer carries the particle's contribution -/
  contributionLayer : ContentLayer
  /-- For scalar particles: threshold on alternatives exceeded -/
  threshold : Option EvenThreshold
  /-- FIP application type -/
  application : FIPApplication
  deriving Repr, BEq

/-- "even" — scalar focus particle.
    @cite{francescotti-1995}: not truth-functional (Equivalence Thesis),
    contributes via conventional implicature, felicity requires exceeding
    MOST alternatives in surprise. -/
def even_ : Entry :=
  { form := "even"
  , truthFunctional := false           -- Equivalence Thesis
  , contributionLayer := .implicature  -- conventional implicature
  , threshold := some .most            -- @cite{francescotti-1995}
  , application := .focusingAdverb }

/-- "only" — exclusive focus particle.
    Truth-functional (asserts exclusion of alternatives),
    prejacent is a presupposition. -/
def only_ : Entry :=
  { form := "only"
  , truthFunctional := true
  , contributionLayer := .atIssue
  , threshold := none
  , application := .focusingAdverb }

/-- "also"/"too" — additive focus particle.
    Presupposes existence of a true alternative. -/
def also : Entry :=
  { form := "also"
  , truthFunctional := false
  , contributionLayer := .presupposition
  , threshold := none
  , application := .focusingAdverb }

def allEntries : List Entry := [even_, only_, also]

-- ============================================================
-- Verification
-- ============================================================

/-- "even" does not affect truth conditions (Equivalence Thesis). -/
theorem even_not_truth_functional :
    even_.truthFunctional = false := rfl

/-- "even" contributes via conventional implicature. -/
theorem even_is_implicature :
    even_.contributionLayer = .implicature := rfl

/-- "even" uses Francescotti's "most" threshold. -/
theorem even_uses_most_threshold :
    even_.threshold = some .most := rfl

/-- "only" IS truth-functional (unlike "even"). -/
theorem only_is_truth_functional :
    only_.truthFunctional = true := rfl

/-- "even" and "only" differ on truth-functionality. -/
theorem even_only_differ_on_truth :
    even_.truthFunctional ≠ only_.truthFunctional := by decide

end Fragments.English.FocusParticles
