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
open Core.InformationStructure (FIPApplication ExclusionVariety)

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
  /-- Exclusion variety (@cite{umbach-2004} §2.3): *only* excludes
      additional alternatives ("no one *in addition to* X"), while
      contrastive focus excludes by substitution ("no one *instead of* X").
      `none` for non-exclusive particles like *even* and *also*. -/
  exclusionVariety : Option ExclusionVariety := none
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
    prejacent is a presupposition.
    @cite{umbach-2004} §2.3: *only* excludes additional alternatives — it
    excludes the possibility that someone *in addition to* the focused item
    satisfies the predicate. -/
def only_ : Entry :=
  { form := "only"
  , truthFunctional := true
  , contributionLayer := .atIssue
  , threshold := none
  , application := .focusingAdverb
  , exclusionVariety := some .additional }

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

/-- "only" is an exclusive particle (additional exclusion variety).
    @cite{umbach-2004} §2.3: excludes alternatives *in addition to* X. -/
theorem only_excludes_additional :
    only_.exclusionVariety = some .additional := rfl

/-- "also" is additive, not exclusive — no exclusion variety. -/
theorem also_not_exclusive :
    also.exclusionVariety = none := rfl

/-- "even" is scalar, not exclusive — no exclusion variety. -/
theorem even_not_exclusive :
    even_.exclusionVariety = none := rfl

end Fragments.English.FocusParticles
