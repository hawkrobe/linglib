import Linglib.Theories.Semantics.Focus.Particles
import Linglib.Core.Semantics.ContentLayer
import Linglib.Features.InformationStructure

/-!
# English Focus-Sensitive Particles
@cite{rooth-1992} @cite{karttunen-peters-1979} @cite{francescotti-1995}

Lexical entries for English focus-sensitive particles, typed by
`Semantics.FocusParticles` theory types.
-/

namespace Fragments.English.FocusParticles

open Semantics.FocusParticles (EvenThreshold)
open Core.Semantics.ContentLayer (ContentLayer)
open Features.InformationStructure (FIPApplication ExclusionVariety)

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

/-- "too" — additive focus particle, sentence-final.
    @cite{thomas-2026}: felicity requires existence of an antecedent
    fact and a contextually relevant question RQ such that the Antecedent,
    Conjunction, and Prejacent Conditions (Def. 64) all hold.
    Subsumes @cite{heim-1992}'s individual-based presupposition as a
    special case of the standard focus-alternative use.
    Unlike sentence-initial "also", subject to the full Prejacent
    Condition including maximality (Def. 64c.ii). -/
def too_ : Entry :=
  { form := "too"
  , truthFunctional := false
  , contributionLayer := .presupposition
  , threshold := none
  , application := .focusingAdverb }

/-- "either" — negative-polarity additive focus particle.
    @cite{rullmann-2003}: complementary distribution with "too" in
    polarity contexts. @cite{thomas-2026} defers full characterization
    to future work (footnote 9); felicity conditions likely share the
    core Antecedent/Conjunction structure with additional polarity
    constraints. See @cite{ahn-2015} for a Boolean algebra account. -/
def either_ : Entry :=
  { form := "either"
  , truthFunctional := false
  , contributionLayer := .presupposition
  , threshold := none
  , application := .focusingAdverb }

/-- "just" — domain-widening focus particle.
    @cite{deo-thomas-2025}: *just* signals that the CQ is the widest
    answerable construal of an underspecified question. Unlike *only*,
    *just* does not conventionally encode exclusion — exhaustification
    arises as a mandatory Quantity implicature.
    Not truth-functional: the at-issue content is simply the prejacent.
    The CQ-signaling component is backgrounded (fn. 22 of the paper
    leaves the precise status as presupposition vs conventional implicature
    open for future research). -/
def just_ : Entry :=
  { form := "just"
  , truthFunctional := false
  , contributionLayer := .presupposition
  , threshold := none
  , application := .focusingAdverb
  , exclusionVariety := none }

def allEntries : List Entry := [even_, only_, just_, also, too_, either_]

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

/-- "too" is additive, not truth-functional — like "also". -/
theorem too_not_truth_functional :
    too_.truthFunctional = false := rfl

/-- "too" contributes via presupposition. -/
theorem too_is_presuppositional :
    too_.contributionLayer = .presupposition := rfl

/-- "too" and "also" have the same semantic profile. -/
theorem too_matches_also :
    too_.truthFunctional = also.truthFunctional ∧
    too_.contributionLayer = also.contributionLayer ∧
    too_.threshold = also.threshold := ⟨rfl, rfl, rfl⟩

/-- "either" is additive, not truth-functional. -/
theorem either_not_truth_functional :
    either_.truthFunctional = false := rfl

/-- "either" and "too" differ only in form (and polarity, which is
not captured in the Entry type — polarity licensing is in
`Theories.Pragmatics.Particles.Additive`). -/
theorem either_same_profile_as_too :
    either_.truthFunctional = too_.truthFunctional ∧
    either_.contributionLayer = too_.contributionLayer := ⟨rfl, rfl⟩

-- ============================================================
-- "just" (@cite{deo-thomas-2025})
-- ============================================================

/-- "just" does not affect truth conditions (prejacent is the at-issue content). -/
theorem just_not_truth_functional :
    just_.truthFunctional = false := rfl

/-- "just" is not an exclusive — no conventional exclusion.
    Exhaustification arises pragmatically via mandatory Quantity implicature
    (@cite{deo-thomas-2025} §4.1). -/
theorem just_not_exclusive :
    just_.exclusionVariety = none := rfl

/-- "just" and "only" differ on truth-functionality and exclusion.
    This is the core of @cite{deo-thomas-2025}'s argument: *just* is not
    a variant of *only* — it has a fundamentally different discourse function.
    *only* conventionally excludes alternatives; *just* widens the question. -/
theorem just_only_differ :
    just_.truthFunctional ≠ only_.truthFunctional ∧
    just_.exclusionVariety ≠ only_.exclusionVariety := by
  exact ⟨by decide, by decide⟩

/-- "just" and "even" are both non-truth-functional but differ in content layer.
    *even* contributes via conventional implicature (likelihood presupposition);
    *just* contributes via presupposition (CQ-signaling). -/
theorem just_even_same_truth_diff_layer :
    just_.truthFunctional = even_.truthFunctional ∧
    just_.contributionLayer ≠ even_.contributionLayer := by
  exact ⟨rfl, by decide⟩

end Fragments.English.FocusParticles
