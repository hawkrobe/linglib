import Linglib.Features.IndefiniteType

/-!
# English Indefinite Pronouns
@cite{haspelmath-1997}

English *some-* is the prototypical unmarked indefinite (type i): it
can appear in all three specificity contexts (specific known, specific
unknown, non-specific). This yields the AAA syncretism pattern.

This file follows the same shape as the other `Fragments/{Lang}/Indefinites.lean`
siblings (Russian, German, Yakut, Latin, Kannada): per-form entries +
a `paradigm` aggregator + a single `paradigm_consistent` claim.
-/

set_option autoImplicit false

namespace Fragments.English.Indefinites

open Features.IndefiniteType

/-- English *some-*: unmarked (type i), all three functions (AAA).
    @cite{haspelmath-1997}, @cite{bubnov-2026} Table 1. -/
def someEntry : IndefiniteEntry where
  language := "English"
  form := "some-"
  gloss := "some"
  specType := .unmarked
  allowsSK := true
  allowsSU := true
  allowsNS := true
  source := "Haspelmath 1997"

/-- The full English indefinite paradigm. -/
def paradigm : List IndefiniteEntry := [someEntry]

theorem paradigm_consistent : paradigm.all (·.distributionConsistent) := by decide

end Fragments.English.Indefinites
