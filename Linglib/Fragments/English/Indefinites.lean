import Linglib.Core.IndefiniteType

/-!
# English Indefinite Pronouns
@cite{haspelmath-1997}

English *some-* is the prototypical unmarked indefinite (type i): it
can appear in all three specificity contexts (specific known, specific
unknown, non-specific). This yields the AAA syncretism pattern.
-/

set_option autoImplicit false

namespace Fragments.English.Indefinites

open Core.IndefiniteType

/-- English *some-*: unmarked (type i), all three functions (AAA).
    @cite{haspelmath-1997}, @cite{bubnov-2026} Table 1. -/
def some_ : IndefiniteEntry where
  language := "English"
  form := "some-"
  gloss := "some"
  specType := .unmarked
  allowsSK := true; allowsSU := true; allowsNS := true
  source := "Haspelmath 1997"

theorem some_consistent : some_.distributionConsistent = true := rfl

end Fragments.English.Indefinites
