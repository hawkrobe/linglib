/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Language.ForbiddenPairs
import Linglib.Phonology.Harmony.Basic

/-!
# Harmony patterns are tier-based strictly local

The bridge between the pattern layer and the consensus subregular mechanism
([aksenova-rawski-graf-heinz-2024]): a harmony pattern's surface predicate is
a TSL₂ language by construction. The tier is the pattern's
participating-plus-opaque projection; the banned bigrams are the incompatible
pairs. Strictly local grammars cannot express harmony (unbounded distance) and
strictly piecewise grammars cannot express blocking; the tier-based class
captures both, which is why it is the chapter's consensus characterization.

## Main results

* `Pattern.harmonic_iff_mem_tsl`: harmonicity is membership in the
  forbidden-pairs TSL₂ grammar over the pattern's tier.
-/

namespace Phonology.Harmony

open Subregular

variable {α : Type*} {V : Type*}

/-- **Harmony is TSL₂ by construction** ([aksenova-rawski-graf-heinz-2024]):
    a pattern's surface harmonicity is membership in the tier-based strictly
    2-local grammar whose tier is `Pattern.OnTier` and whose banned bigrams
    are the incompatible pairs. -/
theorem Pattern.harmonic_iff_mem_tsl [DecidableEq V]
    (p : Pattern α V) (w : List α) :
    p.Harmonic w ↔
      w ∈ (TSLGrammar.ofForbiddenPairs
        (R := fun a b => ¬ p.Compatible a b) p.OnTier).lang := by
  rw [mem_ofForbiddenPairs_lang_iff_filter_isChain]
  unfold Pattern.Harmonic Pattern.tier
  simp only [not_not]

end Phonology.Harmony
