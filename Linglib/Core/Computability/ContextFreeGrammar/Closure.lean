import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.DFA
import Linglib.Core.Computability.ContextFreeGrammar.Map
import Linglib.Core.Computability.ContextFreeGrammar.InterRegular

/-!
# Closure Properties of Context-Free Languages

CFLs are closed under several operations relevant to non-context-freeness
arguments: string homomorphism, intersection with regular languages, and
reversal. Mathlib (as of this writing) proves only `Language.IsContextFree.reverse`;
homomorphism closure is proved in `Map.lean` (`Language.IsContextFree.stringMap`)
and intersection-with-regular closure is proved in `InterRegular.lean`
(`Language.IsContextFree.inter_isRegular`, via the Bar-Hillel triple-product).
This file owns the contrapositive corollaries that consume both.

## What this file enables

The contrapositive corollaries (the *useful* direction for non-CF arguments)
ARE proved here:

* `Language.not_isContextFree_of_stringMap_not` — if a homomorphic image is
  not context-free, neither is the source.
* `Language.not_isContextFree_of_inter_regular_not` — if `L ∩ R` is not
  context-free for some regular `R`, neither is `L`.
* `Language.not_isContextFree_via_witness` — the packaged [shieber-1985]
  proof schema: argue `L` is non-CF by mapping it through a homomorphism,
  intersecting with a regular filter, and exhibiting a non-CF witness in
  the result. Used by Swiss German non-CF (Shieber 1985), Dutch non-CF
  (Huybregts 1976 / Bresnan et al. 1982), and any future natural-language
  non-CF argument.
-/

-- ============================================================================
-- Contrapositive corollaries (the useful direction for non-CF arguments)
-- ============================================================================
-- The closure theorems themselves: `Language.IsContextFree.stringMap` lives in
-- `Map.lean`; `Language.IsContextFree.inter_isRegular` lives in `InterRegular.lean`.

/-- Contrapositive of homomorphism closure: if the homomorphic image of `L`
    is not context-free, then `L` is not context-free. -/
theorem Language.not_isContextFree_of_stringMap_not {α β : Type*}
    (f : α → List β) {L : Language α}
    (hImg : ¬ (Language.stringMap f L).IsContextFree) :
    ¬ L.IsContextFree :=
  fun hL => hImg (Language.IsContextFree.stringMap f hL)

/-- Contrapositive of regular-intersection closure: if `L ∩ R` is not
    context-free for some regular `R`, then `L` is not context-free. -/
theorem Language.not_isContextFree_of_inter_regular_not {α : Type*}
    {L R : Language α}
    (hR : R.IsRegular) (hInter : ¬ (L ⊓ R).IsContextFree) :
    ¬ L.IsContextFree :=
  fun hL => hInter (Language.IsContextFree.inter_isRegular hL hR)

/-- **The Shieber-style non-context-freeness proof schema.** If the
    homomorphic image of `L` intersected with a regular language `R`
    contains a non-context-free witness, then `L` is not context-free.

    This is the proof shape used by [shieber-1985] for Swiss German,
    closely paralleled by [huybregts-1976] for Dutch, and applicable
    to any future natural-language non-CF argument that proceeds via
    homomorphic abstraction (e.g., case-marker-only projection) plus
    regular filtering (e.g., case-sorted clause shape). -/
theorem Language.not_isContextFree_via_witness {α β : Type*}
    (f : α → List β) (R : Language β) {L : Language α}
    (hR : R.IsRegular)
    (hWitness : ¬ (Language.stringMap f L ⊓ R).IsContextFree) :
    ¬ L.IsContextFree :=
  fun hL =>
    hWitness ((Language.IsContextFree.stringMap f hL).inter_isRegular hR)
