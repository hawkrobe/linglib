import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.DFA
import Linglib.Core.StringHom
import Linglib.Core.Computability.ContextFreeGrammar.Map

/-!
# Closure Properties of Context-Free Languages

CFLs are closed under several operations relevant to non-context-freeness
arguments: string homomorphism, intersection with regular languages, and
reversal. Mathlib (as of this writing) proves only `Language.IsContextFree.reverse`;
homomorphism closure is proved in `Map.lean` (`Language.IsContextFree.stringMap`),
and intersection-with-regular closure remains as an `axiom` here, pending
in-house proof or upstream contribution to mathlib.

## What this file enables

The contrapositive corollaries (the *useful* direction for non-CF arguments)
ARE proved here:

* `Language.not_isContextFree_of_stringMap_not` — if a homomorphic image is
  not context-free, neither is the source.
* `Language.not_isContextFree_of_inter_regular_not` — if `L ∩ R` is not
  context-free for some regular `R`, neither is `L`.
* `Language.not_isContextFree_via_witness` — the packaged @cite{shieber-1985}
  proof schema: argue `L` is non-CF by mapping it through a homomorphism,
  intersecting with a regular filter, and exhibiting a non-CF witness in
  the result. Used by Swiss German non-CF (Shieber 1985), Dutch non-CF
  (Huybregts 1976 / Bresnan et al. 1982), and any future natural-language
  non-CF argument.

## Proof obligations (deferred)

The remaining axiom admits a standard textbook construction:

* **Regular-intersection closure** (Bar-Hillel, Perles & Shamir 1961;
  Hopcroft–Ullman 1979 Thm 6.5): triple-product construction. Pair each
  CFG nonterminal `A` with a pair of DFA states `(p, q)` to track that the
  yield of `A` drives the DFA from `p` to `q`.

Either constructed in linglib or contributed upstream to mathlib (the
natural home).
-/

/-- **Bridge to mathlib's `Language.map`.** When `h` is the letter-to-letter
    `StringHom.letterMap f` (each input symbol → singleton output), the
    homomorphic image collapses to mathlib's `Language.map f`, the
    letter-by-letter image. Lifts mathlib's existing ringHom structure to
    the letter-map case of `stringMap` automatically. -/
@[simp] theorem Language.stringMap_letterMap {α β : Type*}
    (f : α → β) (L : Language α) :
    Language.stringMap (Core.StringHom.letterMap f) L = Language.map f L := by
  ext w
  simp only [Language.stringMap, Set.mem_setOf_eq, Core.StringHom.apply_letterMap,
             Language.map, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
             Set.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩

-- ============================================================================
-- Closure axioms (Hopcroft–Ullman 1979) — `stringMap` proven in `Map.lean`
-- ============================================================================

/-- **CFL closure under intersection with a regular language**
    (@cite{hopcroft-ullman-1979} Theorem 6.5; Bar-Hillel, Perles & Shamir
    1961): if `L` is context-free and `R` is regular, then `L ∩ R` is
    context-free.

    Proof obligation: Bar-Hillel triple-product construction. Deferred —
    see the module docstring of `Linglib/Core/Computability/ContextFreeGrammar/Closure.lean`. -/
axiom Language.IsContextFree.inter_isRegular {α : Type*}
    {L R : Language α}
    (hL : L.IsContextFree) (hR : R.IsRegular) :
    (L ⊓ R).IsContextFree

-- ============================================================================
-- Contrapositive corollaries (the useful direction for non-CF arguments)
-- ============================================================================

/-- Contrapositive of homomorphism closure: if the homomorphic image of `L`
    is not context-free, then `L` is not context-free. -/
theorem Language.not_isContextFree_of_stringMap_not {α β : Type*}
    (h : Core.StringHom α β) {L : Language α}
    (hImg : ¬ (Language.stringMap h L).IsContextFree) :
    ¬ L.IsContextFree :=
  fun hL => hImg (Language.IsContextFree.stringMap h hL)

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

    This is the proof shape used by @cite{shieber-1985} for Swiss German,
    closely paralleled by @cite{huybregts-1976} for Dutch, and applicable
    to any future natural-language non-CF argument that proceeds via
    homomorphic abstraction (e.g., case-marker-only projection) plus
    regular filtering (e.g., case-sorted clause shape). -/
theorem Language.not_isContextFree_via_witness {α β : Type*}
    (h : Core.StringHom α β) (R : Language β) {L : Language α}
    (hR : R.IsRegular)
    (hWitness : ¬ (Language.stringMap h L ⊓ R).IsContextFree) :
    ¬ L.IsContextFree :=
  fun hL =>
    hWitness ((Language.IsContextFree.stringMap h hL).inter_isRegular hR)
