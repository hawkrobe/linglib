import Linglib.Theories.Semantics.Tense.LexicalType
import Mathlib.Order.Bounds.Basic

/-!
# `before`-clauses @cite{beaver-condoravdi-2003} @cite{sharvit-2014}

@cite{beaver-condoravdi-2003}'s semantics for `before`, as adopted by
@cite{sharvit-2014} for the cross-linguistic *before*-clause typology.

## The B&C semantics (@cite{sharvit-2014} (23)-(24), p. 271)

`before^{B&C}` takes a body `p` (a partial time-predicate) and an
evaluation interval `t`. Its definedness presuppositions are:
1. `t ⊆ C` (containment in the contextually-supplied restrictor `C`)
2. `EARLIEST_C({t' ∈ C | p t'})` is defined
3. `MIN(C) < EARLIEST_C(...)` (a strict predecessor in `C` exists)

When defined, `[[before^{B&C}]]^{C,g}(p)(t)` is true iff
`t < EARLIEST_C(...)`.

## Inherent Presupposition Failure (IPF, @cite{sharvit-2014} p. 272-273)

The central cross-linguistic prediction. Presupposition (2) fails
inherently whenever the body `p` itself contains an existential quantifier
over a dense time axis: there is no "first" time `t` such that some
`t'' < t'` satisfies the embedded predicate, because density supplies
arbitrarily-late witnesses below any candidate minimum.

This blocks past-under-past in *before*-clauses when the language has
quantificational tenses (Japanese), and is the technical core of the
pronominal/quantificational distinction in @cite{sharvit-2014}'s typology.
A pronominal past, by contrast, denotes a single time `g k` (no embedded
existential), so its body in `before^{B&C}` is constant in `t` and IPF
does not arise.
-/

namespace Semantics.Tense.TemporalConnectives.Before

open Semantics.Tense (LexicalType quantificationalPast)

variable {Time : Type*} [LinearOrder Time]

/-- @cite{sharvit-2014} (24) presupposition (ii), p. 271: `EARLIEST_C` is
    defined for body `p` iff the set of `C`-times where `p` holds has a
    least element (mathlib's `IsLeast`). -/
def hasEarliest (C : Set Time) (p : Time → Prop) : Prop :=
  ∃ t, IsLeast {t' | t' ∈ C ∧ p t'} t

/-- IPF (@cite{sharvit-2014} (27), p. 272): when the body of
    `before^{B&C}` is the quantificational past `[[PAST]]^{K,g}(q)`, and
    the restrictor `C` is order-dense (interval-like) with `K ⊆ C`, the
    `EARLIEST` presupposition fails. The proof is by contradiction:
    a witness `t_q < t_min` with `q t_q` lifts via density to a strictly
    smaller body-witness `t_mid` in `C`.

    This is the technical core of @cite{sharvit-2014}'s thesis that only
    languages with pronominal tenses license past-under-past in
    `before`-clauses. The `q`-witness is not a separate hypothesis: it
    falls out of `hasEarliest`'s witness for `t_min`, which is why no
    `∃ t ∈ K, q t` premise appears. -/
theorem ipf_quantificationalPast
    {C K : Set Time}
    (hK : K ⊆ C)
    (hC_dense : ∀ a b, a ∈ C → b ∈ C → a < b → ∃ c ∈ C, a < c ∧ c < b)
    (q : Time → Prop) :
    ¬ hasEarliest C (quantificationalPast K q) := by
  rintro ⟨t_min, ⟨ht_min_C, t_q, ht_q_K, ht_q_lt, hq_t_q⟩, hmin⟩
  obtain ⟨t_mid, ht_mid_C, ht_q_lt_mid, ht_mid_lt_min⟩ :=
    hC_dense t_q t_min (hK ht_q_K) ht_min_C ht_q_lt
  exact absurd (hmin ⟨ht_mid_C, t_q, ht_q_K, ht_q_lt_mid, hq_t_q⟩)
    (not_le.mpr ht_mid_lt_min)

/-- The Bool-valued IPF dispatch on tense lexical type, for use in
    cross-linguistic typology theorems. Quantificational tenses trigger
    IPF in *before*-clauses; pronominal tenses do not. -/
def triggersIPFInBefore : LexicalType → Bool
  | .quantificational => true
  | .pronominal       => false

/-- @cite{sharvit-2014}'s prediction ((27), p. 272): a language's
    past tense is well-formed under `before^{B&C}` iff its tense lexical
    type does not trigger IPF — i.e., iff it is pronominal. -/
@[simp] theorem pastUnderBefore_wellFormed_iff (τ : LexicalType) :
    triggersIPFInBefore τ = false ↔ τ = .pronominal := by
  cases τ <;> simp [triggersIPFInBefore]

end Semantics.Tense.TemporalConnectives.Before
