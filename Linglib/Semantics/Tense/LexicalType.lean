import Mathlib.Data.Set.Basic
import Linglib.Semantics.Quantification.Basic

/-!
# Tense as a typed lexical object

[sharvit-2014] argues tense comes in two cross-linguistic semantic types ((30), p. 274):
*pronominal* (after [partee-1973]; an element of `D_i`) and *quantificational* (a Priorean
operator over time-predicates). They diverge on past-under-past in *before*-clauses, where
quantificational past triggers Inherent Presupposition Failure under [beaver-condoravdi-2003]'s
`before` (`Tense.TemporalConnectives.Before`). The pronominal-past lookup ((30a)), its
grounding in `TensePronoun`, and the cross-linguistic typology ((98), (99)) live in
`Studies.Sharvit2014`.

## Main definitions

* `Tense.LexicalType` — pronominal vs quantificational tense.
* `Tense.quantificationalPast` — the quantificational past, the GQ `some` over `K` ((30b)).
-/

namespace Tense

/-- [sharvit-2014]'s two semantic types of tense ((30)). -/
inductive LexicalType
  /-- Pronominal: an element of `D_i`, two-indexed `past_{j,k}`. -/
  | pronominal
  /-- Quantificational: an operator over time-predicates. -/
  | quantificational
  deriving DecidableEq, Repr

/-- [sharvit-2014] (30b): quantificational past as the generalized quantifier
    `some` (`Quantification.some_sem`) over the contextual restrictor `K`,
    with scope "precedes `t` and satisfies `p`". Definitionally
    `∃ t' ∈ K, t' < t ∧ p t'`. -/
def quantificationalPast {Time : Type*} [LT Time]
    (K : Set Time) (p : Time → Prop) (t : Time) : Prop :=
  Quantification.some_sem (· ∈ K) (fun t' => t' < t ∧ p t')

end Tense
