import Mathlib.Data.Set.Basic
import Linglib.Semantics.Tense.GramTense

/-!
# Tense as a typed lexical object

[sharvit-2014] argues tense comes in two cross-linguistic semantic types ((30), p. 274):
*pronominal* (after [partee-1973]; an element of `D_i`) and *quantificational* (a Priorean
operator over time-predicates). They diverge on past-under-past in *before*-clauses, where
quantificational past triggers Inherent Presupposition Failure under [beaver-condoravdi-2003]'s
`before` (`Tense.TemporalConnectives.Before`); the cross-linguistic typology ((98), (99)) is
in `Studies.Sharvit2014`.

## Main definitions

* `Tense.LexicalType` — pronominal vs quantificational tense.
* `Tense.pronominalLookup` — the pronominal-past partial lookup ((30a)).
* `Tense.quantificationalPast` — the quantificational past operator ((30b)).
-/

namespace Tense

/-- [sharvit-2014]'s two semantic types of tense ((30)). -/
inductive LexicalType
  /-- Pronominal: an element of `D_i`, two-indexed `past_{j,k}`. -/
  | pronominal
  /-- Quantificational: an operator over time-predicates. -/
  | quantificational
  deriving DecidableEq, Repr

/-- The two semantic types are distinct. ([sharvit-2014]'s language-level no-mixing
    constraint — a language has tenses of just one type — lives in `Studies.Sharvit2014`.) -/
theorem LexicalType.pronominal_ne_quantificational :
    LexicalType.pronominal ≠ LexicalType.quantificational :=
  nofun

/-- [sharvit-2014] (30a): pronominal-past lookup `[[past_{j,k}]]^g`. Indices `j`
    (evaluation), `k` (referential); defined iff `g k < g j`, then `g k`. Uses `Option`
    (not `Part`/`PFun`) as the domain is decidable; the shape is `Option.guard`. -/
def pronominalLookup {Time : Type*} [LT Time] [DecidableLT Time]
    (g : ℕ → Time) (j k : ℕ) : Option Time :=
  if g k < g j then some (g k) else none

/-- The pronominal past denotes the referential index when defined. -/
@[simp]
theorem pronominalLookup_eq_some_iff {Time : Type*} [LT Time]
    [DecidableLT Time] (g : ℕ → Time) (j k : ℕ) (t : Time) :
    pronominalLookup g j k = some t ↔ g k < g j ∧ g k = t := by
  unfold pronominalLookup; split <;> simp_all

/-- The pronominal past is undefined exactly when the constraint fails. -/
@[simp]
theorem pronominalLookup_eq_none_iff {Time : Type*} [LT Time]
    [DecidableLT Time] (g : ℕ → Time) (j k : ℕ) :
    pronominalLookup g j k = none ↔ ¬ g k < g j := by
  unfold pronominalLookup; split <;> simp_all

/-- The two codebase formalizations of [partee-1973] pronominal tense coincide:
    `pronominalLookup` agrees with the `TensePronoun` architecture (full presupposition
    plus resolution), for any binding `mode`. -/
theorem pronominalLookup_eq_some_iff_tensePronoun {Time : Type*} [LinearOrder Time]
    (g : TemporalAssignment Time) (j k : ℕ) (t : Time) (mode : TenseInterpretation) :
    pronominalLookup g j k = some t ↔
      (TensePronoun.mk k .past mode j).fullPresupposition g ∧
      (TensePronoun.mk k .past mode j).resolve g = t :=
  pronominalLookup_eq_some_iff g j k t

/-- [sharvit-2014] (30b): quantificational past; restrictor `K` bounds the
    quantification domain. -/
def quantificationalPast {Time : Type*} [LT Time]
    (K : Set Time) (p : Time → Prop) (t : Time) : Prop :=
  ∃ t' ∈ K, t' < t ∧ p t'

/-- The quantificational past is monotone in its body predicate. -/
theorem quantificationalPast_mono {Time : Type*} [LT Time]
    {K : Set Time} {p q : Time → Prop} (h : ∀ t, p t → q t) {t : Time} :
    quantificationalPast K p t → quantificationalPast K q t := by
  rintro ⟨t', htK, hlt, hp⟩
  exact ⟨t', htK, hlt, h _ hp⟩

end Tense
