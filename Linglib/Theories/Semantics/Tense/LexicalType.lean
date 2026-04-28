import Mathlib.Data.Set.Basic

/-!
# Tense as a typed lexical object @cite{sharvit-2014}

@cite{sharvit-2014}'s central distinction ((30), p. 274): tenses come in
two semantic types across languages, motivated by cross-linguistic
variation in *before*-clauses (Japanese vs Polish/English) and attitude
reports (English vs Japanese vs Polish).

## Two semantic types

- **Pronominal tense** (after @cite{partee-1973}): an element of `D_i`. A
  pronominal past `past_{j,k}` carries two indices — `j` *evaluation*,
  `k` *referential*. When defined, `[[past_{j,k}]]^g := g k`, with
  definedness condition `g k < g j` ((30a)).

- **Quantificational tense** (after Prior 1967, Montague 1974): an
  operator. `[[PAST]]^{K,g}(p)(t)` is true iff `∃ t' ∈ K, t' < t ∧ p t'`
  ((30b)). The contextually-supplied restrictor `K ⊆ Time` constrains the
  domain of quantification.

## Empirical signature

The two types make different predictions for *past-under-past in
before-clauses*: quantificational past triggers Inherent Presupposition
Failure under @cite{beaver-condoravdi-2003}'s `before` semantics, because
no minimum exists in a dense set of times preceded by a quantificational-
past witness. The IPF mechanism is in
`Theories/Semantics/Tense/TemporalConnectives/Before.lean`.

The cross-linguistic typology ((98), (99)) lives in
`Phenomena/TenseAspect/Studies/Sharvit2014.lean`.
-/

namespace Semantics.Tense

/-- @cite{sharvit-2014}'s two semantic types for tense lexical items
    ((30), p. 274). -/
inductive LexicalType
  /-- Pronominal: an element of `D_i`, two-indexed `past_{j,k}`. -/
  | pronominal
  /-- Quantificational: an operator over time-predicates. -/
  | quantificational
  deriving DecidableEq, Repr

/-- @cite{sharvit-2014}'s no-mixing assumption (§6.1, p. 300): a language
    has either pronominal or quantificational tenses, not both, and not
    neither. The two types are distinct as a structural fact. -/
theorem LexicalType.pronominal_ne_quantificational :
    LexicalType.pronominal ≠ LexicalType.quantificational :=
  nofun

/-- @cite{sharvit-2014} (30a), p. 274: pronominal-past lookup. The two
    indices are `j` (evaluation) and `k` (referential); the past is
    *defined* iff `g k < g j`, in which case it denotes `g k`.

    Modeled as `Option Time` (mathlib idiom for partial functions). -/
def pronominalLookup {Time : Type*} [LT Time] [DecidableLT Time]
    (g : ℕ → Time) (j k : ℕ) : Option Time :=
  if g k < g j then some (g k) else none

/-- The pronominal past denotes the referential index when defined. -/
theorem pronominalLookup_eq_some_iff {Time : Type*} [LT Time]
    [DecidableLT Time] (g : ℕ → Time) (j k : ℕ) (t : Time) :
    pronominalLookup g j k = some t ↔ g k < g j ∧ g k = t := by
  unfold pronominalLookup
  by_cases h : g k < g j <;> simp [h, eq_comm]

/-- @cite{sharvit-2014} (30b), p. 274: quantificational past. The
    contextual restrictor `K` constrains the domain of quantification. -/
def quantificationalPast {Time : Type*} [LT Time]
    (K : Set Time) (p : Time → Prop) (t : Time) : Prop :=
  ∃ t' ∈ K, t' < t ∧ p t'

/-- The quantificational past is monotone in its body predicate. -/
theorem quantificationalPast_mono {Time : Type*} [LT Time]
    {K : Set Time} {p q : Time → Prop} (h : ∀ t, p t → q t) {t : Time} :
    quantificationalPast K p t → quantificationalPast K q t := by
  rintro ⟨t', htK, hlt, hp⟩
  exact ⟨t', htK, hlt, h _ hp⟩

end Semantics.Tense
