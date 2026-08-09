import Linglib.Syntax.Clause.Complementation

/-!
# Washo Clausal Embedding Inventory

[bochnak-hanink-2021]

Washo (Hokan/isolate, ISO 639-3 `was`) inventory of complement-taking
predicates. Theory-light: each predicate carries its
[noonan-2007] CTP class where clear, [bochnak-hanink-2021]'s
*presuppositional* classification ((5); their §5.3.2 argues factivity is
*not* lexically specified — complements of 'remember'/'know' can be
false, (86)–(87) — so this field deliberately is not named `factive`),
and one morphological observable — the shape of the complement edge.

Forms follow the paper's orthography (after [jacobsen-1964]): `:` marks
vowel length, ʔ ɨ ŋ are IPA, stress is acute. 'know' and 'remember'
belong to a small inherently-negative class — the positive reading
requires the negative suffix *-e:s*, and 'remember' is simply negated
'forget' (their fn. 7).
-/

namespace Washo.Clause

/-! ### Predicate schema -/

/-- Morphological shape of a predicate's notional-complement edge
    ([bochnak-hanink-2021] Table 1). The two morphemes co-vary without
    exception in their data, so one two-valued observable is faithful;
    there is no marginal cell. The *-gi ~ -ge* alternation is case
    (nominative vs accusative, their fn. 6) conditioned by the
    nominalization's matrix function — attitude complements are all
    accusative *-ge*. -/
inductive ComplementEdge where
  /-- Clausal nominalization: nominalizer *-gi ~ -ge* over independent
      mood *-i*. -/
  | nominalized
  /-- Bare clause: dependent mood *-aʔ*, never nominalized. -/
  | bare
  deriving DecidableEq, Repr

/-- A Washo complement-taking predicate.

    - `ctpClass`: [noonan-2007] category; `none` where the assignment
      is unclear ('dream').
    - `presuppositional`: [bochnak-hanink-2021] (5) — "the embedded
      clause refers to familiar content" — their descriptive
      classification, deliberately not `factive` (§5.3.2).
    - `edge`: the complement-edge observable (Table 1). -/
structure WashoEmbedder where
  form : String
  gloss : String
  ctpClass : Option CTPClass
  presuppositional : Bool
  edge : ComplementEdge
  deriving DecidableEq, Repr

/-! ### Presuppositional predicates — nominalized complements

[bochnak-hanink-2021] (5b), §2: complements are always nominalized with
*-gi ~ -ge* and occur with the independent mood suffix *-i*. -/

/-- *hamup'ay* 'forget'. [bochnak-hanink-2021] (1), (9), (31), (33). -/
def hamupay : WashoEmbedder where
  form := "hamup'ay"; gloss := "forget"
  ctpClass := some .knowledge
  presuppositional := true
  edge := .nominalized

/-- *hamup'ay-e:s* 'remember' — negated 'forget' (inherently-negative
    class, fn. 7). [bochnak-hanink-2021] (8), (86). -/
def hamupayEs : WashoEmbedder where
  form := "hamup'ay-e:s"; gloss := "remember"
  ctpClass := some .knowledge
  presuppositional := true
  edge := .nominalized

/-- *ašaš-e:s* 'know' — negated 'not know' (inherently-negative class).
    [bochnak-hanink-2021] (6), (32), (87). -/
def ashashEs : WashoEmbedder where
  form := "ašaš-e:s"; gloss := "know"
  ctpClass := some .knowledge
  presuppositional := true
  edge := .nominalized

/-- *i:gi* 'see'. Attested with a propositional complement ('I saw that
    it rained', (10)) and with plain DP objects ((89)).
    [bochnak-hanink-2021] (10), (20), (88). -/
def iigi : WashoEmbedder where
  form := "i:gi"; gloss := "see"
  ctpClass := some .perception
  presuppositional := true
  edge := .nominalized

/-- *damal* 'hear'. Attested only on the event-perception reading ('I
    heard it raining', (11); 'I heard the man singing', (84b)).
    [bochnak-hanink-2021] (11), (84). -/
def damal : WashoEmbedder where
  form := "damal"; gloss := "hear"
  ctpClass := some .perception
  presuppositional := true
  edge := .nominalized

/-! ### Non-presuppositional predicates — bare complements

[bochnak-hanink-2021] (5a), §2: complements "surface with the
'dependent' mood marker -aʔ" and "are never nominalized". -/

/-- *hamu* 'think'. [bochnak-hanink-2021] (2), (13), (41), (42). -/
def hamu : WashoEmbedder where
  form := "hamu"; gloss := "think"
  ctpClass := some .propAttitude
  presuppositional := false
  edge := .bare

/-- *i:d* 'say'. [bochnak-hanink-2021] (14), (37), (50). -/
def iid : WashoEmbedder where
  form := "i:d"; gloss := "say"
  ctpClass := some .utterance
  presuppositional := false
  edge := .bare

/-- *mɨtgi:bɨl-e:s* 'believe' — negated 'disbelieve' (inherently-
    negative class, fn. 7). [bochnak-hanink-2021] (16). -/
def metgiibilEs : WashoEmbedder where
  form := "mɨtgi:bɨl-e:s"; gloss := "believe"
  ctpClass := some .propAttitude
  presuppositional := false
  edge := .bare

/-- *gum-suʔuʔuš* 'dream' (reflexive *gum-*). Its 'that'-complement is
    always bare ((15), (52), (54)); the nominalized complement of the
    non-reflexive form is an internally headed relative, not a notional
    complement ((55)). No clear [noonan-2007] class.
    [bochnak-hanink-2021] §3.2.2. -/
def gumsuus : WashoEmbedder where
  form := "gum-suʔuʔuš"; gloss := "dream"
  ctpClass := none
  presuppositional := false
  edge := .bare

/-! ### Inventories -/

/-- The complement-taking predicates with quotable per-predicate data in
    [bochnak-hanink-2021]. -/
def allEmbedders : List WashoEmbedder :=
  [hamupay, hamupayEs, ashashEs, iigi, damal,
   hamu, iid, metgiibilEs, gumsuus]

/-- The predicates taking nominalized complements. -/
def nominalizedTakers : List WashoEmbedder :=
  allEmbedders.filter (·.edge == .nominalized)

/-- The predicates taking bare complements. -/
def bareTakers : List WashoEmbedder :=
  allEmbedders.filter (·.edge == .bare)

/-- Drift sentry: the nominalized-takers are exactly the five
    presuppositional predicates. -/
theorem nominalizedTakers_membership :
    nominalizedTakers = [hamupay, hamupayEs, ashashEs, iigi, damal] := by
  decide

/-- [bochnak-hanink-2021] Table 1's correlation, stated exceptionless in
    both directions: a predicate takes nominalized complements iff it is
    presuppositional. -/
theorem presuppositional_iff_nominalized :
    ∀ v ∈ allEmbedders,
      (v.presuppositional = true ↔ v.edge = .nominalized) := by decide

end Washo.Clause
