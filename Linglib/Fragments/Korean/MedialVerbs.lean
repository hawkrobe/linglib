import Linglib.Syntax.Clause.Chaining

/-!
# Korean conjunctive suffixes

Korean chains clauses with conjunctive suffixes on the verb of each medial clause before a
single final verb, and a chain can be extended without limit. There is no switch-reference:
each suffix encodes the relation between its clause and the next, *-go* 'and, and then',
*-myeonseo* 'while', *-eoseo* 'because, and then', *-(eu)myeon* 'if, when', *-jiman* 'but',
*-dorok* 'so that', *-nikka* 'since' and *-(eu)ryeo* 'in order to'. Tense may be marked on the
medial verb before the conditional, concessive and causal *-nikka* suffixes and not before the
others, and the medial clause may be negated on its own before every suffix. The
clause-chaining system is read off the inventory: the retention of tense and polarity on
medial verbs from the suffixes admitting them and the marked relations from the suffixes'
relations, as Sohn describes them.

## Main definitions

* `Korean.MedialVerbs.ConjSuffixEntry`, `Korean.MedialVerbs.allSuffixes` — the suffixes
* `Korean.MedialVerbs.chaining` — the clause-chaining system, derived from the inventory

## References

* [sarvasy-aikhenvald-2025]
* [sohn-1999]
-/

namespace Korean.MedialVerbs

open Clause.Chaining (InterclauseRelation CategoryRetention)

/-- A conjunctive suffix: its form, gloss, the relations it encodes, and whether the medial
verb may carry tense and negation before it. -/
structure ConjSuffixEntry where
  /-- The romanized form. -/
  form : String
  /-- The gloss. -/
  gloss : String
  /-- The interclausal relations the suffix encodes. -/
  relations : List InterclauseRelation
  /-- Tense may be marked on the medial verb. -/
  AllowsTense : Prop
  /-- The medial clause may be negated on its own. -/
  AllowsNegation : Prop
  [decidableTense : Decidable AllowsTense]
  [decidableNegation : Decidable AllowsNegation]

instance (e : ConjSuffixEntry) : Decidable e.AllowsTense := e.decidableTense
instance (e : ConjSuffixEntry) : Decidable e.AllowsNegation := e.decidableNegation

/-- A suffix admitting negation on the medial clause and admitting tense as stated. -/
private def suffix (form gloss : String) (relations : List InterclauseRelation)
    (tense : Prop) [Decidable tense] : ConjSuffixEntry :=
  { form, gloss, relations, AllowsTense := tense, AllowsNegation := True }

/-- *-go* 'and, and then', the least constrained connective. -/
def go : ConjSuffixEntry := suffix "-go" "and, and then" [.sequential, .additive] False

/-- *-myeonseo* 'while', the two events overlapping. -/
def myeonseo : ConjSuffixEntry := suffix "-myeonseo" "while" [.simultaneous] False

/-- *-eoseo* 'because, and then', the medial event the cause or the immediately preceding
event. -/
def eoseo : ConjSuffixEntry := suffix "-eoseo" "because, and then" [.causal, .sequential] False

/-- *-(eu)myeon* 'if, when', taking past tense for counterfactuals. -/
def myeon : ConjSuffixEntry := suffix "-(eu)myeon" "if, when" [.conditional] True

/-- *-jiman* 'but, although'. -/
def jiman : ConjSuffixEntry := suffix "-jiman" "but, although" [.concessive] True

/-- *-dorok* 'so that, until', the medial event the goal or limit of the next. -/
def dorok : ConjSuffixEntry := suffix "-dorok" "so that, until" [.purpose] False

/-- *-nikka* 'since, because', the medial event an established reason. -/
def nikka : ConjSuffixEntry := suffix "-nikka" "since, because" [.causal] True

/-- *-(eu)ryeo* 'in order to', the subject intending the medial event. -/
def ryeo : ConjSuffixEntry := suffix "-(eu)ryeo" "in order to" [.purpose] False

/-- The conjunctive suffixes. -/
def allSuffixes : List ConjSuffixEntry :=
  [go, myeonseo, eoseo, myeon, jiman, dorok, nikka, ryeo]

/-- How far medial verbs retain a category: fully when every suffix admits it, restrictedly
when some do, not at all when none does. -/
def retention (p : ConjSuffixEntry → Prop) [DecidablePred p] : CategoryRetention :=
  if ∀ e ∈ allSuffixes, p e then .full
  else if ∃ e ∈ allSuffixes, p e then .restricted
  else .absent

/-- The clause-chaining system: medial-final chains without switch-reference, tense and
polarity retained as the suffixes admit them, no agreement, and medial clauses able to stand
alone. -/
def chaining : Clause.Chaining.System where
  direction := .medialFinal
  srSystem := .none
  srTarget := none
  srObligatory := false
  srMarkedness := none
  medialMorph := {
    tense := retention (·.AllowsTense)
    agreement := .absent
    mood := .restricted
    polarity := retention (·.AllowsNegation)
    aspect := .restricted }
  relationsMarked := (allSuffixes.flatMap (·.relations)).eraseDups
  hasRecapLinkage := false
  hasSummaryLinkage := false
  medialCanStandAlone := true

end Korean.MedialVerbs
