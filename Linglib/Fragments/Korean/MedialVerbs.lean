import Linglib.Syntax.Clause.Chaining

/-!
# Korean converbs

Korean chains clauses with conjunctive suffixes, Sohn's term for its converbs, on the verb of
each medial clause before a single final verb. There is no switch-reference: each suffix
encodes the relation between its clause and the next, *-go* 'and, and then', the most
productive of them, *-myeonseo* 'while', *-eoseo* 'because, and then', *-(eu)myeon* 'if,
when', *-jiman* 'but', *-dorok* 'so that, to the extent that, until', *-nikka* 'since' and
*-(eu)ryeo(go)* 'intending to'. Sohn states that the sequential *-eoseo* and *-go(seo)* and the
simultaneous *-myeonseo* take no past tense before them; his examples nonetheless show the past
before *-go* and *-myeonseo* in their coordinate and concessive uses, before the conditional,
which takes it for hypothetical readings, and before *-jiman* and *-nikka*, and they show the
medial clause negated on its own before *-go*, *-eoseo*, *-(eu)myeon* and *-jiman*. The
suffixes are entered in the Revised Romanization; Sohn writes *-ko*, *-(u)myense*, *-ese*,
*-(u)myen*, *-ciman*, *-tolok*, *-(u)nikka* and *-(u)lyeko*. The clause-chaining system is
read off the inventory: the retention of tense and polarity on medial verbs from the suffixes
admitting them, and the marked relations from the suffixes' relations.

## Main definitions

* `Korean.Converb`, `Korean.converbs` — the converbs
* `Korean.chaining` — the clause-chaining system, derived from the inventory

## References

* [sarvasy-aikhenvald-2025]
* [sohn-1994]
-/

namespace Korean

open Clause.Chaining (InterclauseRelation CategoryRetention)

/-- A converb: its form, gloss, the relations it encodes, and whether the medial verb may
carry tense and negation before it. -/
structure Converb where
  /-- The romanized form. -/
  form : String
  /-- The gloss. -/
  gloss : String
  /-- The interclausal relations the converb encodes. -/
  relations : List InterclauseRelation
  /-- Tense may be marked on the medial verb. -/
  AllowsTense : Prop
  /-- The medial clause may be negated on its own. -/
  AllowsNegation : Prop
  [decidableTense : Decidable AllowsTense]
  [decidableNegation : Decidable AllowsNegation]

instance (c : Converb) : Decidable c.AllowsTense := c.decidableTense
instance (c : Converb) : Decidable c.AllowsNegation := c.decidableNegation

/-- A converb admitting negation on the medial clause and admitting tense as stated. -/
private def converb (form gloss : String) (relations : List InterclauseRelation)
    (tense : Prop) [Decidable tense] : Converb :=
  { form, gloss, relations, AllowsTense := tense, AllowsNegation := True }

/-- *-go* 'and, and then', the least constrained connective; the past occurs before it in its
coordinate use, *hae-ss-go* 'did, and'. -/
def go : Converb := converb "-go" "and, and then" [.sequential, .additive] True

/-- *-myeonseo* 'while', the two events overlapping; the past occurs before it in its
concessive use. -/
def myeonseo : Converb := converb "-myeonseo" "while" [.simultaneous] True

/-- *-eoseo* 'because, and then', the medial event the cause or the immediately preceding
event; no tense before it. -/
def eoseo : Converb := converb "-eoseo" "because, and then" [.causal, .sequential] False

/-- *-(eu)myeon* 'if, when', taking the past for hypothetical readings. -/
def myeon : Converb := converb "-(eu)myeon" "if, when" [.conditional] True

/-- *-jiman* 'but, although'. -/
def jiman : Converb := converb "-jiman" "but, although" [.concessive] True

/-- *-dorok* 'so that, to the extent that, until', the medial event the goal, extent or limit
of the next. -/
def dorok : Converb := converb "-dorok" "so that, until" [.purpose] False

/-- *-nikka* 'since, because', the reason as the speaker presents it. -/
def nikka : Converb := converb "-nikka" "since, because" [.causal] True

/-- *-(eu)ryeo(go)* 'intending to'. -/
def ryeo : Converb := converb "-(eu)ryeo(go)" "intending to" [.purpose] False

/-- The converbs. -/
def converbs : List Converb := [go, myeonseo, eoseo, myeon, jiman, dorok, nikka, ryeo]

/-- How far medial verbs retain a category: fully when every converb admits it, restrictedly
when some do, not at all when none does. -/
def retention (p : Converb → Prop) [DecidablePred p] : CategoryRetention :=
  if ∀ c ∈ converbs, p c then .full
  else if ∃ c ∈ converbs, p c then .restricted
  else .absent

/-- The clause-chaining system: medial-final chains without switch-reference, tense and
polarity retained as the converbs admit them, no agreement, and medial clauses able to stand
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
  relationsMarked := (converbs.flatMap (·.relations)).eraseDups
  hasRecapLinkage := false
  hasSummaryLinkage := false
  medialCanStandAlone := true

end Korean
