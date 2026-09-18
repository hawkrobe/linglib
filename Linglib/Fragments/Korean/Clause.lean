import Mathlib.Data.Finset.Union
import Linglib.Data.UD.Features
import Linglib.Morphology.Morph
import Linglib.Syntax.Clause.Chaining

/-!
# Korean converbs

Korean chains clauses with conjunctive suffixes, Sohn's term for its converbs, on the
nonfinite verb of each medial clause before a single final verb, and a nonfinite verb keeps
its voice, subject-honorific and tense slots but takes no sentence ender, so no speech level
or sentence type. There is no switch-reference: each suffix encodes the relation between its
clause and the next. The coordinative *-go* 'and' is the most frequent, and its formal
counterpart is *-(eu)na*; the contracted *-go(seo)* and *-eoseo* 'and then' sequence events,
the choice between them depending on the verb and on whether the subjects are the same, and
*-eoseo* also gives the manner, *georeoseo* 'by walking', and, with different subjects, the
cause; *-jamaja* 'as soon as' and the transferentive *-daga* 'and then, while', which
repeated marks alternation, also sequence, while *-myeonseo* 'while' marks simultaneity.
*-(eu)nikka* 'because, as' gives the reason as the speaker presents it; *-(eu)myeon* 'if,
when' conditions; *-jiman*, *-(eu)na* and *-eodo* 'but, although, even if' concede;
*-dorok* 'so that, to the extent that, until' gives a result or limit; *-(eu)ryeogo* 'intending
to' and *-(eu)reo* 'in order to' give the intention or purpose; *-(eu)ni* 'since, as, after'
gives the reason or the antecedent; *-neunde* 'given that, and, but' supplies background; and
*-geona* and *-deunji* 'or' disjoin. Every conjunctive suffix admits the subject honorific
before it, but only some the past or perfect *-eoss* and fewer still the modal *-gess*, and
never the addressee honorific. Tense before the suffix is relative to the final verb. Sohn
marks *-eoseo*, *-go(seo)*, *-dorok*, *-(eu)ryeogo*, *-(eu)reo* and *-jamaja* as excluding
the past, and with it the modal; *-myeonseo* excludes both in its simultaneous reading, the
tense of the final clause governing its clause, and admits both in its concessive 'while …
yet' reading; before *-(eu)myeon* the past marks a hypothetical; *-eodo* and *-deunji* admit
the past but not the modal; and *-go*, *-(eu)na*, *-jiman*, *-neunde*, *-(eu)ni*,
*-(eu)nikka*, *-daga* and *-geona* admit both. The negative adverbs *an* and *mot* and the
negative verb *malda* occur in a medial clause, their choice governed by the sentence type of
the final clause. The suffixes are entered in the Revised Romanization; Sohn writes *-ko*,
*-ko(se)*, *-(u)myense*, *-e(se)*, *-(u)myen*, *-ciman*, *-(u)na*, *-eto*, *-tolok*,
*-(u)nikka*, *-(u)ni*, *-nuntey*, *-(u)lyeko*, *-(u)le*, *-taka*, *-ca(maca)*, *-kena* and
*-tunci*.

## Main definitions

* `Korean.Converb` — the eighteen conjunctive suffixes, with their morphs (`morphs`,
  `form`), gloss, the relations they encode (`relations`), whether the past (`AllowsTense`)
  and the modal (`AllowsModal`) may precede them, and their verb form (`verbForm`); they are
  an instance of `Clause.Chaining.MedialForm`
* `Korean.Converb.allowsModal_imp_allowsTense` — a suffix admitting the modal admits the past

## Implementation notes

`AllowsTense` and `AllowsModal` follow the features Sohn attaches to each conjunctor in his
survey and, for *-jamaja*, *-geona* and *-deunji*, which the list omits, his statements that
the suffixes excluding the past exclude every mood suffix, his example of the past before
*-geona*, and the synonymy of *-geona* with *-deunji*. The clause-chaining typology over the
converbs is in `Studies/SarvasyAikhenvald2025.lean`; disjunction and background are
relations the inventory of interclausal relations does not name.

## References

* [sohn-1994]
* [sohn-1999]
-/

namespace Korean

open Clause.Chaining (InterclauseRelation)
open Morphology (Morph)

/-- The conjunctive suffixes. -/
inductive Converb where
  /-- *-go* 'and', the coordinative suffix, tense before it absolute or relative. -/
  | go
  /-- *-go(seo)* 'and then', the contracted temporal suffix, also the manner, *malaeul
  tagoseo* 'riding a horse'. -/
  | goseo
  /-- *-myeonseo* 'while', the two events overlapping; the past before it when the medial
  event comes first. -/
  | myeonseo
  /-- *-eoseo* 'and then, so, by', the sequence, cause or manner; no past before it. -/
  | eoseo
  /-- *-(eu)myeon* 'if, when', taking the past for hypothetical readings. -/
  | myeon
  /-- *-jiman* 'but, although'. -/
  | jiman
  /-- *-(eu)na* 'but', the formal concessive. -/
  | na
  /-- *-eodo* 'although, even if, no matter'. -/
  | eodo
  /-- *-dorok* 'so that, to the extent that, until', a result, extent or temporal limit; no
  past before it. -/
  | dorok
  /-- *-(eu)nikka* 'because, as, since, when', the reason as the speaker presents it. -/
  | nikka
  /-- *-(eu)ni* 'since, as, after'. -/
  | ni
  /-- *-neunde* 'given that, and, but', supplying background. -/
  | neunde
  /-- *-(eu)ryeogo* 'intending to'. -/
  | ryeo
  /-- *-(eu)reo* 'in order to'. -/
  | reo
  /-- *-daga* 'and then, while', the transferentive, marking alternation when repeated. -/
  | daga
  /-- *-jamaja* 'as soon as'; no past before it. -/
  | jamaja
  /-- *-geona* 'or'. -/
  | geona
  /-- *-deunji* 'or', the formal disjunction. -/
  | deunji
  deriving DecidableEq, Repr, Fintype

namespace Converb

/-- The morphs of a converb. -/
def morphs : Converb → List Morph
  | go => [.suff "go"]
  | goseo => [.suff "go(seo)"]
  | myeonseo => [.suff "myeonseo"]
  | eoseo => [.suff "eoseo"]
  | myeon => [.suff "(eu)myeon"]
  | jiman => [.suff "jiman"]
  | na => [.suff "(eu)na"]
  | eodo => [.suff "eodo"]
  | dorok => [.suff "dorok"]
  | nikka => [.suff "(eu)nikka"]
  | ni => [.suff "(eu)ni"]
  | neunde => [.suff "neunde"]
  | ryeo => [.suff "(eu)ryeogo"]
  | reo => [.suff "(eu)reo"]
  | daga => [.suff "daga"]
  | jamaja => [.suff "jamaja"]
  | geona => [.suff "geona"]
  | deunji => [.suff "deunji"]

/-- The form of a converb in boundary notation. -/
def form (c : Converb) : String := Morph.surface c.morphs

/-- The gloss. -/
def gloss : Converb → String
  | go => "and"
  | goseo => "and then"
  | myeonseo => "while"
  | eoseo => "and then, so, by"
  | myeon => "if, when"
  | jiman => "but, although"
  | na => "but"
  | eodo => "although, even if"
  | dorok => "so that, to the extent that, until"
  | nikka => "because, as, since, when"
  | ni => "since, as, after"
  | neunde => "given that, and, but"
  | ryeo => "intending to"
  | reo => "in order to"
  | daga => "and then, while"
  | jamaja => "as soon as"
  | geona | deunji => "or"

/-- The interclausal relations a converb encodes. -/
def relations : Converb → Finset InterclauseRelation
  | go => {.additive}
  | goseo => {.sequential, .manner}
  | myeonseo => {.simultaneous}
  | eoseo => {.sequential, .causal, .manner}
  | myeon => {.conditional}
  | jiman | na | eodo => {.concessive}
  | dorok | ryeo | reo => {.purpose}
  | nikka => {.causal}
  | ni => {.causal, .sequential}
  | neunde => {.additive, .concessive}
  | daga => {.sequential, .simultaneous}
  | jamaja => {.sequential}
  | geona | deunji => ∅

/-- The past or perfect may be marked on the medial verb before the converb; before
*-myeonseo* only in its concessive reading. -/
def AllowsTense (c : Converb) : Prop :=
  c = go ∨ c = myeonseo ∨ c = myeon ∨ c = jiman ∨ c = na ∨ c = eodo ∨ c = nikka ∨ c = ni ∨
    c = neunde ∨ c = daga ∨ c = geona ∨ c = deunji

instance : DecidablePred AllowsTense :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

/-- The modal *-gess* may be marked on the medial verb before the converb; before
*-myeonseo* only in its concessive reading. -/
def AllowsModal (c : Converb) : Prop :=
  c = go ∨ c = myeonseo ∨ c = myeon ∨ c = jiman ∨ c = na ∨ c = nikka ∨ c = ni ∨ c = neunde ∨
    c = daga ∨ c = geona

instance : DecidablePred AllowsModal :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

/-- A converb admitting the modal admits the past, since the clauses that exclude the past
exclude every mood suffix. -/
theorem allowsModal_imp_allowsTense (c : Converb) : c.AllowsModal → c.AllowsTense := by
  revert c; decide

/-- The verb form of a converb. -/
def verbForm (_ : Converb) : UD.VerbForm := .Conv

/-- The converbs as medial forms, neutral to switch-reference, encoding their relations, and
never indexing the subject. -/
instance : Clause.Chaining.MedialForm Converb where
  sr _ := none
  relations := relations
  IndexesSubject _ := False

end Converb

end Korean
