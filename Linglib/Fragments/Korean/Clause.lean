import Mathlib.Data.Finset.Union
import Linglib.Data.UD.Features
import Linglib.Morphology.Morph
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
*-(u)myen*, *-ciman*, *-tolok*, *-(u)nikka* and *-(u)lyeko*.

## Main definitions

* `Korean.Converb` — the eight converbs, with their morphs (`morphs`, `form`), gloss, the
  relations they encode (`relations`), whether the medial verb may carry tense
  (`AllowsTense`) and negation (`AllowsNegation`) before them, and their verb form
  (`verbForm`); they are an instance of `Clause.Chaining.MedialForm`

## Implementation notes

The clause-chaining typology over these forms is in `Studies/SarvasyAikhenvald2025.lean`.

## References

* [sarvasy-aikhenvald-2025]
* [sohn-1994]
-/

namespace Korean

open Clause.Chaining (InterclauseRelation)
open Morphology (Morph)

/-- The conjunctive suffixes. -/
inductive Converb where
  /-- *-go* 'and, and then', the least constrained connective; the past occurs before it in
  its coordinate use, *hae-ss-go* 'did, and'. -/
  | go
  /-- *-myeonseo* 'while', the two events overlapping; the past occurs before it in its
  concessive use. -/
  | myeonseo
  /-- *-eoseo* 'because, and then', the medial event the cause or the immediately preceding
  event; no tense before it. -/
  | eoseo
  /-- *-(eu)myeon* 'if, when', taking the past for hypothetical readings. -/
  | myeon
  /-- *-jiman* 'but, although'. -/
  | jiman
  /-- *-dorok* 'so that, to the extent that, until', the medial event the goal, extent or
  limit of the next. -/
  | dorok
  /-- *-nikka* 'since, because', the reason as the speaker presents it. -/
  | nikka
  /-- *-(eu)ryeo(go)* 'intending to'. -/
  | ryeo
  deriving DecidableEq, Repr, Fintype

namespace Converb

/-- The morphs of a converb. -/
def morphs : Converb → List Morph
  | go => [.suff "go"]
  | myeonseo => [.suff "myeonseo"]
  | eoseo => [.suff "eoseo"]
  | myeon => [.suff "(eu)myeon"]
  | jiman => [.suff "jiman"]
  | dorok => [.suff "dorok"]
  | nikka => [.suff "nikka"]
  | ryeo => [.suff "(eu)ryeo(go)"]

/-- The form of a converb in boundary notation. -/
def form (c : Converb) : String := Morph.surface c.morphs

/-- The gloss. -/
def gloss : Converb → String
  | go => "and, and then"
  | myeonseo => "while"
  | eoseo => "because, and then"
  | myeon => "if, when"
  | jiman => "but, although"
  | dorok => "so that, until"
  | nikka => "since, because"
  | ryeo => "intending to"

/-- The interclausal relations a converb encodes. -/
def relations : Converb → Finset InterclauseRelation
  | go => {.sequential, .additive}
  | myeonseo => {.simultaneous}
  | eoseo => {.causal, .sequential}
  | myeon => {.conditional}
  | jiman => {.concessive}
  | dorok | ryeo => {.purpose}
  | nikka => {.causal}

/-- Tense may be marked on the medial verb before the converb. -/
def AllowsTense (c : Converb) : Prop :=
  c = go ∨ c = myeonseo ∨ c = myeon ∨ c = jiman ∨ c = nikka

instance : DecidablePred AllowsTense :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _))

/-- The medial clause may be negated on its own before every converb. -/
def AllowsNegation (_ : Converb) : Prop := True

instance : DecidablePred AllowsNegation := fun _ => inferInstanceAs (Decidable True)

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
