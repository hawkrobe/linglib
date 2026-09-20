import Linglib.Fragments.German.Verbs
import Linglib.Syntax.Category.Verb.Tense
import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
import Linglib.Semantics.ArgumentStructure.Unaccusativity
import Linglib.Pragmatics.SocialMeaning.Register

/-!
# German tense forms

This file describes the tense forms of German, following Durrell's reference grammar. German has
six tenses. Two are simple, the present *kauft* and the past *kaufte*, and four are compound.
The perfect *hat gekauft* and the pluperfect *hatte gekauft* put the past participle under the
present and the past of *haben* or *sein*, and the future *wird kaufen* and the future perfect
*wird gekauft haben* put an infinitive under the present of *werden*. German has no progressive
forms. A verb forms its perfect with *sein* when it is an intransitive verb of motion or of
change of state, and with *haben* otherwise; the auxiliaries *sein* and *haben* each form their
own perfect with themselves.

The past and the perfect overlap in meaning, and the choice between them is largely one of
register: narration is in the past in written German and in the perfect in speech. In South
Germany, Austria and Switzerland the past is practically never used in everyday speech, and the
pluperfect is there commonly formed with the perfect of the auxiliary, the double perfect *hat
gesehen gehabt*, which is colloquial and not accepted as standard.

## Main declarations

* `German.PrincipalParts`: the infinitive, third person singular present and past, and past
  participle of a verb, with its perfect auxiliary.
* `German.haben`, `German.sein`, `German.werden`: the tense auxiliaries.
* `German.perfectAuxiliary`: the perfect auxiliary of a verb entry, *sein* for an unaccusative.
* `German.periphrasis`, `German.PrincipalParts.tenseForm`: the means by which German builds its
  tense forms, and the words of a tense form of a verb, finite verb first.
* `German.tenseForms`, `German.southernTenseForms`: the forms of the standard language and of
  southern speech.
* `German.register`: the register of a form as a narrative tense.

## Implementation notes

`PrincipalParts.tenseForm` gives the third person singular, the finite verb first and the
nonfinite verbs in their clause-final order, the lexical verb before the auxiliaries it stands
under. The choice of *sein* keys on unaccusativity, which covers the verbs of motion and change of
state; *bleiben* and *sein* themselves, which also take *sein*, are outside it.

## References

* [durrell-2011]
-/

namespace German

open ArgumentStructure.AuxiliarySelection

/-- The principal parts of a verb, in the third person singular, with the auxiliary of its
perfect. -/
structure PrincipalParts where
  /-- The infinitive. -/
  infinitive : String
  /-- The third person singular present. -/
  present : String
  /-- The third person singular past. -/
  past : String
  /-- The past participle. -/
  pastParticiple : String
  /-- The auxiliary of the perfect. -/
  perfect : PerfectAux
  deriving DecidableEq, Repr

/-- The auxiliary *haben* forms the perfect of most verbs, and its own. -/
def haben : PrincipalParts := ⟨"haben", "hat", "hatte", "gehabt", .have⟩

/-- The auxiliary *sein* forms the perfect of intransitive verbs of motion and change of state,
and its own. -/
def sein : PrincipalParts := ⟨"sein", "ist", "war", "gewesen", .be⟩

/-- The auxiliary *werden* forms the future with the infinitive. -/
def werden : PrincipalParts := ⟨"werden", "wird", "wurde", "geworden", .be⟩

/-- The auxiliary verb a perfect is formed with. -/
def PrincipalParts.perfectVerb (v : PrincipalParts) : PrincipalParts :=
  match v.perfect with
  | .be => sein
  | .have => haben

/-- A verb forms its perfect with *sein* when it is unaccusative, and with *haben* otherwise. -/
def perfectAuxiliary (v : Verb) : PerfectAux := if v.IsUnaccusative then .be else .have

/-- The choice agrees with the selection rule for German, under which only the unaccusatives
among the transitivity classes select *sein*. -/
theorem germanSelection_eq_be_iff (c : TransitivityClass) :
    germanSelection c = .be ↔ c = .unaccusative := by
  cases c <;> decide

/-- The principal parts of a verb entry. -/
def Verbs.GermanVerbEntry.principalParts (v : Verbs.GermanVerbEntry) : PrincipalParts :=
  ⟨v.form, v.form3sg, v.formPast, v.formPastPart, perfectAuxiliary v.toVerb⟩

/-- German builds its tense forms with the past participle under the verb's perfect auxiliary and
the infinitive under *werden*. It has no future inflection and no form with a present
participle. -/
def periphrasis : Tense.Periphrasis PrincipalParts where
  finite
    | v, .present => some v.present
    | v, .past => some v.past
    | _, .future => none
  nonfinite
    | v, .pastParticiple => some v.pastParticiple
    | v, .infinitive => some v.infinitive
    | _, .presentParticiple => none
  auxiliary
    | v, .pastParticiple => some v.perfectVerb
    | _, .infinitive => some werden
    | _, .presentParticiple => none

/-- `v.tenseForm f` gives the words of the tense form `f` of `v` in the third person singular, the
finite verb first and then the nonfinite verbs in their clause-final order, the lexical verb
before the auxiliaries it stands under. -/
def PrincipalParts.tenseForm (v : PrincipalParts) (f : Tense.Form) : Option (List String) :=
  (periphrasis.realize v f).map fun x ↦ x.1 :: x.2

/-- A realized tense form has one word for its finite verb and one for each nonfinite form. -/
theorem PrincipalParts.length_of_mem_tenseForm {v : PrincipalParts} {f : Tense.Form}
    {ws : List String} (h : ws ∈ v.tenseForm f) : ws.length = f.nonfinite.length + 1 := by
  obtain ⟨x, hx, rfl⟩ := Option.mem_map.1 h
  simp [periphrasis.length_of_mem_realize hx]

/-- Standard German has the present, the past, the perfect, the pluperfect, the future and the
future perfect. -/
def tenseForms : List Tense.Form :=
  [.simplePresent, .simplePast, .presentPerfect, .pastPerfect, .future, .futurePerfect]

/-- Southern speech lacks the past, and with it the standard pluperfect, and has the double
perfect. -/
def southernTenseForms : List Tense.Form :=
  [.simplePresent, .presentPerfect, .doublePerfect, .future, .futurePerfect]

/-- Every tense form of either variety is realized for every verb. -/
theorem PrincipalParts.tenseForm_isSome (v : PrincipalParts) {f : Tense.Form}
    (hf : f ∈ tenseForms ∨ f ∈ southernTenseForms) : (v.tenseForm f).isSome := by
  simp only [tenseForms, southernTenseForms, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;> rfl

/-- As a narrative tense the past belongs to written German and the double perfect to colloquial
speech, and the other forms are unmarked. -/
def register (f : Tense.Form) : SocialMeaning.Register :=
  if f = .simplePast then .formal else if f = .doublePerfect then .informal else .neutral

open Verbs in
/-- *zerbrechen* 'break', a transitive verb, forms its perfect with *haben*, and the unaccusative
*frieren* 'freeze' with *sein*. -/
example :
    zerbrechen.principalParts.tenseForm .presentPerfect = some ["hat", "zerbrochen"] ∧
      zerbrechen.principalParts.tenseForm .doublePerfect = some ["hat", "zerbrochen", "gehabt"] ∧
      zerbrechen.principalParts.tenseForm .futurePerfect = some ["wird", "zerbrochen", "haben"] ∧
      frieren.principalParts.tenseForm .pastPerfect = some ["war", "gefroren"] ∧
      frieren.principalParts.tenseForm .futurePerfect = some ["wird", "gefroren", "sein"] ∧
      frieren.principalParts.tenseForm .pastProgressive = none := by
  decide

end German
