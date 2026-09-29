module

public import Linglib.Fragments.German.Verbs
public import Linglib.Syntax.Category.Verb.Tense
public import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
public import Linglib.Semantics.ArgumentStructure.Unaccusativity
public import Linglib.Pragmatics.SocialMeaning.Register

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
* `German.perfect`: the auxiliary of the perfect of a verb on a frame, by the rule of §12.3.2.
* `German.periphrasis`, `German.PrincipalParts.tenseForm`: the means by which German builds its
  tense forms, and the words of a tense form of a verb, finite verb first.
* `German.tenseForms`, `German.southernTenseForms`: the forms of the standard language and of
  southern speech.
* `German.register`: the register of a form as a narrative tense.

## Implementation notes

`PrincipalParts.tenseForm` gives the third person singular, the finite verb first and the
nonfinite verbs in their clause-final order, the lexical verb before the auxiliaries it stands
under. The perfect auxiliary follows from the meaning of the verb on a frame, as Durrell's rule
has it, not from the verb alone: an accusative object, an unaccusative frame, a path of motion
and the continuation of a state are what the rule reads. So *rennen* 'run' takes *sein* as a
verb of motion although it is not unaccusative, and *tanzen* 'dance' takes *sein* only with a
directional phrase (`German.perfect_withPath_intransitive`). The verbs of happening of §12.3.2a
take *sein* on an unaccusative frame; the compounds of *gehen* and *werden* that take *sein* with
an accusative object (*die Strecke abgegangen*) are exceptions the rule does not cover.

## References

* [durrell-2011]
-/

@[expose] public section

namespace German

open ArgumentStructure (PerfectAux)

/-- The principal parts of a verb are its stem, the infinitive, the third person singular present
and past and the past participle, with the auxiliary of its perfect. -/
structure PrincipalParts extends Conjugation.Stem where
  /-- The auxiliary of the perfect. -/
  perfect : PerfectAux
  deriving DecidableEq, Repr

/-- The auxiliary *haben* forms the perfect of most verbs, and its own. -/
def haben : PrincipalParts := ⟨Conjugation.strong "haben" "hat" "hatte" "gehabt", .have⟩

/-- The auxiliary *sein* forms the perfect of intransitive verbs of motion and change of state,
and its own. -/
def sein : PrincipalParts := ⟨Conjugation.strong "sein" "ist" "war" "gewesen", .be⟩

/-- The auxiliary *werden* forms the future with the infinitive. -/
def werden : PrincipalParts := ⟨Conjugation.strong "werden" "wird" "wurde" "geworden", .be⟩

/-- The auxiliary verb a perfect is formed with. -/
def PrincipalParts.perfectVerb (v : PrincipalParts) : PrincipalParts :=
  match v.perfect with
  | .be => sein
  | .have => haben

/-- The auxiliary of the perfect of `v` on the frame `fr` ([durrell-2011] §12.3.2): *sein* on an
unaccusative frame, for a change of state or a verb of happening (a.ii, a.iii); *haben* on a frame
with an accusative object (b.i); *sein* for a verb of motion and for the continuation of a state,
*bleiben* (a.i, a.iv); and *haben* otherwise (b.iii–v). -/
def perfect (v : Verb) (fr : ArgumentFrame) : PerfectAux :=
  if fr.IsUnaccusative then .be
  else if fr.HasNominal ∧ .acc ∈ v.objects then .have
  else if v.direction.isSome ∨ v.phasal = some .continuation then .be
  else .have

/-- A directional phrase gives an intransitive verb *sein*: the verbs of motion that name the
activity as such, *tanzen* 'dance' and *segeln* 'sail', take *sein* when they express movement
from one place to another (§12.3.2c). -/
theorem perfect_withPath_intransitive (v : Verb) {p : Adposition.SpatialReading}
    (hv : v.TakesSpatial) (hp : p.direction ≠ .place) :
    perfect (v.withPath p) .intransitive = .be := by
  simp [perfect, _root_.Verb.direction_withPath hv hp, ArgumentFrame.intransitive,
    ArgumentFrame.IsUnaccusative, ArgumentFrame.HasNominal]

/-- The verbs of manner of motion select a directional phrase: every entry that displaces its
subject with no direction takes a spatial complement (§12.3.2c). -/
theorem takesSpatial_of_direction_eq_place :
    ∀ v ∈ Verbs.allVerbs, v.direction = some .place → v.TakesSpatial := by
  decide

/-- The principal parts of a verb entry on a frame, its citation frame by default, are its stem
with the auxiliary of its perfect there. -/
def Verb.principalParts (v : Verb) (fr : ArgumentFrame := v.frames.headD .intransitive) :
    PrincipalParts :=
  ⟨v.stem, perfect v fr⟩

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
/-- The groups of §12.3.2: *sein* for the verbs of motion *rennen*, *laufen* and *ankommen*, for
*frieren* as a change of state and for *bleiben*; *haben* for the transitive *bauen*, for
*arbeiten* and *tanzen*, which denote an activity as such, and for impersonal *frieren*; and
*sein* for *tanzen* with a directional phrase, which it selects, but not for *arbeiten*, which
selects none. -/
example :
    [perfect rennen .intransitive, perfect laufen .intransitive, perfect ankommen .unaccusative,
      perfect frieren .unaccusative, perfect bleiben .intransitive] = [.be, .be, .be, .be, .be] ∧
    [perfect bauen .np, perfect arbeiten .intransitive, perfect tanzen .intransitive,
      perfect frieren .impersonal] = [.have, .have, .have, .have] ∧
    perfect (tanzen.withPath Adposition.into) .intransitive = .be ∧
    perfect (arbeiten.withPath Adposition.into) .intransitive = .have := by
  decide

open Verbs in
/-- *zerbrechen* 'break', a transitive verb, forms its perfect with *haben*, and the unaccusative
*frieren* 'freeze' and *rennen* 'run', a verb of motion, with *sein*. -/
example :
    zerbrechen.principalParts.tenseForm .presentPerfect = some ["hat", "zerbrochen"] ∧
      zerbrechen.principalParts.tenseForm .doublePerfect = some ["hat", "zerbrochen", "gehabt"] ∧
      zerbrechen.principalParts.tenseForm .futurePerfect = some ["wird", "zerbrochen", "haben"] ∧
      frieren.principalParts.tenseForm .pastPerfect = some ["war", "gefroren"] ∧
      frieren.principalParts.tenseForm .futurePerfect = some ["wird", "gefroren", "sein"] ∧
      frieren.principalParts.tenseForm .pastProgressive = none ∧
      rennen.principalParts.tenseForm .presentPerfect = some ["ist", "gerannt"] := by
  decide

end German
