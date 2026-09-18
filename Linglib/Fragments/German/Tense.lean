import Linglib.Fragments.German.Predicates
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
* `German.realize`: the words of a tense form of a verb, finite verb first.
* `German.tenseForms`, `German.southernTenseForms`: the forms of the standard language and of
  southern speech.
* `German.register`: the register of a form as a narrative tense.

## Implementation notes

`realize` gives the third person singular, the finite verb first and the nonfinite verbs in
their clause-final order, the lexical verb before the auxiliaries it stands under. The choice of
*sein* keys on unaccusativity, which covers the verbs of motion and change of state; *bleiben*
and *sein* themselves, which also take *sein*, are outside it.

## References

* [durrell-2011]
-/

namespace German

open ArgumentStructure.AuxiliarySelection SocialMeaning.Register

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
def Predicates.GermanVerbEntry.principalParts (v : Predicates.GermanVerbEntry) : PrincipalParts :=
  ⟨v.form, v.form3sg, v.formPast, v.formPastPart, perfectAuxiliary v.toVerb⟩

/-- `v.nonfinite ns` gives the nonfinite verbs of a tense form of `v` with nonfinite chain `ns`,
innermost first, and the verb left to be inflected. Each nonfinite form is taken by the verb
below it, and the auxiliary that governs it is the next verb up. German has no tense form with a
present participle. -/
def PrincipalParts.nonfinite (v : PrincipalParts) :
    List Tense.Form.Nonfinite → Option (List String × PrincipalParts)
  | [] => some ([], v)
  | n :: ns => do
    let (ws, u) ← v.nonfinite ns
    match n with
    | .pastParticiple => some (ws ++ [u.pastParticiple], u.perfectVerb)
    | .infinitive => some (ws ++ [u.infinitive], werden)
    | .presentParticiple => none

/-- `realize v f` gives the words of the tense form `f` of `v` in the third person singular, the
finite verb first and then the nonfinite verbs in their clause-final order. -/
def realize (v : PrincipalParts) (f : Tense.Form) : Option (List String) := do
  let (ws, u) ← v.nonfinite f.nonfinite
  match f.finite with
  | .present => some (u.present :: ws)
  | .past => some (u.past :: ws)
  | .future => none

/-- The nonfinite verbs of a tense form are as many as its nonfinite forms. -/
theorem PrincipalParts.length_of_nonfinite (v : PrincipalParts) :
    ∀ (ns : List Tense.Form.Nonfinite) {ws : List String} {u : PrincipalParts},
      v.nonfinite ns = some (ws, u) → ws.length = ns.length
  | [], ws, u, h => by
    obtain ⟨rfl, -⟩ : [] = ws ∧ v = u := by simpa [nonfinite] using h
    rfl
  | n :: ns, ws, u, h => by
    obtain ⟨⟨ws', u'⟩, h', h⟩ := Option.bind_eq_some_iff.1 h
    have ih := v.length_of_nonfinite ns h'
    cases n <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    all_goals obtain ⟨rfl, -⟩ := h; simp [ih]

/-- A realized tense form has one word for its finite verb and one for each nonfinite form. -/
theorem length_of_mem_realize {v : PrincipalParts} {f : Tense.Form} {ws : List String}
    (h : ws ∈ realize v f) : ws.length = f.nonfinite.length + 1 := by
  obtain ⟨⟨ws', u⟩, h', h⟩ := Option.bind_eq_some_iff.1 h
  have ih := v.length_of_nonfinite _ h'
  cases hf : f.finite <;> simp only [hf, Option.some.injEq, reduceCtorEq] at h
  all_goals subst h; simp [ih]

/-- Standard German has the present, the past, the perfect, the pluperfect, the future and the
future perfect. -/
def tenseForms : List Tense.Form :=
  [.simplePresent, .simplePast, .presentPerfect, .pastPerfect, .future, .futurePerfect]

/-- Southern speech lacks the past, and with it the standard pluperfect, and has the double
perfect. -/
def southernTenseForms : List Tense.Form :=
  [.simplePresent, .presentPerfect, .doublePerfect, .future, .futurePerfect]

/-- Every tense form of either variety is realized for every verb. -/
theorem realize_isSome (v : PrincipalParts) {f : Tense.Form}
    (hf : f ∈ tenseForms ∨ f ∈ southernTenseForms) : (realize v f).isSome := by
  simp only [tenseForms, southernTenseForms, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl) <;> rfl

/-- As a narrative tense the past belongs to written German and the double perfect to colloquial
speech, and the other forms are unmarked. -/
def register (f : Tense.Form) : Level :=
  if f = .simplePast then .formal else if f = .doublePerfect then .informal else .neutral

open Predicates in
/-- *zerbrechen* 'break', a transitive verb, forms its perfect with *haben*, and the unaccusative
*frieren* 'freeze' with *sein*. -/
example :
    realize zerbrechen.principalParts .presentPerfect = some ["hat", "zerbrochen"] ∧
      realize zerbrechen.principalParts .doublePerfect = some ["hat", "zerbrochen", "gehabt"] ∧
      realize zerbrechen.principalParts .futurePerfect = some ["wird", "zerbrochen", "haben"] ∧
      realize frieren.principalParts .pastPerfect = some ["war", "gefroren"] ∧
      realize frieren.principalParts .futurePerfect = some ["wird", "gefroren", "sein"] ∧
      realize frieren.principalParts .pastProgressive = none := by
  decide

end German
