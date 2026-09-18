import Linglib.Syntax.Category.Verb.Tense

/-!
# German tense forms

This file lists the tense forms of German. The German verb has two synthetic tense forms, the
*Präsens*, which is the simple present, and the *Präteritum*, which is the simple past, and it
builds the rest with auxiliaries. The *Perfekt* is the present perfect, the past participle
under the present of *haben* or *sein*, as in *Borromini hat diese Kirche gebaut* 'Borromini
built this church'. The *Plusquamperfekt* is the past perfect, as in *den er selber gefangen
hatte* 'that he had caught himself'. South German dialects have given up the *Präteritum*
except with a few stative verbs and use the *Perfekt* in its place, and their form for the past
of the past is the double perfect. The forms and the dialect split follow the description in
Kratzer's paper on pronouns and tenses. Which of *haben* and *sein* a verb selects is the matter
of `Semantics/ArgumentStructure/AuxiliarySelection.lean`.

## TODO

The future forms with *werden* are not entered.

## References

* [kratzer-1998]
-/

namespace German

/-- Standard German has the *Präsens*, the *Präteritum*, the *Perfekt* and the
*Plusquamperfekt*. -/
def tenseForms : List Tense.Form := [.simplePresent, .simplePast, .presentPerfect, .pastPerfect]

-- UNVERIFIED: the paper names the South German double perfect without an example; its make-up
-- as the perfect of the perfect is the traditional description of the form.
/-- The South German dialects lack the *Präteritum*, and with it the *Plusquamperfekt*, and
have the double perfect. -/
def southernTenseForms : List Tense.Form := [.simplePresent, .presentPerfect, .doublePerfect]

end German
