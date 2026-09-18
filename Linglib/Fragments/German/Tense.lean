import Linglib.Syntax.Category.Verb.Tense

/-!
# German tense forms

This file lists the tense forms of German. The German verb has two synthetic tense forms, the
*Präsens* and the *Präteritum*, and builds the rest with auxiliaries. The *Perfekt* puts the past
participle under the present of *haben* or *sein*, as in *Borromini hat diese Kirche gebaut*
'Borromini built this church', and the *Plusquamperfekt* puts it under their *Präteritum*, as in
*den er selber gefangen hatte* 'that he had caught himself'. South German dialects have given up
the *Präteritum* except with a few stative verbs and use the *Perfekt* in its place; their form
for the past of the past is the double perfect, a perfect of the perfect auxiliary. The forms and
the dialect split follow the description in Kratzer's paper on pronouns and tenses. Which of
*haben* and *sein* a verb selects is the matter of
`Semantics/ArgumentStructure/AuxiliarySelection.lean`.

## TODO

The future forms with *werden* are not entered.

## References

* [kratzer-1998]
-/

namespace German

/-- The *Präsens* is the synthetic present, as *baut* 'builds'. -/
def praesens : Tense.Form := { name := "Präsens", finite := .Pres }

/-- The *Präteritum* is the synthetic past, as *baute* 'built'. -/
def praeteritum : Tense.Form := { name := "Präteritum", finite := .Past }

/-- The *Perfekt* puts the past participle under present *haben* or *sein*, as *hat gebaut*. -/
def perfekt : Tense.Form := { name := "Perfekt", finite := .Pres, nonfinite := [.pastParticiple] }

/-- The *Plusquamperfekt* puts the past participle under the *Präteritum* of *haben* or *sein*,
as *hatte gebaut*. -/
def plusquamperfekt : Tense.Form :=
  { name := "Plusquamperfekt", finite := .Past, nonfinite := [.pastParticiple] }

-- UNVERIFIED: the paper names the South German double perfect without an example; the make-up
-- entered here, the participle of the auxiliary over the participle of the verb, is the
-- traditional description of the form.
/-- The double perfect of the South German dialects is the perfect of the perfect auxiliary. -/
def doppelperfekt : Tense.Form :=
  { name := "Doppelperfekt", finite := .Pres, nonfinite := [.pastParticiple, .pastParticiple] }

/-- Standard German has these tense forms. -/
def tenseForms : List Tense.Form := [praesens, praeteritum, perfekt, plusquamperfekt]

/-- The South German dialects have these tense forms, lacking the *Präteritum* and with it the
*Plusquamperfekt*. -/
def southernTenseForms : List Tense.Form := [praesens, perfekt, doppelperfekt]

end German
