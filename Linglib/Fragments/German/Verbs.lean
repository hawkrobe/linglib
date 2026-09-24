module

public import Linglib.Fragments.German.Conjugation
public import Linglib.Semantics.Presupposition.Verb
public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Category.Verb.CaseArray

/-!
# German verbs

This file defines the German verb as a lexical entry: the root `Verb` with its case array and its
stem, the infinitive, third person singular present and past and past participle its conjugation
is built from. The stem of a weak verb is built from its infinitive and that of a verb with a prefix
from the verb it is formed on, by the rules of `German.Conjugation`, so that *bestraft* comes from
*strafen* and *zeigt an* from *zeigen*; a strong verb gives its own principal parts. A verb whose
only object is in the dative, as *danken* 'thank' and *gratulieren* 'congratulate' are, records the
dative in its case array.

The entries are the verbs the studies use: a few causative and attitude verbs, *bauen* 'build',
the simple, change-of-state and prefixed verbs of Benz's resultatives and nominalizations, the
sixteen occasion verbs whose presuppositions Solstad and Bott test for projection, and the
predicates of Schwarzer's experiments, four that take a *dass*-clause and four that do not. The
present tense of *kaufen* 'buy' is the paradigm Dalrymple and Kaplan use for indeterminate
agreement.

## Main definitions

* `German.Verb`: the entry, the root `Verb` with its case array and its stem.
* `German.Verb.ofStem`: the entry with the forms of a stem.
* `German.Verbs.allVerbs`: the entries.
* `German.Verbs.kaufen`: the present tense of *kaufen*.

## References

* [durrell-2011]
* [benz-2025]
* [solstad-bott-2024]
* [schwarzer-2026]
* [dalrymple-kaplan-2000]
-/

@[expose] public section

namespace German

/-- A German verb is the root entry with its case array and its stem. -/
structure Verb extends _root_.Verb, _root_.Verb.CaseArray where
  /-- The stem, from which the verb conjugates. -/
  stem : Conjugation.Stem
  deriving BEq

/-- `Verb.ofStem s` is the entry cited by the infinitive of `s`, with its forms and no further
lexical information. -/
def Verb.ofStem (s : Conjugation.Stem) : Verb := { form := s.infinitive, frames := [], stem := s }

namespace Verbs

open ArgumentStructure Conjugation

/-! ### Causative verbs -/

/-- *lassen* 'let' is a permissive causative with a small clause, as in *Sie ließ ihn gehen* 'she
let him go'. -/
def lassen : Verb :=
  { Verb.ofStem (strong "lassen" "lässt" "ließ" "gelassen") with
    frames := [ArgumentFrame.smallClause]
    readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
    causative := some .enable, objects := [.acc] }

/-- *machen* 'make' is the productive causative, as in *Das macht mich traurig* 'that makes me
sad'. -/
def machen : Verb :=
  { Verb.ofStem (weak "machen") with
    frames := [ArgumentFrame.smallClause]
    readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
    causative := some .make, objects := [.acc] }

/-- *töten* 'kill' is a lexical causative formed on the adjective *tot* 'dead'. -/
def toeten : Verb :=
  { Verb.ofStem (weak "töten") with
    frames := [ArgumentFrame.np], causative := some .make, objects := [.acc] }

/-- *bauen* 'build' is a transitive verb of creation, as in *Borromini baute diese Kirche*
'Borromini built this church'. -/
def bauen : Verb :=
  { Verb.ofStem (weak "bauen") with frames := [ArgumentFrame.np], objects := [.acc] }

/-! ### Verbs of Benz's resultatives and nominalizations -/

/-- *hämmern* 'hammer' is an activity. -/
def haemmern : Verb :=
  { Verb.ofStem (weak "hämmern") with
    frames := [ArgumentFrame.np], vendlerClass := some .activity, objects := [.acc] }

/-- *malen* 'paint' is an activity. -/
def malen : Verb :=
  { Verb.ofStem (weak "malen") with
    frames := [ArgumentFrame.np], vendlerClass := some .activity, objects := [.acc] }

/-- *bemalen* 'paint over' is an accomplishment formed on *malen* with the inseparable *be-*. -/
def bemalen : Verb :=
  { Verb.ofStem (malen.stem.inseparable "be") with
    frames := [ArgumentFrame.np], vendlerClass := some .accomplishment, objects := [.acc] }

/-- *küssen* 'kiss' is an activity. -/
def kuessen : Verb :=
  { Verb.ofStem (weak "küssen") with
    frames := [ArgumentFrame.np], vendlerClass := some .activity, objects := [.acc] }

/-- *führen* 'lead' is an activity. -/
def fuehren : Verb :=
  { Verb.ofStem (weak "führen") with
    frames := [ArgumentFrame.np], vendlerClass := some .activity, objects := [.acc] }

/-- *einführen* 'introduce' is an accomplishment formed on *führen* with the separable *ein-*. -/
def einfuehren : Verb :=
  { Verb.ofStem (fuehren.stem.separable "ein") with
    frames := [ArgumentFrame.np], vendlerClass := some .accomplishment, objects := [.acc] }

/-- *rauben* 'rob' is an activity. -/
def rauben : Verb :=
  { Verb.ofStem (weak "rauben") with
    frames := [ArgumentFrame.np], vendlerClass := some .activity, objects := [.acc] }

/-- *verkaufen* 'sell' is formed on *kaufen* with the inseparable *ver-*. -/
def verkaufen : Verb :=
  { Verb.ofStem ((weak "kaufen").inseparable "ver") with
    frames := [ArgumentFrame.np], objects := [.acc] }

/-- *rennen* 'run' is an irregular weak verb. -/
def rennen : Verb :=
  { Verb.ofStem (strong "rennen" "rennt" "rannte" "gerannt") with
    frames := [ArgumentFrame.intransitive], vendlerClass := some .activity }

/-- *brechen* 'break' is an achievement. -/
def brechen : Verb :=
  { Verb.ofStem (strong "brechen" "bricht" "brach" "gebrochen") with
    frames := [ArgumentFrame.np], vendlerClass := some .achievement, objects := [.acc] }

/-- *zerbrechen* 'break' is a lexical causative formed on *brechen* with the inseparable *zer-*. -/
def zerbrechen : Verb :=
  { Verb.ofStem (brechen.stem.inseparable "zer") with
    frames := [ArgumentFrame.np], causative := some .make, objects := [.acc] }

/-- *frieren* 'freeze' is an unaccusative achievement. -/
def frieren : Verb :=
  { Verb.ofStem (strong "frieren" "friert" "fror" "gefroren") with
    frames := [ArgumentFrame.unaccusative], vendlerClass := some .achievement }

/-- *schießen* 'shoot' is a transitive verb. -/
def schiessen : Verb :=
  { Verb.ofStem (strong "schießen" "schießt" "schoss" "geschossen") with
    frames := [ArgumentFrame.np], objects := [.acc] }

/-- *schämen* 'be ashamed' is inherently reflexive, *sich schämen*. -/
def schaemen : Verb :=
  { Verb.ofStem (weak "schämen") with frames := [ArgumentFrame.intransitive] }

/-- *beobachten* 'observe' is an accomplishment with the inseparable *be-*. -/
def beobachten : Verb :=
  { Verb.ofStem ((weak "obachten").inseparable "be") with
    frames := [ArgumentFrame.np], vendlerClass := some .accomplishment, objects := [.acc] }

/-- *verbinden* 'connect' is an accomplishment formed on *binden* with the inseparable *ver-*. -/
def verbinden : Verb :=
  { Verb.ofStem ((strong "binden" "bindet" "band" "gebunden").inseparable "ver") with
    frames := [ArgumentFrame.np], vendlerClass := some .accomplishment, objects := [.acc] }

/-! ### Attitude verbs -/

/-- *hoffen* 'hope' is a positive preferential attitude verb. -/
def hoffen : Verb :=
  { Verb.ofStem (weak "hoffen") with
    frames := [ArgumentFrame.finiteClause], passivizable := false, opaqueContext := true
    attitude := some (.preferential (.degreeComparison .positive)) }

/-- *wünschen* 'wish' is a positive preferential attitude verb. -/
def wuenschen : Verb :=
  { Verb.ofStem (weak "wünschen") with
    frames := [ArgumentFrame.finiteClause], passivizable := false, opaqueContext := true
    attitude := some (.preferential (.degreeComparison .positive)) }

/-- *fürchten* 'fear' is a negative preferential attitude verb. -/
def fuerchten : Verb :=
  { Verb.ofStem (weak "fürchten") with
    frames := [ArgumentFrame.finiteClause], passivizable := false, opaqueContext := true
    attitude := some (.preferential (.degreeComparison .negative)) }

/-- *befürchten* 'be afraid of' is formed on *fürchten* with the inseparable *be-*. -/
def befuerchten : Verb :=
  { Verb.ofStem (fuerchten.stem.inseparable "be") with
    frames := [ArgumentFrame.finiteClause], passivizable := false, opaqueContext := true
    attitude := some (.preferential (.degreeComparison .negative)) }

/-- *sorgen* 'worry' is used reflexively, *sich sorgen*, and is based on uncertainty. -/
def sorgen : Verb :=
  { Verb.ofStem (weak "sorgen") with
    frames := [ArgumentFrame.finiteClause], passivizable := false, opaqueContext := true
    attitude := some (.preferential .uncertaintyBased) }

/-! ### Occasion verbs

An occasion verb presupposes an earlier eventuality of its object's that occasions the action:
*bestrafen* 'punish' presupposes a wrong, *belohnen* 'reward' a merit. -/

/-- *bestrafen* 'punish' is formed on *strafen* with the inseparable *be-*. -/
def bestrafen : Verb :=
  { Verb.ofStem ((weak "strafen").inseparable "be") with
    frames := [ArgumentFrame.np], senseTag := .occasion, objects := [.acc] }

/-- *belohnen* 'reward' is formed on *lohnen* with the inseparable *be-*. -/
def belohnen : Verb :=
  { Verb.ofStem ((weak "lohnen").inseparable "be") with
    frames := [ArgumentFrame.np], senseTag := .occasion, objects := [.acc] }

/-- *loben* 'praise' is a weak verb. -/
def loben : Verb :=
  { Verb.ofStem (weak "loben") with
    frames := [ArgumentFrame.np], senseTag := .occasion, objects := [.acc] }

/-- *kritisieren* 'criticize' is a verb in *-ieren*. -/
def kritisieren : Verb :=
  { Verb.ofStem (weak "kritisieren") with
    frames := [ArgumentFrame.np], senseTag := .occasion, objects := [.acc] }

/-- *danken* 'thank' takes its object in the dative. -/
def danken : Verb :=
  { Verb.ofStem (weak "danken") with
    frames := [ArgumentFrame.np], senseTag := .occasion, objects := [.dat] }

/-- *verklagen* 'sue' is formed on *klagen* with the inseparable *ver-*. -/
def verklagen : Verb :=
  { Verb.ofStem ((weak "klagen").inseparable "ver") with
    frames := [ArgumentFrame.np], senseTag := .occasion, objects := [.acc] }

/-- *gratulieren* 'congratulate' takes its object in the dative. -/
def gratulieren : Verb :=
  { Verb.ofStem (weak "gratulieren") with
    frames := [ArgumentFrame.np], senseTag := .occasion, objects := [.dat] }

/-- *zurechtweisen* 'reprimand' is formed on *weisen* with the separable *zurecht-*. -/
def zurechtweisen : Verb :=
  { Verb.ofStem ((strong "weisen" "weist" "wies" "gewiesen").separable "zurecht") with
    frames := [ArgumentFrame.np], senseTag := .occasion, objects := [.acc] }

/-- *anzeigen* 'report (to the authorities)' is formed on *zeigen* with the separable *an-*. -/
def anzeigen : Verb :=
  { Verb.ofStem ((weak "zeigen").separable "an") with
    frames := [ArgumentFrame.np], senseTag := .occasion, objects := [.acc] }

/-- *auszeichnen* 'honour (with an award)' is formed on *zeichnen* with the separable *aus-*. -/
def auszeichnen : Verb :=
  { Verb.ofStem ((weak "zeichnen").separable "aus") with
    frames := [ArgumentFrame.np], senseTag := .occasion, objects := [.acc] }

/-- *belangen* 'prosecute' is formed on *langen* with the inseparable *be-*. -/
def belangen : Verb :=
  { Verb.ofStem ((weak "langen").inseparable "be") with
    frames := [ArgumentFrame.np], senseTag := .occasion, objects := [.acc] }

/-- *ehren* 'honour' is a weak verb. -/
def ehren : Verb :=
  { Verb.ofStem (weak "ehren") with
    frames := [ArgumentFrame.np], senseTag := .occasion, objects := [.acc] }

/-- *entlassen* 'dismiss' is formed on *lassen* with the inseparable *ent-*. -/
def entlassen : Verb :=
  { Verb.ofStem (lassen.stem.inseparable "ent") with
    frames := [ArgumentFrame.np], senseTag := .occasion, objects := [.acc] }

/-- *rächen* 'avenge' is used reflexively with *an*, *sich rächen an* 'take revenge on'. -/
def raechen : Verb :=
  { Verb.ofStem (weak "rächen") with frames := [ArgumentFrame.np], senseTag := .occasion }

/-- *revanchieren* 'return the favour' is used reflexively with *bei*, *sich revanchieren bei*. -/
def revanchieren : Verb :=
  { Verb.ofStem (weak "revanchieren") with frames := [ArgumentFrame.np], senseTag := .occasion }

/-- *zur Verantwortung ziehen* 'hold accountable' is a phrase whose noun phrase stands where a
separable particle would. -/
def zurVerantwortungZiehen : Verb :=
  { Verb.ofStem
      { infinitive := "zur Verantwortung ziehen", present := "zieht zur Verantwortung",
        past := "zog zur Verantwortung", participle := "zur Verantwortung gezogen",
        prefixGe := false } with
    frames := [ArgumentFrame.np], senseTag := .occasion, objects := [.acc] }

/-! ### Predicates of Schwarzer's experiments -/

/-- *beenden* 'end' is formed on *enden* with the inseparable *be-*, and takes a noun phrase and no
*dass*-clause. -/
def beenden : Verb :=
  { Verb.ofStem ((weak "enden").inseparable "be") with
    frames := [ArgumentFrame.np], vendlerClass := some .accomplishment, objects := [.acc] }

/-- *streichen* 'cancel' takes a noun phrase and no *dass*-clause. -/
def streichen : Verb :=
  { Verb.ofStem (strong "streichen" "streicht" "strich" "gestrichen") with
    frames := [ArgumentFrame.np], vendlerClass := some .accomplishment, objects := [.acc] }

/-- *übereilen* 'rush' is formed on *eilen* with the inseparable *über-*, and takes a noun phrase
and no *dass*-clause. -/
def uebereilen : Verb :=
  { Verb.ofStem ((weak "eilen").inseparable "über") with
    frames := [ArgumentFrame.np], objects := [.acc] }

/-- *entwickeln* 'develop' is formed on *wickeln* with the inseparable *ent-*, and takes a noun
phrase and no *dass*-clause. -/
def entwickeln : Verb :=
  { Verb.ofStem ((weak "wickeln").inseparable "ent") with
    frames := [ArgumentFrame.np], vendlerClass := some .accomplishment, objects := [.acc] }

/-- *veranlassen* 'induce' is a weak verb formed with *ver-* on the noun *Anlass* 'occasion', and
takes a noun phrase or a *dass*-clause. -/
def veranlassen : Verb :=
  { Verb.ofStem ((weak "anlassen").inseparable "ver") with
    frames := [ArgumentFrame.np, ArgumentFrame.finiteClause], objects := [.acc] }

/-- *vergessen* 'forget' takes a noun phrase or a *dass*-clause; its *ver-* is not separable from
a simple verb of today. -/
def vergessen : Verb :=
  { Verb.ofStem
      { infinitive := "vergessen", present := "vergisst", past := "vergaß",
        participle := "vergessen", prefixGe := false } with
    frames := [ArgumentFrame.np, ArgumentFrame.finiteClause], opaqueContext := true
    objects := [.acc] }

/-- *erwarten* 'expect' is formed on *warten* with the inseparable *er-*, and takes a noun phrase
or a *dass*-clause. -/
def erwarten : Verb :=
  { Verb.ofStem ((weak "warten").inseparable "er") with
    frames := [ArgumentFrame.np, ArgumentFrame.finiteClause], opaqueContext := true
    objects := [.acc] }

/-- *beschließen* 'decide' is formed on *schließen* with the inseparable *be-*, and takes a noun
phrase or a *dass*-clause. -/
def beschliessen : Verb :=
  { Verb.ofStem ((strong "schließen" "schließt" "schloss" "geschlossen").inseparable "be") with
    frames := [ArgumentFrame.np, ArgumentFrame.finiteClause], objects := [.acc] }

/-! ### The entries -/

/-- `allVerbs` lists the entries. -/
def allVerbs : List Verb :=
  [lassen, machen, toeten, bauen,
   haemmern, malen, bemalen, kuessen, fuehren, einfuehren, rauben, verkaufen, rennen,
   brechen, zerbrechen, frieren, schiessen, schaemen, beobachten, verbinden,
   hoffen, wuenschen, fuerchten, befuerchten, sorgen,
   bestrafen, belohnen, loben, kritisieren, danken, verklagen, gratulieren, zurechtweisen,
   anzeigen, auszeichnen, belangen, ehren, entlassen, raechen, revanchieren,
   zurVerantwortungZiehen,
   beenden, streichen, uebereilen, entwickeln, veranlassen, vergessen, erwarten, beschliessen]

/-- Every entry is cited by the infinitive of its stem. -/
theorem form_eq_infinitive : ∀ v ∈ allVerbs, v.form = v.stem.infinitive := by decide

/-- `kaufen` gives the present tense of *kaufen* 'buy'. -/
def kaufen : Person × Number → Option String := weakPresent "kaufen"

end Verbs

end German
