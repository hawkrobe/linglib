module

public import Linglib.Syntax.Voice.Basic
public import Linglib.Fragments.Finnish.Infinitives

/-!
# Finnish verbs

A Finnish verb has two stems. The infinitive stem is the dictionary form without the ending of
the A infinitive, as *tul-* of *tul-la* 'come', and the inflectional stem, from which the
present is formed, is *tule-*, as in *tule-n* 'I come'. Karlsson sorts the verbs into six
conjugations by how the two stems are related, each named after a member. *Anta-a* 'give'
verbs, whose infinitive ending follows a short vowel, and *saa-da* 'get' verbs, whose ending
follows a long vowel or a diphthong, have the infinitive stem alone. *Tul-la* 'come' and
*nous-ta* 'rise' verbs add -e to it. The final -t of the infinitive stem becomes -A in
*huomat-a* 'notice' verbs, is followed by -se in *tarvit-a* 'need' verbs and becomes -ne in
*lämm-et-ä* 'get warm' verbs. Consonant gradation gives the infinitive stem the weak grade
where the inflectional stem has the strong one, as in *hypät-ä* 'jump' against *hyppää-n* 'I
jump'.

Each verb has an active and an impersonal form, as *avat-a* 'open' has *avaa* 'opens' and
*avat-a-an* 'one opens, it is opened'. The impersonal form, traditionally the passive and the
fourth person of Karlsson's grammar, says that an unspecified human agent performs the
action, has no subject expressed as an independent phrase, and admits no correspondent to an
Indo-European *by*-agent; it is the impersonal passive of the typology.

A verb taking an infinitival complement governs its infinitive and case, the A infinitive for
*uskaltaa* 'dare', as in *uskals-i avat-a ove-n* 'dared to open the door', and the MA
infinitive illative for *pystyä* 'be able', as in *pysty-i tappelema-an* 'was able to fight'.
The entries include the implicative verbs of [nadathur-2023-implicatives], with the polarity
of the complement they entail.

## Main definitions

* `Finnish.Conjugation`: Karlsson's six conjugations.
* `Finnish.Verb`: a Finnish verb, the root `Verb` with its conjugation, its two stems and the
  infinitive its complement takes.
* `Finnish.Verb.infinitive`: the infinitives of a verb.
* `Finnish.verbs`: the entries.

## Main results

* `Finnish.ofString?_form`: the citation form of each entry is the A infinitive of its stem.
* `Finnish.inflectionalStem_eq`: the verbs of the *anta-a* and *saa-da* conjugations have one
  stem.
* `Finnish.complement_mem_cases`: each entry's complement is in a case its infinitive takes.

## References

* [karlsson-2017]
* [nadathur-2023-implicatives]
-/

@[expose] public section

namespace Finnish

open Phonology

/-- The conjugations, named after a member (§6.2). -/
inductive Conjugation where
  /-- The infinitive ending follows a short vowel, and there is one stem: *anta-a* 'give'. -/
  | antaa
  /-- The infinitive ending follows a long vowel or a diphthong, and there is one stem:
  *saa-da* 'get'. -/
  | saada
  /-- The inflectional stem adds -e: *tul-la* 'come', *nous-ta* 'rise'. -/
  | tulla
  /-- The final -t of the infinitive stem is -A in the inflectional stem: *huomat-a*
  'notice'. -/
  | huomata
  /-- The inflectional stem adds -se: *tarvit-a* 'need'. -/
  | tarvita
  /-- The final -t of the infinitive stem is -ne in the inflectional stem: *lämm-et-ä* 'get
  warm'. -/
  | lämmetä
  deriving DecidableEq, Repr

/-- A Finnish verb is the root entry, whose `form` is the A infinitive, together with its
conjugation, its two stems and the infinitive and case its complement takes. -/
structure Verb extends _root_.Verb where
  /-- The conjugation. -/
  conjugation : Conjugation
  /-- The infinitive stem, on which the A and E infinitives are built. -/
  infinitiveStem : List Segment
  /-- The inflectional stem, in the strong grade, on which the present and the MA and MINEN
  infinitives are built. -/
  inflectionalStem : List Segment
  /-- The infinitive and case of the complement. -/
  complement : Option (Infinitive × Case) := none

namespace Verb

/-- The infinitive `i` of the verb before a case ending: the A and E infinitives are built on
the infinitive stem, the MA and MINEN infinitives on the inflectional stem. -/
def infinitive (v : Verb) : Infinitive → List Segment
  | .a => surface (Infinitive.a.base v.infinitiveStem)
  | .e => surface (Infinitive.e.base v.infinitiveStem)
  | .ma => surface (Infinitive.ma.base v.inflectionalStem)
  | .minen => surface (Infinitive.minen.base v.inflectionalStem)

end Verb

/-! ### Voice

The impersonal passive is marked by the suffix *-tA-* and its variants with the personal ending
*-Vn* ([karlsson-2017] §21.1). The inventory lists the voices projecting transitive clauses. -/

/-- The impersonal passive, the fourth person: the passive marker, *-ttA*, *-tA*, *-dA* or
*-A*, with the personal ending *-Vn*. -/
def impersonalPassive : Voice := Voice.impersonalPassive.marked [.suff "tA", .suff "Vn"]

/-- The active and the impersonal passive. -/
def voices : Finset Voice := {.active, impersonalPassive}

/-! ### Entries -/

/-- *avata* 'open', with *avaa* 'opens' and the impersonal *avataan*. -/
def avata : Verb where
  form := "avata"
  frames := [ArgumentFrame.np]
  conjugation := .huomata
  infinitiveStem := [a, v, a, t]
  inflectionalStem := [a, v, a, a]

/-- *lukea* 'read'. -/
def lukea : Verb where
  form := "lukea"
  frames := [ArgumentFrame.np]
  conjugation := .antaa
  infinitiveStem := [l, u, k, e]
  inflectionalStem := [l, u, k, e]

/-- *tulla* 'come'. -/
def tulla : Verb where
  form := "tulla"
  frames := [ArgumentFrame.intransitive]
  conjugation := .tulla
  infinitiveStem := [t, u, l]
  inflectionalStem := [t, u, l, e]

/-- *haluta* 'want', with the A infinitive. -/
def haluta : Verb where
  form := "haluta"
  frames := [ArgumentFrame.np, ArgumentFrame.infinitival]
  conjugation := .huomata
  infinitiveStem := [h, a, l, u, t]
  inflectionalStem := [h, a, l, u, a]
  complement := some (.a, .nom)

/-! ### Implicative verbs

The positive implicatives entail their complement or its negation, *onnistua* 'manage' both
ways and *jaksaa* 'have the strength' only when negated. *Laiminlyödä* 'neglect' and
*epäröidä* 'hesitate' reverse the polarity. -/

/-- *onnistua* 'succeed, manage', with the MA infinitive illative. -/
def onnistua : Verb where
  form := "onnistua"
  frames := [ArgumentFrame.infinitival]
  conjugation := .antaa
  infinitiveStem := [o, n, n, i, s, t, u]
  inflectionalStem := [o, n, n, i, s, t, u]
  complement := some (.ma, .ill)
  implicative := some .positive

/-- *uskaltaa* 'dare'. -/
def uskaltaa : Verb where
  form := "uskaltaa"
  frames := [ArgumentFrame.infinitival]
  conjugation := .antaa
  infinitiveStem := [u, s, k, a, l, t, a]
  inflectionalStem := [u, s, k, a, l, t, a]
  complement := some (.a, .nom)
  implicative := some .positive

/-- *viitsiä* 'bother'. -/
def viitsiä : Verb where
  form := "viitsiä"
  frames := [ArgumentFrame.infinitival]
  conjugation := .antaa
  infinitiveStem := [v, i, i, t, s, i]
  inflectionalStem := [v, i, i, t, s, i]
  complement := some (.a, .nom)
  implicative := some .positive

/-- *malttaa* 'have the patience'. -/
def malttaa : Verb where
  form := "malttaa"
  frames := [ArgumentFrame.infinitival]
  conjugation := .antaa
  infinitiveStem := [m, a, l, t, t, a]
  inflectionalStem := [m, a, l, t, t, a]
  complement := some (.a, .nom)
  implicative := some .positive

/-- *hennoa* 'have the heart'. -/
def hennoa : Verb where
  form := "hennoa"
  frames := [ArgumentFrame.infinitival]
  conjugation := .antaa
  infinitiveStem := [h, e, n, n, o]
  inflectionalStem := [h, e, n, n, o]
  complement := some (.a, .nom)
  implicative := some .positive

/-- *kehdata* 'be unembarrassed, act without shame'. -/
def kehdata : Verb where
  form := "kehdata"
  frames := [ArgumentFrame.infinitival]
  conjugation := .huomata
  infinitiveStem := [k, e, h, d, a, t]
  inflectionalStem := [k, e, h, t, a, a]
  complement := some (.a, .nom)
  implicative := some .positive

/-- *ehtiä* 'find time, make time'. -/
def ehtiä : Verb where
  form := "ehtiä"
  frames := [ArgumentFrame.infinitival]
  conjugation := .antaa
  infinitiveStem := [e, h, t, i]
  inflectionalStem := [e, h, t, i]
  complement := some (.a, .nom)
  implicative := some .positive

/-- *jaksaa* 'have the strength'. -/
def jaksaa : Verb where
  form := "jaksaa"
  frames := [ArgumentFrame.infinitival]
  conjugation := .antaa
  infinitiveStem := [j, a, k, s, a]
  inflectionalStem := [j, a, k, s, a]
  complement := some (.a, .nom)
  implicative := some .positive

/-- *mahtua* 'fit, be small enough', with the MA infinitive illative. -/
def mahtua : Verb where
  form := "mahtua"
  frames := [ArgumentFrame.infinitival]
  conjugation := .antaa
  infinitiveStem := [m, a, h, t, u]
  inflectionalStem := [m, a, h, t, u]
  complement := some (.ma, .ill)
  implicative := some .positive

/-- *pystyä* 'be able', with the MA infinitive illative. -/
def pystyä : Verb where
  form := "pystyä"
  frames := [ArgumentFrame.infinitival]
  conjugation := .antaa
  infinitiveStem := [p, y, s, t, y]
  inflectionalStem := [p, y, s, t, y]
  complement := some (.ma, .ill)
  implicative := some .positive

/-- *laiminlyödä* 'neglect'. -/
def laiminlyödä : Verb where
  form := "laiminlyödä"
  frames := [ArgumentFrame.infinitival]
  conjugation := .saada
  infinitiveStem := [l, a, i, m, i, n, l, y, ö]
  inflectionalStem := [l, a, i, m, i, n, l, y, ö]
  complement := some (.a, .nom)
  implicative := some .negative

/-- *epäröidä* 'hesitate'. -/
def epäröidä : Verb where
  form := "epäröidä"
  frames := [ArgumentFrame.infinitival]
  conjugation := .saada
  infinitiveStem := [e, p, ä, r, ö, i]
  inflectionalStem := [e, p, ä, r, ö, i]
  complement := some (.a, .nom)
  implicative := some .negative

/-- The entries. -/
def verbs : List Verb :=
  [avata, lukea, tulla, haluta, onnistua, uskaltaa, viitsiä, malttaa, hennoa, kehdata, ehtiä,
    jaksaa, mahtua, pystyä, laiminlyödä, epäröidä]

/-- The citation form of each entry is the A infinitive of its infinitive stem. -/
theorem ofString?_form : ∀ v ∈ verbs, ofString? v.form = some (v.infinitive .a) := by
  decide +kernel

/-- The verbs of the *anta-a* and *saa-da* conjugations have one stem. -/
theorem inflectionalStem_eq : ∀ v ∈ verbs, v.conjugation = .antaa ∨ v.conjugation = .saada →
    v.inflectionalStem = v.infinitiveStem := by
  decide +kernel

/-- Each entry's complement is in a case its infinitive takes. -/
theorem complement_mem_cases : ∀ v ∈ verbs, ∀ ic ∈ v.complement, ic.2 ∈ ic.1.cases := by
  decide +kernel

end Finnish
