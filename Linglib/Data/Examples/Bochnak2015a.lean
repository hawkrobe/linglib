module

public import Linglib.Data.Examples.Schema

/-!
# `Bochnak2015a` — typed example data

Auto-generated from `Linglib/Data/Examples/Bochnak2015a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Bochnak2015a.Examples`.
-/

@[expose] public section

namespace Bochnak2015a.Examples

open Data.Examples

def ex10 : LinguisticExample :=
  { id := "bochnak2015a_ex10"
    source := ⟨"bochnak-2015a", "(10b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "bévali wí:diʔ lé:šɨl k’éʔi"
    discourseSegments := []
    glossedTokens := [("bevali", "Beverly"), ("wi:diʔ", "this"), ("le-išɨl", "1-give"), ("k’-eʔ-i", "3-MOD-IPFV")]
    translation := "I need to give this to Beverly."
    context := "You borrowed a pot from Beverly, and now you need to give it back to her."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "necessity"), ("flavor", "deontic")]
    comment := "" }

def ex11 : LinguisticExample :=
  { id := "bochnak2015a_ex11"
    source := ⟨"bochnak-2015a", "(11b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "súku baŋáya ʔéʔišgi k’éʔi"
    discourseSegments := []
    glossedTokens := [("suku", "dog"), ("baŋaya", "outside"), ("ʔ-eʔ-i-š-gi", "3-COP-IPFV-SR-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    translation := "The dog has to stay outside."
    context := "A friend comes to visit, and brings her dog along. You don’t want the dog to come in the house."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "necessity"), ("flavor", "deontic")]
    comment := "" }

def ex12 : LinguisticExample :=
  { id := "bochnak2015a_ex12"
    source := ⟨"bochnak-2015a", "(12b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "wát wútpɨda léʔgabigi Léʔi"
    discourseSegments := []
    glossedTokens := [("wat", "tomorrow"), ("wutpɨd-a", "Woodfords-LOC"), ("le-eʔ-gab-i-gi", "1-COP-FUT-IPFV-REL"), ("L-eʔ-i", "1-MOD-IPFV")]
    translation := "I will be in Woodfords tomorrow."
    context := "I ask you where you will spend the day tomorrow. You say:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "necessity"), ("flavor", "metaphysical")]
    comment := "The sentence of (8). Headed 'Metaphysical/future necessity'. The embedded -eʔ is the copula with the stage-level agreement le-, the matrix one the modal with the individual-level agreement L-." }

def ex13 : LinguisticExample :=
  { id := "bochnak2015a_ex13"
    source := ⟨"bochnak-2015a", "(13b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "mé:hu šáwlamhuhak’a wagayáyʔigi k’éʔi"
    discourseSegments := []
    glossedTokens := [("me:hu", "boy"), ("šawlamhu-hak’a", "girl-with"), ("wagayayʔ-i-gi", "talk-IPFV-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    translation := "The boy will talk to the girl."
    context := "At a school dance, you wonder whether a shy boy will talk to a girl he likes. Your friend says “Yes, …”"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "necessity"), ("flavor", "metaphysical")]
    comment := "Headed 'Metaphysical/future necessity'. The same sentence is deontic possibility in (19)." }

def ex14 : LinguisticExample :=
  { id := "bochnak2015a_ex14"
    source := ⟨"bochnak-2015a", "(14b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "déʔešáŋawiš yéweš gumbeyéc’igigi k’éʔi"
    discourseSegments := []
    glossedTokens := [("deʔeš-aŋaw-i-š", "snow-good-IPFV-SR"), ("yeweš", "road"), ("gum-beyec’ig-i-gi", "REFL-close-IPFV-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    translation := "It’s snowing a lot, so the road must be closed."
    context := "You are planning to drive over the mountains. It’s started to snow, and you know that whenever it snows, the road over the mountains is closed."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "necessity"), ("flavor", "epistemic")]
    comment := "Footnote 4: -eʔ is dispreferred in epistemic contexts, where speakers tend to use an evidential or a paraphrase without a modal." }

def ex15 : LinguisticExample :=
  { id := "bochnak2015a_ex15"
    source := ⟨"bochnak-2015a", "(15b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "ʔát’abi léʔwigi Léʔi"
    discourseSegments := []
    glossedTokens := [("ʔat’abi", "fish"), ("le-iʔiw-i-gi", "1-eat-IPFV-REL"), ("L-eʔ-i", "1-MOD-IPFV")]
    translation := "I have to eat the fish!"
    context := "You are at a restaurant, and the waiter says that today’s special is fish, your favorite food. You say:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "necessity"), ("flavor", "bouletic")]
    comment := "" }

def ex16 : LinguisticExample :=
  { id := "bochnak2015a_ex16"
    source := ⟨"bochnak-2015a", "(16b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "mé:hu šáwlamhu wagayáŋaʔ k’éʔi"
    discourseSegments := []
    glossedTokens := [("me:hu", "boy"), ("šawlamhu", "girl"), ("wagayaŋaʔ", "talk"), ("k’-eʔ-i", "3-MOD-IPFV")]
    translation := "The boy should talk to the girl."
    context := "At a school dance, you tell your friend that a boy who is being shy should talk to a girl he likes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "weak necessity"), ("flavor", "bouletic")]
    comment := "" }

def ex17 : LinguisticExample :=
  { id := "bochnak2015a_ex17"
    source := ⟨"bochnak-2015a", "(17)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "lí:nuya pú:luŋa deyéwamé:sha k’éʔi"
    discourseSegments := []
    glossedTokens := [("li:nu-a", "Reno-LOC"), ("pu:lul-ŋa", "car-NC"), ("de-yewam-e:s-ha", "NMLZ-drive-NEG-CAUS"), ("k’-eʔ-i", "3-COP-IPFV")]
    translation := "He never drives to Reno."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("flavor", "generic")]
    comment := "The sentence of (7), where -eʔ embeds a non-finite clause. Headed 'Generic', with no force. The source glosses -eʔ COP here." }

def ex18 : LinguisticExample :=
  { id := "bochnak2015a_ex18"
    source := ⟨"bochnak-2015a", "(18b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "wádiŋ hé:š ʔump’áyt’igišuweʔ k’éʔi"
    discourseSegments := []
    glossedTokens := [("wadiŋ", "now"), ("he:š", "Q"), ("ʔum-p’ayt’i-giš-uweʔ", "2-play-along-hence"), ("k’-eʔ-i", "3-MOD-IPFV")]
    translation := "Now are you allowed to come play?"
    context := "Mary’s friends come over to see if she is allowed to come out to play."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "possibility"), ("flavor", "deontic")]
    comment := "" }

def ex19 : LinguisticExample :=
  { id := "bochnak2015a_ex19"
    source := ⟨"bochnak-2015a", "(19b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "mé:hu šáwlamhuhak’a wagayáyʔigi k’éʔi"
    discourseSegments := []
    glossedTokens := [("me:hu", "boy"), ("šawlamhu-hak’a", "girl-with"), ("wagayayʔ-i-gi", "talk-IPFV-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    translation := "The boy is allowed to talk to the girl."
    context := "At a school dance, you see a shy boy who wants to talk to a girl but isn’t. You ask your friend if that boy is allowed to talk to that girl. Your friend responds: “Yes …”"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "possibility"), ("flavor", "deontic")]
    comment := "The sentence of (13), metaphysical necessity there." }

def ex20 : LinguisticExample :=
  { id := "bochnak2015a_ex20"
    source := ⟨"bochnak-2015a", "(20b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "wát didó:damamaʔišgi k’éʔi"
    discourseSegments := []
    glossedTokens := [("wat", "tomorrow"), ("di-do:da-mamaʔ-i-š-gi", "1-build-finish-IPFV-SR-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    translation := "I might finish building it tomorrow."
    context := "You have been working on building a house for quite a while now. I ask when you will be finished. You say it’s possible you’ll finish tomorrow."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "possibility"), ("flavor", "metaphysical")]
    comment := "Headed 'Future possibility'; (12) and (13) are headed 'Metaphysical/future necessity'." }

def ex21 : LinguisticExample :=
  { id := "bochnak2015a_ex21"
    source := ⟨"bochnak-2015a", "(21b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "bévali k’éheligi k’éʔi"
    discourseSegments := []
    glossedTokens := [("bevali", "Beverly"), ("k’-eʔ-hel-i-gi", "3-COP-SUBJ-IPFV-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    translation := "It might be Beverly."
    context := "You hear a knock at the door. You can’t see who it is, but can see that the person looks about the same height as Beverly."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "possibility"), ("flavor", "epistemic")]
    comment := "" }

def ex22 : LinguisticExample :=
  { id := "bochnak2015a_ex22"
    source := ⟨"bochnak-2015a", "(22b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "déʔek hádigi t’í:yeliʔ dibípɨsišgi k’éʔi"
    discourseSegments := []
    glossedTokens := [("deʔeg", "rock"), ("hadigi", "that"), ("t’-i:yel-iʔ", "NMLZ-big-ATTR"), ("di-bips-i-š-gi", "1-pick.up-IPFV-SR-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    translation := "I can lift that big rock."
    context := "You see someone trying to pick up a very heavy rock. You are very strong, so you tell them that you can lift that rock."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "possibility"), ("flavor", "circumstantial")]
    comment := "The sentence of (9). The segmentation line prints k-eʔ-i, without the ejective the surface line has." }

def ex23 : LinguisticExample :=
  { id := "bochnak2015a_ex23"
    source := ⟨"bochnak-2015a", "(23b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "dawpáp’ɨl ʔíʔmiʔaŋawigi k’éʔi wáʔ ŋáwaya"
    discourseSegments := []
    glossedTokens := [("dawp’ap’ɨl", "flower"), ("ʔiʔimiʔ-aŋaw-i-gi", "grow-good-IPFV-REL"), ("k’-eʔ-i", "3-MOD-IPFV"), ("waʔ", "here"), ("ŋawa-a", "dirt-LOC")]
    translation := "Flowers could grow well here in this dirt."
    context := "You are discussing what could grow in the garden, given the type of soil."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "possibility"), ("flavor", "circumstantial")]
    comment := "" }

def ex30 : LinguisticExample :=
  { id := "bochnak2015a_ex30"
    source := ⟨"bochnak-2015a", "(30b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "déʔek t’í:yeliŋa dibípɨsé:sišgi k’éʔi"
    discourseSegments := []
    glossedTokens := [("deʔek", "rock"), ("t’-i:yel-iʔ-ŋa", "NMLZ-big-ATTR-NC"), ("di-bips-e:s-i-š-gi", "1-pick.up-NEG-IPFV-SR-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    translation := "I can’t pick up that big rock."
    context := "You see someone trying to pick up a very heavy rock, but they can’t lift it. You are not very strong, so you say that you can’t pick up the rock either."
    judgment := .acceptable
    alternatives := [("deʔek t’-i:yel-iʔ-ŋa di-bips-i-š-gi k’-eʔ-e:s-i", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5"), ("force", "necessity"), ("flavor", "circumstantial"), ("prejacent", "negated")]
    comment := "The alternative, (30c), marks the negation on the modal. The source sets the section 5 examples in IPA length marks and g; they are given in the orthography of section 3." }

def ex31 : LinguisticExample :=
  { id := "bochnak2015a_ex31"
    source := ⟨"bochnak-2015a", "(31b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "wát didó:damamaʔe:sgabišgi k’éʔi"
    discourseSegments := []
    glossedTokens := [("wat", "tomorrow"), ("di-do:da-mamaʔ-e:s-gab-i-š-gi", "1-build-finish-NEG-FUT-IPFV-SR-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    translation := "I won’t finish building it tomorrow."
    context := "You have been working on building a house for quite a while now, and you still won’t finish it by tomorrow."
    judgment := .acceptable
    alternatives := [("wat di-do:da-mamaʔ-gab-i-š-gi k’-eʔ-e:s-i", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5"), ("force", "necessity"), ("flavor", "metaphysical"), ("prejacent", "negated")]
    comment := "The alternative, (31c), marks the negation on the modal." }

def ex32 : LinguisticExample :=
  { id := "bochnak2015a_ex32"
    source := ⟨"bochnak-2015a", "(32b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "demuc’úc’uŋa léʔwé:sigi Léʔi"
    discourseSegments := []
    glossedTokens := [("demuc’uc’u-ŋa", "sweet-NC"), ("le-iʔiw-e:s-i-gi", "1-eat-NEG-IPFV-REL"), ("L-eʔ-i", "1-MOD-IPFV")]
    translation := "I shouldn’t eat candy."
    context := "Someone offers you some candy, but your doctor says you shouldn’t eat candy."
    judgment := .acceptable
    alternatives := [("demuc’uc’u-ŋa le-iʔiw-i-gi L-eʔ-e:s-i", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5"), ("force", "necessity"), ("flavor", "deontic"), ("prejacent", "negated")]
    comment := "The alternative, (32c), marks the negation on the modal. The source glosses le-iʔiw as 1.eat." }

def ex33 : LinguisticExample :=
  { id := "bochnak2015a_ex33"
    source := ⟨"bochnak-2015a", "(33b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "wát didó:damamaʔé:sheligi Léʔi"
    discourseSegments := []
    glossedTokens := [("wat", "tomorrow"), ("di-do:da-mamaʔ-e:s-hel-i-gi", "1-build-finish-NEG-SUBJ-IPFV-REL"), ("L-eʔ-i", "1-MOD-IPFV")]
    translation := "I might not finish building it tomorrow."
    context := "You have been working on building a house for quite a while now, and you’re not sure if you’ll finish it by tomorrow."
    judgment := .acceptable
    alternatives := [("wat di-do:da-mamaʔ-hel-i-gi L-eʔ-e:s-i", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5"), ("force", "possibility"), ("flavor", "metaphysical"), ("prejacent", "negated")]
    comment := "The alternative, (33c), marks the negation on the modal." }

def ex34 : LinguisticExample :=
  { id := "bochnak2015a_ex34"
    source := ⟨"bochnak-2015a", "(34b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "wát háʔašé:sgabigi k’éʔi"
    discourseSegments := []
    glossedTokens := [("wat", "tomorrow"), ("haʔaš-e:s-gab-i-gi", "rain-NEG-FUT-IPFV-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    translation := "It might not rain tomorrow."
    context := "We are discussing the weather for tomorrow. It might rain, but it might not."
    judgment := .acceptable
    alternatives := [("wát háʔaš-gab-i-gi k’-éʔ-e:s-i", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5"), ("force", "possibility"), ("flavor", "metaphysical"), ("prejacent", "negated")]
    comment := "The alternative, (34c), marks the negation on the modal." }

def all : List LinguisticExample := [ex10, ex11, ex12, ex13, ex14, ex15, ex16, ex17, ex18, ex19, ex20, ex21, ex22, ex23, ex30, ex31, ex32, ex33, ex34]

end Bochnak2015a.Examples
