import Linglib.Data.Examples.Schema

/-!
# `JinKoenig2021` — typed example data

Auto-generated from `Linglib/Data/Examples/JinKoenig2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace JinKoenig2021.Examples`.
-/

namespace JinKoenig2021.Examples

open Data.Examples

def jk2021_1 : LinguisticExample :=
  { id := "jk2021_1"
    source := ⟨"jin-koenig-2021", "(1)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "J'ai peur qu'il ne pleuve demain."
    discourseSegments := []
    glossedTokens := []
    translation := "I fear that it will rain tomorrow."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("concept", "fear"), ("negator", "ne"), ("negator_kind", "dedicated"), ("entrenched", "high")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_3 : LinguisticExample :=
  { id := "jk2021_3"
    source := ⟨"jin-koenig-2021", "(3)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "*Je souhaite qu'il ne pleuve demain."
    discourseSegments := []
    glossedTokens := []
    translation := "Intended: I wish that it will rain tomorrow."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2")]
    comment := "wish is not a trigger: the negator is licensed by the meaning of fear."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_4 : LinguisticExample :=
  { id := "jk2021_4"
    source := ⟨"jin-koenig-2021", "(4)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "míng wǎngyǒu mángzhe quànshuō, què wàng-le méi bàojǐng."
    discourseSegments := []
    glossedTokens := []
    translation := "netizens were busy persuading, but forgot to call the police."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("concept", "forget"), ("negator", "méi"), ("negator_kind", "standard")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_14 : LinguisticExample :=
  { id := "jk2021_14"
    source := ⟨"jin-koenig-2021", "(14)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "wǒ yě tǐng pà tā bié xiǎngbùkāi, zuò shǎ shì."
    discourseSegments := []
    glossedTokens := []
    translation := "I also fear that he will take it too hard and do stupid things."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.1"), ("concept", "fear"), ("negator", "bié"), ("negator_kind", "imperative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_15 : LinguisticExample :=
  { id := "jk2021_15"
    source := ⟨"jin-koenig-2021", "(15)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "wǒ zěnyàng nénggòu bìmiǎn bú zài zuò yí gè piànzi?"
    discourseSegments := []
    glossedTokens := []
    translation := "How can I avoid being a liar anymore?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.1"), ("concept", "avoid"), ("negator", "bù"), ("negator_kind", "standard")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_16 : LinguisticExample :=
  { id := "jk2021_16"
    source := ⟨"jin-koenig-2021", "(16)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Je regrette qu'il ne faille souvent attendre des années avant que l'histoire ne juge les tyrans."
    discourseSegments := []
    glossedTokens := []
    translation := "I regret that it often should take years before history judges tyrants."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.2"), ("concept", "regret"), ("negator", "ne"), ("negator_kind", "dedicated"), ("entrenched", "low")]
    comment := "Previously reported not to trigger EN; the negator modifies the deontic falloir."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_17 : LinguisticExample :=
  { id := "jk2021_17"
    source := ⟨"jin-koenig-2021", "(17)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "...gèng hòuhuǐ zìjǐ bùgāi tīng Lǔ Sù de zhǔzhāng..."
    discourseSegments := []
    glossedTokens := []
    translation := "...and furthermore, he regretted having listened to Su Lu's opinion..."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.2"), ("concept", "regret"), ("negator", "bùgāi"), ("negator_kind", "deontic")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_18 : LinguisticExample :=
  { id := "jk2021_18"
    source := ⟨"jin-koenig-2021", "(18)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "dàjiā dōu àn'àn-de bàoyuàn Kèmíng bùgāi bǎ nà gè nǚrén gǎnzǒu."
    discourseSegments := []
    glossedTokens := []
    translation := "Everyone secretly complained that Keming had driven the woman away."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.2"), ("concept", "complain"), ("negator", "bùgāi"), ("negator_kind", "deontic")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_19 : LinguisticExample :=
  { id := "jk2021_19"
    source := ⟨"jin-koenig-2021", "(19)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Niez-vous qu'il ne soit un grand artiste?"
    discourseSegments := []
    glossedTokens := []
    translation := "Do you deny that he is a great artist?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.3"), ("concept", "deny"), ("negator", "ne"), ("negator_kind", "dedicated"), ("entrenched", "high")]
    comment := "French DENY-class predicates must be questioned or negated for EN."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_20 : LinguisticExample :=
  { id := "jk2021_20"
    source := ⟨"jin-koenig-2021", "(20)"⟩
    reportedIn := none
    language := "zarm1239"
    primaryText := "a tugu ey se kang a sinda sida."
    discourseSegments := []
    glossedTokens := []
    translation := "She hid from me that she was HIV positive."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.3"), ("concept", "hide"), ("negator", "sinda"), ("negator_kind", "copular")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_21 : LinguisticExample :=
  { id := "jk2021_21"
    source := ⟨"jin-koenig-2021", "(21)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Cet officier a oublié de ne pas tenir compte des avertissements que ses supérieurs lui avait notifiés en son temps."
    discourseSegments := []
    glossedTokens := []
    translation := "This officer forgot to take into account the warnings that his superiors had given him at the time."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.4"), ("concept", "forget"), ("negator", "ne pas"), ("negator_kind", "standard"), ("entrenched", "low")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_22 : LinguisticExample :=
  { id := "jk2021_22"
    source := ⟨"jin-koenig-2021", "(22)"⟩
    reportedIn := none
    language := "zarm1239"
    primaryText := "a batu a mana graduate manang."
    discourseSegments := []
    glossedTokens := []
    translation := "He delayed graduating last year."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.4"), ("concept", "delay"), ("negator", "mana"), ("negator_kind", "standard")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_23 : LinguisticExample :=
  { id := "jk2021_23"
    source := ⟨"jin-koenig-2021", "(23)"⟩
    reportedIn := none
    language := ""
    primaryText := "ta-kallam-na maʕaa-h tʕawaal il-lail, wallah b-il-guwah maa waafag."
    discourseSegments := []
    glossedTokens := []
    translation := "We talked to him all night, and he really barely agreed."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.4"), ("concept", "barely"), ("negator", "maa"), ("negator_kind", "standard")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_24 : LinguisticExample :=
  { id := "jk2021_24"
    source := ⟨"jin-koenig-2021", "(24)"⟩
    reportedIn := none
    language := ""
    primaryText := "gabl maa atzawaʒ ʕisht maʕa ahl-ii."
    discourseSegments := []
    glossedTokens := []
    translation := "Before I got married I lived with my parents."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2"), ("concept", "before"), ("negator", "maa"), ("negator_kind", "standard")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_25 : LinguisticExample :=
  { id := "jk2021_25"
    source := ⟨"jin-koenig-2021", "(25)"⟩
    reportedIn := none
    language := "zarm1239"
    primaryText := "ey si batu a ma si ka."
    discourseSegments := []
    glossedTokens := []
    translation := "I cannot wait for him to come."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2"), ("concept", "cannotWait"), ("negator", "si"), ("negator_kind", "standard")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_26 : LinguisticExample :=
  { id := "jk2021_26"
    source := ⟨"jin-koenig-2021", "(26)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "...les produits laitiers n'entraînent pas à asthme et ne déclenchent pas rarement des symptômes d'asthme..."
    discourseSegments := []
    glossedTokens := []
    translation := "...Dairy products do not cause asthma and rarely trigger symptoms of asthma..."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2"), ("concept", "rarely"), ("negator", "ne pas"), ("negator_kind", "standard")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_27 : LinguisticExample :=
  { id := "jk2021_27"
    source := ⟨"jin-koenig-2021", "(27)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Il ne dépend que de moi qu'il n'obtienne satisfaction."
    discourseSegments := []
    glossedTokens := []
    translation := "Whether or not he is satisfied only depends on me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.3.3"), ("concept", "onlyDependsOn"), ("negator", "ne"), ("negator_kind", "dedicated")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_28 : LinguisticExample :=
  { id := "jk2021_28"
    source := ⟨"jin-koenig-2021", "(28)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "La question se posa sur mes lèvres autrement que je ne l'aurais voulu."
    discourseSegments := []
    glossedTokens := []
    translation := "The question came out of my lips differently than I would have liked."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.4"), ("concept", "differentThan"), ("negator", "ne"), ("negator_kind", "dedicated"), ("entrenched", "high")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jk2021_29 : LinguisticExample :=
  { id := "jk2021_29"
    source := ⟨"jin-koenig-2021", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was sad that I was too full to not be able to eat more!"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.4"), ("concept", "tooTo"), ("negator", "not"), ("negator_kind", "standard")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [jk2021_1, jk2021_3, jk2021_4, jk2021_14, jk2021_15, jk2021_16, jk2021_17, jk2021_18, jk2021_19, jk2021_20, jk2021_21, jk2021_22, jk2021_23, jk2021_24, jk2021_25, jk2021_26, jk2021_27, jk2021_28, jk2021_29]

end JinKoenig2021.Examples
