module

public import Linglib.Data.Examples.Schema

/-!
# `ZaenenMalingThrainsson1985` — typed example data

Auto-generated from `Linglib/Data/Examples/ZaenenMalingThrainsson1985.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ZaenenMalingThrainsson1985.Examples`.
-/

@[expose] public section

namespace ZaenenMalingThrainsson1985.Examples

open Data.Examples

def zmt1985_8a : LinguisticExample :=
  { id := "zmt1985_8a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(8a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég hjálpaði honum."
    glossedTokens := [("Ég", "I"), ("hjálpaði", "helped"), ("honum", "him.DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hjálpa"), ("voice", "active"), ("cases", "nom dat")] }

def zmt1985_8b : LinguisticExample :=
  { id := "zmt1985_8b"
    source := ⟨"zaenen-maling-thrainsson-1985", "(8b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég mun sakna hans."
    glossedTokens := [("Ég", "I"), ("mun", "will"), ("sakna", "miss"), ("hans", "him.GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sakna"), ("voice", "active"), ("cases", "nom gen")] }

def zmt1985_9a : LinguisticExample :=
  { id := "zmt1985_9a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(9a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Það var dansað í gær."
    glossedTokens := [("Það", "there"), ("var", "was"), ("dansað", "danced"), ("í", "in"), ("gær", "yesterday")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "dansa"), ("voice", "passive"), ("cases", "")] }

def zmt1985_11a : LinguisticExample :=
  { id := "zmt1985_11a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(11a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeim var hjálpað."
    glossedTokens := [("Þeim", "them.DAT"), ("var", "was"), ("hjálpað", "helped")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hjálpa"), ("voice", "passive"), ("cases", "dat")] }

def zmt1985_11b : LinguisticExample :=
  { id := "zmt1985_11b"
    source := ⟨"zaenen-maling-thrainsson-1985", "(11b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hennar var saknað."
    glossedTokens := [("Hennar", "her.GEN"), ("var", "was"), ("saknað", "missed")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sakna"), ("voice", "passive"), ("cases", "gen")] }

def zmt1985_13 : LinguisticExample :=
  { id := "zmt1985_13"
    source := ⟨"zaenen-maling-thrainsson-1985", "(13)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Henni hefur alltaf þótt Ólafur leiðinlegur."
    glossedTokens := [("Henni", "her.DAT"), ("hefur", "has"), ("alltaf", "always"), ("þótt", "thought"), ("Ólafur", "Olaf.NOM"), ("leiðinlegur", "boring.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "þykja"), ("voice", "active"), ("cases", "dat nom")] }

def zmt1985_29a : LinguisticExample :=
  { id := "zmt1985_29a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(29a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Mig vantar peninga."
    glossedTokens := [("Mig", "me.ACC"), ("vantar", "lacks"), ("peninga", "money.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "vanta"), ("voice", "active"), ("cases", "acc acc")] }

def zmt1985_37a : LinguisticExample :=
  { id := "zmt1985_37a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(37a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeir leyndu Ólaf sannleikanum."
    glossedTokens := [("Þeir", "they"), ("leyndu", "concealed"), ("Ólaf", "Olaf.ACC"), ("sannleikanum", "the-truth.DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "leyna"), ("voice", "active"), ("cases", "nom acc dat")] }

def zmt1985_37b : LinguisticExample :=
  { id := "zmt1985_37b"
    source := ⟨"zaenen-maling-thrainsson-1985", "(37b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón bað mig bónar."
    glossedTokens := [("Jón", "John"), ("bað", "asked"), ("mig", "me.ACC"), ("bónar", "a-favor.GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "biðja"), ("voice", "active"), ("cases", "nom acc gen")] }

def zmt1985_37c : LinguisticExample :=
  { id := "zmt1985_37c"
    source := ⟨"zaenen-maling-thrainsson-1985", "(37c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég sagði þér söguna."
    glossedTokens := [("Ég", "I"), ("sagði", "told"), ("þér", "you.DAT"), ("söguna", "a-story.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "segja"), ("voice", "active"), ("cases", "nom dat acc")] }

def zmt1985_37d : LinguisticExample :=
  { id := "zmt1985_37d"
    source := ⟨"zaenen-maling-thrainsson-1985", "(37d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ólafur lofaði Maríu þessum hring."
    glossedTokens := [("Ólafur", "Olaf.NOM"), ("lofaði", "promised"), ("Maríu", "Mary.DAT"), ("þessum", "this.DAT"), ("hring", "ring.DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "lofa"), ("voice", "active"), ("cases", "nom dat dat")] }

def zmt1985_37e : LinguisticExample :=
  { id := "zmt1985_37e"
    source := ⟨"zaenen-maling-thrainsson-1985", "(37e)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "María óskaði Ólafi alls góðs."
    glossedTokens := [("María", "Mary"), ("óskaði", "wished"), ("Ólafi", "Olaf.DAT"), ("alls", "everything.GEN"), ("góðs", "good.GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "óska"), ("voice", "active"), ("cases", "nom dat gen")] }

def zmt1985_42a : LinguisticExample :=
  { id := "zmt1985_42a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(42a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég skilaði henni peningunum."
    glossedTokens := [("Ég", "I"), ("skilaði", "returned"), ("henni", "her.DAT"), ("peningunum", "the-money.DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "skila"), ("voice", "active"), ("cases", "nom dat dat")] }

def zmt1985_42b : LinguisticExample :=
  { id := "zmt1985_42b"
    source := ⟨"zaenen-maling-thrainsson-1985", "(42b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Henni var skilað peningunum."
    glossedTokens := [("Henni", "she.DAT"), ("var", "was"), ("skilað", "returned"), ("peningunum", "the-money.DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "skila"), ("voice", "passive"), ("cases", "dat dat"), ("test", "passive"), ("tested", "goal")] }

def zmt1985_42c : LinguisticExample :=
  { id := "zmt1985_42c"
    source := ⟨"zaenen-maling-thrainsson-1985", "(42c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Peningunum var skilað henni."
    glossedTokens := [("Peningunum", "the-money.DAT"), ("var", "was"), ("skilað", "returned"), ("henni", "her.DAT")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "skila"), ("voice", "passive"), ("test", "passive"), ("tested", "theme")] }

def zmt1985_44a : LinguisticExample :=
  { id := "zmt1985_44a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(44a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Konunginum voru gefnar ambáttir."
    glossedTokens := [("Konunginum", "the-king.DAT"), ("voru", "were"), ("gefnar", "given.F.PL"), ("ambáttir", "slaves.NOM.F.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "gefa"), ("voice", "passive"), ("cases", "dat nom"), ("test", "passive"), ("tested", "goal")] }

def zmt1985_44b : LinguisticExample :=
  { id := "zmt1985_44b"
    source := ⟨"zaenen-maling-thrainsson-1985", "(44b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ambáttin var gefin konunginum."
    glossedTokens := [("Ambáttin", "the-slave.NOM"), ("var", "was"), ("gefin", "given.F.SG"), ("konunginum", "the-king.DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "gefa"), ("voice", "passive"), ("cases", "nom dat"), ("test", "passive"), ("tested", "theme")] }

def zmt1985_64a : LinguisticExample :=
  { id := "zmt1985_64a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(64a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Sjórinn svipti hana manni sínum."
    glossedTokens := [("Sjórinn", "the-sea"), ("svipti", "deprived"), ("hana", "her.ACC"), ("manni", "husband.DAT"), ("sínum", "her.REFL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "svipta"), ("voice", "active"), ("cases", "nom acc dat")] }

def zmt1985_66b : LinguisticExample :=
  { id := "zmt1985_66b"
    source := ⟨"zaenen-maling-thrainsson-1985", "(66b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þú hefur óskað þess."
    glossedTokens := [("Þú", "you"), ("hefur", "have"), ("óskað", "wished"), ("þess", "this.GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "óska (transitive)"), ("voice", "active"), ("cases", "nom gen")] }

def zmt1985_66c : LinguisticExample :=
  { id := "zmt1985_66c"
    source := ⟨"zaenen-maling-thrainsson-1985", "(66c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þú hefur óskað henni."
    glossedTokens := [("Þú", "you"), ("hefur", "have"), ("óskað", "wished"), ("henni", "her.DAT")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "óska"), ("voice", "active")] }

def zmt1985_14b : LinguisticExample :=
  { id := "zmt1985_14b"
    source := ⟨"zaenen-maling-thrainsson-1985", "(14b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég taldi Guðrúnu í barnaskap mínum sakna Haraldar."
    glossedTokens := [("Ég", "I"), ("taldi", "believed"), ("Guðrúnu", "Gudrun.ACC"), ("í", "in"), ("barnaskap", "foolishness"), ("mínum", "my"), ("sakna", "to-miss"), ("Haraldar", "Harold.GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sakna"), ("voice", "active"), ("test", "raising"), ("tested", "experiencer")] }

def zmt1985_14d : LinguisticExample :=
  { id := "zmt1985_14d"
    source := ⟨"zaenen-maling-thrainsson-1985", "(14d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég taldi Haraldar sakna Guðrún."
    glossedTokens := [("Ég", "I"), ("taldi", "believed"), ("Haraldar", "Harold.GEN"), ("sakna", "to-miss"), ("Guðrún", "Gudrun.NOM")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "sakna"), ("voice", "active"), ("test", "raising"), ("tested", "theme")] }

def zmt1985_16 : LinguisticExample :=
  { id := "zmt1985_16"
    source := ⟨"zaenen-maling-thrainsson-1985", "(16)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég tel henni hafa alltaf þótt Ólafur leiðinlegur."
    glossedTokens := [("Ég", "I"), ("tel", "believe"), ("henni", "her.DAT"), ("hafa", "to-have"), ("alltaf", "always"), ("þótt", "thought"), ("Ólafur", "Olaf.NOM"), ("leiðinlegur", "boring.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "þykja"), ("voice", "active"), ("test", "raising"), ("tested", "experiencer")] }

def zmt1985_18a : LinguisticExample :=
  { id := "zmt1985_18a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(18a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Henni þykir bróðir sinn leiðinlegur."
    glossedTokens := [("Henni", "her.DAT"), ("þykir", "thinks"), ("bróðir", "brother.NOM"), ("sinn", "her.REFL"), ("leiðinlegur", "boring")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "þykja"), ("voice", "active"), ("test", "reflexivization"), ("tested", "experiencer")] }

def zmt1985_21a : LinguisticExample :=
  { id := "zmt1985_21a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(21a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hefur henni alltaf þótt Ólafur leiðinlegur?"
    glossedTokens := [("Hefur", "has"), ("henni", "her.DAT"), ("alltaf", "always"), ("þótt", "thought"), ("Ólafur", "Olaf.NOM"), ("leiðinlegur", "boring.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "þykja"), ("voice", "active"), ("test", "inversion"), ("tested", "experiencer")] }

def zmt1985_21c : LinguisticExample :=
  { id := "zmt1985_21c"
    source := ⟨"zaenen-maling-thrainsson-1985", "(21c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hefur Ólafur henni alltaf þótt leiðinlegur?"
    glossedTokens := [("Hefur", "has"), ("Ólafur", "Olaf.NOM"), ("henni", "her.DAT"), ("alltaf", "always"), ("þótt", "thought"), ("leiðinlegur", "boring")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "þykja"), ("voice", "active"), ("test", "inversion"), ("tested", "theme")] }

def zmt1985_23b : LinguisticExample :=
  { id := "zmt1985_23b"
    source := ⟨"zaenen-maling-thrainsson-1985", "(23b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hvenær telur Jón að henni hafi þótt Ólafur leiðinlegur?"
    glossedTokens := [("Hvenær", "when"), ("telur", "believes"), ("Jón", "John.NOM"), ("að", "that"), ("henni", "her.DAT"), ("hafi", "has"), ("þótt", "thought"), ("Ólafur", "Olaf"), ("leiðinlegur", "boring")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "þykja"), ("voice", "active"), ("test", "extraction"), ("tested", "experiencer")] }

def zmt1985_23d : LinguisticExample :=
  { id := "zmt1985_23d"
    source := ⟨"zaenen-maling-thrainsson-1985", "(23d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hvenær telur Jón að Ólafur hafi henni þótt leiðinlegur?"
    glossedTokens := [("Hvenær", "when"), ("telur", "believes"), ("Jón", "John.NOM"), ("að", "that"), ("Ólafur", "Olaf.NOM"), ("hafi", "has"), ("henni", "her.DAT"), ("þótt", "thought"), ("leiðinlegur", "boring")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "þykja"), ("voice", "active"), ("test", "extraction"), ("tested", "theme")] }

def zmt1985_25a : LinguisticExample :=
  { id := "zmt1985_25a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(25a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Það hefur einhverjum þótt Ólafur leiðinlegur."
    glossedTokens := [("Það", "there"), ("hefur", "has"), ("einhverjum", "someone.DAT"), ("þótt", "thought"), ("Ólafur", "Olaf.NOM"), ("leiðinlegur", "boring.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "þykja"), ("voice", "active"), ("test", "postposing"), ("tested", "experiencer")] }

def zmt1985_25c : LinguisticExample :=
  { id := "zmt1985_25c"
    source := ⟨"zaenen-maling-thrainsson-1985", "(25c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Það hefur Ólafur einhverjum þótt leiðinlegur."
    glossedTokens := [("Það", "there"), ("hefur", "has"), ("Ólafur", "Olaf.NOM"), ("einhverjum", "someone.DAT"), ("þótt", "thought"), ("leiðinlegur", "boring")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "þykja"), ("voice", "active"), ("test", "postposing"), ("tested", "theme")] }

def zmt1985_27a : LinguisticExample :=
  { id := "zmt1985_27a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(27a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hann segist vera duglegur, en finnst verkefnið of þungt."
    glossedTokens := [("Hann", "he.NOM"), ("segist", "says-self"), ("vera", "to-be"), ("duglegur,", "diligent"), ("en", "but"), ("finnst", "finds"), ("verkefnið", "the-homework.NOM"), ("of", "too"), ("þungt", "hard")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "finnast"), ("voice", "active"), ("test", "ellipsis"), ("tested", "experiencer")] }

def zmt1985_27b : LinguisticExample :=
  { id := "zmt1985_27b"
    source := ⟨"zaenen-maling-thrainsson-1985", "(27b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hann segist vera duglegur, en mér finnst latur."
    glossedTokens := [("Hann", "he.NOM"), ("segist", "says-self"), ("vera", "to-be"), ("duglegur,", "diligent"), ("en", "but"), ("mér", "me.DAT"), ("finnst", "find"), ("latur", "lazy")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "finnast"), ("voice", "active"), ("test", "ellipsis"), ("tested", "theme")] }

def zmt1985_29b : LinguisticExample :=
  { id := "zmt1985_29b"
    source := ⟨"zaenen-maling-thrainsson-1985", "(29b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég vonast til að vanta ekki peninga."
    glossedTokens := [("Ég", "I"), ("vonast", "hope"), ("til", "for"), ("að", "to"), ("vanta", "lack"), ("ekki", "not"), ("peninga", "money.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "vanta"), ("voice", "active"), ("test", "control"), ("tested", "experiencer")] }

def zmt1985_30 : LinguisticExample :=
  { id := "zmt1985_30"
    source := ⟨"zaenen-maling-thrainsson-1985", "(30)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég tel þeim hafa verið hjálpað í prófinu."
    glossedTokens := [("Ég", "I"), ("tel", "believe"), ("þeim", "them.DAT"), ("hafa", "to-have"), ("verið", "been"), ("hjálpað", "helped"), ("í", "in"), ("prófinu", "the-exam")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hjálpa"), ("voice", "passive"), ("test", "raising"), ("tested", "theme")] }

def zmt1985_31 : LinguisticExample :=
  { id := "zmt1985_31"
    source := ⟨"zaenen-maling-thrainsson-1985", "(31)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Honum var oft hjálpað af foreldrum sínum."
    glossedTokens := [("Honum", "he.DAT"), ("var", "was"), ("oft", "often"), ("hjálpað", "helped"), ("af", "by"), ("foreldrum", "parents"), ("sínum", "his.REFL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hjálpa"), ("voice", "passive"), ("test", "reflexivization"), ("tested", "theme")] }

def zmt1985_32a : LinguisticExample :=
  { id := "zmt1985_32a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(32a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Var honum aldrei hjálpað af foreldrum sínum?"
    glossedTokens := [("Var", "was"), ("honum", "he.DAT"), ("aldrei", "never"), ("hjálpað", "helped"), ("af", "by"), ("foreldrum", "parents"), ("sínum", "his")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hjálpa"), ("voice", "passive"), ("test", "inversion"), ("tested", "theme")] }

def zmt1985_33b : LinguisticExample :=
  { id := "zmt1985_33b"
    source := ⟨"zaenen-maling-thrainsson-1985", "(33b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hvenær telur hann að henni hafi verið hjálpað?"
    glossedTokens := [("Hvenær", "when"), ("telur", "believes"), ("hann", "he"), ("að", "that"), ("henni", "she.DAT"), ("hafi", "has"), ("verið", "been"), ("hjálpað", "helped")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hjálpa"), ("voice", "passive"), ("test", "extraction"), ("tested", "theme")] }

def zmt1985_34 : LinguisticExample :=
  { id := "zmt1985_34"
    source := ⟨"zaenen-maling-thrainsson-1985", "(34)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Það hefur mörgum stúdentum verið hjálpað í prófinu."
    glossedTokens := [("Það", "there"), ("hefur", "has"), ("mörgum", "many.DAT"), ("stúdentum", "students.DAT"), ("verið", "been"), ("hjálpað", "helped"), ("í", "on"), ("prófinu", "the-exam")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hjálpa"), ("voice", "passive"), ("test", "postposing"), ("tested", "theme")] }

def zmt1985_35 : LinguisticExample :=
  { id := "zmt1985_35"
    source := ⟨"zaenen-maling-thrainsson-1985", "(35)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hann segist vera saklaus en hefur víst verið hjálpað í prófinu."
    glossedTokens := [("Hann", "he.NOM"), ("segist", "says-self"), ("vera", "to-be"), ("saklaus", "innocent"), ("en", "but"), ("hefur", "has"), ("víst", "apparently"), ("verið", "been"), ("hjálpað", "helped"), ("í", "on"), ("prófinu", "the-exam")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hjálpa"), ("voice", "passive"), ("test", "ellipsis"), ("tested", "theme")] }

def zmt1985_36a : LinguisticExample :=
  { id := "zmt1985_36a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(36a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég vonast til að verða hjálpað."
    glossedTokens := [("Ég", "I"), ("vonast", "hope"), ("til", "for"), ("að", "to"), ("verða", "be"), ("hjálpað", "helped")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hjálpa"), ("voice", "passive"), ("test", "control"), ("tested", "theme")] }

def zmt1985_45a : LinguisticExample :=
  { id := "zmt1985_45a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(45a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég tel konunginum hafa verið gefnar ambáttir."
    glossedTokens := [("Ég", "I"), ("tel", "believe"), ("konunginum", "the-king.DAT"), ("hafa", "have"), ("verið", "been"), ("gefnar", "given.F.PL"), ("ambáttir", "slaves.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "gefa"), ("voice", "passive"), ("test", "raising"), ("tested", "goal")] }

def zmt1985_45b : LinguisticExample :=
  { id := "zmt1985_45b"
    source := ⟨"zaenen-maling-thrainsson-1985", "(45b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég tel ambáttina hafa verið gefna konunginum."
    glossedTokens := [("Ég", "I"), ("tel", "believe"), ("ambáttina", "the-slave.ACC"), ("hafa", "have"), ("verið", "been"), ("gefna", "given.ACC"), ("konunginum", "the-king.DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "gefa"), ("voice", "passive"), ("test", "raising"), ("tested", "theme")] }

def zmt1985_68a : LinguisticExample :=
  { id := "zmt1985_68a"
    source := ⟨"zaenen-maling-thrainsson-1985", "(68a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þess var óskað."
    glossedTokens := [("Þess", "this.GEN"), ("var", "was"), ("óskað", "wished")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "óska (transitive)"), ("voice", "passive"), ("cases", "gen"), ("test", "passive"), ("tested", "theme")] }

def zmt1985_68a_prime : LinguisticExample :=
  { id := "zmt1985_68a_prime"
    source := ⟨"zaenen-maling-thrainsson-1985", "(68a')"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þess var óskað henni."
    glossedTokens := [("Þess", "this.GEN"), ("var", "was"), ("óskað", "wished"), ("henni", "her.DAT")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "óska"), ("voice", "passive"), ("test", "passive"), ("tested", "theme")] }

def zmt1985_68c : LinguisticExample :=
  { id := "zmt1985_68c"
    source := ⟨"zaenen-maling-thrainsson-1985", "(68c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Henni var óskað þess."
    glossedTokens := [("Henni", "her.DAT"), ("var", "was"), ("óskað", "wished"), ("þess", "this.GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "óska"), ("voice", "passive"), ("cases", "dat gen"), ("test", "passive"), ("tested", "goal")] }

def all : List LinguisticExample := [zmt1985_8a, zmt1985_8b, zmt1985_9a, zmt1985_11a, zmt1985_11b, zmt1985_13, zmt1985_29a, zmt1985_37a, zmt1985_37b, zmt1985_37c, zmt1985_37d, zmt1985_37e, zmt1985_42a, zmt1985_42b, zmt1985_42c, zmt1985_44a, zmt1985_44b, zmt1985_64a, zmt1985_66b, zmt1985_66c, zmt1985_14b, zmt1985_14d, zmt1985_16, zmt1985_18a, zmt1985_21a, zmt1985_21c, zmt1985_23b, zmt1985_23d, zmt1985_25a, zmt1985_25c, zmt1985_27a, zmt1985_27b, zmt1985_29b, zmt1985_30, zmt1985_31, zmt1985_32a, zmt1985_33b, zmt1985_34, zmt1985_35, zmt1985_36a, zmt1985_45a, zmt1985_45b, zmt1985_68a, zmt1985_68a_prime, zmt1985_68c]

end ZaenenMalingThrainsson1985.Examples
