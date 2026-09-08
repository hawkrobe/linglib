import Linglib.Data.Examples.Schema

/-!
# `Carstens2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Carstens2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Carstens2026.Examples`.
-/

namespace Carstens2026.Examples

open Data.Examples

def ex6a : LinguisticExample :=
  { id := "carstens2026_ex6a"
    source := ⟨"carstens-2026", "(6a)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Um-mi nom-ongameli ba-ya-ncokola."
    discourseSegments := []
    glossedTokens := [("Um-mi", "1-citizen"), ("nom-ongameli", "and.1-president"), ("ba-ya-ncokola", "2SM-DISJ-chat")]
    translation := "The citizen and the president are chatting."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "ummi"), ("conjunct2", "umongameli"), ("agreement", "2")]
    comment := "[1&1=2]."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6b : LinguisticExample :=
  { id := "carstens2026_ex6b"
    source := ⟨"carstens-2026", "(6b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "U-L no-M ba-phezu kwetafile."
    discourseSegments := []
    glossedTokens := [("U-L", "1a-L"), ("no-M", "and.1a-M"), ("ba-phezu", "2SM-are.on"), ("kwetafile", "LOC.table")]
    translation := "The letters L and M are on the table."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "uL"), ("conjunct2", "uM"), ("agreement", "2")]
    comment := "[1&1=2]: arbitrary members of gender A."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex7b : LinguisticExample :=
  { id := "carstens2026_ex7b"
    source := ⟨"carstens-2026", "(7b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Is-anuse nes-azi zi-ya-sebenza."
    discourseSegments := []
    glossedTokens := [("Is-anuse", "7-diviner"), ("nes-azi", "and.7-scientist"), ("zi-ya-sebenza", "8SM-DISJ-work")]
    translation := "The diviner and the scientist are working."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "isanuse"), ("conjunct2", "isazi"), ("agreement", "8")]
    comment := "[7&7=8] with human conjuncts of class 7."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex8b : LinguisticExample :=
  { id := "carstens2026_ex8b"
    source := ⟨"carstens-2026", "(8b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "I-qanda ne-cepe z-a-wa."
    discourseSegments := []
    glossedTokens := [("I-qanda", "5-egg"), ("ne-cepe", "and.5-spoon"), ("z-a-wa", "8SM-ASP-fall")]
    translation := "The egg and the spoon fell."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "iqanda"), ("conjunct2", "icepe"), ("agreement", "8"), ("rejected", "6")]
    comment := "[5+5=8; ≠6]: the class 6 marker of the plural (8d) is ruled out."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex9a : LinguisticExample :=
  { id := "carstens2026_ex9a"
    source := ⟨"carstens-2026", "(9a)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Is-anuse nen-tombi ba-ya-sebenza."
    discourseSegments := []
    glossedTokens := [("Is-anuse", "7-medium"), ("nen-tombi", "and.9-girl"), ("ba-ya-sebenza", "2SM-DISJ-work")]
    translation := "The medium and the girl are working."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "isanuse"), ("conjunct2", "intombi"), ("agreement", "2")]
    comment := "Mismatched humans, repeated as (87a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex9b : LinguisticExample :=
  { id := "carstens2026_ex9b"
    source := ⟨"carstens-2026", "(9b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "U-bhaka nen-cwadi zi-ngaphandle."
    discourseSegments := []
    glossedTokens := [("U-bhaka", "1a-backpack"), ("nen-cwadi", "and.9-book"), ("zi-ngaphandle", "8SM-be.outside")]
    translation := "The backpack and the book are outside."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "ubhaka"), ("conjunct2", "incwadi"), ("agreement", "8")]
    comment := "Mismatched inanimates, repeated as (87b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex37a : LinguisticExample :=
  { id := "carstens2026_ex37a"
    source := ⟨"carstens-2026", "(37a)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Um-gewu nom-lwelwe ba-sebenza ndawonye."
    discourseSegments := []
    glossedTokens := [("Um-gewu", "3-criminal"), ("nom-lwelwe", "and.3-sick.person"), ("ba-sebenza", "2SM-work"), ("ndawonye", "9place.one")]
    translation := "A criminal and a sick person are working in one place."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "umgewu"), ("conjunct2", "umlwelwe"), ("agreement", "2"), ("rejected", "4"), ("matching", "0"), ("default", "15"), ("judgments", "15")]
    comment := "[3&3=2; ≠4], from Taraldsen et al. 2018. Table 13 [3&3] human: 15 speakers."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex38a : LinguisticExample :=
  { id := "carstens2026_ex38a"
    source := ⟨"carstens-2026", "(38a)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Um-nqwazi nom-pu zi-se tafile-ni."
    discourseSegments := []
    glossedTokens := [("Um-nqwazi", "3-hat"), ("nom-pu", "and.3-gun"), ("zi-se", "8SM-are"), ("tafile-ni", "table-LOC")]
    translation := "A hat and a gun are on the table."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "umnqwazi"), ("conjunct2", "umpu"), ("agreement", "8"), ("rejected", "4"), ("matching", "1"), ("default", "33"), ("judgments", "45")]
    comment := "[3+3=8; ≠4]. Table 13 [3&3] non-human: 45 judgments over (38a-c), one gender-matching i-."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex38b : LinguisticExample :=
  { id := "carstens2026_ex38b"
    source := ⟨"carstens-2026", "(38b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Um-hlonyane nom-nquma zi-ya-khula."
    discourseSegments := []
    glossedTokens := [("Um-hlonyane", "3-wormwood.tree"), ("nom-nquma", "and.3-wild.olive"), ("zi-ya-khula", "8SM-DISJ-grow")]
    translation := "The wormwood tree and the wild olive tree are growing."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "umhlonyane"), ("conjunct2", "umnquma"), ("agreement", "8"), ("rejected", "4")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex38c : LinguisticExample :=
  { id := "carstens2026_ex38c"
    source := ⟨"carstens-2026", "(38c)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Um-khonto nom-bhobho zi-nomhlwa."
    discourseSegments := []
    glossedTokens := [("Um-khonto", "3-spear"), ("nom-bhobho", "and.3-pipe"), ("zi-nomhlwa", "8SM-have.rust")]
    translation := "The spear and the pipe are rusty."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "umkhonto"), ("conjunct2", "umbhobho"), ("agreement", "8"), ("rejected", "4")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40a : LinguisticExample :=
  { id := "carstens2026_ex40a"
    source := ⟨"carstens-2026", "(40a)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "I-gqwetha ne-sela ba-phum-ile."
    discourseSegments := []
    glossedTokens := [("I-gqwetha", "5-lawyer"), ("ne-sela", "and.5-thief"), ("ba-phum-ile", "2SM-left.PST.DISJ")]
    translation := "The lawyer and the thief left."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "igqwetha"), ("conjunct2", "isela"), ("agreement", "2"), ("rejected", "6"), ("matching", "0"), ("default", "19"), ("judgments", "30")]
    comment := "[5+5=2; ≠6]. Table 13 [5&5] human: 30 judgments over (40a,b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40b : LinguisticExample :=
  { id := "carstens2026_ex40b"
    source := ⟨"carstens-2026", "(40b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "I-gorha ne-khoboka ba-phum-ile."
    discourseSegments := []
    glossedTokens := [("I-gorha", "5-hero"), ("ne-khoboka", "and.5-slave"), ("ba-phum-ile", "2SM-left")]
    translation := "The hero and the slave left."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "igorha"), ("conjunct2", "ikhoboka"), ("agreement", "2"), ("rejected", "6")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex41a : LinguisticExample :=
  { id := "carstens2026_ex41a"
    source := ⟨"carstens-2026", "(41a)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Ili-tye ne-qanda zi-nyamalele."
    discourseSegments := []
    glossedTokens := [("Ili-tye", "5-stone"), ("ne-qanda", "and.5-egg"), ("zi-nyamalele", "8SM-disappeared")]
    translation := "The stone and the egg disappeared."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "ilitye"), ("conjunct2", "iqanda"), ("agreement", "8"), ("rejected", "6"), ("matching", "0"), ("default", "22"), ("judgments", "30")]
    comment := "[5&5=8; ≠6]. Table 13 [5&5] non-human: 30 judgments over (41a,b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex41b : LinguisticExample :=
  { id := "carstens2026_ex41b"
    source := ⟨"carstens-2026", "(41b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "I-cepe ne-cici zi-a-bi-wa."
    discourseSegments := []
    glossedTokens := [("I-cepe", "5-spoon"), ("ne-cici", "and.5-earring"), ("zi-a-bi-wa", "8SM-steal-PASS")]
    translation := "The spoon and the earring were stolen."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "icepe"), ("conjunct2", "icici"), ("agreement", "8"), ("rejected", "6")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex44 : LinguisticExample :=
  { id := "carstens2026_ex44"
    source := ⟨"carstens-2026", "(44)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Um-ntwana nom-fazi ba-ya-dlala."
    discourseSegments := []
    glossedTokens := [("Um-ntwana", "1-child"), ("nom-fazi", "and.1-woman"), ("ba-ya-dlala", "2SM-DISJ-play")]
    translation := "The child and the woman are playing."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "umntwana"), ("conjunct2", "umfazi"), ("agreement", "2"), ("matching", "30"), ("default", "30"), ("judgments", "30")]
    comment := "[1&1=2]. Table 13 [1&1] human: ba- is matching and default alike, the two merged."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex45a : LinguisticExample :=
  { id := "carstens2026_ex45a"
    source := ⟨"carstens-2026", "(45a)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "U-L no-M ba-se tafile-ni."
    discourseSegments := []
    glossedTokens := [("U-L", "1a-L"), ("no-M", "and.1a-M"), ("ba-se", "2SM-LOC"), ("tafile-ni", "table-LOC")]
    translation := "The L and the M are on the table."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "uL"), ("conjunct2", "uM"), ("agreement", "2"), ("matching", "22"), ("default", "7"), ("judgments", "30")]
    comment := "[1&1=2], from Taraldsen et al. 2018. Table 13 [1&1] non-human: 30 judgments over (45a,b), default zi- in the rest."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex45b : LinguisticExample :=
  { id := "carstens2026_ex45b"
    source := ⟨"carstens-2026", "(45b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "U-loliwe kunye no-matshini ba-ya-hamba."
    discourseSegments := []
    glossedTokens := [("U-loliwe", "1a-train"), ("kunye", "and"), ("no-matshini", "and.1a-machine"), ("ba-ya-hamba", "2SM-DISJ-move")]
    translation := "The train and the machine are moving."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "uloliwe"), ("conjunct2", "umatshini"), ("agreement", "2")]
    comment := "[1&1=2]."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46a : LinguisticExample :=
  { id := "carstens2026_ex46a"
    source := ⟨"carstens-2026", "(46a)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Isi-bane nesi-tya zi-nyamalele."
    discourseSegments := []
    glossedTokens := [("Isi-bane", "7-lamp"), ("nesi-tya", "and.7-dish"), ("zi-nyamalele", "8SM-disappeared")]
    translation := "The lamp and the dish have disappeared."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "isibane"), ("conjunct2", "isitya"), ("agreement", "8"), ("matching", "30"), ("default", "30"), ("judgments", "30")]
    comment := "[7&7=8], also (7a). Table 13 [7&7] non-human: zi- matching and default alike."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46b : LinguisticExample :=
  { id := "carstens2026_ex46b"
    source := ⟨"carstens-2026", "(46b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Isi-Xhosa nesi-Zulu zi-theth-wa e-Mzantsi Afrika."
    discourseSegments := []
    glossedTokens := [("Isi-Xhosa", "7-Xhosa"), ("nesi-Zulu", "and.7-Zulu"), ("zi-theth-wa", "8SM-speak-PASS"), ("e-Mzantsi Afrika", "LOC-South Africa")]
    translation := "Xhosa and Zulu are spoken in South Africa."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "isiXhosa"), ("conjunct2", "isiZulu"), ("agreement", "8")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex47a : LinguisticExample :=
  { id := "carstens2026_ex47a"
    source := ⟨"carstens-2026", "(47a)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Is-anuse nes-angoma zi-sebenza ndawonye."
    discourseSegments := []
    glossedTokens := [("Is-anuse", "7-diviner"), ("nes-angoma", "and.7-healer"), ("zi-sebenza", "8SM-work"), ("ndawonye", "9place.one")]
    translation := "The diviner and the healer work together."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "isanuse"), ("conjunct2", "isangoma"), ("agreement", "8"), ("agreement", "2"), ("matching", "18"), ("default", "9"), ("judgments", "30")]
    comment := "[7&7] human, from Taraldsen et al. 2018: Table 13 zi- 60%, ba- 30%, either 10% over (47a,b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex47b : LinguisticExample :=
  { id := "carstens2026_ex47b"
    source := ⟨"carstens-2026", "(47b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Isi-bhanxa nes-azi zi-ya-funda."
    discourseSegments := []
    glossedTokens := [("Isi-bhanxa", "7-fool"), ("nes-azi", "and.7-scholar"), ("zi-ya-funda", "8SM-DISJ-study")]
    translation := "The fool and the scholar are studying."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "isibhanxa"), ("conjunct2", "isazi"), ("agreement", "8"), ("agreement", "2")]
    comment := "ba- for the same conjunction is (81b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48a : LinguisticExample :=
  { id := "carstens2026_ex48a"
    source := ⟨"carstens-2026", "(48a)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "In-tombi nem-bongi zi-ya-cula."
    discourseSegments := []
    glossedTokens := [("In-tombi", "9-girl"), ("nem-bongi", "and.9-poet"), ("zi-/ba-ya-cula", "10/2SM-DISJ-sing")]
    translation := "The girl and the poet are singing."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "intombi"), ("conjunct2", "imbongi"), ("agreement", "10"), ("agreement", "2"), ("matching", "15"), ("default", "12"), ("judgments", "30")]
    comment := "[9&9=10 or 2]. Table 13 [9&9] human: zi- 50%, ba- 40%, either 10% over (48a,b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48b : LinguisticExample :=
  { id := "carstens2026_ex48b"
    source := ⟨"carstens-2026", "(48b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "In-gcaphephe nen-gcali a-zi-vumel-an-i."
    discourseSegments := []
    glossedTokens := [("In-gcaphephe", "9-expert"), ("nen-gcali", "and.9-specialist"), ("a-zi-/ba-vumel-an-i", "NEG-10/2SM-agree-RECIP-NEG")]
    translation := "The expert and the specialist disagree."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "ingcaphephe"), ("conjunct2", "ingcali"), ("agreement", "10"), ("agreement", "2")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex49a : LinguisticExample :=
  { id := "carstens2026_ex49a"
    source := ⟨"carstens-2026", "(49a)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "In-cwadi nepeni zi-se tafile-ni."
    discourseSegments := []
    glossedTokens := [("In-cwadi", "9-book"), ("nepeni", "and.9-pen"), ("zi-se", "10SM/8SM-LOC"), ("tafile-ni", "table-LOC")]
    translation := "The book and the pen are on the table."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "incwadi"), ("conjunct2", "ipeni"), ("agreement", "10"), ("agreement", "8"), ("matching", "30"), ("default", "30"), ("judgments", "30")]
    comment := "[9&9=10]: zi- is ambiguous between matching class 10 and default class 8. Table 13 [9&9] non-human: zi- throughout."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex49b : LinguisticExample :=
  { id := "carstens2026_ex49b"
    source := ⟨"carstens-2026", "(49b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "In-dlovu kunye nen-gwe zi-ya-lwa."
    discourseSegments := []
    glossedTokens := [("In-dlovu", "9-elephant"), ("kunye", "and"), ("nen-gwe", "and.9-leopard"), ("zi-ya-lwa", "10SM-DISJ-fight")]
    translation := "The elephant and the leopard are fighting."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "indlovu"), ("conjunct2", "ingwe"), ("agreement", "10")]
    comment := "Conjoined animals of class 9: zi- taken as class 10, the [animal] default."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex55a : LinguisticExample :=
  { id := "carstens2026_ex55a"
    source := ⟨"carstens-2026", "(55a)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Um-vundla nom-qhagi zi-yanxila."
    discourseSegments := []
    glossedTokens := [("Um-vundla", "3-rabbit"), ("nom-qhagi", "and.3-rooster"), ("zi-yanxila", "10SM-drunk")]
    translation := "The rabbit and the rooster are drunk."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "umvundla"), ("conjunct2", "umqhagi"), ("agreement", "10"), ("rejected", "4")]
    comment := "[3&3=10; ≠4]: animals of class 3 take the [animal] default."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex55b : LinguisticExample :=
  { id := "carstens2026_ex55b"
    source := ⟨"carstens-2026", "(55b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Isi-khova ne-hobe zi-nokubhabha."
    discourseSegments := []
    glossedTokens := [("Isi-khova", "7-owl"), ("ne-hobe", "and.5-dove"), ("zi-nokubhabha", "10SM-fly")]
    translation := "The owl and the dove can fly."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "isikhova"), ("conjunct2", "ihobe"), ("agreement", "10")]
    comment := "[7&5=10]: mismatched visible genders, shared [animal] core."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex81a : LinguisticExample :=
  { id := "carstens2026_ex81a"
    source := ⟨"carstens-2026", "(81a)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "U-L no-M zi-se tafile-ni."
    discourseSegments := []
    glossedTokens := [("U-L", "1a-L"), ("no-M", "and.1a-M"), ("zi-se", "8SM-LOC"), ("tafile-ni", "table-LOC")]
    translation := "The L and the M are on the table."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "uL"), ("conjunct2", "uM"), ("agreement", "8")]
    comment := "The Best-Semantic-Match choice for (45a): the shared [inanimate] core."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex81b : LinguisticExample :=
  { id := "carstens2026_ex81b"
    source := ⟨"carstens-2026", "(81b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Isi-bhanxa nes-azi ba-ya-funda."
    discourseSegments := []
    glossedTokens := [("Isi-bhanxa", "7-fool"), ("nes-azi", "and.7-scholar"), ("ba-ya-funda", "2SM-DISJ-study")]
    translation := "The fool and the scholar are studying."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "isibhanxa"), ("conjunct2", "isazi"), ("agreement", "2")]
    comment := "The Best-Semantic-Match choice for (47b): the shared [human] core."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex83 : LinguisticExample :=
  { id := "carstens2026_ex83"
    source := ⟨"carstens-2026", "(83)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "U-nonkala no-krebe ba-ya-lwa."
    discourseSegments := []
    glossedTokens := [("U-nonkala", "1a-crab"), ("no-krebe", "and.1a-shark"), ("ba-/zi-ya-lwa", "2SM/10SM-DISJ-fight")]
    translation := "The crab and the shark are fighting."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "unonkala"), ("conjunct2", "ukrebe"), ("agreement", "2"), ("agreement", "10")]
    comment := "Five of six speakers chose ba- (Highest Wins), one zi- (Best Semantic Match)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex85a : LinguisticExample :=
  { id := "carstens2026_ex85a"
    source := ⟨"carstens-2026", "(85a)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Um-gulukudu ne-polisa ba-sebenza ndawonye."
    discourseSegments := []
    glossedTokens := [("Um-gulukudu", "3-gangster"), ("ne-polisa", "and.5-policeman"), ("ba-sebenza", "2SM-PRES-work"), ("ndawonye", "9place.one")]
    translation := "The criminal and the policeman are working together."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "umgulukudu"), ("conjunct2", "ipolisa"), ("agreement", "2")]
    comment := "Mismatched u-genders above shared [human] cores (86a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex85b : LinguisticExample :=
  { id := "carstens2026_ex85b"
    source := ⟨"carstens-2026", "(85b)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Um-nqathe ne-qanda zi-se tafile-ni."
    discourseSegments := []
    glossedTokens := [("Um-nqathe", "3-carrot"), ("ne-qanda", "and.5-egg"), ("zi-se", "8SM-LOC"), ("tafile-ni", "table-LOC")]
    translation := "The carrot and the egg are on the table."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "umnqathe"), ("conjunct2", "iqanda"), ("agreement", "8")]
    comment := "Mismatched u-genders above shared [inanimate] cores (86b); from Mitchley 2015."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex89 : LinguisticExample :=
  { id := "carstens2026_ex89"
    source := ⟨"carstens-2026", "(89)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "Um-twana no-lolilwe ba-ya-hamba."
    discourseSegments := []
    glossedTokens := [("Um-twana", "1-child"), ("no-lolilwe", "and.1a-train"), ("ba-ya-hamba", "2SM-DISJ-move")]
    translation := "The child and the train are moving."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "umntwana"), ("conjunct2", "uloliwe"), ("agreement", "2")]
    comment := "(90): the [human] flavor of class 1 and the [entity] flavor of class 1a share the formal gender feature."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex91 : LinguisticExample :=
  { id := "carstens2026_ex91"
    source := ⟨"carstens-2026", "(91)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "*In-tombi no-lolilwe zi-/ba-gilana."
    discourseSegments := []
    glossedTokens := [("In-tombi", "9-girl"), ("no-lolilwe", "and.1a-train"), ("zi-/ba-gilana", "8SM/2SM-collide")]
    translation := "Intended: The girl and the train collided."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "intombi"), ("conjunct2", "uloliwe"), ("rejected", "8"), ("rejected", "2")]
    comment := "(92): neither the visible genders 9 and 1a nor the cores 1 and 7 match; ineffable."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex111 : LinguisticExample :=
  { id := "carstens2026_ex111"
    source := ⟨"carstens-2026", "(111)"⟩
    reportedIn := none
    language := "xhos1239"
    primaryText := "*Um-ntwana nen-dlovu ba-/zi-ya-dlala."
    discourseSegments := []
    glossedTokens := [("Um-ntwana", "1-child"), ("nen-dlovu", "and.9-elephant"), ("ba-/zi-ya-dlala", "2SM/10SM-DISJ-play")]
    translation := "The child and the elephant are playing."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "umntwana"), ("conjunct2", "indlovu"), ("rejected", "2"), ("rejected", "10")]
    comment := "(112): a human and an animal share no formal gender feature, whatever animacy feature they share."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex58 : LinguisticExample :=
  { id := "carstens2026_ex58"
    source := ⟨"carstens-2026", "(58)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "Mu-rume ne-mu-kadzi va-ri panze."
    discourseSegments := []
    glossedTokens := [("Mu-rume", "1-man"), ("ne-mu-kadzi", "and-1-woman"), ("va-ri", "2SM-be"), ("panze", "outside")]
    translation := "The man and the woman are outside."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "murume"), ("conjunct2", "mukadzi"), ("agreement", "2")]
    comment := "[1&1=2]."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex59 : LinguisticExample :=
  { id := "carstens2026_ex59"
    source := ⟨"carstens-2026", "(59)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "Mu-nwe ne-mu-romo zvi-ne utachiona."
    discourseSegments := []
    glossedTokens := [("Mu-nwe", "3-finger"), ("ne-mu-romo", "and-3-mouth"), ("zvi-ne", "8SM-have"), ("utachiona", "14infection")]
    translation := "The mouth and the finger are infected."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "munwe"), ("conjunct2", "muromo"), ("agreement", "8"), ("rejected", "4")]
    comment := "[3&3=8; ≠4]. The paper's gloss line pairs the two nouns in the order of the translation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex60 : LinguisticExample :=
  { id := "carstens2026_ex60"
    source := ⟨"carstens-2026", "(60)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "Dombo ne-zai zvi-ri panze."
    discourseSegments := []
    glossedTokens := [("Dombo", "5stone"), ("ne-zai", "and-5egg"), ("zvi-ri", "8SM-be"), ("panze", "outside")]
    translation := "The stone and the egg are outside."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "dombo"), ("conjunct2", "zai"), ("agreement", "8"), ("rejected", "6")]
    comment := "[5&5=8; ≠6]."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex61 : LinguisticExample :=
  { id := "carstens2026_ex61"
    source := ⟨"carstens-2026", "(61)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "Benzi ne-dinga va-ri ku-shayikwa."
    discourseSegments := []
    glossedTokens := [("Benzi", "5fool"), ("ne-dinga", "and-5dimwit"), ("va-ri", "2SM-be"), ("ku-shayikwa", "15-missing")]
    translation := "The fool and the dimwit are missing."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "benzi"), ("conjunct2", "dinga"), ("agreement", "2"), ("rejected", "6")]
    comment := "[5&5=2; ≠6]."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex62 : LinguisticExample :=
  { id := "carstens2026_ex62"
    source := ⟨"carstens-2026", "(62)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "Chi-ngwa ne-chi-bage zvi-ri pa-tafura."
    discourseSegments := []
    glossedTokens := [("Chi-ngwa", "7-bread"), ("ne-chi-bage", "and-7-maize"), ("zvi-ri", "8SM-be"), ("pa-tafura", "LOC-table")]
    translation := "The bread and the maize are on the table."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "chingwa"), ("conjunct2", "chibage"), ("agreement", "8")]
    comment := "[7&7=8], inanimate."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex63 : LinguisticExample :=
  { id := "carstens2026_ex63"
    source := ⟨"carstens-2026", "(63)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "Chi-dhakwa ne-chi-komana va-ri ku-netsana."
    discourseSegments := []
    glossedTokens := [("Chi-dhakwa", "7-drunkard"), ("ne-chi-komana", "and-7-small.boy"), ("va-ri/?zvi-", "2SM/8SM-be"), ("ku-netsana", "15-argue")]
    translation := "The drunkard and the small boy argued."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "chidhakwa"), ("conjunct2", "chikomana"), ("agreement", "2"), ("agreement", "8")]
    comment := "[7&7=2 or 8], human: class 2 volunteered, class 8 judged acceptable though less good (fn. 27)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex64b : LinguisticExample :=
  { id := "carstens2026_ex64b"
    source := ⟨"carstens-2026", "(64b)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "N-herera ne-n-yanzvi va-aka-on-ana."
    discourseSegments := []
    glossedTokens := [("N-herera", "9-orphan"), ("ne-n-yanzvi", "and-9-expert"), ("va-aka-on-ana", "2SM-PST-see-RECIP")]
    translation := "The orphan and the expert saw each other."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "nherera"), ("conjunct2", "nyanzvi"), ("agreement", "2"), ("rejected", "10")]
    comment := "[9&9=2; *10]."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex64c : LinguisticExample :=
  { id := "carstens2026_ex64c"
    source := ⟨"carstens-2026", "(64c)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "Im-bwa n-hema ne-m-hou chena zvi-aka-rwa."
    discourseSegments := []
    glossedTokens := [("Im-bwa", "9-dog"), ("n-hema", "9-black"), ("ne-m-hou", "and-9-cow"), ("chena", "9-white"), ("zvi-aka-rwa", "8SM-PST-fall")]
    translation := "The black dog and the white cow fell."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "imbwa"), ("conjunct2", "mhou"), ("agreement", "8"), ("rejected", "10")]
    comment := "[9&9=8; *10]: the [animal] association has bleached from Shona 9/10."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex64d : LinguisticExample :=
  { id := "carstens2026_ex64d"
    source := ⟨"carstens-2026", "(64d)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "M-huno iyi ne nzeve iyi zvi-ne utachiona."
    discourseSegments := []
    glossedTokens := [("M-huno", "9-nose"), ("iyi", "9this"), ("ne", "and"), ("nzeve", "9ear"), ("iyi", "9this"), ("zvi-ne", "8SM-have"), ("utachiona", "14-infection")]
    translation := "This nose and this ear are infected."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "mhuno"), ("conjunct2", "nzeve"), ("agreement", "8"), ("rejected", "10")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex64e : LinguisticExample :=
  { id := "carstens2026_ex64e"
    source := ⟨"carstens-2026", "(64e)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "M-biya iyi ne-sando iyo zvi-ne n-gura."
    discourseSegments := []
    glossedTokens := [("M-biya", "9-bowl"), ("iyi", "9-this"), ("ne-sando", "and-9hammer"), ("iyo", "9-that"), ("zvi-ne", "8SM-have"), ("n-gura", "9-rust")]
    translation := "This bowl and that hammer are rusty."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "mbiya"), ("conjunct2", "sando"), ("agreement", "8"), ("rejected", "10")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex64f : LinguisticExample :=
  { id := "carstens2026_ex64f"
    source := ⟨"carstens-2026", "(64f)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "N-yota ne-n-zara zv-aka-tambudza va-fambi."
    discourseSegments := []
    glossedTokens := [("N-yota", "9-thirst"), ("ne-n-zara", "and-9-hunger"), ("zv-aka-tambudza", "8SM-PST-afflict"), ("va-fambi", "2-travelers")]
    translation := "Hunger and thirst afflicted the travelers."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "nyota"), ("conjunct2", "nzara"), ("agreement", "8"), ("rejected", "10")]
    comment := "The paper's gloss line pairs the two nouns in the order of the translation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex65a : LinguisticExample :=
  { id := "carstens2026_ex65a"
    source := ⟨"carstens-2026", "(65a)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "Ru-kova urwu no-ru-kova urwo zvi-asvibiswa."
    discourseSegments := []
    glossedTokens := [("Ru-kova", "11-stream"), ("urwu", "11this"), ("no-ru-kova", "and-11-stream"), ("urwo", "11that"), ("zvi-asvibiswa", "8SM-PERF.polluted")]
    translation := "This stream and that stream are polluted."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "rukova"), ("conjunct2", "rukova"), ("agreement", "8"), ("rejected", "10")]
    comment := "[11&11=8; *10]: the class 10 dzi- of the plural (65b) is ruled out."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex66a : LinguisticExample :=
  { id := "carstens2026_ex66a"
    source := ⟨"carstens-2026", "(66a)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "U-ta ne-u-tanho zvi-ri kunze."
    discourseSegments := []
    glossedTokens := [("U-ta", "14-bow"), ("ne-u-tanho", "and-14-ladder"), ("zvi-ri", "8SM-be"), ("kunze", "outside")]
    translation := "The bow and the ladder are outside."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "uta"), ("conjunct2", "utanho"), ("agreement", "8"), ("rejected", "6")]
    comment := "[14&14=8; *6]: the class 6 a- of the plural (66b) is ruled out."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex68a : LinguisticExample :=
  { id := "carstens2026_ex68a"
    source := ⟨"carstens-2026", "(68a)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "Ka-sikana ne-ka-kómaná v-a-nyangadika."
    discourseSegments := []
    glossedTokens := [("Ka-sikana", "12-girl"), ("ne-ka-kómaná", "and-12-boy"), ("v-a-nyangadika", "2SM-ASP-disappear")]
    translation := "The tiny girl and the tiny boy disappeared."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "kasikana"), ("conjunct2", "kakomana"), ("agreement", "2"), ("rejected", "13")]
    comment := "[12&12=2; *13]: conjoined diminutives take class 2, not the class 13 tu- of their plurals (67b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex68b : LinguisticExample :=
  { id := "carstens2026_ex68b"
    source := ⟨"carstens-2026", "(68b)"⟩
    reportedIn := none
    language := "shon1251"
    primaryText := "Ka-mba ne-ka-motokari zv-a-nyangadika."
    discourseSegments := []
    glossedTokens := [("Ka-mba", "12-house"), ("ne-ka-motokari", "and-12-car"), ("zv-a-nyangadika", "8SM-ASP-disappear")]
    translation := "The tiny house and the tiny car disappeared."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("conjunct1", "kamba"), ("conjunct2", "kamotokari"), ("agreement", "8"), ("rejected", "13")]
    comment := "[12&12=8; *13]."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex6a, ex6b, ex7b, ex8b, ex9a, ex9b, ex37a, ex38a, ex38b, ex38c, ex40a, ex40b, ex41a, ex41b, ex44, ex45a, ex45b, ex46a, ex46b, ex47a, ex47b, ex48a, ex48b, ex49a, ex49b, ex55a, ex55b, ex81a, ex81b, ex83, ex85a, ex85b, ex89, ex91, ex111, ex58, ex59, ex60, ex61, ex62, ex63, ex64b, ex64c, ex64d, ex64e, ex64f, ex65a, ex66a, ex68a, ex68b]

end Carstens2026.Examples
