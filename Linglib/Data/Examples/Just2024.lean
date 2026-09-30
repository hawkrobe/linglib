module

public import Linglib.Data.Examples.Schema

/-!
# `Just2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Just2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Just2024.Examples`.
-/

@[expose] public section

namespace Just2024.Examples

open Data.Examples

def ex_2a : LinguisticExample :=
  { id := "just2024_2a"
    source := ⟨"just-2024", "(2a)"⟩
    reportedIn := none
    language := "east2879"
    primaryText := "äj-nø=tee-nø wöär-s-øt"
    glossedTokens := [("äj-nø=tee-nø", "drink-GER=eat-GER"), ("wöär-s-øt", "make-PST-3PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "false"), ("condition", "indefinite")] }

def ex_2b : LinguisticExample :=
  { id := "just2024_2b"
    source := ⟨"just-2024", "(2b)"⟩
    reportedIn := none
    language := "east2879"
    primaryText := "õõw-øm öät kont-iitø"
    glossedTokens := [("õõw-øm", "door-ACC"), ("öät", "NEG"), ("kont-iitø", "find-3SG>SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "true"), ("condition", "topical")] }

def ex_3 : LinguisticExample :=
  { id := "just2024_3"
    source := ⟨"just-2024", "(3)"⟩
    reportedIn := none
    language := "mace1250"
    primaryText := "Jana *(go)=bara režiser-ot"
    glossedTokens := [("Jana", "Jana"), ("*(go)=bara", "3SG.M.ACC=look.for.3SG"), ("režiser-ot", "movie.director-DEF.M")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "true"), ("condition", "definite")] }

def ex_4a : LinguisticExample :=
  { id := "just2024_4a"
    source := ⟨"just-2024", "(4a)"⟩
    reportedIn := none
    language := "kagu1239"
    primaryText := "Awafele ha-wa-koma dijoka"
    glossedTokens := [("Awafele", "C2.woman"), ("ha-wa-koma", "PST-C2.A-kill"), ("dijoka", "C5.snake")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "false")] }

def ex_4b : LinguisticExample :=
  { id := "just2024_4b"
    source := ⟨"just-2024", "(4b)"⟩
    reportedIn := none
    language := "kagu1239"
    primaryText := "Ka-mu-on-aga imukulu akwe"
    glossedTokens := [("Ka-mu-on-aga", "PST.3SG.A-C1.P-see-IPFV"), ("imukulu", "C1.big"), ("akwe", "3SG.POSS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "true"), ("condition", "animate")] }

def ex_4c : LinguisticExample :=
  { id := "just2024_4c"
    source := ⟨"just-2024", "(4c)"⟩
    reportedIn := none
    language := "kagu1239"
    primaryText := "Mheho i-ku-mu-ogoh-es-a"
    glossedTokens := [("Mheho", "C9.cold"), ("i-ku-mu-ogoh-es-a", "C9.A-PRS-3SG.P-fear-CAUS-FV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "true"), ("condition", "animate")] }

def ex_5a : LinguisticExample :=
  { id := "just2024_5a"
    source := ⟨"just-2024", "(5a)"⟩
    reportedIn := none
    language := "teiw1235"
    primaryText := "Miaag yivar ga-sii"
    glossedTokens := [("Miaag", "yesterday"), ("yivar", "dog"), ("ga-sii", "3SG.P-bite")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "true"), ("condition", "animate")] }

def ex_5b : LinguisticExample :=
  { id := "just2024_5b"
    source := ⟨"just-2024", "(5b)"⟩
    reportedIn := none
    language := "teiw1235"
    primaryText := "Miaag yivar ga'an sii"
    glossedTokens := [("Miaag", "yesterday"), ("yivar", "dog"), ("ga'an", "3SG"), ("sii", "bite")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "false"), ("condition", "focus")] }

def ex_6a : LinguisticExample :=
  { id := "just2024_6a"
    source := ⟨"just-2024", "(6a)"⟩
    reportedIn := none
    language := "rund1242"
    primaryText := "Abâna ba-ára-nyôye amatá"
    glossedTokens := [("Abâna", "C2.children"), ("ba-ára-nyôye", "C2-PST-drink:PFV"), ("amatá", "C1.milk")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "topical")] }

def ex_6b : LinguisticExample :=
  { id := "just2024_6b"
    source := ⟨"just-2024", "(6b)"⟩
    reportedIn := none
    language := "rund1242"
    primaryText := "Amatá y-á-nyôye abâna"
    glossedTokens := [("Amatá", "C1.milk"), ("y-á-nyôye", "C1.PST-drink:PFV"), ("abâna", "C2.children")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "focus")] }

def ex_6c : LinguisticExample :=
  { id := "just2024_6c"
    source := ⟨"just-2024", "(6c)"⟩
    reportedIn := none
    language := "rund1242"
    primaryText := "ha-á-nyôye amatá abâna"
    glossedTokens := [("ha-á-nyôye", "C10.LOC-PST-drink:PFV"), ("amatá", "C1.milk"), ("abâna", "C2.children")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "focus")] }

def ex_7a : LinguisticExample :=
  { id := "just2024_7a"
    source := ⟨"just-2024", "(7a)"⟩
    reportedIn := none
    language := "wels1247"
    primaryText := "Gwel-on nhw ddraig"
    glossedTokens := [("Gwel-on", "see-3PL.PST"), ("nhw", "they"), ("ddraig", "dragon")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "pronominal")] }

def ex_7b : LinguisticExample :=
  { id := "just2024_7b"
    source := ⟨"just-2024", "(7b)"⟩
    reportedIn := none
    language := "wels1247"
    primaryText := "Gwel-odd y bechgyn ddraig"
    glossedTokens := [("Gwel-odd", "see-3SG.PST"), ("y", "DEF"), ("bechgyn", "boy.PL"), ("ddraig", "dragon")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "lexical")] }

def ex_7c : LinguisticExample :=
  { id := "just2024_7c"
    source := ⟨"just-2024", "(7c)"⟩
    reportedIn := none
    language := "wels1247"
    primaryText := "*Gwel-on y bechgyn ddraig"
    glossedTokens := [("Gwel-on", "see-3PL.PST"), ("y", "DEF"), ("bechgyn", "boy.PL"), ("ddraig", "dragon")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "lexical")] }

def ex_8a : LinguisticExample :=
  { id := "just2024_8a"
    source := ⟨"just-2024", "(8a)"⟩
    reportedIn := none
    language := "koor1239"
    primaryText := "nun-i doro woon-d-uu-ns'i-ko"
    glossedTokens := [("nun-i", "we-NOM"), ("doro", "sheep"), ("woon-d-uu-ns'i-ko", "buy-PFV-PST-1PL-FOC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "predicateFocus")] }

def ex_8b : LinguisticExample :=
  { id := "just2024_8b"
    source := ⟨"just-2024", "(8b)"⟩
    reportedIn := none
    language := "koor1239"
    primaryText := "nun-i doro-ko woon-d-o"
    glossedTokens := [("nun-i", "we-NOM"), ("doro-ko", "sheep-FOC"), ("woon-d-o", "buy-PFV-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "otherFocus")] }

def ex_8c : LinguisticExample :=
  { id := "just2024_8c"
    source := ⟨"just-2024", "(8c)"⟩
    reportedIn := none
    language := "koor1239"
    primaryText := "tamba-ko doro woon-d-a"
    glossedTokens := [("tamba-ko", "me-FOC"), ("doro", "sheep"), ("woon-d-a", "buy-PFV-REL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "focus")] }

def ex_8d : LinguisticExample :=
  { id := "just2024_8d"
    source := ⟨"just-2024", "(8d)"⟩
    reportedIn := none
    language := "koor1239"
    primaryText := "*nun-i doro-ko woon-d-uu-ns'i"
    glossedTokens := [("nun-i", "we-NOM"), ("doro-ko", "sheep-FOC"), ("woon-d-uu-ns'i", "buy-PFV-PST-1PL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "otherFocus")] }

def ex_9a : LinguisticExample :=
  { id := "just2024_9a"
    source := ⟨"just-2024", "(9a)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "toofan-ha-ya peyapey dehkæde ra viran kærd"
    glossedTokens := [("toofan-ha-ya", "storm-PL-EZ"), ("peyapey", "constant"), ("dehkæde", "village"), ("ra", "ACC"), ("viran", "destroy"), ("kærd", "did.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "inanimate")] }

def ex_9b : LinguisticExample :=
  { id := "just2024_9b"
    source := ⟨"just-2024", "(9b)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "dozd-an-e gharætgar dehkæde ra viran kærd-ænd"
    glossedTokens := [("dozd-an-e", "thief-PL-EZ"), ("gharætgar", "marauder"), ("dehkæde", "village"), ("ra", "ACC"), ("viran", "destroy"), ("kærd-ænd", "did-3PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "animate")] }

def ex_10a : LinguisticExample :=
  { id := "just2024_10a"
    source := ⟨"just-2024", "(10a)"⟩
    reportedIn := none
    language := "anua1242"
    primaryText := "kwʌ̌n ā-cám ɲìlàal(-lì)"
    glossedTokens := [("kwʌ̌n", "porridge"), ("ā-cám", "PST-eat"), ("ɲìlàal(-lì)", "child(-DEF)")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false")] }

def ex_10b : LinguisticExample :=
  { id := "just2024_10b"
    source := ⟨"just-2024", "(10b)"⟩
    reportedIn := none
    language := "anua1242"
    primaryText := "ɲìlàal kwʌ̌n ā-cám-ε"
    glossedTokens := [("ɲìlàal", "child"), ("kwʌ̌n", "porridge"), ("ā-cám-ε", "PST-eat-3SG.A")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "topical")] }

def ex_10c : LinguisticExample :=
  { id := "just2024_10c"
    source := ⟨"just-2024", "(10c)"⟩
    reportedIn := none
    language := "anua1242"
    primaryText := "ɲìlàal cám-á kwʌ̌n"
    glossedTokens := [("ɲìlàal", "child"), ("cám-á", "eat-FOC"), ("kwʌ̌n", "porridge")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "otherFocus")] }

def ex_10d : LinguisticExample :=
  { id := "just2024_10d"
    source := ⟨"just-2024", "(10d)"⟩
    reportedIn := none
    language := "anua1242"
    primaryText := "kwʌ̌n cám-á ɲìlàal(-li)"
    glossedTokens := [("kwʌ̌n", "porridge"), ("cám-á", "eat-FOC"), ("ɲìlàal(-li)", "child(-DEF)")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "focus")] }

def ex_12a : LinguisticExample :=
  { id := "just2024_12a"
    source := ⟨"just-2024", "(12a)"⟩
    reportedIn := none
    language := "shek1245"
    primaryText := "gébèn bây dàdù nyààs=í-k"
    glossedTokens := [("gébèn", "Geben"), ("bây", "female"), ("dàdù", "child"), ("nyààs=í-k", "give.birth=3SG.F.A-REAL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "predicateFocus")] }

def ex_12b : LinguisticExample :=
  { id := "just2024_12b"
    source := ⟨"just-2024", "(12b)"⟩
    reportedIn := none
    language := "shek1245"
    primaryText := "m-bāyǹ nata gasku-k-ə"
    glossedTokens := [("m-bāyǹ", "1SG.POSS-wife"), ("nata", "1SG"), ("gasku-k-ə", "insult-REAL-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "focus")] }

def ex_13a_A : LinguisticExample :=
  { id := "just2024_13a_A"
    source := ⟨"just-2024", "(13a)"⟩
    reportedIn := none
    language := "maka1311"
    primaryText := "Na=cini'=i tedong-ku i Ali"
    glossedTokens := [("Na=cini'=i", "3SG.A=see=3SG.P"), ("tedong-ku", "buffalo-1SG.POSS"), ("i", "PERS"), ("Ali", "Ali")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "topical")] }

def ex_13a_P : LinguisticExample :=
  { id := "just2024_13a_P"
    source := ⟨"just-2024", "(13a)"⟩
    reportedIn := none
    language := "maka1311"
    primaryText := "Na=cini'=i tedong-ku i Ali"
    glossedTokens := [("Na=cini'=i", "3SG.A=see=3SG.P"), ("tedong-ku", "buffalo-1SG.POSS"), ("i", "PERS"), ("Ali", "Ali")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "true"), ("condition", "definite")] }

def ex_13b_A : LinguisticExample :=
  { id := "just2024_13b_A"
    source := ⟨"just-2024", "(13b)"⟩
    reportedIn := none
    language := "maka1311"
    primaryText := "kongkong=a a-buno=i miong=a"
    glossedTokens := [("kongkong=a", "dog=DEF"), ("a-buno=i", "AF-kill=3SG.P"), ("miong=a", "cat=DEF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "false"), ("condition", "focus")] }

def ex_13b_P : LinguisticExample :=
  { id := "just2024_13b_P"
    source := ⟨"just-2024", "(13b)"⟩
    reportedIn := none
    language := "maka1311"
    primaryText := "kongkong=a a-buno=i miong=a"
    glossedTokens := [("kongkong=a", "dog=DEF"), ("a-buno=i", "AF-kill=3SG.P"), ("miong=a", "cat=DEF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "true"), ("condition", "definite")] }

def ex_13c_P : LinguisticExample :=
  { id := "just2024_13c_P"
    source := ⟨"just-2024", "(13c)"⟩
    reportedIn := none
    language := "maka1311"
    primaryText := "miong=a na=buno kongkong=a"
    glossedTokens := [("miong=a", "cat=DEF"), ("na=buno", "3SG.A=kill"), ("kongkong=a", "dog=DEF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "P"), ("indexed", "false"), ("condition", "focus")] }

def ex_13c_A : LinguisticExample :=
  { id := "just2024_13c_A"
    source := ⟨"just-2024", "(13c)"⟩
    reportedIn := none
    language := "maka1311"
    primaryText := "miong=a na=buno kongkong=a"
    glossedTokens := [("miong=a", "cat=DEF"), ("na=buno", "3SG.A=kill"), ("kongkong=a", "dog=DEF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "A"), ("indexed", "true"), ("condition", "topical")] }

def t1_a1_p2 : LinguisticExample :=
  { id := "just2024_t1_a1_p2"
    source := ⟨"just-2024", "Table 1"⟩
    reportedIn := none
    language := "reye1240"
    primaryText := "A 1 with P 2"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aPerson", "1"), ("pPerson", "2"), ("indexed", "P")] }

def t1_a1_p3 : LinguisticExample :=
  { id := "just2024_t1_a1_p3"
    source := ⟨"just-2024", "Table 1"⟩
    reportedIn := none
    language := "reye1240"
    primaryText := "A 1 with P 3"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aPerson", "1"), ("pPerson", "3"), ("indexed", "A")] }

def t1_a2_p1 : LinguisticExample :=
  { id := "just2024_t1_a2_p1"
    source := ⟨"just-2024", "Table 1"⟩
    reportedIn := none
    language := "reye1240"
    primaryText := "A 2 with P 1"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aPerson", "2"), ("pPerson", "1"), ("indexed", "A")] }

def t1_a2_p3 : LinguisticExample :=
  { id := "just2024_t1_a2_p3"
    source := ⟨"just-2024", "Table 1"⟩
    reportedIn := none
    language := "reye1240"
    primaryText := "A 2 with P 3"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aPerson", "2"), ("pPerson", "3"), ("indexed", "A")] }

def t1_a3_p1 : LinguisticExample :=
  { id := "just2024_t1_a3_p1"
    source := ⟨"just-2024", "Table 1"⟩
    reportedIn := none
    language := "reye1240"
    primaryText := "A 3 with P 1"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aPerson", "3"), ("pPerson", "1"), ("indexed", "AP")] }

def t1_a3_p2 : LinguisticExample :=
  { id := "just2024_t1_a3_p2"
    source := ⟨"just-2024", "Table 1"⟩
    reportedIn := none
    language := "reye1240"
    primaryText := "A 3 with P 2"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aPerson", "3"), ("pPerson", "2"), ("indexed", "AP")] }

def t1_a3_p3 : LinguisticExample :=
  { id := "just2024_t1_a3_p3"
    source := ⟨"just-2024", "Table 1"⟩
    reportedIn := none
    language := "reye1240"
    primaryText := "A 3 with P 3"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aPerson", "3"), ("pPerson", "3"), ("indexed", "A")] }

def all : List LinguisticExample := [ex_2a, ex_2b, ex_3, ex_4a, ex_4b, ex_4c, ex_5a, ex_5b, ex_6a, ex_6b, ex_6c, ex_7a, ex_7b, ex_7c, ex_8a, ex_8b, ex_8c, ex_8d, ex_9a, ex_9b, ex_10a, ex_10b, ex_10c, ex_10d, ex_12a, ex_12b, ex_13a_A, ex_13a_P, ex_13b_A, ex_13b_P, ex_13c_P, ex_13c_A, t1_a1_p2, t1_a1_p3, t1_a2_p1, t1_a2_p3, t1_a3_p1, t1_a3_p2, t1_a3_p3]

end Just2024.Examples
