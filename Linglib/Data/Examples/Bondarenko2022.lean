import Linglib.Data.Examples.Schema

/-!
# `Bondarenko2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Bondarenko2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Bondarenko2022.Examples`.
-/

namespace Bondarenko2022.Examples

open Data.Examples

def ch2_105 : LinguisticExample :=
  { id := "bondarenko2022_ch2_105"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (105)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Ideja čto grjadut reformy javljaetsja vernoj."
    discourseSegments := []
    glossedTokens := [("Ideja", "idea"), ("čto", "COMP"), ("grjadut", "are.coming"), ("reformy", "reforms"), ("javljaetsja", "is"), ("vernoj", "true")]
    translation := "An idea / a situation that reforms are coming is true / mistaken."
    context := ""
    judgment := .acceptable
    alternatives := [("Situacija čto grjadut reformy javljaetsja vernoj.", .ungrammatical), ("Ideja čto grjadut reformy javljaetsja ošibočnoj.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "truth-predicates"), ("nounSort", "content")]
    comment := "Paper prints the alternations 'Ideja /*situacija' and 'vernoj /ošibočnoj' inside one example; expanded here per the alternatives convention. Cont-NP 'idea' combines with 'true'/'mistaken', Sit-NP 'situation' does not. Bracketed [CP ...] markup dropped from primaryText."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ch2_106 : LinguisticExample :=
  { id := "bondarenko2022_ch2_106"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (106)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-i kecis-i-ta."
    discourseSegments := []
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-i", "claim-NOM"), ("kecis-i-ta", "falsehood-COP-DECL")]
    translation := "The claim that Swuna solved the problem is false/true."
    context := ""
    judgment := .acceptable
    alternatives := [("Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-i cham-i-ta.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "truth-predicates"), ("nounSort", "content")]
    comment := "Paper prints 'kecis-i-ta /cham-i-ta' (falsehood-COP-DECL /truth-COP-DECL) in one example; the cham- variant is expanded into alternatives. Bracketing dropped from primaryText."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ch2_107 : LinguisticExample :=
  { id := "bondarenko2022_ch2_107"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (107)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka mwuncey-lul phwul-un sanghwang-i kecis-i-ta."
    discourseSegments := []
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-i", "situation-NOM"), ("kecis-i-ta", "falsehood-COP-DECL")]
    translation := "The situation that Swuna solved the problem is false/true."
    context := ""
    judgment := .ungrammatical
    alternatives := [("Swuna-ka mwuncey-lul phwul-un sanghwang-i cham-i-ta.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "truth-predicates"), ("nounSort", "situation")]
    comment := "Star scopes over both predicate variants ('kecis-i-ta /cham-i-ta'). Extraction prints the gloss of phwul-un as 'solve--adn' (double hyphen artifact); normalized to solve-ADN per the same form in (110), (112), (122)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ch2_108 : LinguisticExample :=
  { id := "bondarenko2022_ch2_108"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (108)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Včera proizošla situacija čto moj zakaz zaderžali."
    discourseSegments := []
    glossedTokens := [("Včera", "yesterday"), ("proizošla", "occured"), ("situacija", "situation"), ("čto", "COMP"), ("moj", "my"), ("zakaz", "order"), ("zaderžali", "delayed")]
    translation := "Yesterday a situation/idea that my order was delayed happened/occurred."
    context := ""
    judgment := .acceptable
    alternatives := [("Včera proizošla ideja čto moj zakaz zaderžali.", .ungrammatical), ("Včera slučilas’ situacija čto moj zakaz zaderžali.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "occurrence-predicates"), ("nounSort", "situation")]
    comment := "Paper prints 'proizošla /slučilas’ *ideja /situacija' in one example; expanded here. Occurrence verbs combine with Sit-NPs, not Cont-NPs. Gloss 'occured' is the paper's own spelling. Bracketing dropped from primaryText."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ch2_109 : LinguisticExample :=
  { id := "bondarenko2022_ch2_109"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (109)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-i ilena-ss-ta"
    discourseSegments := []
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-i", "claim-NOM"), ("ilena-ss-ta", "occur-PST-DECL")]
    translation := "A claim that Swuna solved the problem occured."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "occurrence-predicates"), ("nounSort", "content")]
    comment := "Translation spelling 'occured' is the paper's own."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ch2_110 : LinguisticExample :=
  { id := "bondarenko2022_ch2_110"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (110)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka mwuncey-lul phwul-un sanghwang-i ilena-ss-ta"
    discourseSegments := []
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-i", "situation-NOM"), ("ilena-ss-ta", "occur-PST-DECL")]
    translation := "A situation that Swuna solved the problem occured."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "occurrence-predicates"), ("nounSort", "situation")]
    comment := "Translation spelling 'occured' is the paper's own."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ch2_111 : LinguisticExample :=
  { id := "bondarenko2022_ch2_111"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (111)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-ul alachay-ss-ta"
    discourseSegments := []
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-ul", "claim-ACC"), ("alachay-ss-ta", "notice-PST-DECL")]
    translation := "Mina noticed the claim that Swuna solved the problem."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "situation-only-predicate-notice"), ("nounSort", "content")]
    comment := "Consultant comment (fn. 28): 'This verb [alachay] just does not sound good with claim'."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ch2_112 : LinguisticExample :=
  { id := "bondarenko2022_ch2_112"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (112)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka Swuna-ka mwuncey-lul phwul-un sanghwang-ul alachay-ss-ta"
    discourseSegments := []
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-ul", "situation-ACC"), ("alachay-ss-ta", "notice-PST-DECL")]
    translation := "Mina noticed the situation that Swuna solved the problem."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "situation-only-predicate-notice"), ("nounSort", "situation")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ch2_120a : LinguisticExample :=
  { id := "bondarenko2022_ch2_120a"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (120a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Lena zametila slux čto èta ženščina priexala na kone."
    discourseSegments := []
    glossedTokens := [("Lena", "Lena"), ("zametila", "noticed"), ("slux", "rumor"), ("čto", "COMP"), ("èta", "this"), ("ženščina", "woman"), ("priexala", "arrived"), ("na", "on"), ("kone", "horse")]
    translation := "Lena noticed a rumor /an event that this woman arrived on a horse."
    context := ""
    judgment := .acceptable
    alternatives := [("Lena zametila slučaj čto èta ženščina priexala na kone.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "premise-a")]
    comment := "Paper prints 'slux /slučaj' (rumor /event) in one example. Premise (a) of the (120) substitution triple: with Cont-NP slux, premises (a),(b) do not entail conclusion (c) (opacity); with Sit-NP slučaj they do (transparency). Bracketing dropped from primaryText."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ch2_120b : LinguisticExample :=
  { id := "bondarenko2022_ch2_120b"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (120b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "èta ženščina — koroleva Velikobritanii."
    discourseSegments := []
    glossedTokens := [("èta", "this"), ("ženščina", "woman"), ("koroleva", "queen"), ("Velikobritanii", "Great.Britain")]
    translation := "This woman is the queen of Great Britain."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "premise-b")]
    comment := "Identity premise (b) of the (120) substitution triple; the em dash is the Russian null copula."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ch2_120c : LinguisticExample :=
  { id := "bondarenko2022_ch2_120c"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (120c)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Lena zametila slux čto koroleva Velikobritanii priexala na kone."
    discourseSegments := []
    glossedTokens := [("Lena", "Lena"), ("zametila", "noticed"), ("slux", "rumor"), ("čto", "COMP"), ("koroleva", "queen"), ("Velikobritanii", "Great.Britain"), ("priexala", "arrived"), ("na", "on"), ("kone", "horse")]
    translation := "Lena noticed a rumor /an event that the queen of Great Britain arrived on a horse."
    context := ""
    judgment := .acceptable
    alternatives := [("Lena zametila slučaj čto koroleva Velikobritanii priexala na kone.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "conclusion")]
    comment := "Conclusion (c) of the (120) substitution triple: does not follow from (a),(b) with Cont-NP slux (opacity); follows with Sit-NP slučaj (transparency). Bracketing dropped from primaryText."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ch2_121a : LinguisticExample :=
  { id := "bondarenko2022_ch2_121a"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (121a)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka Swuna-ka mwuncey-lul phwul-ess-ta-nun cwucang-ul kiekhay-ss-ta."
    discourseSegments := []
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-ul", "claim-ACC"), ("kiekhay-ss-ta", "remember-PST-DECL")]
    translation := "Mina remembers that Swuna solved the problem."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("nounSort", "content"), ("role", "premise-a")]
    comment := "Premise (a) of the (121) opacity triple: with Cont-NP cwucang 'claim', premises (a),(b) do not entail conclusion (c)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ch2_121b : LinguisticExample :=
  { id := "bondarenko2022_ch2_121b"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (121b)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka pan-eyse kacang khi-ga khu-ta."
    discourseSegments := []
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("pan-eyse", "class-LOC"), ("kacang", "most"), ("khi-ga", "height-NOM"), ("khu-ta", "large-DECL")]
    translation := "Swuna is the tallest in the class."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "premise-b")]
    comment := "Identity premise (b) of the (121) opacity triple."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ch2_121c : LinguisticExample :=
  { id := "bondarenko2022_ch2_121c"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (121c)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka pan-eyse kacang khi-ga khun sonye-ka mwuncey-lul phwul-ess-ta-nun cwucang-ul kiekhay-ss-ta."
    discourseSegments := []
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("pan-eyse", "class-LOC"), ("kacang", "most"), ("khi-ga", "height-NOM"), ("khun", "large"), ("sonye-ka", "girl-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-ess-ta-nun", "solve-PST-DECL-ADN"), ("cwucang-ul", "claim-ACC"), ("kiekhay-ss-ta", "remember-PST-DECL")]
    translation := "Mina remembers that the tallest girl in the class solved the problem."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("nounSort", "content"), ("role", "conclusion")]
    comment := "Conclusion (c) of the (121) opacity triple: does not follow from (a),(b) — Cont-CPs are referentially opaque."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ch2_122a : LinguisticExample :=
  { id := "bondarenko2022_ch2_122a"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (122a)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka Swuna-ka mwuncey-lul phwul-un sanghwang-ul kiekhay-ss-ta."
    discourseSegments := []
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("Swuna-ka", "Swuna-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-ul", "situation-ACC"), ("kiekhay-ss-ta", "remember-PST-DECL")]
    translation := "Mina remembers that Swuna solved the problem."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("nounSort", "situation"), ("role", "premise-a")]
    comment := "Premise (a) of the (122) transparency triple: with Sit-NP sanghwang 'situation', premises (a),(b) entail conclusion (c)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ch2_122b : LinguisticExample :=
  { id := "bondarenko2022_ch2_122b"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (122b)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Swuna-ka pan-eyse kacang khi-ga khu-ta."
    discourseSegments := []
    glossedTokens := [("Swuna-ka", "Swuna-NOM"), ("pan-eyse", "class-LOC"), ("kacang", "most"), ("khi-ga", "height-NOM"), ("khu-ta", "large-DECL")]
    translation := "Swuna is the tallest girl in the class."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("role", "premise-b")]
    comment := "Identity premise (b) of the (122) transparency triple."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ch2_122c : LinguisticExample :=
  { id := "bondarenko2022_ch2_122c"
    source := ⟨"bondarenko-2022", "§2.2.3 ex. (122c)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mina-ka pan-eyse kacang khi-ga khun sonye-ka mwuncey-lul phwul-un sanghwang-ul kiekhay-ss-ta."
    discourseSegments := []
    glossedTokens := [("Mina-ka", "Mina-NOM"), ("pan-eyse", "class-LOC"), ("kacang", "most"), ("khi-ga", "height-NOM"), ("khun", "large"), ("sonye-ka", "girl-NOM"), ("mwuncey-lul", "problem-ACC"), ("phwul-un", "solve-ADN"), ("sanghwang-ul", "situation-ACC"), ("kiekhay-ss-ta", "remember-PST-DECL")]
    translation := "Mina remembers that the tallest girl in the class solved the problem."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "substitution"), ("nounSort", "situation"), ("role", "conclusion")]
    comment := "Conclusion (c) of the (122) transparency triple: follows from (a),(b) — Sit-CPs are referentially transparent."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ch4_30 : LinguisticExample :=
  { id := "bondarenko2022_ch4_30"
    source := ⟨"bondarenko-2022", "§4.3.1 ex. (30)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Dugar mi:sgɘi zagaha ɘdj-ɘ: gɘ-žɘ han-a:"
    discourseSegments := []
    glossedTokens := [("Dugar", "Dugar.NOM"), ("mi:sgɘi", "cat.NOM"), ("zagaha", "fish"), ("ɘdj-ɘ:", "eat-PST"), ("gɘ-žɘ", "say-CVB"), ("han-a:", "think-PST")]
    translation := "Dugar thought that the cat ate the fish."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "Cont-CP"), ("shape", "bare gɘ-žɘ clause")]
    comment := "Barguzin Buryat. Bare CP: [... V-TENSE gɘ-žɘ] with the say-root gɘ plus converb -žɘ, combining directly with the verb. Bracketing dropped from primaryText."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ch4_31 : LinguisticExample :=
  { id := "bondarenko2022_ch4_31"
    source := ⟨"bondarenko-2022", "§4.3.1 ex. (31)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Dugar mi:sgɘi-n zagaha ɘdj-ɘ:š-i:jɘ-(n’) han-a:"
    discourseSegments := []
    glossedTokens := [("Dugar", "Dugar.NOM"), ("mi:sgɘi-n", "cat-GEN"), ("zagaha", "fish"), ("ɘdj-ɘ:š-i:jɘ-(n’)", "eat-PART-ACC-(3)"), ("han-a:", "think-PST")]
    translation := "Dugar remembered (an event of) the cat’s eating the fish."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "Sit-CP"), ("shape", "nominalized participial clause")]
    comment := "Barguzin Buryat. Nominalized Sit-CP: [... V-PART-CASE], genitive subject, participial -A:šA plus obligatory case and optional possessive marking. Bracketing dropped from primaryText."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ch4_32 : LinguisticExample :=
  { id := "bondarenko2022_ch4_32"
    source := ⟨"bondarenko-2022", "§4.3.1 ex. (32)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Dugar mi:sgɘi-n zagaha ɘdj-ɘ: g-ɘ:š-i:jɘ-(n’) han-a:"
    discourseSegments := []
    glossedTokens := [("Dugar", "Dugar.NOM"), ("mi:sgɘi-n", "cat-GEN"), ("zagaha", "fish"), ("ɘdj-ɘ:", "eat-PST"), ("g-ɘ:š-i:jɘ-(n’)", "say-PART-ACC-(3)"), ("han-a:", "think-PST")]
    translation := "Dugar remembers (a claim) that the cat ate the fish."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "Cont-CP"), ("shape", "nominalized gɘ-participial clause")]
    comment := "Barguzin Buryat. Nominalized Cont-CP: [... V-TENSE g-ɘ:š-CASE], the say-root gɘ plus participial -A:šA plus case (fn. 10: hiatus between gɘ and ɘ:šɘ resolved by vowel deletion in gɘ). Bracketing dropped from primaryText."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [ch2_105, ch2_106, ch2_107, ch2_108, ch2_109, ch2_110, ch2_111, ch2_112, ch2_120a, ch2_120b, ch2_120c, ch2_121a, ch2_121b, ch2_121c, ch2_122a, ch2_122b, ch2_122c, ch4_30, ch4_31, ch4_32]

end Bondarenko2022.Examples
