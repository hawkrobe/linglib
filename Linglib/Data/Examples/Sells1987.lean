module

public import Linglib.Data.Examples.Schema

/-!
# `Sells1987` — typed example data

Auto-generated from `Linglib/Data/Examples/Sells1987.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Sells1987.Examples`.
-/

@[expose] public section

namespace Sells1987.Examples

def ex_11a : Datum :=
  { id := "sells1987_11a"
    source := ⟨"sells-1987", "(11a)"⟩
    reportedIn := none
    language := "ewee1241"
    primaryText := "kofi be yè-dzo"
    glossedTokens := [("kofi", "Kofi"), ("be", "say"), ("yè-dzo", "Log-leave")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "yè"), ("environment", "logophoric verb")] }

def ex_12 : Datum :=
  { id := "sells1987_12"
    source := ⟨"sells-1987", "(12)"⟩
    reportedIn := none
    language := "ewee1241"
    primaryText := "ana kpɔ dyidzo be yè-dyi vi"
    glossedTokens := [("ana", "Ana"), ("kpɔ", "see"), ("dyidzo", "happiness"), ("be", "Comp"), ("yè-dyi", "Log-bear"), ("vi", "child")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "yè"), ("environment", "psych-verb")] }

def ex_17 : Datum :=
  { id := "sells1987_17"
    source := ⟨"sells-1987", "(17)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hann sagði að sig vantaði hæfileika."
    glossedTokens := [("Hann", "he"), ("sagði", "said"), ("að", "that"), ("sig", "self"), ("vantaði", "lacked"), ("hæfileika", "ability")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "sig"), ("environment", "logophoric verb")] }

def ex_43 : Datum :=
  { id := "sells1987_43"
    source := ⟨"sells-1987", "(43)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo wa Yosiko ga zibun o aisiteiru to itta."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "logophoric verb")] }

def ex_44 : Datum :=
  { id := "sells1987_44"
    source := ⟨"sells-1987", "(44)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Yosiko ga zibun o musisita koto ga Taroo o yuutunisita."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "psych-verb")] }

def ex_45 : Datum :=
  { id := "sells1987_45"
    source := ⟨"sells-1987", "(45)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa Taroo ni baka no Yosiko ga zibun o oikake-mawasiteiru koto o hanasita."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("Taroo", "Taroo"), ("ni", "Dat"), ("baka", "fool"), ("no", "Gen"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("oikake-mawasiteiru", "chase-around-be"), ("koto", "Comp"), ("o", "Obj"), ("hanasita", "told")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable), ("external speaker", .marginal)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "that fool"), ("environment", "logophoric verb")] }

def ex_46 : Datum :=
  { id := "sells1987_46"
    source := ⟨"sells-1987", "(46)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo wa Takasi kara baka no Yosiko ga zibun o oikake-mawasiteiru to kiita."
    glossedTokens := [("Taroo", "Taroo"), ("wa", "Top"), ("Takasi", "Takasi"), ("kara", "from"), ("baka", "fool"), ("no", "Gen"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("oikake-mawasiteiru", "chase-around-be"), ("to", "Comp"), ("kiita", "heard")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable), ("external speaker", .acceptable)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "that fool"), ("environment", "logophoric verb")] }

def ex_47 : Datum :=
  { id := "sells1987_47"
    source := ⟨"sells-1987", "(47)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Baka no Yosiko ga zibun o oikake-mawasiteiru koto ga Mitiko o zetuboo e oiyatta."
    glossedTokens := [("Baka", "fool"), ("no", "Gen"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("oikake-mawasiteiru", "chase-around-be"), ("koto", "Comp"), ("ga", "Subj"), ("Mitiko", "Mitiko"), ("o", "Obj"), ("zetuboo", "desperation"), ("e", "to"), ("oiyatta", "drove")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .unacceptable), ("external speaker", .acceptable)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "that fool"), ("environment", "psych-verb")] }

def ex_48 : Datum :=
  { id := "sells1987_48"
    source := ⟨"sells-1987", "(48)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo wa baka no Yosiko ga mizu o zibun no ue ni kobosita node nurete-simatta."
    glossedTokens := [("Taroo", "Taroo"), ("wa", "Top"), ("baka", "fool"), ("no", "Gen"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("mizu", "water"), ("o", "Obj"), ("zibun", "self"), ("no", "Gen"), ("ue", "on"), ("ni", "Loc"), ("kobosita", "spilled"), ("node", "because"), ("nurete-simatta", "wet-got")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .unacceptable), ("external speaker", .acceptable)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "that fool"), ("environment", "3POV")] }

def ex_49 : Datum :=
  { id := "sells1987_49"
    source := ⟨"sells-1987", "(49)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa Yosiko ga hukakainimo ato o tuke-mawasiteiru to itta."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("hukakainimo", "mysteriously"), ("ato o tuke-mawasiteiru", "be-following"), ("to", "Comp"), ("itta", "said")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable)]
    paperFeatures := [("diagnostic", "mysteriously"), ("environment", "logophoric verb")] }

def ex_50 : Datum :=
  { id := "sells1987_50"
    source := ⟨"sells-1987", "(50)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo wa Takasi kara Yosiko ga hukakainimo ato o tuke-mawasiteiru to kiita."
    glossedTokens := [("Taroo", "Taroo"), ("wa", "Top"), ("Takasi", "Takasi"), ("kara", "from"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("hukakainimo", "mysteriously"), ("ato o tuke-mawasiteiru", "be-following"), ("to", "Comp"), ("kiita", "heard")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable)]
    paperFeatures := [("diagnostic", "mysteriously"), ("environment", "logophoric verb")] }

def ex_51 : Datum :=
  { id := "sells1987_51"
    source := ⟨"sells-1987", "(51)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Yosiko ga hukakainimo ato o tuke-mawasiteiru koto ga Takasi o iradataseteiru."
    glossedTokens := [("Yosiko", "Yosiko"), ("ga", "Subj"), ("hukakainimo", "mysteriously"), ("ato o tuke-mawasiteiru", "be-following"), ("koto", "Comp"), ("ga", "Subj"), ("Takasi", "Takasi"), ("o", "Obj"), ("iradataseteiru", "bothers")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable)]
    paperFeatures := [("diagnostic", "mysteriously"), ("environment", "psych-verb")] }

def ex_52 : Datum :=
  { id := "sells1987_52"
    source := ⟨"sells-1987", "(52)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Yosiko ga hukakainimo ato o tuke-mawasiteiru noni Takasi wa ki ni sitei-nai."
    glossedTokens := [("Yosiko", "Yosiko"), ("ga", "Subj"), ("hukakainimo", "mysteriously"), ("ato o tuke-mawasiteiru", "be-following"), ("noni", "though"), ("Takasi", "Takasi"), ("wa", "Top"), ("ki", "care"), ("ni", "to"), ("sitei-nai", "give-not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .unacceptable), ("external speaker", .acceptable)]
    paperFeatures := [("diagnostic", "mysteriously"), ("environment", "3POV")] }

def ex_56 : Datum :=
  { id := "sells1987_56"
    source := ⟨"sells-1987", "(56)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa Taroo ni itosii Yosiko ga zibun o nikundeiru koto o hanasita."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("Taroo", "Taroo"), ("ni", "Dat"), ("itosii", "beloved"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("nikundeiru", "be-hating"), ("koto", "Comp"), ("o", "Obj"), ("hanasita", "told")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "beloved"), ("environment", "logophoric verb")] }

def ex_57 : Datum :=
  { id := "sells1987_57"
    source := ⟨"sells-1987", "(57)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo wa Takasi kara itosii Yosiko ga zibun o nikundeiru to kiita."
    glossedTokens := [("Taroo", "Taroo"), ("wa", "Top"), ("Takasi", "Takasi"), ("kara", "from"), ("itosii", "beloved"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("nikundeiru", "be-hating"), ("to", "Comp"), ("kiita", "heard")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "beloved"), ("environment", "logophoric verb")] }

def ex_58 : Datum :=
  { id := "sells1987_58"
    source := ⟨"sells-1987", "(58)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Itosii Yosiko ga zibun o nikundeiru koto ga Mitiko o zetuboo e oiyatta."
    glossedTokens := [("Itosii", "beloved"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("nikundeiru", "be-hating"), ("koto", "Comp"), ("ga", "Subj"), ("Mitiko", "Mitiko"), ("o", "Obj"), ("zetuboo", "desperation"), ("e", "to"), ("oiyatta", "drove")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "beloved"), ("environment", "psych-verb")] }

def ex_59 : Datum :=
  { id := "sells1987_59"
    source := ⟨"sells-1987", "(59)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa itosii Yosiko ga mizu o zibun no ue ni kobosita node nurete-simatta."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("itosii", "beloved"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("mizu", "water"), ("o", "Obj"), ("zibun", "self"), ("no", "Gen"), ("ue", "on"), ("ni", "Loc"), ("kobosita", "spilled"), ("node", "because"), ("nurete-simatta", "wet-got")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal protagonist", .acceptable)]
    paperFeatures := [("pronoun", "zibun"), ("diagnostic", "beloved"), ("environment", "3POV")] }

def ex_60 : Datum :=
  { id := "sells1987_60"
    source := ⟨"sells-1987", "(60)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa Yosiko ga mizu o zibun no ue ni kobosita node nurete-simatta."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("mizu", "water"), ("o", "Obj"), ("zibun", "self"), ("no", "Gen"), ("ue", "on"), ("ni", "Loc"), ("kobosita", "spilled"), ("node", "because"), ("nurete-simatta", "wet-got")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "3POV")] }

def ex_61 : Datum :=
  { id := "sells1987_61"
    source := ⟨"sells-1987", "(61)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa Yosiko ga mizu o zibun no ue ni kobosita toki nurete-simatta."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("mizu", "water"), ("o", "Obj"), ("zibun", "self"), ("no", "Gen"), ("ue", "on"), ("ni", "Loc"), ("kobosita", "spilled"), ("toki", "when"), ("nurete-simatta", "wet-got")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "external")] }

def ex_71 : Datum :=
  { id := "sells1987_71"
    source := ⟨"sells-1987", "(71)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Oedipus wa Jocasta ga zibun o unda ie de ima wa kodomotati to koohuku-soo-ni kurasite-imasu."
    glossedTokens := [("Oedipus", "Oedipus"), ("wa", "Top"), ("Jocasta", "Jocasta"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("unda", "bore"), ("ie", "house"), ("de", "Loc"), ("ima", "now"), ("wa", "Top"), ("kodomotati", "children"), ("to", "with"), ("koohuku-soo-ni", "happily"), ("kurasite-imasu", "living-is")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "3POV")] }

def ex_72 : Datum :=
  { id := "sells1987_72"
    source := ⟨"sells-1987", "(72)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa Taroo ni Yosiko ga zibun o nikundeiru koto o hanasanakatta."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("Taroo", "Taroo"), ("ni", "Dat"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("nikundeiru", "be-hating"), ("koto", "Comp"), ("o", "Obj"), ("hanasanakatta", "told-not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "logophoric verb")] }

def ex_73 : Datum :=
  { id := "sells1987_73"
    source := ⟨"sells-1987", "(73)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo wa Takasi kara Yosiko ga zibun o nikundeiru to kikanakatta."
    glossedTokens := [("Taroo", "Taroo"), ("wa", "Top"), ("Takasi", "Takasi"), ("kara", "from"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("nikundeiru", "be-hating"), ("to", "Comp"), ("kikanakatta", "heard-not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "logophoric verb")] }

def ex_74 : Datum :=
  { id := "sells1987_74"
    source := ⟨"sells-1987", "(74)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Yosiko ga zibun o nikundeiru koto ga Mitiko o yuutunisite-wa-inai."
    glossedTokens := [("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("nikundeiru", "be-hating"), ("koto", "Comp"), ("ga", "Subj"), ("Mitiko", "Mitiko"), ("o", "Obj"), ("yuutunisite-wa-inai", "bothered-at all-not")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "psych-verb")] }

def ex_75 : Datum :=
  { id := "sells1987_75"
    source := ⟨"sells-1987", "(75)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Takasi wa Yosiko ga zibun o tazunete-kita node kanasigaranakatta."
    glossedTokens := [("Takasi", "Takasi"), ("wa", "Top"), ("Yosiko", "Yosiko"), ("ga", "Subj"), ("zibun", "self"), ("o", "Obj"), ("tazunete-kita", "visit-came"), ("node", "because"), ("kanasigaranakatta", "sad(verb)-not-Past")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "zibun"), ("environment", "3POV")] }

def ex_76 : Datum :=
  { id := "sells1987_76"
    source := ⟨"sells-1987", "(76)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón er hér enn þó að María kyssi sig."
    glossedTokens := [("Jón", "Jon"), ("er", "is"), ("hér", "here"), ("enn", "still"), ("þó að", "although"), ("María", "Maria"), ("kyssi", "kisses(subj)"), ("sig", "self")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "sig"), ("environment", "external")] }

def ex_77 : Datum :=
  { id := "sells1987_77"
    source := ⟨"sells-1987", "(77)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón segir að Haraldur sé hér enn þó að María kyssi sig."
    glossedTokens := [("Jón", "Jon"), ("segir", "says"), ("að", "that"), ("Haraldur", "Harold"), ("sé", "is(subj)"), ("hér", "here"), ("enn", "still"), ("þó að", "although"), ("María", "Maria"), ("kyssi", "kisses(subj)"), ("sig", "self")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "sig"), ("environment", "logophoric verb")] }

def all : List Datum := [ex_11a, ex_12, ex_17, ex_43, ex_44, ex_45, ex_46, ex_47, ex_48, ex_49, ex_50, ex_51, ex_52, ex_56, ex_57, ex_58, ex_59, ex_60, ex_61, ex_71, ex_72, ex_73, ex_74, ex_75, ex_76, ex_77]

end Sells1987.Examples
