module

public import Linglib.Data.Examples.Schema

/-!
# `BrananErlewine2023` — typed example data

Auto-generated from `Linglib/Data/Examples/BrananErlewine2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BrananErlewine2023.Examples`.
-/

@[expose] public section

namespace BrananErlewine2023.Examples

def ex_1 : Datum :=
  { id := "brananerlewine2023_1"
    source := ⟨"branan-erlewine-2023", "(1)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A házigazda Katinak mutatta be Jánost."
    glossedTokens := [("A", "the"), ("házigazda", "host"), ("Katinak", "Cathy.DAT"), ("mutatta", "show"), ("be", "VM"), ("Jánost", "John.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("goal", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "goal"), ("mismatch", "none")] }

def ex_2 : Datum :=
  { id := "brananerlewine2023_2"
    source := ⟨"branan-erlewine-2023", "(2)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-wa hon-mo kat-ta."
    glossedTokens := [("Hanako-wa", "Hanako-TOP"), ("hon-mo", "book-also"), ("kat-ta", "buy-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("object", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "object"), ("mismatch", "none")] }

def ex_3 : Datum :=
  { id := "brananerlewine2023_3"
    source := ⟨"branan-erlewine-2023", "(3)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Anna a használt autót adta el."
    glossedTokens := [("Anna", "Anna"), ("a", "the"), ("használt", "used"), ("autót", "car.ACC"), ("adta", "sold"), ("el", "VM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("adjective", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "object"), ("mismatch", "piedPiping")] }

def ex_4 : Datum :=
  { id := "brananerlewine2023_4"
    source := ⟨"branan-erlewine-2023", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-wa hon-o kai-mo shi, zasshi-o kai-mo shi-ta."
    glossedTokens := [("Hanako-wa", "Hanako-TOP"), ("hon-o", "book-ACC"), ("kai-mo", "buy-also"), ("shi", "do"), ("zasshi-o", "magazine-ACC"), ("kai-mo", "buy-also"), ("shi-ta", "do-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("object", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "predicate"), ("mismatch", "piedPiping")] }

def ex_7 : Datum :=
  { id := "brananerlewine2023_7"
    source := ⟨"branan-erlewine-2023", "(7)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Péter a Hamletet olvasta fel a kertben, nem pedig úszott."
    glossedTokens := [("Péter", "Peter"), ("a", "the"), ("Hamletet", "Hamlet.ACC"), ("olvasta", "read"), ("fel", "VM"), ("a", "the"), ("kertben", "garden.INE"), ("nem", "not"), ("pedig", "rather"), ("úszott", "swim")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("predicate", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "object"), ("mismatch", "antiPiedPiping")] }

def ex_8 : Datum :=
  { id := "brananerlewine2023_8"
    source := ⟨"branan-erlewine-2023", "(8)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ame-mo furu-shi, kaze-mo fuku."
    glossedTokens := [("Ame-mo", "rain-also"), ("furu-shi", "falls-CONJ"), ("kaze-mo", "wind-also"), ("fuku", "blows")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "subject"), ("mismatch", "antiPiedPiping")] }

def ex_17b : Datum :=
  { id := "brananerlewine2023_17b"
    source := ⟨"branan-erlewine-2023", "(17b)"⟩
    reportedIn := none
    language := "yaey1239"
    primaryText := "Hajasi-san-du ziroo-ba bari."
    glossedTokens := [("Hajasi-san-du", "Hayashi-san-PRT"), ("ziroo-ba", "Jiro-BA"), ("bari", "hit")]
    context := "Answer to 'What happened?'"
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "subject"), ("leftmost", "strong"), ("mismatch", "antiPiedPiping")] }

def ex_18b : Datum :=
  { id := "brananerlewine2023_18b"
    source := ⟨"branan-erlewine-2023", "(18b)"⟩
    reportedIn := none
    language := "yaey1239"
    primaryText := "Kunu midunpïto-o izï-ba-du fai."
    glossedTokens := [("Kunu", "this"), ("midunpïto-o", "woman-TOP"), ("izï-ba-du", "fish-BA-PRT"), ("fai", "ate")]
    context := "Answer to 'What did that woman do?'"
    judgment := .acceptable
    alternatives := []
    readings := [("predicate", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "object"), ("leftmost", "strong"), ("mismatch", "antiPiedPiping")] }

def ex_21 : Datum :=
  { id := "brananerlewine2023_21"
    source := ⟨"branan-erlewine-2023", "(21)"⟩
    reportedIn := none
    language := "ishk1246"
    primaryText := "Salima kulča-məs pacu."
    glossedTokens := [("Salima", "Salima"), ("kulča-məs", "kulcha-also"), ("pacu", "bake")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("object", .acceptable), ("predicate", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "object"), ("leftmost", "strong")] }

def ex_30a : Datum :=
  { id := "brananerlewine2023_30a"
    source := ⟨"branan-erlewine-2023", "(30a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-ga tako-o tabe-mo shi-ta."
    glossedTokens := [("Taro-ga", "Taro-NOM"), ("tako-o", "octopus-ACC"), ("tabe-mo", "eat-also"), ("shi-ta", "do-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("predicate", .acceptable), ("object", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "predicate"), ("leftmost", "weak")] }

def ex_30b : Datum :=
  { id := "brananerlewine2023_30b"
    source := ⟨"branan-erlewine-2023", "(30b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-ga tako-mo tabe-ta."
    glossedTokens := [("Taro-ga", "Taro-NOM"), ("tako-mo", "octopus-also"), ("tabe-ta", "eat-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("predicate", .acceptable), ("object", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "object"), ("leftmost", "weak")] }

def ex_38 : Datum :=
  { id := "brananerlewine2023_38"
    source := ⟨"branan-erlewine-2023", "(38)"⟩
    reportedIn := none
    language := "ishk1246"
    primaryText := "Wai mol-məs xi dusto-i zənayu isu."
    glossedTokens := [("Wai", "DEM"), ("mol-məs", "husband-also"), ("xi", "REFL"), ("dusto-i", "hands-ACC"), ("zənayu", "wash"), ("isu", "come")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("subject", .acceptable), ("sentence", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "subject"), ("leftmost", "strong")] }

def ex_65_goal : Datum :=
  { id := "brananerlewine2023_65_goal"
    source := ⟨"branan-erlewine-2023", "(65)"⟩
    reportedIn := none
    language := "tibe1272"
    primaryText := "Kun.dga’ khyi-la-yang kha.lag sprad.gi.’dug."
    glossedTokens := [("Kun.dga’", "Kunga"), ("khyi-la-yang", "dog-DAT-also"), ("kha.lag", "food"), ("sprad.gi.’dug", "gives")]
    context := "Kunga's a very good person. She prays at the temple every day."
    judgment := .acceptable
    alternatives := []
    readings := [("predicate", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "goal"), ("leftmost", "weak")] }

def ex_65_theme : Datum :=
  { id := "brananerlewine2023_65_theme"
    source := ⟨"branan-erlewine-2023", "(65)"⟩
    reportedIn := none
    language := "tibe1272"
    primaryText := "Kun.dga’ khyi-la kha.lag-yang sprad.gi.’dug."
    glossedTokens := [("Kun.dga’", "Kunga"), ("khyi-la", "dog-DAT"), ("kha.lag-yang", "food-also"), ("sprad.gi.’dug", "gives")]
    context := "Kunga's a very good person. She prays at the temple every day."
    judgment := .marginal
    alternatives := []
    readings := [("predicate", .marginal)]
    paperFeatures := [("process", "particle"), ("msf", "theme"), ("leftmost", "weak")] }

def ex_66a : Datum :=
  { id := "brananerlewine2023_66a"
    source := ⟨"branan-erlewine-2023", "(66a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-mo piano-o hiita."
    glossedTokens := [("Taro-mo", "Taro-also"), ("piano-o", "piano-ACC"), ("hiita", "played")]
    context := "At yesterday's party, not only did Hanako dance, but ..."
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "subject"), ("leftmost", "weak")] }

def ex_66b : Datum :=
  { id := "brananerlewine2023_66b"
    source := ⟨"branan-erlewine-2023", "(66b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taro-ga piano-mo hiita."
    glossedTokens := [("Taro-ga", "Taro-NOM"), ("piano-mo", "piano-also"), ("hiita", "played")]
    context := "At yesterday's party, not only did Hanako dance, but ..."
    judgment := .marginal
    alternatives := []
    readings := [("sentence", .marginal)]
    paperFeatures := [("process", "particle"), ("msf", "object"), ("leftmost", "weak")] }

def ex_67_goal : Datum :=
  { id := "brananerlewine2023_67_goal"
    source := ⟨"branan-erlewine-2023", "(67)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "Vo sirf bachcho-ko hii tohfe de payaa hai."
    glossedTokens := [("Vo", "3SG"), ("sirf", "only"), ("bachcho-ko", "children-DAT"), ("hii", "PRT"), ("tohfe", "gifts"), ("de", "give"), ("payaa", "able"), ("hai", "AUX")]
    context := "During Diwali, Pulkit plans to feed the poor and also distribute gifts to children. However, due to some emergency, he fails to be able to feed the poor."
    judgment := .acceptable
    alternatives := []
    readings := [("predicate", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "goal"), ("leftmost", "weak")] }

def ex_67_theme : Datum :=
  { id := "brananerlewine2023_67_theme"
    source := ⟨"branan-erlewine-2023", "(67)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "Vo sirf bachcho-ko tohfe hii de payaa hai."
    glossedTokens := [("Vo", "3SG"), ("sirf", "only"), ("bachcho-ko", "children-DAT"), ("tohfe", "gifts"), ("hii", "PRT"), ("de", "give"), ("payaa", "able"), ("hai", "AUX")]
    context := "During Diwali, Pulkit plans to feed the poor and also distribute gifts to children. However, due to some emergency, he fails to be able to feed the poor."
    judgment := .marginal
    alternatives := []
    readings := [("predicate", .marginal)]
    paperFeatures := [("process", "particle"), ("msf", "theme"), ("leftmost", "weak")] }

def ex_68a : Datum :=
  { id := "brananerlewine2023_68a"
    source := ⟨"branan-erlewine-2023", "(68a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Bücher hab ich ins Regal gestellt."
    glossedTokens := [("Die", "the"), ("Bücher", "books"), ("hab", "have"), ("ich", "1SG"), ("ins", "into.the"), ("Regal", "shelf"), ("gestellt", "placed")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("theme", .acceptable), ("predicate", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "theme"), ("leftmost", "strong")] }

def ex_68b : Datum :=
  { id := "brananerlewine2023_68b"
    source := ⟨"branan-erlewine-2023", "(68b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ins Regal hab ich die Bücher gestellt."
    glossedTokens := [("Ins", "into.the"), ("Regal", "shelf"), ("hab", "have"), ("ich", "1SG"), ("die", "the"), ("Bücher", "books"), ("gestellt", "placed")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("goal", .acceptable), ("predicate", .ungrammatical)]
    paperFeatures := [("process", "movement"), ("msf", "goal"), ("leftmost", "strong")] }

def ex_69a : Datum :=
  { id := "brananerlewine2023_69a"
    source := ⟨"branan-erlewine-2023", "(69a)"⟩
    reportedIn := none
    language := "kiku1240"
    primaryText := "Ne-mwana Abdul aðomaɣera iβuku."
    glossedTokens := [("Ne-mwana", "PRT-1.child"), ("Abdul", "Abdul"), ("aðomaɣera", "read"), ("iβuku", "book")]
    context := "Q: What does Abdul do?"
    judgment := .acceptable
    alternatives := []
    readings := [("predicate", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "goal"), ("leftmost", "weak")] }

def ex_69b : Datum :=
  { id := "brananerlewine2023_69b"
    source := ⟨"branan-erlewine-2023", "(69b)"⟩
    reportedIn := none
    language := "kiku1240"
    primaryText := "Ne-iβuku Abdul aðomaɣera mwana."
    glossedTokens := [("Ne-iβuku", "PRT-book"), ("Abdul", "Abdul"), ("aðomaɣera", "read"), ("mwana", "child")]
    context := "Q: What does Abdul do?"
    judgment := .marginal
    alternatives := []
    readings := [("predicate", .marginal)]
    paperFeatures := [("process", "movement"), ("msf", "theme"), ("leftmost", "weak")] }

def ex_70a : Datum :=
  { id := "brananerlewine2023_70a"
    source := ⟨"branan-erlewine-2023", "(70a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Tsìnà shàshi koñu."
    glossedTokens := [("Tsìnà", "dog"), ("shàshi", "ate"), ("koñu", "meat")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "subject"), ("leftmost", "free")] }

def ex_70b : Datum :=
  { id := "brananerlewine2023_70b"
    source := ⟨"branan-erlewine-2023", "(70b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Koñu shàshi tsìnà."
    glossedTokens := [("Koñu", "meat"), ("shàshi", "ate"), ("tsìnà", "dog")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "object"), ("leftmost", "free")] }

def ex_109a : Datum :=
  { id := "brananerlewine2023_109a"
    source := ⟨"branan-erlewine-2023", "(109a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Janu Linda hledala."
    glossedTokens := [("Janu", "Jana.ACC"), ("Linda", "Linda.NOM"), ("hledala", "looked.for.SG.F")]
    context := "Q: What's new?"
    judgment := .unacceptable
    alternatives := []
    readings := [("sentence", .unacceptable), ("object", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "object"), ("leftmost", "strong")] }

def ex_109b : Datum :=
  { id := "brananerlewine2023_109b"
    source := ⟨"branan-erlewine-2023", "(109b)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Janu někdo hledal."
    glossedTokens := [("Janu", "Jana.ACC"), ("někdo", "somebody.NOM"), ("hledal", "looked.for.SG.M")]
    context := "Q: What's new?"
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "object"), ("leftmost", "strong"), ("skipped", "subject")] }

def ex_111a : Datum :=
  { id := "brananerlewine2023_111a"
    source := ⟨"branan-erlewine-2023", "(111a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "dareka-mo piano-o hiita."
    glossedTokens := [("dareka-mo", "someone-also"), ("piano-o", "piano-ACC"), ("hiita", "played")]
    context := "At yesterday's party, not only did Hanako dance a dance, but ..."
    judgment := .unacceptable
    alternatives := []
    readings := [("sentence", .unacceptable)]
    paperFeatures := [("process", "particle"), ("msf", "subject"), ("leftmost", "weak"), ("skipped", "subject")] }

def ex_111b : Datum :=
  { id := "brananerlewine2023_111b"
    source := ⟨"branan-erlewine-2023", "(111b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "dareka-ga piano-mo hiita."
    glossedTokens := [("dareka-ga", "someone-NOM"), ("piano-mo", "piano-also"), ("hiita", "played")]
    context := "At yesterday's party, not only did Hanako dance a dance, but ..."
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "object"), ("leftmost", "weak"), ("skipped", "subject")] }

def ex_114a : Datum :=
  { id := "brananerlewine2023_114a"
    source := ⟨"branan-erlewine-2023", "(114a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "B’àràayii nèe su-kà yi mîn saatàa!"
    glossedTokens := [("B’àràayii", "robbers"), ("nèe", "FM"), ("su-kà", "3PL-REL"), ("yi", "do"), ("mîn", "to.me"), ("saatàa", "theft")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "subject"), ("leftmost", "strong")] }

def ex_114b : Datum :=
  { id := "brananerlewine2023_114b"
    source := ⟨"branan-erlewine-2023", "(114b)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Dabboobi-n jeejìi nèe mutàanee su-kà kaamàa."
    glossedTokens := [("Dabboobi-n", "animals-of"), ("jeejìi", "wild"), ("nèe", "FM"), ("mutàanee", "men"), ("su-kà", "3PL-REL"), ("kaamàa", "catch")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("sentence", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "object"), ("leftmost", "strong"), ("skipped", "subject")] }

def ex_120a : Datum :=
  { id := "brananerlewine2023_120a"
    source := ⟨"branan-erlewine-2023", "(120a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whose picture did you frame?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wh", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "phrase"), ("leftmost", "strong")] }

def ex_120b : Datum :=
  { id := "brananerlewine2023_120b"
    source := ⟨"branan-erlewine-2023", "(120b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A picture of whom did you frame?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("wh", .ungrammatical)]
    paperFeatures := [("process", "movement"), ("msf", "phrase"), ("leftmost", "strong")] }

def ex_121a : Datum :=
  { id := "brananerlewine2023_121a"
    source := ⟨"branan-erlewine-2023", "(121a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whose brother's friend's father did you see?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wh", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "phrase"), ("leftmost", "strong")] }

def ex_121b : Datum :=
  { id := "brananerlewine2023_121b"
    source := ⟨"branan-erlewine-2023", "(121b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The father of whose brother's friend did you see?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("wh", .ungrammatical)]
    paperFeatures := [("process", "movement"), ("msf", "phrase"), ("leftmost", "strong")] }

def ex_123 : Datum :=
  { id := "brananerlewine2023_123"
    source := ⟨"branan-erlewine-2023", "(123)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To which student's friend did you speak?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wh", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "phrase"), ("leftmost", "strong"), ("skipped", "phrase")] }

def ex_124 : Datum :=
  { id := "brananerlewine2023_124"
    source := ⟨"branan-erlewine-2023", "(124)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "ob eās-que rēs"
    glossedTokens := [("ob", "because"), ("eās-que", "these-also"), ("rēs", "things")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("phrase", .acceptable)]
    paperFeatures := [("process", "particle"), ("msf", "demonstrative"), ("leftmost", "strong"), ("skipped", "phrase")] }

def ex_125 : Datum :=
  { id := "brananerlewine2023_125"
    source := ⟨"branan-erlewine-2023", "(125)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Interesno na sestre druga č’ej materi on ženilsja."
    glossedTokens := [("Interesno", "interesting"), ("na", "on"), ("sestre", "sister"), ("druga", "friend"), ("č’ej", "whose"), ("materi", "mother"), ("on", "he"), ("ženilsja", "married")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wh", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "phrase"), ("leftmost", "free")] }

def ex_126 : Datum :=
  { id := "brananerlewine2023_126"
    source := ⟨"branan-erlewine-2023", "(126)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Reports the height of the lettering on the covers of which the government prescribes should be abolished."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wh", .acceptable)]
    paperFeatures := [("process", "movement"), ("msf", "phrase"), ("leftmost", "free")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_7, ex_8, ex_17b, ex_18b, ex_21, ex_30a, ex_30b, ex_38, ex_65_goal, ex_65_theme, ex_66a, ex_66b, ex_67_goal, ex_67_theme, ex_68a, ex_68b, ex_69a, ex_69b, ex_70a, ex_70b, ex_109a, ex_109b, ex_111a, ex_111b, ex_114a, ex_114b, ex_120a, ex_120b, ex_121a, ex_121b, ex_123, ex_124, ex_125, ex_126]

end BrananErlewine2023.Examples
