module

public import Linglib.Data.Examples.Schema

/-!
# `Lahiri1998` — typed example data

Auto-generated from `Linglib/Data/Examples/Lahiri1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Lahiri1998.Examples`.
-/

@[expose] public section

namespace Lahiri1998.Examples

def ex6a : Datum :=
  { id := "lahiri1998_ex6a"
    source := ⟨"lahiri-1998", "(6a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "koii bhii aayaa"
    glossedTokens := [("koii bhii", "anyone"), ("aayaa", "came")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("npi", "koii bhii"), ("environment", "positive (UE)")] }

def ex6b : Datum :=
  { id := "lahiri1998_ex6b"
    source := ⟨"lahiri-1998", "(6b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "koii bhii nahiiN aayaa"
    glossedTokens := [("koii bhii", "anyone"), ("nahiiN", "not"), ("aayaa", "came")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "koii bhii"), ("environment", "negation")] }

def ex6c : Datum :=
  { id := "lahiri1998_ex6c"
    source := ⟨"lahiri-1998", "(6c)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "maiN-ne kisii-ko bhii dekhaa"
    glossedTokens := [("maiN-ne", "I-ERG"), ("kisii-ko bhii", "anyone"), ("dekhaa", "saw")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("npi", "kisii-ko bhii"), ("environment", "positive (UE)")] }

def ex6d : Datum :=
  { id := "lahiri1998_ex6d"
    source := ⟨"lahiri-1998", "(6d)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "maiN-ne kisii-ko bhii nahiiN dekhaa"
    glossedTokens := [("maiN-ne", "I-ERG"), ("kisii-ko bhii", "anyone"), ("nahiiN", "not"), ("dekhaa", "saw")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "kisii-ko bhii"), ("environment", "negation")] }

def ex7a : Datum :=
  { id := "lahiri1998_ex7a"
    source := ⟨"lahiri-1998", "(7a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "ek bhii aadmii aayaa"
    glossedTokens := [("ek bhii", "any"), ("aadmii", "man"), ("aayaa", "came")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("npi", "ek bhii"), ("environment", "positive (UE)")] }

def ex7b : Datum :=
  { id := "lahiri1998_ex7b"
    source := ⟨"lahiri-1998", "(7b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "ek bhii aadmii nahiiN aayaa"
    glossedTokens := [("ek bhii", "any"), ("aadmii", "man"), ("nahiiN", "not"), ("aayaa", "came")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "ek bhii"), ("environment", "negation")] }

def ex8a : Datum :=
  { id := "lahiri1998_ex8a"
    source := ⟨"lahiri-1998", "(8a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "maiN-ne kuch bhii khaayaa"
    glossedTokens := [("maiN-ne", "I-ERG"), ("kuch bhii", "anything"), ("khaayaa", "ate")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("npi", "kuch bhii"), ("environment", "positive (UE)")] }

def ex8b : Datum :=
  { id := "lahiri1998_ex8b"
    source := ⟨"lahiri-1998", "(8b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "maiN-ne kuch bhii nahiiN khaayaa"
    glossedTokens := [("maiN-ne", "I-ERG"), ("kuch bhii", "anything"), ("nahiiN", "not"), ("khaayaa", "ate")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "kuch bhii"), ("environment", "negation")] }

def ex9a : Datum :=
  { id := "lahiri1998_ex9a"
    source := ⟨"lahiri-1998", "(9a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "maiN-ne zaraa bhii khaanaa khaayaa"
    glossedTokens := [("maiN-ne", "I-ERG"), ("zaraa", "a little"), ("bhii", "even"), ("khaanaa", "food"), ("khaayaa", "ate")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("npi", "zaraa bhii"), ("environment", "positive (UE)")] }

def ex9b : Datum :=
  { id := "lahiri1998_ex9b"
    source := ⟨"lahiri-1998", "(9b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "maiN-ne zaraa bhii khaanaa nahiiN khaayaa"
    glossedTokens := [("maiN-ne", "I-ERG"), ("zaraa", "a little"), ("bhii", "even"), ("khaanaa", "food"), ("nahiiN", "not"), ("khaayaa", "ate")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "zaraa bhii"), ("environment", "negation")] }

def ex10a : Datum :=
  { id := "lahiri1998_ex10a"
    source := ⟨"lahiri-1998", "(10a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "agar raam kisii-ko bhii dekhegaa to tumheN bataayegaa"
    glossedTokens := [("agar", "if"), ("raam", "Ram"), ("kisii-ko bhii", "anyone"), ("dekhegaa", "see-FUT"), ("to", "then"), ("tumheN", "you"), ("bataayegaa", "tell-FUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "kisii-ko bhii"), ("environment", "conditional protasis")] }

def ex10c : Datum :=
  { id := "lahiri1998_ex10c"
    source := ⟨"lahiri-1998", "(10c)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "agar raam aayegaa, to kuch bhii karegaa"
    glossedTokens := [("agar", "if"), ("raam", "Ram"), ("aayegaa", "come-FUT"), ("to", "then"), ("kuch bhii", "anything"), ("karegaa", "do-FUT")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("npi", "kuch bhii"), ("environment", "conditional apodosis")] }

def ex11a : Datum :=
  { id := "lahiri1998_ex11a"
    source := ⟨"lahiri-1998", "(11a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "aisaa har chaatr jisne ek bhii kitaab paRhii, paas ho gayaa"
    glossedTokens := [("aisaa", "such"), ("har", "every"), ("chaatr", "student"), ("jisne", "who"), ("ek", "one"), ("bhii", "even"), ("kitaab", "book"), ("paRhii", "read"), ("paas ho gayaa", "passed")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "ek bhii"), ("environment", "universal restrictor")] }

def ex12a : Datum :=
  { id := "lahiri1998_ex12a"
    source := ⟨"lahiri-1998", "(12a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "aisaa koii chaatr jisne ek bhii kitaab paRhii, paas ho gayaa"
    glossedTokens := [("aisaa", "such"), ("koii", "some"), ("chaatr", "student"), ("jisne", "who"), ("ek", "one"), ("bhii", "even"), ("kitaab", "book"), ("paRhii", "read"), ("paas ho gayaa", "passed")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("npi", "ek bhii"), ("environment", "existential restrictor")] }

def ex29a : Datum :=
  { id := "lahiri1998_ex29a"
    source := ⟨"lahiri-1998", "(29a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "mujhe is baat par aaScarya huaa ki ek bhii aadmii tumhaare ghar gayaa"
    glossedTokens := [("mujhe", "me"), ("is baat par", "this fact on"), ("aaScarya", "surprise"), ("huaa", "be"), ("ki", "that"), ("ek", "one"), ("bhii", "even"), ("aadmii", "person"), ("tumhaare", "your"), ("ghar", "house"), ("gayaa", "went")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "ek bhii"), ("environment", "adversative")] }

def ex29b : Datum :=
  { id := "lahiri1998_ex29b"
    source := ⟨"lahiri-1998", "(29b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "mujhe is baat par aaScarya huaa ki koii bhii tumhaare ghar gayaa"
    glossedTokens := [("mujhe", "me"), ("is baat par", "this fact on"), ("aaScarya", "surprise"), ("huaa", "be"), ("ki", "that"), ("koii bhii", "anyone"), ("tumhaare", "your"), ("ghar", "house"), ("gayaa", "went")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "koii bhii"), ("environment", "adversative")] }

def ex29c : Datum :=
  { id := "lahiri1998_ex29c"
    source := ⟨"lahiri-1998", "(29c)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "maiN-ne rameS-ko kisii-se bhii baat-ciit karne-se manaa kiyaa"
    glossedTokens := [("maiN-ne", "I"), ("rameS-ko", "Rames"), ("kisii-se bhii", "anyone"), ("baat-ciit karne-se", "talk"), ("manaa kiyaa", "prohibited")]
    context := ""
    judgment := .acceptable
    alternatives := [("maiN-ne rameS-ko kisii-se bhii baat-ciit karne-se rokaa", .questionable)]
    readings := []
    paperFeatures := [("npi", "kisii-se bhii"), ("environment", "prohibition verb")] }

def ex29d : Datum :=
  { id := "lahiri1998_ex29d"
    source := ⟨"lahiri-1998", "(29d)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "maiN-ne kisii-ko bhii rameS-se baat-ciit karne-se manaa kiyaa"
    glossedTokens := [("maiN-ne", "I"), ("kisii-ko bhii", "anyone"), ("rameS-se", "Rames"), ("baat-ciit karne-se", "talk"), ("manaa kiyaa", "prohibited")]
    context := ""
    judgment := .ungrammatical
    alternatives := [("maiN-ne kisii-ko bhii rameS-se baat-ciit karne-se rokaa", .ungrammatical)]
    readings := []
    paperFeatures := [("npi", "kisii-ko bhii"), ("environment", "outside prohibition scope")] }

def ex31a : Datum :=
  { id := "lahiri1998_ex31a"
    source := ⟨"lahiri-1998", "(31a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "maiN is baat par khuS huuN ki koii bhii mere ghar aayaa"
    glossedTokens := [("maiN", "I"), ("is baat par", "this fact on"), ("khuS", "happy"), ("huuN", "be"), ("ki", "that"), ("koii bhii", "anyone"), ("mere", "my"), ("ghar", "house"), ("aayaa", "came")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("npi", "koii bhii"), ("environment", "non-adversative factive")] }

def ex31b : Datum :=
  { id := "lahiri1998_ex31b"
    source := ⟨"lahiri-1998", "(31b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "tum is baat se khuS raho ki koii bhii tumhaare ghar aayaa"
    glossedTokens := [("tum", "you"), ("is baat se", "this fact with"), ("khuS", "happy"), ("raho", "stay"), ("ki", "that"), ("koii bhii", "anyone"), ("tumhaare", "your"), ("ghar", "house"), ("aayaa", "came")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "koii bhii"), ("environment", "settle-for-less glad")] }

def ex32a : Datum :=
  { id := "lahiri1998_ex32a"
    source := ⟨"lahiri-1998", "(32a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "kisiike bhii aane-se pahle raam ghar calaa gayaa"
    glossedTokens := [("kisiike bhii", "anyone's"), ("aane-se", "coming"), ("pahle", "before"), ("raam", "Ram"), ("ghar", "home"), ("calaa gayaa", "went")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "kisiike bhii"), ("environment", "before-clause")] }

def ex33a : Datum :=
  { id := "lahiri1998_ex33a"
    source := ⟨"lahiri-1998", "(33a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "kisiike bhii aane-ke baad raam ghar calaa gayaa"
    glossedTokens := [("kisiike bhii", "anyone's"), ("aane-ke baad", "coming after"), ("raam", "Ram"), ("ghar", "home"), ("calaa gayaa", "went")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("npi", "kisiike bhii"), ("environment", "after-clause")] }

def ex34a : Datum :=
  { id := "lahiri1998_ex34a"
    source := ⟨"lahiri-1998", "(34a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "tumheN koii bhii kitaab pasand aayii kyaa?"
    glossedTokens := [("tumheN", "you"), ("koii bhii", "any"), ("kitaab", "book"), ("pasand aayii", "like"), ("kyaa", "Q")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "koii bhii"), ("environment", "question")] }

def ex41a : Datum :=
  { id := "lahiri1998_ex41a"
    source := ⟨"lahiri-1998", "(41a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "koi bhii aadmii nahiiN aayaa"
    glossedTokens := [("koi bhii", "any"), ("aadmii", "man"), ("nahiiN", "not"), ("aayaa", "came")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "koi bhii"), ("environment", "negation (subject NPI)")] }

def ex35a : Datum :=
  { id := "lahiri1998_ex35a"
    source := ⟨"lahiri-1998", "(35a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "koii bhii aadmii is mez-ko uThaa letaa hai"
    glossedTokens := [("koii bhii", "any"), ("aadmii", "man"), ("is mez-ko", "this table"), ("uThaa letaa hai", "lifts")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "koii bhii"), ("environment", "generic")] }

def ex35b : Datum :=
  { id := "lahiri1998_ex35b"
    source := ⟨"lahiri-1998", "(35b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "koii bhii ulluu cuuhoN-kaa Sikaar karta hai"
    glossedTokens := [("koii bhii", "any"), ("ulluu", "owl"), ("cuuhoN-kaa", "mice"), ("Sikaar karta hai", "hunts")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "koii bhii"), ("environment", "generic")] }

def ex35d : Datum :=
  { id := "lahiri1998_ex35d"
    source := ⟨"lahiri-1998", "(35d)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "ek bhii cingaarii ghar-ko jalaa detii hai"
    glossedTokens := [("ek", "one"), ("bhii", "even"), ("cingaarii", "spark"), ("ghar-ko", "house"), ("jalaa detii hai", "burns")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "ek bhii"), ("environment", "generic")] }

def ex35e : Datum :=
  { id := "lahiri1998_ex35e"
    source := ⟨"lahiri-1998", "(35e)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "zaraa bhii zahar khaane-ko bigaaR detii hai"
    glossedTokens := [("zaraa", "a little"), ("bhii", "even"), ("zahar", "poison"), ("khaane-ko", "food"), ("bigaaR detii hai", "spoils")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "zaraa bhii"), ("environment", "generic")] }

def ex36a : Datum :=
  { id := "lahiri1998_ex36a"
    source := ⟨"lahiri-1998", "(36a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "ek bhii aadmii is mez-ko uThaa saktaa hai"
    glossedTokens := [("ek", "one"), ("bhii", "even"), ("aadmii", "man"), ("is mez-ko", "this table"), ("uThaa", "lift"), ("saktaa hai", "can")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "ek bhii"), ("environment", "possibility modal")] }

def ex36b : Datum :=
  { id := "lahiri1998_ex36b"
    source := ⟨"lahiri-1998", "(36b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "koii bhii aadmii is mez-ko uThaa saktaa hai"
    glossedTokens := [("koii bhii", "any"), ("aadmii", "man"), ("is mez-ko", "this table"), ("uThaa", "lift"), ("saktaa hai", "can")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "koii bhii"), ("environment", "possibility modal")] }

def ex36c : Datum :=
  { id := "lahiri1998_ex36c"
    source := ⟨"lahiri-1998", "(36c)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "tum kabhii bhii ghar jaa sakte ho"
    glossedTokens := [("tum", "you"), ("kabhii bhii", "anytime"), ("ghar", "home"), ("jaa", "go"), ("sakte ho", "may")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "kabhii bhii"), ("environment", "possibility modal")] }

def ex36d : Datum :=
  { id := "lahiri1998_ex36d"
    source := ⟨"lahiri-1998", "(36d)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "kisii-ko bhii ghar jaanaa caahiye"
    glossedTokens := [("kisii-ko bhii", "anyone"), ("ghar", "home"), ("jaanaa", "go"), ("caahiye", "must")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("npi", "kisii-ko bhii"), ("environment", "necessity modal")] }

def ex36e : Datum :=
  { id := "lahiri1998_ex36e"
    source := ⟨"lahiri-1998", "(36e)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "ek bhii aadmii-ko ghar jaanaa caahiye"
    glossedTokens := [("ek", "one"), ("bhii", "even"), ("aadmii-ko", "man"), ("ghar", "home"), ("jaanaa", "go"), ("caahiye", "must")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("npi", "ek bhii"), ("environment", "necessity modal")] }

def ex37a : Datum :=
  { id := "lahiri1998_ex37a"
    source := ⟨"lahiri-1998", "(37a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "kal raam koii bhii mez uThaa sakaa"
    glossedTokens := [("kal", "yesterday"), ("raam", "Ram"), ("koii bhii", "any"), ("mez", "table"), ("uThaa sakaa", "lift could")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "koii bhii"), ("environment", "episodic possibility modal")] }

def ex38a : Datum :=
  { id := "lahiri1998_ex38a"
    source := ⟨"lahiri-1998", "(38a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "ek bhii aadmii is mez-ko uThaa legaa"
    glossedTokens := [("ek bhii", "one even"), ("aadmii", "man"), ("is", "this"), ("mez-ko", "table"), ("uThaa legaa", "lift will")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "ek bhii"), ("environment", "generic future")] }

def ex38e : Datum :=
  { id := "lahiri1998_ex38e"
    source := ⟨"lahiri-1998", "(38e)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "kal tiin bajee koii bhii aadmii is mez-ko uThaa legaa"
    glossedTokens := [("kal", "tomorrow"), ("tiin bajee", "3 o'clock"), ("koii bhii", "any"), ("aadmii", "man"), ("is", "this"), ("mez-ko", "table"), ("uThaa legaa", "lift will")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "koii bhii"), ("environment", "episodic future")] }

def ex39a : Datum :=
  { id := "lahiri1998_ex39a"
    source := ⟨"lahiri-1998", "(39a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "kuchh bhii khaa lo"
    glossedTokens := [("kuchh bhii", "anything"), ("khaa lo", "eat")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "kuchh bhii"), ("environment", "imperative")] }

def ex39b : Datum :=
  { id := "lahiri1998_ex39b"
    source := ⟨"lahiri-1998", "(39b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "koii bhii seb uThaa lo"
    glossedTokens := [("koii bhii", "any"), ("seb", "apple"), ("uThaa lo", "pick")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "koii bhii"), ("environment", "imperative")] }

def ex40a : Datum :=
  { id := "lahiri1998_ex40a"
    source := ⟨"lahiri-1998", "(40a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "zaraa bhii khaa lo"
    glossedTokens := [("zaraa", "a little"), ("bhii", "even"), ("khaa lo", "eat")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "zaraa bhii"), ("environment", "imperative")] }

def ex40b : Datum :=
  { id := "lahiri1998_ex40b"
    source := ⟨"lahiri-1998", "(40b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "ek bhii seb uThaa to"
    glossedTokens := [("ek", "one"), ("bhii", "even"), ("seb", "apple"), ("uThaa to", "pick")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "ek bhii"), ("environment", "imperative")] }

def ex100a : Datum :=
  { id := "lahiri1998_ex100a"
    source := ⟨"lahiri-1998", "(100a)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "koii bhii tiin log is mez-ko uThaa sakte haiN"
    glossedTokens := [("koii bhii", "any"), ("tiin", "three"), ("log", "people"), ("is mez-ko", "this table"), ("uThaa", "lift"), ("sakte haiN", "can")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "koii bhii"), ("environment", "generic, with numeral")] }

def ex100b : Datum :=
  { id := "lahiri1998_ex100b"
    source := ⟨"lahiri-1998", "(100b)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "ek bhii tiin log is mez-ko uThaa sakte haiN"
    glossedTokens := [("ek", "one"), ("bhii", "even"), ("tiin", "three"), ("log", "people"), ("is mez-ko", "this table"), ("uThaa", "lift"), ("sakte haiN", "can")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("npi", "ek bhii"), ("environment", "generic, with numeral")] }

def all : List Datum := [ex6a, ex6b, ex6c, ex6d, ex7a, ex7b, ex8a, ex8b, ex9a, ex9b, ex10a, ex10c, ex11a, ex12a, ex29a, ex29b, ex29c, ex29d, ex31a, ex31b, ex32a, ex33a, ex34a, ex41a, ex35a, ex35b, ex35d, ex35e, ex36a, ex36b, ex36c, ex36d, ex36e, ex37a, ex38a, ex38e, ex39a, ex39b, ex40a, ex40b, ex100a, ex100b]

end Lahiri1998.Examples
