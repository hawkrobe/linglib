module

public import Linglib.Data.Examples.Schema

/-!
# `Mizuno2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Mizuno2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Mizuno2024.Examples`.
-/

@[expose] public section

namespace Mizuno2024.Examples

def en1a : Datum :=
  { id := "mizuno2024_en1a"
    source := ⟨"mizuno-2024", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You're right. If Jones had taken arsenic last night, he would show those symptoms which he is now showing."
    glossedTokens := []
    context := "Jones is in the ER with poisoning symptoms; the team is figuring out which chemical. The boss says he must have taken arsenic. A member responds with (1a), and the follow-up (1b) 'So, it looks like he did take arsenic' is felicitous — an Anderson conditional arguing FOR the truth of its antecedent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "x-marking")] }

def en2 : Datum :=
  { id := "mizuno2024_en2"
    source := ⟨"mizuno-2024", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Jones took arsenic, he shows just exactly those symptoms which he does in fact show."
    glossedTokens := []
    context := "Same scenario as (1). The O-marked (simple-past indicative / present) counterpart of (1a)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "o-marking")] }

def ja3 : Datum :=
  { id := "mizuno2024_ja3"
    source := ⟨"mizuno-2024", "(3)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-ga ima kono siai-no naka-ni ir-eba, syoohai-wa mada wakar-ana-katta daroo."
    glossedTokens := [("John-ga", "John-NOM"), ("ima", "now"), ("kono", "this"), ("siai-no", "game-GEN"), ("naka-ni", "inside-LOC"), ("ir-eba", "be-COND"), ("syoohai-wa", "outcome-TOP"), ("mada", "yet"), ("wakar-ana-katta", "be.clear-NEG-PAST"), ("daroo", "MOD")]
    context := "John, an ace player, has recently left the team for better pay. The team weakens considerably after losing their mainstay, and their defeat in today's game is already certain during the first half. A fan who is currently watching the game says the following."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "fake-past"), ("x_exponent", "-ta")] }

def ja4a : Datum :=
  { id := "mizuno2024_ja4a"
    source := ⟨"mizuno-2024", "(4a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Tasikani, Jones-si-ga sakuya hiso-o nom-eba, kare-ga ima mise-tei-ru syoozyoo-to mattaku onazi syoozyoo-o ima mise-ru hazuda."
    glossedTokens := [("Tasikani", "you're.right"), ("Jones-si-ga", "Jones-Mr.-NOM"), ("sakuya", "last.night"), ("hiso-o", "arsenic-ACC"), ("nom-eba", "drink-COND"), ("kare-ga", "he-NOM"), ("ima", "now"), ("mise-tei-ru", "show-ASP-NPST"), ("syoozyoo-to", "symptom-as"), ("mattaku", "exactly"), ("onazi", "same"), ("syoozyoo-o", "symptom-ACC"), ("ima", "now"), ("mise-ru", "show-NPST"), ("hazuda", "MOD")]
    context := "Uttered in the context in (1) — the Anderson scenario."
    judgment := .acceptable
    alternatives := [("Tasikani, Jones-si-ga sakuya hiso-o nom-eba, kare-ga ima mise-tei-ru syoozyoo-to mattaku onazi syoozyoo-o ima mise-ta hazuda.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "o-marking")] }

def ja7a : Datum :=
  { id := "mizuno2024_ja7a"
    source := ⟨"mizuno-2024", "(7a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Tasikani, Jones-ga ototoi Manila-o syuppatusu-reba, kare-no zissai-no nyuukoku geeto-to mattaku onazi geeto-o, kinoo-no tuuka zikoku-to mattaku onazi zikoku-ni tuukas-uru hazuda."
    glossedTokens := [("Tasikani", "you're.right"), ("Jones-ga", "Jones-NOM"), ("ototoi", "two.days.ago"), ("Manila-o", "Manila-ACC"), ("syuppatusu-reba", "leave-COND"), ("kare-no", "he-GEN"), ("zissai-no", "actual-GEN"), ("nyuukoku.geeto-to", "immigration.gate-as"), ("mattaku", "exactly"), ("onazi", "same"), ("geeto-o", "gate-ACC"), ("kinoo-no", "yesterday-GEN"), ("tuuka.zikoku-to", "passage.time-as"), ("mattaku", "exactly"), ("onazi", "same"), ("zikoku-ni", "time-at"), ("tuukas-uru", "pass-NPST"), ("hazuda", "MOD")]
    context := "Jones is a fugitive who reportedly entered Korea via Incheon yesterday; the team infers the country he flew from. The consequent event lies overtly in the past (adverbial kinoo 'yesterday'), yet Non-Past is still required."
    judgment := .acceptable
    alternatives := [("Tasikani, Jones-ga ototoi Manila-o syuppatusu-reba, ... kinoo-no tuuka zikoku-to mattaku onazi zikoku-ni tuukas-ita hazuda.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "o-marking"), ("hp_type", "radical")] }

def ma13a : Datum :=
  { id := "mizuno2024_ma13a"
    source := ⟨"mizuno-2024", "(13a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai shiji chuxian de zheyangde zhengzhuang."
    glossedTokens := [("Ruguo", "if"), ("Jones", "Jones"), ("zuotian", "yesterday"), ("he", "drink"), ("le", "PERF"), ("pishuang", "arsenic"), ("jiu", "then"), ("hui", "MOD"), ("chuxian", "show"), ("ta", "he"), ("xianzai", "now"), ("shiji", "actually"), ("chuxian", "show"), ("de", "REL"), ("zheyangde", "such"), ("zhengzhuang", "symptoms")]
    context := "Uttered in the context in (1) — the Anderson scenario."
    judgment := .acceptable
    alternatives := [("Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai shiji chuxian de zheyangde zhengzhuang le.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "o-marking")] }

def en8 : Datum :=
  { id := "mizuno2024_en8"
    source := ⟨"mizuno-2024", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John came tomorrow, the party would be fun, but he probably won't come tomorrow, I think."
    glossedTokens := []
    context := "Future Less Vivid conditional with an unlikeliness follow-up."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "flv"), ("strategy", "x-marking"), ("flv_xmarking", "available")] }

def ja9 : Datum :=
  { id := "mizuno2024_ja9"
    source := ⟨"mizuno-2024", "(9)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-ga asita kur-eba, paatii-wa totemo moriagar-u daroo, kedo tabun kare-wa asita ko-na-i to omou."
    glossedTokens := [("John-ga", "John-NOM"), ("asita", "tomorrow"), ("kur-eba", "come-COND"), ("paatii-wa", "party-TOP"), ("totemo", "very"), ("moriagar-u", "be.fun-NPST"), ("daroo", "MOD"), ("kedo", "but"), ("tabun", "probably"), ("kare-wa", "he-TOP"), ("asita", "tomorrow"), ("ko-na-i", "come-NEG-NPST"), ("to", "COMP"), ("omou", "think")]
    context := "Future Less Vivid conditional with an unlikeliness follow-up."
    judgment := .acceptable
    alternatives := [("John-ga asita kur-eba, paatii-wa totemo moriagat-ta daroo, #kedo tabun kare-wa asita ko-na-i to omou.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "flv"), ("strategy", "o-marking"), ("flv_xmarking", "unavailable")] }

def ma11 : Datum :=
  { id := "mizuno2024_ma11"
    source := ⟨"mizuno-2024", "(11)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ruguo mingtian John lai, paidui de qifen jiu neng huoyue qilai, danshi wo juede ta mingtian bu hui lai."
    glossedTokens := [("Ruguo", "if"), ("mingtian", "tomorrow"), ("John", "John"), ("lai", "come"), ("paidui", "party"), ("de", "GEN"), ("qifen", "atmosphere"), ("jiu", "then"), ("neng", "MOD"), ("huoyue", "be.lively"), ("qilai", "get"), ("danshi", "but"), ("wo", "I"), ("juede", "think"), ("ta", "he"), ("mingtian", "tomorrow"), ("bu", "not"), ("hui", "will"), ("lai", "come")]
    context := "Future Less Vivid conditional with an unlikeliness follow-up."
    judgment := .acceptable
    alternatives := [("Ruguo mingtian John lai, paidui de qifen jiu neng huoyue qilai le, #danshi wo juede ta mingtian bu hui lai.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "flv"), ("strategy", "o-marking"), ("flv_xmarking", "unavailable")] }

def all : List Datum := [en1a, en2, ja3, ja4a, ja7a, ma13a, en8, ja9, ma11]

end Mizuno2024.Examples
