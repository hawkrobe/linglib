import Linglib.Data.Examples.Schema

/-!
# `Mizuno2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Mizuno2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Mizuno2024.Examples`.
-/

namespace Mizuno2024.Examples

open Data.Examples

def en1a : LinguisticExample :=
  { id := "mizuno2024_en1a"
    source := ⟨"mizuno-2024", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You're right. If Jones had taken arsenic last night, he would show those symptoms which he is now showing."
    discourseSegments := []
    glossedTokens := []
    translation := "You're right. If Jones had taken arsenic last night, he would show those symptoms which he is now showing."
    context := "Jones is in the ER with poisoning symptoms; the team is figuring out which chemical. The boss says he must have taken arsenic. A member responds with (1a), and the follow-up (1b) 'So, it looks like he did take arsenic' is felicitous — an Anderson conditional arguing FOR the truth of its antecedent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "x-marking")]
    comment := "Mizuno's adaptation of Anderson's (1951) original ('If Jones had taken arsenic, he would have shown just exactly those symptoms which he does in fact show.'). English X-marks: past-perfect antecedent, 'would' consequent describing the observed fact."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en2 : LinguisticExample :=
  { id := "mizuno2024_en2"
    source := ⟨"mizuno-2024", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Jones took arsenic, he shows just exactly those symptoms which he does in fact show."
    discourseSegments := []
    glossedTokens := []
    translation := "If Jones took arsenic, he shows just exactly those symptoms which he does in fact show."
    context := "Same scenario as (1). The O-marked (simple-past indicative / present) counterpart of (1a)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "o-marking")]
    comment := "Infelicitous: the non-expanded domain D makes the consequent (an observed fact) hold everywhere, so the conditional is trivially true (Stalnaker 1975, von Fintel 1999)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ja4a : LinguisticExample :=
  { id := "mizuno2024_ja4a"
    source := ⟨"mizuno-2024", "(4a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Tasikani, Jones-si-ga sakuya hiso-o nom-eba, kare-ga ima mise-tei-ru syoozyoo-to mattaku onazi syoozyoo-o ima mise-ru hazuda."
    discourseSegments := []
    glossedTokens := [("Tasikani", "you're.right"), ("Jones-si-ga", "Jones-Mr.-NOM"), ("sakuya", "last.night"), ("hiso-o", "arsenic-ACC"), ("nom-eba", "drink-COND"), ("kare-ga", "he-NOM"), ("ima", "now"), ("mise-tei-ru", "show-ASP-NPST"), ("syoozyoo-to", "symptom-as"), ("mattaku", "exactly"), ("onazi", "same"), ("syoozyoo-o", "symptom-ACC"), ("ima", "now"), ("mise-ru", "show-NPST"), ("hazuda", "MOD")]
    translation := "If Jones had taken arsenic last night, he would show exactly the same symptoms as he is now showing."
    context := "Uttered in the context in (1) — the Anderson scenario."
    judgment := .acceptable
    alternatives := [("Tasikani, Jones-si-ga sakuya hiso-o nom-eba, kare-ga ima mise-tei-ru syoozyoo-to mattaku onazi syoozyoo-o ima mise-ta hazuda.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "o-marking")]
    comment := "Japanese O-marks: Non-Past -ru triggers a Historical-Present shift expanding the domain. The X-marked alternative (Past -ta) forces a counterfactual reading, contradicting the Anderson follow-up (4b), so it is infelicitous."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ja7a : LinguisticExample :=
  { id := "mizuno2024_ja7a"
    source := ⟨"mizuno-2024", "(7a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Tasikani, Jones-ga ototoi Manila-o syuppatusu-reba, kare-no zissai-no nyuukoku geeto-to mattaku onazi geeto-o, kinoo-no tuuka zikoku-to mattaku onazi zikoku-ni tuukas-uru hazuda."
    discourseSegments := []
    glossedTokens := [("Tasikani", "you're.right"), ("Jones-ga", "Jones-NOM"), ("ototoi", "two.days.ago"), ("Manila-o", "Manila-ACC"), ("syuppatusu-reba", "leave-COND"), ("kare-no", "he-GEN"), ("zissai-no", "actual-GEN"), ("nyuukoku.geeto-to", "immigration.gate-as"), ("mattaku", "exactly"), ("onazi", "same"), ("geeto-o", "gate-ACC"), ("kinoo-no", "yesterday-GEN"), ("tuuka.zikoku-to", "passage.time-as"), ("mattaku", "exactly"), ("onazi", "same"), ("zikoku-ni", "time-at"), ("tuukas-uru", "pass-NPST"), ("hazuda", "MOD")]
    translation := "If Jones had left Manila two days ago, he would have passed exactly the same immigration gate that he actually passed yesterday, exactly at the same time as he actually did it."
    context := "Jones is a fugitive who reportedly entered Korea via Incheon yesterday; the team infers the country he flew from. The consequent event lies overtly in the past (adverbial kinoo 'yesterday'), yet Non-Past is still required."
    judgment := .acceptable
    alternatives := [("Tasikani, Jones-ga ototoi Manila-o syuppatusu-reba, ... kinoo-no tuuka zikoku-to mattaku onazi zikoku-ni tuukas-ita hazuda.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "o-marking"), ("hp_type", "radical")]
    comment := "Radical-HP case: consequent event overtly past, yet Non-Past required. Temporal indexicals ototoi and kinoo evaluate against the utterance time (theta = origin), paralleling Schlenker 2004's Historical Present."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ma13a : LinguisticExample :=
  { id := "mizuno2024_ma13a"
    source := ⟨"mizuno-2024", "(13a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai shiji chuxian de zheyangde zhengzhuang."
    discourseSegments := []
    glossedTokens := [("Ruguo", "if"), ("Jones", "Jones"), ("zuotian", "yesterday"), ("he", "drink"), ("le", "PERF"), ("pishuang", "arsenic"), ("jiu", "then"), ("hui", "MOD"), ("chuxian", "show"), ("ta", "he"), ("xianzai", "now"), ("shiji", "actually"), ("chuxian", "show"), ("de", "REL"), ("zheyangde", "such"), ("zhengzhuang", "symptoms")]
    translation := "If Jones drank arsenic yesterday, he would show exactly such symptoms as he actually shows now."
    context := "Uttered in the context in (1) — the Anderson scenario."
    judgment := .acceptable
    alternatives := [("Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai shiji chuxian de zheyangde zhengzhuang le.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "o-marking")]
    comment := "Mandarin O-marks (no consequent-final le); the conditional marker is ruguo. The X-marked alternative (consequent-final perfective le) induces strong counterfactuality, like Japanese Past -ta, so it is infelicitous for the Anderson reading."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def en8 : LinguisticExample :=
  { id := "mizuno2024_en8"
    source := ⟨"mizuno-2024", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John came tomorrow, the party would be fun, but he probably won't come tomorrow, I think."
    discourseSegments := ["If John came tomorrow, the party would be fun,", "but he probably won't come tomorrow, I think."]
    glossedTokens := []
    translation := "If John came tomorrow, the party would be fun, but he probably won't come tomorrow, I think."
    context := "Future Less Vivid conditional with an unlikeliness follow-up."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "flv"), ("strategy", "x-marking"), ("flv_xmarking", "available")]
    comment := "English X-marking is available for FLV: the X-marked conditional (8a) takes an unlikeliness follow-up (8b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ja9 : LinguisticExample :=
  { id := "mizuno2024_ja9"
    source := ⟨"mizuno-2024", "(9)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-ga asita kur-eba, paatii-wa totemo moriagar-u daroo, kedo tabun kare-wa asita ko-na-i to omou."
    discourseSegments := []
    glossedTokens := [("John-ga", "John-NOM"), ("asita", "tomorrow"), ("kur-eba", "come-COND"), ("paatii-wa", "party-TOP"), ("totemo", "very"), ("moriagar-u", "be.fun-NPST"), ("daroo", "MOD"), ("kedo", "but"), ("tabun", "probably"), ("kare-wa", "he-TOP"), ("asita", "tomorrow"), ("ko-na-i", "come-NEG-NPST"), ("to", "COMP"), ("omou", "think")]
    translation := "If John came tomorrow, the party would be fun, but probably he won't come tomorrow, I think."
    context := "Future Less Vivid conditional with an unlikeliness follow-up."
    judgment := .acceptable
    alternatives := [("John-ga asita kur-eba, paatii-wa totemo moriagat-ta daroo, #kedo tabun kare-wa asita ko-na-i to omou.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "flv"), ("strategy", "o-marking"), ("flv_xmarking", "unavailable")]
    comment := "Japanese FLV must O-mark (Non-Past -u, ex 9). The X-marked variant (Past -ta, ex 10) induces strong counterfactuality, making the unlikeliness follow-up contradictory."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ma11 : LinguisticExample :=
  { id := "mizuno2024_ma11"
    source := ⟨"mizuno-2024", "(11)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ruguo mingtian John lai, paidui de qifen jiu neng huoyue qilai, danshi wo juede ta mingtian bu hui lai."
    discourseSegments := []
    glossedTokens := [("Ruguo", "if"), ("mingtian", "tomorrow"), ("John", "John"), ("lai", "come"), ("paidui", "party"), ("de", "GEN"), ("qifen", "atmosphere"), ("jiu", "then"), ("neng", "MOD"), ("huoyue", "be.lively"), ("qilai", "get"), ("danshi", "but"), ("wo", "I"), ("juede", "think"), ("ta", "he"), ("mingtian", "tomorrow"), ("bu", "not"), ("hui", "will"), ("lai", "come")]
    translation := "If John comes tomorrow, the party atmosphere would get lively, but I think he won't come tomorrow."
    context := "Future Less Vivid conditional with an unlikeliness follow-up."
    judgment := .acceptable
    alternatives := [("Ruguo mingtian John lai, paidui de qifen jiu neng huoyue qilai le, #danshi wo juede ta mingtian bu hui lai.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "flv"), ("strategy", "o-marking"), ("flv_xmarking", "unavailable")]
    comment := "Mandarin FLV must O-mark (no le, ex 11). The X-marked variant (perfective le, ex 12) induces strong counterfactuality, making the unlikeliness follow-up contradictory."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [en1a, en2, ja4a, ja7a, ma13a, en8, ja9, ma11]

end Mizuno2024.Examples
