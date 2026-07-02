import Linglib.Data.Complementation.Schema

/-!
# Noonan2007 — complement-taking-predicate sample (generated)
[noonan-2007]

Auto-generated from `Linglib/Data/Complementation/Noonan2007.json` by
`scripts/gen_complementation.py`. **Do not edit by hand** — edit the JSON and
re-run the generator. The 36 CTP rows of [noonan-2007]'s 7-language
sample: per-row CTP class, attested complement types, equi-deletion, and
negative raising.
-/

namespace Data.Complementation.Noonan2007

def english_say : Datum :=
  ⟨"say", .utterance, [.indicative, .paratactic], false, false⟩

def english_tell : Datum :=
  ⟨"tell", .utterance, [.indicative, .infinitive], false, false⟩

def english_believe : Datum :=
  ⟨"believe", .propAttitude, [.indicative], false, true⟩

def english_think : Datum :=
  ⟨"think", .propAttitude, [.indicative], false, true⟩

def english_regret : Datum :=
  ⟨"regret", .commentative, [.indicative, .nominalized], false, false⟩

def english_know : Datum :=
  ⟨"know", .knowledge, [.indicative], false, false⟩

def english_realize : Datum :=
  ⟨"realize", .knowledge, [.indicative], false, false⟩

def english_see : Datum :=
  ⟨"see", .perception, [.indicative, .infinitive, .participle], false, false⟩

def english_want : Datum :=
  ⟨"want", .desiderative, [.infinitive], true, true⟩

def english_hope : Datum :=
  ⟨"hope", .desiderative, [.indicative, .infinitive], true, true⟩

def english_wish : Datum :=
  ⟨"wish", .desiderative, [.indicative, .subjunctive], false, false⟩

def english_make : Datum :=
  ⟨"make", .manipulative, [.infinitive, .paratactic], false, false⟩

def english_persuade : Datum :=
  ⟨"persuade", .manipulative, [.infinitive], true, false⟩

def english_manage : Datum :=
  ⟨"manage", .achievement, [.infinitive], true, false⟩

def english_stop : Datum :=
  ⟨"stop", .phasal, [.nominalized], true, false⟩

def english_start : Datum :=
  ⟨"start", .phasal, [.nominalized, .infinitive], true, false⟩

def english_continue : Datum :=
  ⟨"continue", .phasal, [.nominalized, .infinitive], true, false⟩

/-- The `english` rows of the sample (17 rows). -/
def english : List Datum :=
  [english_say, english_tell, english_believe, english_think, english_regret, english_know,
   english_realize, english_see, english_want, english_hope, english_wish, english_make,
   english_persuade, english_manage, english_stop, english_start, english_continue]

def latin_dicere : Datum :=
  ⟨"dicere", .utterance, [.indicative, .infinitive], false, false⟩

def latin_credere : Datum :=
  ⟨"credere", .propAttitude, [.infinitive], false, false⟩

def latin_velle : Datum :=
  ⟨"velle", .desiderative, [.subjunctive, .infinitive], true, false⟩

def latin_iubere : Datum :=
  ⟨"iubere", .manipulative, [.subjunctive, .infinitive], true, false⟩

/-- The `latin` rows of the sample (4 rows). -/
def latin : List Datum :=
  [latin_dicere, latin_credere, latin_velle, latin_iubere]

def turkish_sanmak : Datum :=
  ⟨"sanmak", .propAttitude, [.nominalized, .indicative], false, false⟩

def turkish_istemek : Datum :=
  ⟨"istemek", .desiderative, [.nominalized, .infinitive], true, false⟩

def turkish_baslamak : Datum :=
  ⟨"başlamak", .phasal, [.nominalized, .infinitive], true, false⟩

/-- The `turkish` rows of the sample (3 rows). -/
def turkish : List Datum :=
  [turkish_sanmak, turkish_istemek, turkish_baslamak]

def irish_abair : Datum :=
  ⟨"abair", .utterance, [.indicative, .subjunctive], false, false⟩

def irish_ceap : Datum :=
  ⟨"ceap", .propAttitude, [.indicative], false, false⟩

/-- The `irish` rows of the sample (2 rows). -/
def irish : List Datum :=
  [irish_abair, irish_ceap]

def persian_goftan : Datum :=
  ⟨"goftan", .utterance, [.indicative, .subjunctive], false, false⟩

def persian_khastan : Datum :=
  ⟨"khastan", .desiderative, [.subjunctive], false, false⟩

def persian_danestan : Datum :=
  ⟨"danestan", .knowledge, [.indicative], false, false⟩

/-- The `persian` rows of the sample (3 rows). -/
def persian : List Datum :=
  [persian_goftan, persian_khastan, persian_danestan]

def hindi_urdu_sochna : Datum :=
  ⟨"sochna", .propAttitude, [.indicative], false, false⟩

def hindi_urdu_jaanna : Datum :=
  ⟨"jaanna", .knowledge, [.indicative], false, false⟩

def hindi_urdu_chaahna : Datum :=
  ⟨"chaahna", .desiderative, [.subjunctive], false, false⟩

/-- The `hindiUrdu` rows of the sample (3 rows). -/
def hindiUrdu : List Datum :=
  [hindi_urdu_sochna, hindi_urdu_jaanna, hindi_urdu_chaahna]

def japanese_omou : Datum :=
  ⟨"omou", .propAttitude, [.indicative], false, false⟩

def japanese_shiru : Datum :=
  ⟨"shiru", .knowledge, [.indicative], false, false⟩

def japanese_hoshii : Datum :=
  ⟨"hoshii", .desiderative, [.nominalized], true, false⟩

def japanese_hajimeru : Datum :=
  ⟨"hajimeru", .phasal, [.nominalized, .infinitive], true, false⟩

/-- The `japanese` rows of the sample (4 rows). -/
def japanese : List Datum :=
  [japanese_omou, japanese_shiru, japanese_hoshii, japanese_hajimeru]

/-- The 7-language sample, one row list per language. -/
def sample : List (List Datum) :=
  [english, latin, turkish, irish, persian, hindiUrdu, japanese]

/-- All 36 rows of the sample, pooled. -/
def all : List Datum := sample.flatten

end Data.Complementation.Noonan2007
