module

public import Linglib.Data.Forms.Schema

/-!
# `Stojkovic2026` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Stojkovic2026.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Stojkovic2026.Forms`.
-/

@[expose] public section

namespace Stojkovic2026.Forms

open Data.Forms

def belarusian_plain_lform : Form :=
  { id := "stojkovic2026_belarusian_plain_lform"
    languageId := "bela1254"
    parameterId := "abolish"
    form := "kas-av-a-l-a"
    segments := ["kas", "av", "a", "l", "a"]
    comment := "orthographic <av>; the paper takes the vowel to be /o/ reduced to [a]"
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Belarusian"), ("Root", "plain"), ("Cell", "l-form.f.sg"), ("Verbalizer", "orthographic")] }

def belarusian_plain_prs : Form :=
  { id := "stojkovic2026_belarusian_plain_prs"
    languageId := "bela1254"
    parameterId := "abolish"
    form := "kas-u-je-ʃ"
    segments := ["kas", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Belarusian"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def bos_cro_mon_ser_plain_lform : Form :=
  { id := "stojkovic2026_bos_cro_mon_ser_plain_lform"
    languageId := "sout1528"
    parameterId := "care_for"
    form := "ɲeg-ov-a-l-a"
    segments := ["ɲeg", "ov", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Bos/Cro/Mon/Ser"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def bos_cro_mon_ser_plain_prs : Form :=
  { id := "stojkovic2026_bos_cro_mon_ser_plain_prs"
    languageId := "sout1528"
    parameterId := "care_for"
    form := "ɲeg-u-je-ʃ"
    segments := ["ɲeg", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Bos/Cro/Mon/Ser"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def bulgarian_plain_lform : Form :=
  { id := "stojkovic2026_bulgarian_plain_lform"
    languageId := "bulg1262"
    parameterId := "kiss"
    form := "tsel-uv-a-l-a"
    segments := ["tsel", "uv", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Bulgarian"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def bulgarian_plain_prs : Form :=
  { id := "stojkovic2026_bulgarian_plain_prs"
    languageId := "bulg1262"
    parameterId := "kiss"
    form := "tsel-uv-a-ʃ"
    segments := ["tsel", "uv", "a", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Bulgarian"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def bunyev_ac_plain_lform : Form :=
  { id := "stojkovic2026_bunyev_ac_plain_lform"
    languageId := "sout1528"
    parameterId := "swear_at_god"
    form := "bog-ov-a-l-a"
    segments := ["bog", "ov", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Bunyev(ac)"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def bunyev_ac_plain_prs : Form :=
  { id := "stojkovic2026_bunyev_ac_plain_prs"
    languageId := "sout1528"
    parameterId := "swear_at_god"
    form := "bog-u-je-ʃ"
    segments := ["bog", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Bunyev(ac)"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def carpathian_rusyn_plain_lform : Form :=
  { id := "stojkovic2026_carpathian_rusyn_plain_lform"
    languageId := "rusy1239"
    parameterId := "talk"
    form := "bisid-ov-a-l-a"
    segments := ["bisid", "ov", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Carpathian Rusyn"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def carpathian_rusyn_plain_prs : Form :=
  { id := "stojkovic2026_carpathian_rusyn_plain_prs"
    languageId := "rusy1239"
    parameterId := "talk"
    form := "bisid-u-je-ʃ"
    segments := ["bisid", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Carpathian Rusyn"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def czech_plain_lform : Form :=
  { id := "stojkovic2026_czech_plain_lform"
    languageId := "czec1258"
    parameterId := "buy"
    form := "kup-ov-a-l-a"
    segments := ["kup", "ov", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Czech"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def czech_plain_prs : Form :=
  { id := "stojkovic2026_czech_plain_prs"
    languageId := "czec1258"
    parameterId := "buy"
    form := "kup-u-je-ʃ"
    segments := ["kup", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Czech"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def kashubian_plain_lform : Form :=
  { id := "stojkovic2026_kashubian_plain_lform"
    languageId := "kash1274"
    parameterId := "get_engaged"
    form := "brutk-ov-a-w-a"
    segments := ["brutk", "ov", "a", "w", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Kashubian"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def kashubian_plain_prs : Form :=
  { id := "stojkovic2026_kashubian_plain_prs"
    languageId := "kash1274"
    parameterId := "get_engaged"
    form := "brutk-u-je-ʃ"
    segments := ["brutk", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Kashubian"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def lemko_rusyn_plain_lform : Form :=
  { id := "stojkovic2026_lemko_rusyn_plain_lform"
    languageId := "rusy1239"
    parameterId := "draw"
    form := "rɨs-uv-a-l-a"
    segments := ["rɨs", "uv", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Lemko Rusyn"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def lemko_rusyn_plain_prs : Form :=
  { id := "stojkovic2026_lemko_rusyn_plain_prs"
    languageId := "rusy1239"
    parameterId := "draw"
    form := "rɨs-u-je-ʃ"
    segments := ["rɨs", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Lemko Rusyn"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def lower_sorbian_plain_lform : Form :=
  { id := "stojkovic2026_lower_sorbian_plain_lform"
    languageId := "lowe1385"
    parameterId := "paint"
    form := "mol-ov-a-w-a"
    segments := ["mol", "ov", "a", "w", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Lower Sorbian"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def lower_sorbian_plain_prs : Form :=
  { id := "stojkovic2026_lower_sorbian_plain_prs"
    languageId := "lowe1385"
    parameterId := "paint"
    form := "mol-u-je-ʃ"
    segments := ["mol", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Lower Sorbian"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def macedonian_plain_lform : Form :=
  { id := "stojkovic2026_macedonian_plain_lform"
    languageId := "mace1250"
    parameterId := "believe"
    form := "ver-uv-a-l-a"
    segments := ["ver", "uv", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Macedonian"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def macedonian_plain_prs : Form :=
  { id := "stojkovic2026_macedonian_plain_prs"
    languageId := "mace1250"
    parameterId := "believe"
    form := "ver-uv-a-ʃ"
    segments := ["ver", "uv", "a", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Macedonian"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def pannonian_rusyn_plain_lform : Form :=
  { id := "stojkovic2026_pannonian_rusyn_plain_lform"
    languageId := "pann1240"
    parameterId := "serve"
    form := "rab-ov-a-l-a"
    segments := ["rab", "ov", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Pannonian Rusyn"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def pannonian_rusyn_plain_prs : Form :=
  { id := "stojkovic2026_pannonian_rusyn_plain_prs"
    languageId := "pann1240"
    parameterId := "serve"
    form := "rab-u-je-ʃ"
    segments := ["rab", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Pannonian Rusyn"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def podlachian_plain_lform : Form :=
  { id := "stojkovic2026_podlachian_plain_lform"
    languageId := "east1426"
    parameterId := "aim"
    form := "tsil-ov-a-w-a"
    segments := ["tsil", "ov", "a", "w", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Podlachian"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def podlachian_plain_prs : Form :=
  { id := "stojkovic2026_podlachian_plain_prs"
    languageId := "east1426"
    parameterId := "aim"
    form := "tsil-u-je-ʃ"
    segments := ["tsil", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Podlachian"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def polish_plain_lform : Form :=
  { id := "stojkovic2026_polish_plain_lform"
    languageId := "poli1260"
    parameterId := "work"
    form := "prats-ov-a-w-a"
    segments := ["prats", "ov", "a", "w", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Polish"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def polish_plain_prs : Form :=
  { id := "stojkovic2026_polish_plain_prs"
    languageId := "poli1260"
    parameterId := "work"
    form := "prats-u-je-ʃ"
    segments := ["prats", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Polish"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def russian_plain_lform : Form :=
  { id := "stojkovic2026_russian_plain_lform"
    languageId := "russ1263"
    parameterId := "complain"
    form := "ʒal-ov-a-l-a-sʲ"
    segments := ["ʒal", "ov", "a", "l", "a", "sʲ"]
    comment := "orthographic form, which the paper uses to infer the quality before vowel reduction"
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Russian"), ("Root", "plain"), ("Cell", "l-form.f.sg"), ("Verbalizer", "orthographic")] }

def russian_plain_prs : Form :=
  { id := "stojkovic2026_russian_plain_prs"
    languageId := "russ1263"
    parameterId := "complain"
    form := "ʒal-u-je-ʃ-sʲ"
    segments := ["ʒal", "u", "je", "ʃ", "sʲ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Russian"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def silesian_plain_lform : Form :=
  { id := "stojkovic2026_silesian_plain_lform"
    languageId := "sile1253"
    parameterId := "darn"
    form := "ɕtop-ov-a-w-a"
    segments := ["ɕtop", "ov", "a", "w", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Silesian"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def silesian_plain_prs : Form :=
  { id := "stojkovic2026_silesian_plain_prs"
    languageId := "sile1253"
    parameterId := "darn"
    form := "ɕtop-u-je-ʃ"
    segments := ["ɕtop", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Silesian"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def slovak_plain_lform : Form :=
  { id := "stojkovic2026_slovak_plain_lform"
    languageId := "slov1269"
    parameterId := "battle"
    form := "boj-ov-a-l-a"
    segments := ["boj", "ov", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Slovak"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def slovak_plain_prs : Form :=
  { id := "stojkovic2026_slovak_plain_prs"
    languageId := "slov1269"
    parameterId := "battle"
    form := "boj-u-je-ʃ"
    segments := ["boj", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Slovak"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def slovenian_plain_lform : Form :=
  { id := "stojkovic2026_slovenian_plain_lform"
    languageId := "slov1268"
    parameterId := "travel"
    form := "pot-ov-a-l-a"
    segments := ["pot", "ov", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Slovenian"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def slovenian_plain_prs : Form :=
  { id := "stojkovic2026_slovenian_plain_prs"
    languageId := "slov1268"
    parameterId := "travel"
    form := "pot-u-je-ʃ"
    segments := ["pot", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Slovenian"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def ukrainian_plain_lform : Form :=
  { id := "stojkovic2026_ukrainian_plain_lform"
    languageId := "ukra1253"
    parameterId := "squeeze"
    form := "stis-uv-a-l-a"
    segments := ["stis", "uv", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Ukrainian"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def ukrainian_plain_prs : Form :=
  { id := "stojkovic2026_ukrainian_plain_prs"
    languageId := "ukra1253"
    parameterId := "squeeze"
    form := "stis-u-jeʃ"
    segments := ["stis", "u", "jeʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Ukrainian"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def upper_sorbian_plain_lform : Form :=
  { id := "stojkovic2026_upper_sorbian_plain_lform"
    languageId := "uppe1395"
    parameterId := "buy"
    form := "kup-ov-a-w-a"
    segments := ["kup", "ov", "a", "w", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Upper Sorbian"), ("Root", "plain"), ("Cell", "l-form.f.sg")] }

def upper_sorbian_plain_prs : Form :=
  { id := "stojkovic2026_upper_sorbian_plain_prs"
    languageId := "uppe1395"
    parameterId := "buy"
    form := "kup-u-je-ʃ"
    segments := ["kup", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 1"⟩
    ]
    columns := [("Variety", "Upper Sorbian"), ("Root", "plain"), ("Cell", "2sg.prs")] }

def belarusian_palatal_lform : Form :=
  { id := "stojkovic2026_belarusian_palatal_lform"
    languageId := "bela1254"
    parameterId := "battle"
    form := "vaj-av-a-l-a"
    segments := ["vaj", "av", "a", "l", "a"]
    comment := "orthographic <av>; the paper takes the vowel to be /o/ reduced to [a]"
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Belarusian"), ("Root", "palatal"), ("Cell", "l-form.f.sg"), ("Verbalizer", "orthographic")] }

def belarusian_palatal_prs : Form :=
  { id := "stojkovic2026_belarusian_palatal_prs"
    languageId := "bela1254"
    parameterId := "battle"
    form := "vaj-u-je-ʃ"
    segments := ["vaj", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Belarusian"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def bunyev_ac_palatal_lform : Form :=
  { id := "stojkovic2026_bunyev_ac_palatal_lform"
    languageId := "sout1528"
    parameterId := "prune"
    form := "katʃ-ov-a-l-a"
    segments := ["katʃ", "ov", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Bunyev(ac)"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def bunyev_ac_palatal_prs : Form :=
  { id := "stojkovic2026_bunyev_ac_palatal_prs"
    languageId := "sout1528"
    parameterId := "prune"
    form := "katʃ-u-je-ʃ"
    segments := ["katʃ", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Bunyev(ac)"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def czech_palatal_lform : Form :=
  { id := "stojkovic2026_czech_palatal_lform"
    languageId := "czec1258"
    parameterId := "whip"
    form := "bitʃ-ov-a-l-a"
    segments := ["bitʃ", "ov", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Czech"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def czech_palatal_prs : Form :=
  { id := "stojkovic2026_czech_palatal_prs"
    languageId := "czec1258"
    parameterId := "whip"
    form := "bitʃ-u-je-ʃ"
    segments := ["bitʃ", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Czech"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def kashubian_palatal_lform : Form :=
  { id := "stojkovic2026_kashubian_palatal_lform"
    languageId := "kash1274"
    parameterId := "date"
    form := "vrəj-ov-a-w-a"
    segments := ["vrəj", "ov", "a", "w", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Kashubian"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def kashubian_palatal_prs : Form :=
  { id := "stojkovic2026_kashubian_palatal_prs"
    languageId := "kash1274"
    parameterId := "date"
    form := "vrəj-u-je-ʃ"
    segments := ["vrəj", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Kashubian"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def lower_sorbian_palatal_lform : Form :=
  { id := "stojkovic2026_lower_sorbian_palatal_lform"
    languageId := "lowe1385"
    parameterId := "wander"
    form := "puɕ-ov-a-w-a"
    segments := ["puɕ", "ov", "a", "w", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Lower Sorbian"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def lower_sorbian_palatal_prs : Form :=
  { id := "stojkovic2026_lower_sorbian_palatal_prs"
    languageId := "lowe1385"
    parameterId := "wander"
    form := "puɕ-u-je-ʃ"
    segments := ["puɕ", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Lower Sorbian"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def pannonian_rusyn_palatal_lform : Form :=
  { id := "stojkovic2026_pannonian_rusyn_palatal_lform"
    languageId := "pann1240"
    parameterId := "reign"
    form := "kraʎ-ov-a-l-a"
    segments := ["kraʎ", "ov", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Pannonian Rusyn"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def pannonian_rusyn_palatal_prs : Form :=
  { id := "stojkovic2026_pannonian_rusyn_palatal_prs"
    languageId := "pann1240"
    parameterId := "reign"
    form := "kraʎ-u-je-ʃ"
    segments := ["kraʎ", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Pannonian Rusyn"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def podlachian_palatal_lform : Form :=
  { id := "stojkovic2026_podlachian_palatal_lform"
    languageId := "east1426"
    parameterId := "grub"
    form := "kartʃ-ov-a-w-a"
    segments := ["kartʃ", "ov", "a", "w", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Podlachian"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def podlachian_palatal_prs : Form :=
  { id := "stojkovic2026_podlachian_palatal_prs"
    languageId := "east1426"
    parameterId := "grub"
    form := "kartʃ-u-je-ʃ"
    segments := ["kartʃ", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Podlachian"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def polish_palatal_lform : Form :=
  { id := "stojkovic2026_polish_palatal_lform"
    languageId := "poli1260"
    parameterId := "accommodate"
    form := "hotel'-ov-a-w-a"
    segments := ["hotel'", "ov", "a", "w", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Polish"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def polish_palatal_prs : Form :=
  { id := "stojkovic2026_polish_palatal_prs"
    languageId := "poli1260"
    parameterId := "accommodate"
    form := "hotel'-u-je-ʃ"
    segments := ["hotel'", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Polish"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def slovak_palatal_lform : Form :=
  { id := "stojkovic2026_slovak_palatal_lform"
    languageId := "slov1269"
    parameterId := "battle"
    form := "boj-ov-a-l-a"
    segments := ["boj", "ov", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Slovak"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def slovak_palatal_prs : Form :=
  { id := "stojkovic2026_slovak_palatal_prs"
    languageId := "slov1269"
    parameterId := "battle"
    form := "boj-u-je-ʃ"
    segments := ["boj", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Slovak"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def silesian_palatal_lform : Form :=
  { id := "stojkovic2026_silesian_palatal_lform"
    languageId := "sile1253"
    parameterId := "whip"
    form := "pajtɕ-ov-a-w-a"
    segments := ["pajtɕ", "ov", "a", "w", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Silesian"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def silesian_palatal_prs : Form :=
  { id := "stojkovic2026_silesian_palatal_prs"
    languageId := "sile1253"
    parameterId := "whip"
    form := "pajtɕ-u-je-ʃ"
    segments := ["pajtɕ", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Silesian"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def upper_sorbian_palatal_lform : Form :=
  { id := "stojkovic2026_upper_sorbian_palatal_lform"
    languageId := "uppe1395"
    parameterId := "translate"
    form := "preloʒ-ov-a-w-a"
    segments := ["preloʒ", "ov", "a", "w", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Upper Sorbian"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def upper_sorbian_palatal_prs : Form :=
  { id := "stojkovic2026_upper_sorbian_palatal_prs"
    languageId := "uppe1395"
    parameterId := "translate"
    form := "preloʒ-u-je-ʃ"
    segments := ["preloʒ", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Upper Sorbian"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def bos_cro_mon_ser_palatal_lform : Form :=
  { id := "stojkovic2026_bos_cro_mon_ser_palatal_lform"
    languageId := "sout1528"
    parameterId := "be_teacher"
    form := "utʃiteʎ-ev-a-l-a"
    segments := ["utʃiteʎ", "ev", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Bos/Cro/Mon/Ser"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def bos_cro_mon_ser_palatal_prs : Form :=
  { id := "stojkovic2026_bos_cro_mon_ser_palatal_prs"
    languageId := "sout1528"
    parameterId := "be_teacher"
    form := "utʃiteʎ-u-je-ʃ"
    segments := ["utʃiteʎ", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Bos/Cro/Mon/Ser"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def carpathian_rusyn_palatal_lform : Form :=
  { id := "stojkovic2026_carpathian_rusyn_palatal_lform"
    languageId := "rusy1239"
    parameterId := "compare"
    form := "stupɲ-ev-a-l-a"
    segments := ["stupɲ", "ev", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Carpathian Rusyn"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def carpathian_rusyn_palatal_prs : Form :=
  { id := "stojkovic2026_carpathian_rusyn_palatal_prs"
    languageId := "rusy1239"
    parameterId := "compare"
    form := "stupɲ-u-je-ʃ"
    segments := ["stupɲ", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Carpathian Rusyn"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def russian_palatal_lform : Form :=
  { id := "stojkovic2026_russian_palatal_lform"
    languageId := "russ1263"
    parameterId := "swindle"
    form := "muxlʲ-ev-a-l-a"
    segments := ["muxlʲ", "ev", "a", "l", "a"]
    comment := "orthographic form, which the paper uses to infer the quality before vowel reduction"
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Russian"), ("Root", "palatal"), ("Cell", "l-form.f.sg"), ("Verbalizer", "orthographic")] }

def russian_palatal_prs : Form :=
  { id := "stojkovic2026_russian_palatal_prs"
    languageId := "russ1263"
    parameterId := "swindle"
    form := "muxlʲ-u-je-ʃ"
    segments := ["muxlʲ", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Russian"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def slovenian_palatal_lform : Form :=
  { id := "stojkovic2026_slovenian_palatal_lform"
    languageId := "slov1268"
    parameterId := "rain"
    form := "deʒ-ev-a-l-a"
    segments := ["deʒ", "ev", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Slovenian"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def slovenian_palatal_prs : Form :=
  { id := "stojkovic2026_slovenian_palatal_prs"
    languageId := "slov1268"
    parameterId := "rain"
    form := "deʒ-u-je-ʃ"
    segments := ["deʒ", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Slovenian"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def bulgarian_palatal_lform : Form :=
  { id := "stojkovic2026_bulgarian_palatal_lform"
    languageId := "bulg1262"
    parameterId := "jitter"
    form := "najeʒ-uv-a-l-a"
    segments := ["najeʒ", "uv", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Bulgarian"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def bulgarian_palatal_prs : Form :=
  { id := "stojkovic2026_bulgarian_palatal_prs"
    languageId := "bulg1262"
    parameterId := "jitter"
    form := "najeʒ-uv-a-ʃ"
    segments := ["najeʒ", "uv", "a", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Bulgarian"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def lemko_rusyn_palatal_lform : Form :=
  { id := "stojkovic2026_lemko_rusyn_palatal_lform"
    languageId := "rusy1239"
    parameterId := "adore"
    form := "oboʒ-uv-a-l-a"
    segments := ["oboʒ", "uv", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Lemko Rusyn"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def lemko_rusyn_palatal_prs : Form :=
  { id := "stojkovic2026_lemko_rusyn_palatal_prs"
    languageId := "rusy1239"
    parameterId := "adore"
    form := "oboʒ-u-je-ʃ"
    segments := ["oboʒ", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Lemko Rusyn"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def macedonian_palatal_lform : Form :=
  { id := "stojkovic2026_macedonian_palatal_lform"
    languageId := "mace1250"
    parameterId := "spend_night"
    form := "noc-uv-a-l-a"
    segments := ["noc", "uv", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Macedonian"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def macedonian_palatal_prs : Form :=
  { id := "stojkovic2026_macedonian_palatal_prs"
    languageId := "mace1250"
    parameterId := "spend_night"
    form := "noc-uv-a-ʃ"
    segments := ["noc", "uv", "a", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Macedonian"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def ukrainian_palatal_lform : Form :=
  { id := "stojkovic2026_ukrainian_palatal_lform"
    languageId := "ukra1253"
    parameterId := "be_late"
    form := "zapizɲ-uv-a-l-a"
    segments := ["zapizɲ", "uv", "a", "l", "a"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Ukrainian"), ("Root", "palatal"), ("Cell", "l-form.f.sg")] }

def ukrainian_palatal_prs : Form :=
  { id := "stojkovic2026_ukrainian_palatal_prs"
    languageId := "ukra1253"
    parameterId := "be_late"
    form := "zapizɲ-u-je-ʃ"
    segments := ["zapizɲ", "u", "je", "ʃ"]
    comment := ""
    source := [
      ⟨"stojkovic-2026", "Table 2"⟩
    ]
    columns := [("Variety", "Ukrainian"), ("Root", "palatal"), ("Cell", "2sg.prs")] }

def all : List Form := [belarusian_plain_lform, belarusian_plain_prs, bos_cro_mon_ser_plain_lform, bos_cro_mon_ser_plain_prs, bulgarian_plain_lform, bulgarian_plain_prs, bunyev_ac_plain_lform, bunyev_ac_plain_prs, carpathian_rusyn_plain_lform, carpathian_rusyn_plain_prs, czech_plain_lform, czech_plain_prs, kashubian_plain_lform, kashubian_plain_prs, lemko_rusyn_plain_lform, lemko_rusyn_plain_prs, lower_sorbian_plain_lform, lower_sorbian_plain_prs, macedonian_plain_lform, macedonian_plain_prs, pannonian_rusyn_plain_lform, pannonian_rusyn_plain_prs, podlachian_plain_lform, podlachian_plain_prs, polish_plain_lform, polish_plain_prs, russian_plain_lform, russian_plain_prs, silesian_plain_lform, silesian_plain_prs, slovak_plain_lform, slovak_plain_prs, slovenian_plain_lform, slovenian_plain_prs, ukrainian_plain_lform, ukrainian_plain_prs, upper_sorbian_plain_lform, upper_sorbian_plain_prs, belarusian_palatal_lform, belarusian_palatal_prs, bunyev_ac_palatal_lform, bunyev_ac_palatal_prs, czech_palatal_lform, czech_palatal_prs, kashubian_palatal_lform, kashubian_palatal_prs, lower_sorbian_palatal_lform, lower_sorbian_palatal_prs, pannonian_rusyn_palatal_lform, pannonian_rusyn_palatal_prs, podlachian_palatal_lform, podlachian_palatal_prs, polish_palatal_lform, polish_palatal_prs, slovak_palatal_lform, slovak_palatal_prs, silesian_palatal_lform, silesian_palatal_prs, upper_sorbian_palatal_lform, upper_sorbian_palatal_prs, bos_cro_mon_ser_palatal_lform, bos_cro_mon_ser_palatal_prs, carpathian_rusyn_palatal_lform, carpathian_rusyn_palatal_prs, russian_palatal_lform, russian_palatal_prs, slovenian_palatal_lform, slovenian_palatal_prs, bulgarian_palatal_lform, bulgarian_palatal_prs, lemko_rusyn_palatal_lform, lemko_rusyn_palatal_prs, macedonian_palatal_lform, macedonian_palatal_prs, ukrainian_palatal_lform, ukrainian_palatal_prs]

def parameters : List Parameter := [
  { id := "abolish", name := "abolish", description := "" },
  { id := "accommodate", name := "accommodate", description := "" },
  { id := "adore", name := "adore", description := "" },
  { id := "aim", name := "aim", description := "" },
  { id := "battle", name := "battle", description := "" },
  { id := "be_late", name := "be late", description := "" },
  { id := "be_teacher", name := "be teacher", description := "" },
  { id := "believe", name := "believe", description := "" },
  { id := "buy", name := "buy", description := "" },
  { id := "care_for", name := "care for", description := "" },
  { id := "compare", name := "compare", description := "" },
  { id := "complain", name := "complain", description := "" },
  { id := "darn", name := "darn", description := "" },
  { id := "date", name := "date", description := "" },
  { id := "draw", name := "draw", description := "" },
  { id := "get_engaged", name := "get engaged", description := "" },
  { id := "grub", name := "grub", description := "" },
  { id := "jitter", name := "jitter", description := "" },
  { id := "kiss", name := "kiss", description := "" },
  { id := "paint", name := "paint", description := "" },
  { id := "prune", name := "prune", description := "" },
  { id := "rain", name := "rain", description := "" },
  { id := "reign", name := "reign", description := "" },
  { id := "serve", name := "serve", description := "" },
  { id := "spend_night", name := "spend night", description := "" },
  { id := "squeeze", name := "squeeze", description := "" },
  { id := "swear_at_god", name := "swear at god", description := "" },
  { id := "swindle", name := "swindle", description := "" },
  { id := "talk", name := "talk", description := "" },
  { id := "translate", name := "translate", description := "" },
  { id := "travel", name := "travel", description := "" },
  { id := "wander", name := "wander", description := "" },
  { id := "whip", name := "whip", description := "" },
  { id := "work", name := "work", description := "" }
]

def relations : List FormRelation := []

end Stojkovic2026.Forms
