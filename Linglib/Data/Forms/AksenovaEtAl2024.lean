module

public import Linglib.Data.Forms.Schema

/-!
# `AksenovaEtAl2024` — CLDF form data

Auto-generated from `Linglib/Data/Forms/AksenovaEtAl2024.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace AksenovaEtAl2024.Forms`.
-/

@[expose] public section

namespace AksenovaEtAl2024.Forms

open Data.Forms

def f_3a : Form :=
  { id := "aksenovaetal2024_3a"
    languageId := "loka1252"
    parameterId := "smoke"
    form := "èsìsòn"
    segments := ["è", "s", "ì", "s", "ò", "n"]
    comment := "Akinlabi (2009)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(3a)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.1"⟩
    ]
    columns := [("Ill_Formed", "èsìsɔ̀n")] }

def f_3b : Form :=
  { id := "aksenovaetal2024_3b"
    languageId := "loka1252"
    parameterId := "housefly"
    form := "ɛ̀sísɔ̀n"
    segments := ["ɛ̀", "s", "í", "s", "ɔ̀", "n"]
    comment := "Akinlabi (2009)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(3b)"⟩
    ]
    columns := [("Ill_Formed", "ɛ̀sísòn")] }

def f_3c : Form :=
  { id := "aksenovaetal2024_3c"
    languageId := "loka1252"
    parameterId := "matriclan"
    form := "lèjìmə̀"
    segments := ["l", "è", "j", "ì", "m", "ə̀"]
    comment := "Akinlabi (2009)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(3c)"⟩
    ]
    columns := [("Ill_Formed", "lèjìmà")] }

def f_3d : Form :=
  { id := "aksenovaetal2024_3d"
    languageId := "loka1252"
    parameterId := "kind_of_plant"
    form := "ɛ́kílìkà"
    segments := ["ɛ́", "k", "í", "l", "ì", "k", "à"]
    comment := "Akinlabi (2009)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(3d)"⟩
    ]
    columns := [("Ill_Formed", "ékílìkà")] }

def f_5a : Form :=
  { id := "aksenovaetal2024_5a"
    languageId := "kirg1245"
    parameterId := "fire_loc"
    form := "ot-to"
    segments := ["o", "t", "t", "o"]
    comment := "Nanayev (1950)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(5a)"⟩
    ] }

def f_5b : Form :=
  { id := "aksenovaetal2024_5b"
    languageId := "kirg1245"
    parameterId := "who_loc"
    form := "kim-de"
    segments := ["k", "i", "m", "d", "e"]
    comment := "Nanayev (1950)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(5b)"⟩
    ] }

def f_5c : Form :=
  { id := "aksenovaetal2024_5c"
    languageId := "kirg1245"
    parameterId := "house_loc"
    form := "üj-dö"
    segments := ["ü", "j", "d", "ö"]
    comment := "Nanayev (1950). The example line prints uj-do; the prose and Figure 34.3 give the front-vowel form. The ill-formed forms are Figure 34.3's."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(5c)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.3"⟩
    ]
    columns := [("Ill_Formed", "üjde üjdo")] }

def f_5d : Form :=
  { id := "aksenovaetal2024_5d"
    languageId := "kirg1245"
    parameterId := "fire_gen"
    form := "ot-tun"
    segments := ["o", "t", "t", "u", "n"]
    comment := "Nanayev (1950)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(5d)"⟩
    ] }

def f_5e : Form :=
  { id := "aksenovaetal2024_5e"
    languageId := "kirg1245"
    parameterId := "who_gen"
    form := "kim-din"
    segments := ["k", "i", "m", "d", "i", "n"]
    comment := "Nanayev (1950)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(5e)"⟩
    ] }

def f_5f : Form :=
  { id := "aksenovaetal2024_5f"
    languageId := "kirg1245"
    parameterId := "house_gen"
    form := "üj-dün"
    segments := ["ü", "j", "d", "ü", "n"]
    comment := "Nanayev (1950). The example line prints uj-dun; the prose and Figure 34.3 give the front-vowel form."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(5f)"⟩
    ] }

def f_9a : Form :=
  { id := "aksenovaetal2024_9a"
    languageId := "russ1264"
    parameterId := "enter_perf"
    form := "ɔr-ɔːd"
    segments := ["ɔ", "r", "ɔː", "d"]
    comment := ""
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9a)"⟩
    ]
    columns := [("Ill_Formed", "ɔr-aːd")] }

def f_9b : Form :=
  { id := "aksenovaetal2024_9b"
    languageId := "russ1264"
    parameterId := "enter_caus_perf"
    form := "ɔr-ʊːl-aːd"
    segments := ["ɔ", "r", "ʊː", "l", "aː", "d"]
    comment := ""
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9b)"⟩
    ]
    columns := [("Ill_Formed", "ɔr-ʊːl-ɔːd")] }

def f_9c : Form :=
  { id := "aksenovaetal2024_9c"
    languageId := "russ1264"
    parameterId := "wander_perf"
    form := "toːr-oːd"
    segments := ["t", "oː", "r", "oː", "d"]
    comment := ""
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9c)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.4"⟩
    ]
    columns := [("Ill_Formed", "toːr-eːd")] }

def f_9d : Form :=
  { id := "aksenovaetal2024_9d"
    languageId := "russ1264"
    parameterId := "wander_caus_perf"
    form := "toːr-uːl-eːd"
    segments := ["t", "oː", "r", "uː", "l", "eː", "d"]
    comment := ""
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9d)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.4"⟩
    ]
    columns := [("Ill_Formed", "toːr-uːl-oːd")] }

def f_9e : Form :=
  { id := "aksenovaetal2024_9e"
    languageId := "russ1264"
    parameterId := "horse_poss"
    form := "mɔrin-ɔː"
    segments := ["m", "ɔ", "r", "i", "n", "ɔː"]
    comment := ""
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9e)"⟩
    ]
    columns := [("Ill_Formed", "mɔrin-aː")] }

def f_9f : Form :=
  { id := "aksenovaetal2024_9f"
    languageId := "russ1264"
    parameterId := "group_poss"
    form := "oːrin-goː"
    segments := ["oː", "r", "i", "n", "g", "oː"]
    comment := ""
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(9f)"⟩
    ]
    columns := [("Ill_Formed", "oːrin-geː")] }

def f_14a : Form :=
  { id := "aksenovaetal2024_14a"
    languageId := "yaku1245"
    parameterId := "child_pl"
    form := "oɣo-lor"
    segments := ["o", "ɣ", "o", "l", "o", "r"]
    comment := "Kaun (1995)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14a)"⟩
    ]
    columns := [("Ill_Formed", "oɣo-lar")] }

def f_14b : Form :=
  { id := "aksenovaetal2024_14b"
    languageId := "yaku1245"
    parameterId := "wolf_pl"
    form := "börö-lör"
    segments := ["b", "ö", "r", "ö", "l", "ö", "r"]
    comment := "Kaun (1995)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14b)"⟩
    ]
    columns := [("Ill_Formed", "börö-ler")] }

def f_14c : Form :=
  { id := "aksenovaetal2024_14c"
    languageId := "yaku1245"
    parameterId := "child_acc"
    form := "oɣo-nu"
    segments := ["o", "ɣ", "o", "n", "u"]
    comment := "Kaun (1995)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14c)"⟩
    ]
    columns := [("Ill_Formed", "oɣo-nɨ")] }

def f_14d : Form :=
  { id := "aksenovaetal2024_14d"
    languageId := "yaku1245"
    parameterId := "wolf_acc"
    form := "börö-nü"
    segments := ["b", "ö", "r", "ö", "n", "ü"]
    comment := "Kaun (1995)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14d)"⟩
    ]
    columns := [("Ill_Formed", "börö-ni")] }

def f_14e : Form :=
  { id := "aksenovaetal2024_14e"
    languageId := "yaku1245"
    parameterId := "nose_acc"
    form := "murum-u"
    segments := ["m", "u", "r", "u", "m", "u"]
    comment := "Kaun (1995)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14e)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.5"⟩
    ]
    columns := [("Ill_Formed", "murum-ɨ")] }

def f_14f : Form :=
  { id := "aksenovaetal2024_14f"
    languageId := "yaku1245"
    parameterId := "window_acc"
    form := "tünnük-ü"
    segments := ["t", "ü", "n", "n", "ü", "k", "ü"]
    comment := "Kaun (1995)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14f)"⟩
    ]
    columns := [("Ill_Formed", "tünnük-i")] }

def f_14g : Form :=
  { id := "aksenovaetal2024_14g"
    languageId := "yaku1245"
    parameterId := "shaman_pl"
    form := "ojum-lar"
    segments := ["o", "j", "u", "m", "l", "a", "r"]
    comment := "Kaun (1995)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14g)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.5"⟩
    ]
    columns := [("Ill_Formed", "ojum-lor")] }

def f_14h : Form :=
  { id := "aksenovaetal2024_14h"
    languageId := "yaku1245"
    parameterId := "window_pl"
    form := "tünnük-ler"
    segments := ["t", "ü", "n", "n", "ü", "k", "l", "e", "r"]
    comment := "Kaun (1995)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(14h)"⟩
    ]
    columns := [("Ill_Formed", "tünnük-lör")] }

def f_16a : Form :=
  { id := "aksenovaetal2024_16a"
    languageId := "koon1247"
    parameterId := "attach_appl"
    form := "-somp-el-"
    segments := ["s", "o", "mp", "e", "l"]
    comment := "Hyman (1998)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16a)"⟩
    ] }

def f_16b : Form :=
  { id := "aksenovaetal2024_16b"
    languageId := "koon1247"
    parameterId := "languish_appl"
    form := "-leng-el-"
    segments := ["l", "e", "ng", "e", "l"]
    comment := "Hyman (1998)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16b)"⟩
    ] }

def f_16c : Form :=
  { id := "aksenovaetal2024_16c"
    languageId := "koon1247"
    parameterId := "support_appl"
    form := "-sik-il-"
    segments := ["s", "i", "k", "i", "l"]
    comment := "Hyman (1998)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16c)"⟩
    ] }

def f_16d : Form :=
  { id := "aksenovaetal2024_16d"
    languageId := "koon1247"
    parameterId := "surpass_appl"
    form := "-vur-il-"
    segments := ["v", "u", "r", "i", "l"]
    comment := "Hyman (1998)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16d)"⟩
    ] }

def f_16e : Form :=
  { id := "aksenovaetal2024_16e"
    languageId := "koon1247"
    parameterId := "do_trans"
    form := "-tomb-ol-"
    segments := ["t", "o", "mb", "o", "l"]
    comment := "Hyman (1998)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16e)"⟩
    ] }

def f_16f : Form :=
  { id := "aksenovaetal2024_16f"
    languageId := "koon1247"
    parameterId := "broom_trans"
    form := "-lemb-ol-"
    segments := ["l", "e", "mb", "o", "l"]
    comment := "Hyman (1998)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16f)"⟩
    ] }

def f_16g : Form :=
  { id := "aksenovaetal2024_16g"
    languageId := "koon1247"
    parameterId := "move_trans"
    form := "-vil-ul-"
    segments := ["v", "i", "l", "u", "l"]
    comment := "Hyman (1998)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16g)"⟩
    ] }

def f_16h : Form :=
  { id := "aksenovaetal2024_16h"
    languageId := "koon1247"
    parameterId := "bribe_trans"
    form := "-bub-ul-"
    segments := ["b", "u", "b", "u", "l"]
    comment := "Hyman (1998)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(16h)"⟩
    ] }

def f_18a : Form :=
  { id := "aksenovaetal2024_18a"
    languageId := "koon1247"
    parameterId := "wash_perf_act"
    form := "-suk-idi-"
    segments := ["s", "u", "k", "i", "d", "i"]
    comment := "Ao (1991)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(18a)"⟩
    ] }

def f_18b : Form :=
  { id := "aksenovaetal2024_18b"
    languageId := "koon1247"
    parameterId := "ground_perf_act"
    form := "-nik-ini-"
    segments := ["n", "i", "k", "i", "n", "i"]
    comment := "Ao (1991)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(18b)"⟩
    ] }

def f_18c : Form :=
  { id := "aksenovaetal2024_18c"
    languageId := "koon1247"
    parameterId := "hate_perf_act"
    form := "-meng-ene-"
    segments := ["m", "e", "ng", "e", "n", "e"]
    comment := "Ao (1991)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(18c)"⟩
    ] }

def f_18d : Form :=
  { id := "aksenovaetal2024_18d"
    languageId := "koon1247"
    parameterId := "wash_perf_pass"
    form := "-suk-ulu-"
    segments := ["s", "u", "k", "u", "l", "u"]
    comment := "Ao (1991)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(18d)"⟩
    ] }

def f_18e : Form :=
  { id := "aksenovaetal2024_18e"
    languageId := "koon1247"
    parameterId := "ground_perf_pass"
    form := "-nik-unu-"
    segments := ["n", "i", "k", "u", "n", "u"]
    comment := "Ao (1991). The ill-formed forms are Figure 34.6's."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(18e)"⟩,
      ⟨"aksenova-rawski-graf-heinz-2024", "Figure 34.6"⟩
    ]
    columns := [("Ill_Formed", "nikono nikulo")] }

def f_18f : Form :=
  { id := "aksenovaetal2024_18f"
    languageId := "koon1247"
    parameterId := "hate_perf_pass"
    form := "-meng-ono-"
    segments := ["m", "e", "ng", "o", "n", "o"]
    comment := "Ao (1991)."
    source := [
      ⟨"aksenova-rawski-graf-heinz-2024", "(18f)"⟩
    ] }

def all : List Form := [f_3a, f_3b, f_3c, f_3d, f_5a, f_5b, f_5c, f_5d, f_5e, f_5f, f_9a, f_9b, f_9c, f_9d, f_9e, f_9f, f_14a, f_14b, f_14c, f_14d, f_14e, f_14f, f_14g, f_14h, f_16a, f_16b, f_16c, f_16d, f_16e, f_16f, f_16g, f_16h, f_18a, f_18b, f_18c, f_18d, f_18e, f_18f]

def parameters : List Parameter := [
  { id := "smoke", name := "smoke", description := "" },
  { id := "housefly", name := "housefly", description := "" },
  { id := "matriclan", name := "matriclan", description := "" },
  { id := "kind_of_plant", name := "kind of plant", description := "" },
  { id := "fire_loc", name := "fire-LOC", description := "" },
  { id := "who_loc", name := "who-LOC", description := "" },
  { id := "house_loc", name := "house-LOC", description := "" },
  { id := "fire_gen", name := "fire-GEN", description := "" },
  { id := "who_gen", name := "who-GEN", description := "" },
  { id := "house_gen", name := "house-GEN", description := "" },
  { id := "enter_perf", name := "enter-PERF", description := "" },
  { id := "enter_caus_perf", name := "enter-CAUS-PERF", description := "" },
  { id := "wander_perf", name := "wander-PERF", description := "" },
  { id := "wander_caus_perf", name := "wander-CAUS-PERF", description := "" },
  { id := "horse_poss", name := "horse-POSS", description := "" },
  { id := "group_poss", name := "group-POSS", description := "" },
  { id := "child_pl", name := "child-PL", description := "" },
  { id := "wolf_pl", name := "wolf-PL", description := "" },
  { id := "child_acc", name := "child-ACC", description := "" },
  { id := "wolf_acc", name := "wolf-ACC", description := "" },
  { id := "nose_acc", name := "nose-ACC", description := "" },
  { id := "window_acc", name := "window-ACC", description := "" },
  { id := "shaman_pl", name := "shaman-PL", description := "" },
  { id := "window_pl", name := "window-PL", description := "" },
  { id := "attach_appl", name := "attach-APPL", description := "" },
  { id := "languish_appl", name := "languish-APPL", description := "" },
  { id := "support_appl", name := "support-APPL", description := "" },
  { id := "surpass_appl", name := "surpass-APPL", description := "" },
  { id := "do_trans", name := "do-TRANS", description := "" },
  { id := "broom_trans", name := "broom-TRANS", description := "" },
  { id := "move_trans", name := "move-TRANS", description := "" },
  { id := "bribe_trans", name := "bribe-TRANS", description := "" },
  { id := "wash_perf_act", name := "wash-PERF.ACT", description := "" },
  { id := "ground_perf_act", name := "ground-PERF.ACT", description := "" },
  { id := "hate_perf_act", name := "hate-PERF.ACT", description := "" },
  { id := "wash_perf_pass", name := "wash-PERF.PASS", description := "" },
  { id := "ground_perf_pass", name := "ground-PERF.PASS", description := "" },
  { id := "hate_perf_pass", name := "hate-PERF.PASS", description := "" }
]

def relations : List FormRelation := []

end AksenovaEtAl2024.Forms
