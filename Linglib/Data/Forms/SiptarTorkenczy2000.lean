module

public import Linglib.Data.Forms.Schema

/-!
# `SiptarTorkenczy2000` — CLDF form data

Auto-generated from `Linglib/Data/Forms/SiptarTorkenczy2000.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace SiptarTorkenczy2000.Forms`.
-/

@[expose] public section

namespace SiptarTorkenczy2000.Forms

open Data.Forms

def haz : Form :=
  { id := "siptartorkenczy2000_haz"
    languageId := "hung1274"
    parameterId := "house"
    form := "ház"
    segments := ["h", "á", "z"]
    source := [
      ⟨"siptar-torkenczy-2000", "(13)"⟩
    ]
    columns := [("Class", "IA-b")] }

def hazunk : Form :=
  { id := "siptartorkenczy2000_hazunk"
    languageId := "hung1274"
    parameterId := "house_1pl"
    form := "házunk"
    segments := ["h", "á", "z", "u", "n", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(13a)"⟩
    ] }

def haztol : Form :=
  { id := "siptartorkenczy2000_haztol"
    languageId := "hung1274"
    parameterId := "house_abl"
    form := "háztól"
    segments := ["h", "á", "z", "t", "ó", "l"]
    source := [
      ⟨"siptar-torkenczy-2000", "(13b)"⟩
    ] }

def haznak : Form :=
  { id := "siptartorkenczy2000_haznak"
    languageId := "hung1274"
    parameterId := "house_dat"
    form := "háznak"
    segments := ["h", "á", "z", "n", "a", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(13c)"⟩
    ] }

def hazhoz : Form :=
  { id := "siptartorkenczy2000_hazhoz"
    languageId := "hung1274"
    parameterId := "house_all"
    form := "házhoz"
    segments := ["h", "á", "z", "h", "o", "z"]
    source := [
      ⟨"siptar-torkenczy-2000", "(13d)"⟩
    ] }

def tuz : Form :=
  { id := "siptartorkenczy2000_tuz"
    languageId := "hung1274"
    parameterId := "fire"
    form := "tűz"
    segments := ["t", "ű", "z"]
    source := [
      ⟨"siptar-torkenczy-2000", "(14)"⟩
    ]
    columns := [("Class", "IA-f")] }

def tuzunk : Form :=
  { id := "siptartorkenczy2000_tuzunk"
    languageId := "hung1274"
    parameterId := "fire_1pl"
    form := "tüzünk"
    segments := ["t", "ü", "z", "ü", "n", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(14a)"⟩
    ] }

def tuztol : Form :=
  { id := "siptartorkenczy2000_tuztol"
    languageId := "hung1274"
    parameterId := "fire_abl"
    form := "tűztől"
    segments := ["t", "ű", "z", "t", "ő", "l"]
    source := [
      ⟨"siptar-torkenczy-2000", "(14b)"⟩
    ] }

def tuznek : Form :=
  { id := "siptartorkenczy2000_tuznek"
    languageId := "hung1274"
    parameterId := "fire_dat"
    form := "tűznek"
    segments := ["t", "ű", "z", "n", "e", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(14c)"⟩
    ] }

def tuzhoz : Form :=
  { id := "siptartorkenczy2000_tuzhoz"
    languageId := "hung1274"
    parameterId := "fire_all"
    form := "tűzhöz"
    segments := ["t", "ű", "z", "h", "ö", "z"]
    source := [
      ⟨"siptar-torkenczy-2000", "(14d)"⟩
    ] }

def viz : Form :=
  { id := "siptartorkenczy2000_viz"
    languageId := "hung1274"
    parameterId := "water"
    form := "víz"
    segments := ["v", "í", "z"]
    source := [
      ⟨"siptar-torkenczy-2000", "(15)"⟩
    ]
    columns := [("Class", "IIA-f")] }

def vizunk : Form :=
  { id := "siptartorkenczy2000_vizunk"
    languageId := "hung1274"
    parameterId := "water_1pl"
    form := "vizünk"
    segments := ["v", "i", "z", "ü", "n", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(15a)"⟩
    ] }

def viztol : Form :=
  { id := "siptartorkenczy2000_viztol"
    languageId := "hung1274"
    parameterId := "water_abl"
    form := "víztől"
    segments := ["v", "í", "z", "t", "ő", "l"]
    source := [
      ⟨"siptar-torkenczy-2000", "(15b)"⟩
    ] }

def viznek : Form :=
  { id := "siptartorkenczy2000_viznek"
    languageId := "hung1274"
    parameterId := "water_dat"
    form := "víznek"
    segments := ["v", "í", "z", "n", "e", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(15c)"⟩
    ] }

def vizhez : Form :=
  { id := "siptartorkenczy2000_vizhez"
    languageId := "hung1274"
    parameterId := "water_all"
    form := "vízhez"
    segments := ["v", "í", "z", "h", "e", "z"]
    source := [
      ⟨"siptar-torkenczy-2000", "(15d)"⟩
    ] }

def piros : Form :=
  { id := "siptartorkenczy2000_piros"
    languageId := "hung1274"
    parameterId := "red"
    form := "piros"
    segments := ["p", "i", "r", "o", "s"]
    source := [
      ⟨"siptar-torkenczy-2000", "(16)"⟩
    ]
    columns := [("Class", "IA-b")] }

def pirosunk : Form :=
  { id := "siptartorkenczy2000_pirosunk"
    languageId := "hung1274"
    parameterId := "red_1pl"
    form := "pirosunk"
    segments := ["p", "i", "r", "o", "s", "u", "n", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(16a)"⟩
    ] }

def pirostol : Form :=
  { id := "siptartorkenczy2000_pirostol"
    languageId := "hung1274"
    parameterId := "red_abl"
    form := "pirostól"
    segments := ["p", "i", "r", "o", "s", "t", "ó", "l"]
    source := [
      ⟨"siptar-torkenczy-2000", "(16b)"⟩
    ] }

def pirosnak : Form :=
  { id := "siptartorkenczy2000_pirosnak"
    languageId := "hung1274"
    parameterId := "red_dat"
    form := "pirosnak"
    segments := ["p", "i", "r", "o", "s", "n", "a", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(16c)"⟩
    ] }

def piroshoz : Form :=
  { id := "siptartorkenczy2000_piroshoz"
    languageId := "hung1274"
    parameterId := "red_all"
    form := "piroshoz"
    segments := ["p", "i", "r", "o", "s", "h", "o", "z"]
    source := [
      ⟨"siptar-torkenczy-2000", "(16d)"⟩
    ] }

def nuansz : Form :=
  { id := "siptartorkenczy2000_nuansz"
    languageId := "hung1274"
    parameterId := "nuance"
    form := "nüansz"
    segments := ["n", "ü", "a", "n", "sz"]
    source := [
      ⟨"siptar-torkenczy-2000", "(17)"⟩
    ]
    columns := [("Class", "IB-b")] }

def nuanszunk : Form :=
  { id := "siptartorkenczy2000_nuanszunk"
    languageId := "hung1274"
    parameterId := "nuance_1pl"
    form := "nüanszunk"
    segments := ["n", "ü", "a", "n", "sz", "u", "n", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(17a)"⟩
    ] }

def nuansztol : Form :=
  { id := "siptartorkenczy2000_nuansztol"
    languageId := "hung1274"
    parameterId := "nuance_abl"
    form := "nüansztól"
    segments := ["n", "ü", "a", "n", "sz", "t", "ó", "l"]
    source := [
      ⟨"siptar-torkenczy-2000", "(17b)"⟩
    ] }

def nuansznak : Form :=
  { id := "siptartorkenczy2000_nuansznak"
    languageId := "hung1274"
    parameterId := "nuance_dat"
    form := "nüansznak"
    segments := ["n", "ü", "a", "n", "sz", "n", "a", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(17c)"⟩
    ] }

def nuanszhoz : Form :=
  { id := "siptartorkenczy2000_nuanszhoz"
    languageId := "hung1274"
    parameterId := "nuance_all"
    form := "nüanszhoz"
    segments := ["n", "ü", "a", "n", "sz", "h", "o", "z"]
    source := [
      ⟨"siptar-torkenczy-2000", "(17d)"⟩
    ] }

def oreg : Form :=
  { id := "siptartorkenczy2000_oreg"
    languageId := "hung1274"
    parameterId := "old"
    form := "öreg"
    segments := ["ö", "r", "e", "g"]
    source := [
      ⟨"siptar-torkenczy-2000", "(18)"⟩
    ]
    columns := [("Class", "IIB-f")] }

def oregunk : Form :=
  { id := "siptartorkenczy2000_oregunk"
    languageId := "hung1274"
    parameterId := "old_1pl"
    form := "öregünk"
    segments := ["ö", "r", "e", "g", "ü", "n", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(18a)"⟩
    ] }

def oregtol : Form :=
  { id := "siptartorkenczy2000_oregtol"
    languageId := "hung1274"
    parameterId := "old_abl"
    form := "öregtől"
    segments := ["ö", "r", "e", "g", "t", "ő", "l"]
    source := [
      ⟨"siptar-torkenczy-2000", "(18b)"⟩
    ] }

def oregnek : Form :=
  { id := "siptartorkenczy2000_oregnek"
    languageId := "hung1274"
    parameterId := "old_dat"
    form := "öregnek"
    segments := ["ö", "r", "e", "g", "n", "e", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(18c)"⟩
    ] }

def oreghez : Form :=
  { id := "siptartorkenczy2000_oreghez"
    languageId := "hung1274"
    parameterId := "old_all"
    form := "öreghez"
    segments := ["ö", "r", "e", "g", "h", "e", "z"]
    source := [
      ⟨"siptar-torkenczy-2000", "(18d)"⟩
    ] }

def szemolcs : Form :=
  { id := "siptartorkenczy2000_szemolcs"
    languageId := "hung1274"
    parameterId := "wart"
    form := "szemölcs"
    segments := ["sz", "e", "m", "ö", "l", "cs"]
    source := [
      ⟨"siptar-torkenczy-2000", "(19)"⟩
    ]
    columns := [("Class", "IA-f")] }

def szemolcsunk : Form :=
  { id := "siptartorkenczy2000_szemolcsunk"
    languageId := "hung1274"
    parameterId := "wart_1pl"
    form := "szemölcsünk"
    segments := ["sz", "e", "m", "ö", "l", "cs", "ü", "n", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(19a)"⟩
    ] }

def szemolcstol : Form :=
  { id := "siptartorkenczy2000_szemolcstol"
    languageId := "hung1274"
    parameterId := "wart_abl"
    form := "szemölcstől"
    segments := ["sz", "e", "m", "ö", "l", "cs", "t", "ő", "l"]
    source := [
      ⟨"siptar-torkenczy-2000", "(19b)"⟩
    ] }

def szemolcsnek : Form :=
  { id := "siptartorkenczy2000_szemolcsnek"
    languageId := "hung1274"
    parameterId := "wart_dat"
    form := "szemölcsnek"
    segments := ["sz", "e", "m", "ö", "l", "cs", "n", "e", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(19c)"⟩
    ] }

def szemolcshoz : Form :=
  { id := "siptartorkenczy2000_szemolcshoz"
    languageId := "hung1274"
    parameterId := "wart_all"
    form := "szemölcshöz"
    segments := ["sz", "e", "m", "ö", "l", "cs", "h", "ö", "z"]
    source := [
      ⟨"siptar-torkenczy-2000", "(19d)"⟩
    ] }

def sofor : Form :=
  { id := "siptartorkenczy2000_sofor"
    languageId := "hung1274"
    parameterId := "driver"
    form := "sofőr"
    segments := ["s", "o", "f", "ő", "r"]
    source := [
      ⟨"siptar-torkenczy-2000", "(20)"⟩
    ]
    columns := [("Class", "IB-f")] }

def soforunk : Form :=
  { id := "siptartorkenczy2000_soforunk"
    languageId := "hung1274"
    parameterId := "driver_1pl"
    form := "sofőrünk"
    segments := ["s", "o", "f", "ő", "r", "ü", "n", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(20a)"⟩
    ] }

def sofortol : Form :=
  { id := "siptartorkenczy2000_sofortol"
    languageId := "hung1274"
    parameterId := "driver_abl"
    form := "sofőrtől"
    segments := ["s", "o", "f", "ő", "r", "t", "ő", "l"]
    source := [
      ⟨"siptar-torkenczy-2000", "(20b)"⟩
    ] }

def sofornek : Form :=
  { id := "siptartorkenczy2000_sofornek"
    languageId := "hung1274"
    parameterId := "driver_dat"
    form := "sofőrnek"
    segments := ["s", "o", "f", "ő", "r", "n", "e", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(20c)"⟩
    ] }

def soforhoz : Form :=
  { id := "siptartorkenczy2000_soforhoz"
    languageId := "hung1274"
    parameterId := "driver_all"
    form := "sofőrhöz"
    segments := ["s", "o", "f", "ő", "r", "h", "ö", "z"]
    source := [
      ⟨"siptar-torkenczy-2000", "(20d)"⟩
    ] }

def papir : Form :=
  { id := "siptartorkenczy2000_papir"
    languageId := "hung1274"
    parameterId := "paper"
    form := "papír"
    segments := ["p", "a", "p", "í", "r"]
    source := [
      ⟨"siptar-torkenczy-2000", "(21)"⟩
    ]
    columns := [("Class", "IIB-b")] }

def papirunk : Form :=
  { id := "siptartorkenczy2000_papirunk"
    languageId := "hung1274"
    parameterId := "paper_1pl"
    form := "papírunk"
    segments := ["p", "a", "p", "í", "r", "u", "n", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(21a)"⟩
    ] }

def papirtol : Form :=
  { id := "siptartorkenczy2000_papirtol"
    languageId := "hung1274"
    parameterId := "paper_abl"
    form := "papírtól"
    segments := ["p", "a", "p", "í", "r", "t", "ó", "l"]
    source := [
      ⟨"siptar-torkenczy-2000", "(21b)"⟩
    ] }

def papirnak : Form :=
  { id := "siptartorkenczy2000_papirnak"
    languageId := "hung1274"
    parameterId := "paper_dat"
    form := "papírnak"
    segments := ["p", "a", "p", "í", "r", "n", "a", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(21c)"⟩
    ] }

def papirhoz : Form :=
  { id := "siptartorkenczy2000_papirhoz"
    languageId := "hung1274"
    parameterId := "paper_all"
    form := "papírhoz"
    segments := ["p", "a", "p", "í", "r", "h", "o", "z"]
    source := [
      ⟨"siptar-torkenczy-2000", "(21d)"⟩
    ] }

def hid : Form :=
  { id := "siptartorkenczy2000_hid"
    languageId := "hung1274"
    parameterId := "bridge"
    form := "híd"
    segments := ["h", "í", "d"]
    source := [
      ⟨"siptar-torkenczy-2000", "(22)"⟩
    ]
    columns := [("Class", "IIA-b")] }

def hidunk : Form :=
  { id := "siptartorkenczy2000_hidunk"
    languageId := "hung1274"
    parameterId := "bridge_1pl"
    form := "hidunk"
    segments := ["h", "i", "d", "u", "n", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(22a)"⟩
    ] }

def hidtol : Form :=
  { id := "siptartorkenczy2000_hidtol"
    languageId := "hung1274"
    parameterId := "bridge_abl"
    form := "hídtól"
    segments := ["h", "í", "d", "t", "ó", "l"]
    source := [
      ⟨"siptar-torkenczy-2000", "(22b)"⟩
    ] }

def hidnak : Form :=
  { id := "siptartorkenczy2000_hidnak"
    languageId := "hung1274"
    parameterId := "bridge_dat"
    form := "hídnak"
    segments := ["h", "í", "d", "n", "a", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(22c)"⟩
    ] }

def hidhoz : Form :=
  { id := "siptartorkenczy2000_hidhoz"
    languageId := "hung1274"
    parameterId := "bridge_all"
    form := "hídhoz"
    segments := ["h", "í", "d", "h", "o", "z"]
    source := [
      ⟨"siptar-torkenczy-2000", "(22d)"⟩
    ] }

def kodex : Form :=
  { id := "siptartorkenczy2000_kodex"
    languageId := "hung1274"
    parameterId := "codex"
    form := "kódex"
    segments := ["k", "ó", "d", "e", "x"]
    source := [
      ⟨"siptar-torkenczy-2000", "(23)"⟩
    ]
    columns := [("Class", "IB-f")] }

def kodexunk : Form :=
  { id := "siptartorkenczy2000_kodexunk"
    languageId := "hung1274"
    parameterId := "codex_1pl"
    form := "kódexünk"
    segments := ["k", "ó", "d", "e", "x", "ü", "n", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(23a)"⟩
    ] }

def kodextol : Form :=
  { id := "siptartorkenczy2000_kodextol"
    languageId := "hung1274"
    parameterId := "codex_abl"
    form := "kódextől"
    segments := ["k", "ó", "d", "e", "x", "t", "ő", "l"]
    source := [
      ⟨"siptar-torkenczy-2000", "(23b)"⟩
    ] }

def kodexnek : Form :=
  { id := "siptartorkenczy2000_kodexnek"
    languageId := "hung1274"
    parameterId := "codex_dat"
    form := "kódexnek"
    segments := ["k", "ó", "d", "e", "x", "n", "e", "k"]
    source := [
      ⟨"siptar-torkenczy-2000", "(23c)"⟩
    ] }

def kodexhez : Form :=
  { id := "siptartorkenczy2000_kodexhez"
    languageId := "hung1274"
    parameterId := "codex_all"
    form := "kódexhez"
    segments := ["k", "ó", "d", "e", "x", "h", "e", "z"]
    source := [
      ⟨"siptar-torkenczy-2000", "(23d)"⟩
    ] }

def dzsungel : Form :=
  { id := "siptartorkenczy2000_dzsungel"
    languageId := "hung1274"
    parameterId := "jungle"
    form := "dzsungel"
    segments := ["dzs", "u", "n", "g", "e", "l"]
    source := [
      ⟨"siptar-torkenczy-2000", "section 3.2.3.1"⟩
    ]
    columns := [("Class", "IIB-b/IB-f")] }

def dzsungelban : Form :=
  { id := "siptartorkenczy2000_dzsungelban"
    languageId := "hung1274"
    parameterId := "jungle_iness"
    form := "dzsungelban"
    segments := ["dzs", "u", "n", "g", "e", "l", "b", "a", "n"]
    source := [
      ⟨"siptar-torkenczy-2000", "section 3.2.3.1"⟩
    ] }

def dzsungelben : Form :=
  { id := "siptartorkenczy2000_dzsungelben"
    languageId := "hung1274"
    parameterId := "jungle_iness"
    form := "dzsungelben"
    segments := ["dzs", "u", "n", "g", "e", "l", "b", "e", "n"]
    source := [
      ⟨"siptar-torkenczy-2000", "section 3.2.3.1"⟩
    ] }

def all : List Form := [haz, hazunk, haztol, haznak, hazhoz, tuz, tuzunk, tuztol, tuznek, tuzhoz, viz, vizunk, viztol, viznek, vizhez, piros, pirosunk, pirostol, pirosnak, piroshoz, nuansz, nuanszunk, nuansztol, nuansznak, nuanszhoz, oreg, oregunk, oregtol, oregnek, oreghez, szemolcs, szemolcsunk, szemolcstol, szemolcsnek, szemolcshoz, sofor, soforunk, sofortol, sofornek, soforhoz, papir, papirunk, papirtol, papirnak, papirhoz, hid, hidunk, hidtol, hidnak, hidhoz, kodex, kodexunk, kodextol, kodexnek, kodexhez, dzsungel, dzsungelban, dzsungelben]

def relations : List FormRelation := [
  { id := "siptartorkenczy2000_haz_siptartorkenczy2000_hazunk", form := haz, target := hazunk, relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(13a)"⟩
    ] },
  { id := "siptartorkenczy2000_haz_siptartorkenczy2000_haztol", form := haz, target := haztol, relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(13b)"⟩
    ] },
  { id := "siptartorkenczy2000_haz_siptartorkenczy2000_haznak", form := haz, target := haznak, relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(13c)"⟩
    ] },
  { id := "siptartorkenczy2000_haz_siptartorkenczy2000_hazhoz", form := haz, target := hazhoz, relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(13d)"⟩
    ] },
  { id := "siptartorkenczy2000_tuz_siptartorkenczy2000_tuzunk", form := tuz, target := tuzunk, relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(14a)"⟩
    ] },
  { id := "siptartorkenczy2000_tuz_siptartorkenczy2000_tuztol", form := tuz, target := tuztol, relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(14b)"⟩
    ] },
  { id := "siptartorkenczy2000_tuz_siptartorkenczy2000_tuznek", form := tuz, target := tuznek, relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(14c)"⟩
    ] },
  { id := "siptartorkenczy2000_tuz_siptartorkenczy2000_tuzhoz", form := tuz, target := tuzhoz, relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(14d)"⟩
    ] },
  { id := "siptartorkenczy2000_viz_siptartorkenczy2000_vizunk", form := viz, target := vizunk, relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(15a)"⟩
    ] },
  { id := "siptartorkenczy2000_viz_siptartorkenczy2000_viztol", form := viz, target := viztol, relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(15b)"⟩
    ] },
  { id := "siptartorkenczy2000_viz_siptartorkenczy2000_viznek", form := viz, target := viznek, relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(15c)"⟩
    ] },
  { id := "siptartorkenczy2000_viz_siptartorkenczy2000_vizhez", form := viz, target := vizhez, relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(15d)"⟩
    ] },
  { id := "siptartorkenczy2000_piros_siptartorkenczy2000_pirosunk", form := piros, target := pirosunk, relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(16a)"⟩
    ] },
  { id := "siptartorkenczy2000_piros_siptartorkenczy2000_pirostol", form := piros, target := pirostol, relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(16b)"⟩
    ] },
  { id := "siptartorkenczy2000_piros_siptartorkenczy2000_pirosnak", form := piros, target := pirosnak, relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(16c)"⟩
    ] },
  { id := "siptartorkenczy2000_piros_siptartorkenczy2000_piroshoz", form := piros, target := piroshoz, relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(16d)"⟩
    ] },
  { id := "siptartorkenczy2000_nuansz_siptartorkenczy2000_nuanszunk", form := nuansz, target := nuanszunk, relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(17a)"⟩
    ] },
  { id := "siptartorkenczy2000_nuansz_siptartorkenczy2000_nuansztol", form := nuansz, target := nuansztol, relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(17b)"⟩
    ] },
  { id := "siptartorkenczy2000_nuansz_siptartorkenczy2000_nuansznak", form := nuansz, target := nuansznak, relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(17c)"⟩
    ] },
  { id := "siptartorkenczy2000_nuansz_siptartorkenczy2000_nuanszhoz", form := nuansz, target := nuanszhoz, relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(17d)"⟩
    ] },
  { id := "siptartorkenczy2000_oreg_siptartorkenczy2000_oregunk", form := oreg, target := oregunk, relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(18a)"⟩
    ] },
  { id := "siptartorkenczy2000_oreg_siptartorkenczy2000_oregtol", form := oreg, target := oregtol, relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(18b)"⟩
    ] },
  { id := "siptartorkenczy2000_oreg_siptartorkenczy2000_oregnek", form := oreg, target := oregnek, relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(18c)"⟩
    ] },
  { id := "siptartorkenczy2000_oreg_siptartorkenczy2000_oreghez", form := oreg, target := oreghez, relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(18d)"⟩
    ] },
  { id := "siptartorkenczy2000_szemolcs_siptartorkenczy2000_szemolcsunk", form := szemolcs, target := szemolcsunk, relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(19a)"⟩
    ] },
  { id := "siptartorkenczy2000_szemolcs_siptartorkenczy2000_szemolcstol", form := szemolcs, target := szemolcstol, relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(19b)"⟩
    ] },
  { id := "siptartorkenczy2000_szemolcs_siptartorkenczy2000_szemolcsnek", form := szemolcs, target := szemolcsnek, relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(19c)"⟩
    ] },
  { id := "siptartorkenczy2000_szemolcs_siptartorkenczy2000_szemolcshoz", form := szemolcs, target := szemolcshoz, relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(19d)"⟩
    ] },
  { id := "siptartorkenczy2000_sofor_siptartorkenczy2000_soforunk", form := sofor, target := soforunk, relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(20a)"⟩
    ] },
  { id := "siptartorkenczy2000_sofor_siptartorkenczy2000_sofortol", form := sofor, target := sofortol, relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(20b)"⟩
    ] },
  { id := "siptartorkenczy2000_sofor_siptartorkenczy2000_sofornek", form := sofor, target := sofornek, relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(20c)"⟩
    ] },
  { id := "siptartorkenczy2000_sofor_siptartorkenczy2000_soforhoz", form := sofor, target := soforhoz, relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(20d)"⟩
    ] },
  { id := "siptartorkenczy2000_papir_siptartorkenczy2000_papirunk", form := papir, target := papirunk, relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(21a)"⟩
    ] },
  { id := "siptartorkenczy2000_papir_siptartorkenczy2000_papirtol", form := papir, target := papirtol, relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(21b)"⟩
    ] },
  { id := "siptartorkenczy2000_papir_siptartorkenczy2000_papirnak", form := papir, target := papirnak, relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(21c)"⟩
    ] },
  { id := "siptartorkenczy2000_papir_siptartorkenczy2000_papirhoz", form := papir, target := papirhoz, relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(21d)"⟩
    ] },
  { id := "siptartorkenczy2000_hid_siptartorkenczy2000_hidunk", form := hid, target := hidunk, relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(22a)"⟩
    ] },
  { id := "siptartorkenczy2000_hid_siptartorkenczy2000_hidtol", form := hid, target := hidtol, relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(22b)"⟩
    ] },
  { id := "siptartorkenczy2000_hid_siptartorkenczy2000_hidnak", form := hid, target := hidnak, relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(22c)"⟩
    ] },
  { id := "siptartorkenczy2000_hid_siptartorkenczy2000_hidhoz", form := hid, target := hidhoz, relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(22d)"⟩
    ] },
  { id := "siptartorkenczy2000_kodex_siptartorkenczy2000_kodexunk", form := kodex, target := kodexunk, relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(23a)"⟩
    ] },
  { id := "siptartorkenczy2000_kodex_siptartorkenczy2000_kodextol", form := kodex, target := kodextol, relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(23b)"⟩
    ] },
  { id := "siptartorkenczy2000_kodex_siptartorkenczy2000_kodexnek", form := kodex, target := kodexnek, relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(23c)"⟩
    ] },
  { id := "siptartorkenczy2000_kodex_siptartorkenczy2000_kodexhez", form := kodex, target := kodexhez, relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(23d)"⟩
    ] },
  { id := "siptartorkenczy2000_dzsungel_siptartorkenczy2000_dzsungelban", form := dzsungel, target := dzsungelban, relation := "inessive", source := [
      ⟨"siptar-torkenczy-2000", "section 3.2.3.1"⟩
    ] },
  { id := "siptartorkenczy2000_dzsungel_siptartorkenczy2000_dzsungelben", form := dzsungel, target := dzsungelben, relation := "inessive", source := [
      ⟨"siptar-torkenczy-2000", "section 3.2.3.1"⟩
    ] }
]

end SiptarTorkenczy2000.Forms
