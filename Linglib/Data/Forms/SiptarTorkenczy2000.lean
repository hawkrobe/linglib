import Linglib.Data.Forms.Schema

/-!
# `SiptarTorkenczy2000` — CLDF form data

Auto-generated from `Linglib/Data/Forms/SiptarTorkenczy2000.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace SiptarTorkenczy2000.Forms`.
-/

namespace SiptarTorkenczy2000.Forms

open Data.Forms

def haz : Form :=
  { id := "siptartorkenczy2000_haz"
    languageId := "hung1274"
    parameterId := "house"
    form := "ház"
    segments := ["h", "á", "z"]
    comment := "stem of Table 11 class IA-b"
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
    comment := "1pl of ház"
    source := [
      ⟨"siptar-torkenczy-2000", "(13a)"⟩
    ] }

def haztol : Form :=
  { id := "siptartorkenczy2000_haztol"
    languageId := "hung1274"
    parameterId := "house_abl"
    form := "háztól"
    segments := ["h", "á", "z", "t", "ó", "l"]
    comment := "ablative of ház"
    source := [
      ⟨"siptar-torkenczy-2000", "(13b)"⟩
    ] }

def haznak : Form :=
  { id := "siptartorkenczy2000_haznak"
    languageId := "hung1274"
    parameterId := "house_dat"
    form := "háznak"
    segments := ["h", "á", "z", "n", "a", "k"]
    comment := "dative of ház"
    source := [
      ⟨"siptar-torkenczy-2000", "(13c)"⟩
    ] }

def hazhoz : Form :=
  { id := "siptartorkenczy2000_hazhoz"
    languageId := "hung1274"
    parameterId := "house_all"
    form := "házhoz"
    segments := ["h", "á", "z", "h", "o", "z"]
    comment := "allative of ház"
    source := [
      ⟨"siptar-torkenczy-2000", "(13d)"⟩
    ] }

def tuz : Form :=
  { id := "siptartorkenczy2000_tuz"
    languageId := "hung1274"
    parameterId := "fire"
    form := "tűz"
    segments := ["t", "ű", "z"]
    comment := "stem of Table 11 class IA-f"
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
    comment := "1pl of tűz"
    source := [
      ⟨"siptar-torkenczy-2000", "(14a)"⟩
    ] }

def tuztol : Form :=
  { id := "siptartorkenczy2000_tuztol"
    languageId := "hung1274"
    parameterId := "fire_abl"
    form := "tűztől"
    segments := ["t", "ű", "z", "t", "ő", "l"]
    comment := "ablative of tűz"
    source := [
      ⟨"siptar-torkenczy-2000", "(14b)"⟩
    ] }

def tuznek : Form :=
  { id := "siptartorkenczy2000_tuznek"
    languageId := "hung1274"
    parameterId := "fire_dat"
    form := "tűznek"
    segments := ["t", "ű", "z", "n", "e", "k"]
    comment := "dative of tűz"
    source := [
      ⟨"siptar-torkenczy-2000", "(14c)"⟩
    ] }

def tuzhoz : Form :=
  { id := "siptartorkenczy2000_tuzhoz"
    languageId := "hung1274"
    parameterId := "fire_all"
    form := "tűzhöz"
    segments := ["t", "ű", "z", "h", "ö", "z"]
    comment := "allative of tűz"
    source := [
      ⟨"siptar-torkenczy-2000", "(14d)"⟩
    ] }

def viz : Form :=
  { id := "siptartorkenczy2000_viz"
    languageId := "hung1274"
    parameterId := "water"
    form := "víz"
    segments := ["v", "í", "z"]
    comment := "stem of Table 11 class IIA-f"
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
    comment := "1pl of víz"
    source := [
      ⟨"siptar-torkenczy-2000", "(15a)"⟩
    ] }

def viztol : Form :=
  { id := "siptartorkenczy2000_viztol"
    languageId := "hung1274"
    parameterId := "water_abl"
    form := "víztől"
    segments := ["v", "í", "z", "t", "ő", "l"]
    comment := "ablative of víz"
    source := [
      ⟨"siptar-torkenczy-2000", "(15b)"⟩
    ] }

def viznek : Form :=
  { id := "siptartorkenczy2000_viznek"
    languageId := "hung1274"
    parameterId := "water_dat"
    form := "víznek"
    segments := ["v", "í", "z", "n", "e", "k"]
    comment := "dative of víz"
    source := [
      ⟨"siptar-torkenczy-2000", "(15c)"⟩
    ] }

def vizhez : Form :=
  { id := "siptartorkenczy2000_vizhez"
    languageId := "hung1274"
    parameterId := "water_all"
    form := "vízhez"
    segments := ["v", "í", "z", "h", "e", "z"]
    comment := "allative of víz"
    source := [
      ⟨"siptar-torkenczy-2000", "(15d)"⟩
    ] }

def piros : Form :=
  { id := "siptartorkenczy2000_piros"
    languageId := "hung1274"
    parameterId := "red"
    form := "piros"
    segments := ["p", "i", "r", "o", "s"]
    comment := "stem of Table 11 class IA-b"
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
    comment := "1pl of piros"
    source := [
      ⟨"siptar-torkenczy-2000", "(16a)"⟩
    ] }

def pirostol : Form :=
  { id := "siptartorkenczy2000_pirostol"
    languageId := "hung1274"
    parameterId := "red_abl"
    form := "pirostól"
    segments := ["p", "i", "r", "o", "s", "t", "ó", "l"]
    comment := "ablative of piros"
    source := [
      ⟨"siptar-torkenczy-2000", "(16b)"⟩
    ] }

def pirosnak : Form :=
  { id := "siptartorkenczy2000_pirosnak"
    languageId := "hung1274"
    parameterId := "red_dat"
    form := "pirosnak"
    segments := ["p", "i", "r", "o", "s", "n", "a", "k"]
    comment := "dative of piros"
    source := [
      ⟨"siptar-torkenczy-2000", "(16c)"⟩
    ] }

def piroshoz : Form :=
  { id := "siptartorkenczy2000_piroshoz"
    languageId := "hung1274"
    parameterId := "red_all"
    form := "piroshoz"
    segments := ["p", "i", "r", "o", "s", "h", "o", "z"]
    comment := "allative of piros"
    source := [
      ⟨"siptar-torkenczy-2000", "(16d)"⟩
    ] }

def nuansz : Form :=
  { id := "siptartorkenczy2000_nuansz"
    languageId := "hung1274"
    parameterId := "nuance"
    form := "nüansz"
    segments := ["n", "ü", "a", "n", "sz"]
    comment := "stem of Table 11 class IB-b"
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
    comment := "1pl of nüansz"
    source := [
      ⟨"siptar-torkenczy-2000", "(17a)"⟩
    ] }

def nuansztol : Form :=
  { id := "siptartorkenczy2000_nuansztol"
    languageId := "hung1274"
    parameterId := "nuance_abl"
    form := "nüansztól"
    segments := ["n", "ü", "a", "n", "sz", "t", "ó", "l"]
    comment := "ablative of nüansz"
    source := [
      ⟨"siptar-torkenczy-2000", "(17b)"⟩
    ] }

def nuansznak : Form :=
  { id := "siptartorkenczy2000_nuansznak"
    languageId := "hung1274"
    parameterId := "nuance_dat"
    form := "nüansznak"
    segments := ["n", "ü", "a", "n", "sz", "n", "a", "k"]
    comment := "dative of nüansz"
    source := [
      ⟨"siptar-torkenczy-2000", "(17c)"⟩
    ] }

def nuanszhoz : Form :=
  { id := "siptartorkenczy2000_nuanszhoz"
    languageId := "hung1274"
    parameterId := "nuance_all"
    form := "nüanszhoz"
    segments := ["n", "ü", "a", "n", "sz", "h", "o", "z"]
    comment := "allative of nüansz"
    source := [
      ⟨"siptar-torkenczy-2000", "(17d)"⟩
    ] }

def oreg : Form :=
  { id := "siptartorkenczy2000_oreg"
    languageId := "hung1274"
    parameterId := "old"
    form := "öreg"
    segments := ["ö", "r", "e", "g"]
    comment := "stem of Table 11 class IIB-f"
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
    comment := "1pl of öreg"
    source := [
      ⟨"siptar-torkenczy-2000", "(18a)"⟩
    ] }

def oregtol : Form :=
  { id := "siptartorkenczy2000_oregtol"
    languageId := "hung1274"
    parameterId := "old_abl"
    form := "öregtől"
    segments := ["ö", "r", "e", "g", "t", "ő", "l"]
    comment := "ablative of öreg"
    source := [
      ⟨"siptar-torkenczy-2000", "(18b)"⟩
    ] }

def oregnek : Form :=
  { id := "siptartorkenczy2000_oregnek"
    languageId := "hung1274"
    parameterId := "old_dat"
    form := "öregnek"
    segments := ["ö", "r", "e", "g", "n", "e", "k"]
    comment := "dative of öreg"
    source := [
      ⟨"siptar-torkenczy-2000", "(18c)"⟩
    ] }

def oreghez : Form :=
  { id := "siptartorkenczy2000_oreghez"
    languageId := "hung1274"
    parameterId := "old_all"
    form := "öreghez"
    segments := ["ö", "r", "e", "g", "h", "e", "z"]
    comment := "allative of öreg"
    source := [
      ⟨"siptar-torkenczy-2000", "(18d)"⟩
    ] }

def szemolcs : Form :=
  { id := "siptartorkenczy2000_szemolcs"
    languageId := "hung1274"
    parameterId := "wart"
    form := "szemölcs"
    segments := ["sz", "e", "m", "ö", "l", "cs"]
    comment := "stem of Table 11 class IA-f"
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
    comment := "1pl of szemölcs"
    source := [
      ⟨"siptar-torkenczy-2000", "(19a)"⟩
    ] }

def szemolcstol : Form :=
  { id := "siptartorkenczy2000_szemolcstol"
    languageId := "hung1274"
    parameterId := "wart_abl"
    form := "szemölcstől"
    segments := ["sz", "e", "m", "ö", "l", "cs", "t", "ő", "l"]
    comment := "ablative of szemölcs"
    source := [
      ⟨"siptar-torkenczy-2000", "(19b)"⟩
    ] }

def szemolcsnek : Form :=
  { id := "siptartorkenczy2000_szemolcsnek"
    languageId := "hung1274"
    parameterId := "wart_dat"
    form := "szemölcsnek"
    segments := ["sz", "e", "m", "ö", "l", "cs", "n", "e", "k"]
    comment := "dative of szemölcs"
    source := [
      ⟨"siptar-torkenczy-2000", "(19c)"⟩
    ] }

def szemolcshoz : Form :=
  { id := "siptartorkenczy2000_szemolcshoz"
    languageId := "hung1274"
    parameterId := "wart_all"
    form := "szemölcshöz"
    segments := ["sz", "e", "m", "ö", "l", "cs", "h", "ö", "z"]
    comment := "allative of szemölcs"
    source := [
      ⟨"siptar-torkenczy-2000", "(19d)"⟩
    ] }

def sofor : Form :=
  { id := "siptartorkenczy2000_sofor"
    languageId := "hung1274"
    parameterId := "driver"
    form := "sofőr"
    segments := ["s", "o", "f", "ő", "r"]
    comment := "stem of Table 11 class IB-f"
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
    comment := "1pl of sofőr"
    source := [
      ⟨"siptar-torkenczy-2000", "(20a)"⟩
    ] }

def sofortol : Form :=
  { id := "siptartorkenczy2000_sofortol"
    languageId := "hung1274"
    parameterId := "driver_abl"
    form := "sofőrtől"
    segments := ["s", "o", "f", "ő", "r", "t", "ő", "l"]
    comment := "ablative of sofőr"
    source := [
      ⟨"siptar-torkenczy-2000", "(20b)"⟩
    ] }

def sofornek : Form :=
  { id := "siptartorkenczy2000_sofornek"
    languageId := "hung1274"
    parameterId := "driver_dat"
    form := "sofőrnek"
    segments := ["s", "o", "f", "ő", "r", "n", "e", "k"]
    comment := "dative of sofőr"
    source := [
      ⟨"siptar-torkenczy-2000", "(20c)"⟩
    ] }

def soforhoz : Form :=
  { id := "siptartorkenczy2000_soforhoz"
    languageId := "hung1274"
    parameterId := "driver_all"
    form := "sofőrhöz"
    segments := ["s", "o", "f", "ő", "r", "h", "ö", "z"]
    comment := "allative of sofőr"
    source := [
      ⟨"siptar-torkenczy-2000", "(20d)"⟩
    ] }

def papir : Form :=
  { id := "siptartorkenczy2000_papir"
    languageId := "hung1274"
    parameterId := "paper"
    form := "papír"
    segments := ["p", "a", "p", "í", "r"]
    comment := "stem of Table 11 class IIB-b"
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
    comment := "1pl of papír"
    source := [
      ⟨"siptar-torkenczy-2000", "(21a)"⟩
    ] }

def papirtol : Form :=
  { id := "siptartorkenczy2000_papirtol"
    languageId := "hung1274"
    parameterId := "paper_abl"
    form := "papírtól"
    segments := ["p", "a", "p", "í", "r", "t", "ó", "l"]
    comment := "ablative of papír"
    source := [
      ⟨"siptar-torkenczy-2000", "(21b)"⟩
    ] }

def papirnak : Form :=
  { id := "siptartorkenczy2000_papirnak"
    languageId := "hung1274"
    parameterId := "paper_dat"
    form := "papírnak"
    segments := ["p", "a", "p", "í", "r", "n", "a", "k"]
    comment := "dative of papír"
    source := [
      ⟨"siptar-torkenczy-2000", "(21c)"⟩
    ] }

def papirhoz : Form :=
  { id := "siptartorkenczy2000_papirhoz"
    languageId := "hung1274"
    parameterId := "paper_all"
    form := "papírhoz"
    segments := ["p", "a", "p", "í", "r", "h", "o", "z"]
    comment := "allative of papír"
    source := [
      ⟨"siptar-torkenczy-2000", "(21d)"⟩
    ] }

def hid : Form :=
  { id := "siptartorkenczy2000_hid"
    languageId := "hung1274"
    parameterId := "bridge"
    form := "híd"
    segments := ["h", "í", "d"]
    comment := "stem of Table 11 class IIA-b"
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
    comment := "1pl of híd"
    source := [
      ⟨"siptar-torkenczy-2000", "(22a)"⟩
    ] }

def hidtol : Form :=
  { id := "siptartorkenczy2000_hidtol"
    languageId := "hung1274"
    parameterId := "bridge_abl"
    form := "hídtól"
    segments := ["h", "í", "d", "t", "ó", "l"]
    comment := "ablative of híd"
    source := [
      ⟨"siptar-torkenczy-2000", "(22b)"⟩
    ] }

def hidnak : Form :=
  { id := "siptartorkenczy2000_hidnak"
    languageId := "hung1274"
    parameterId := "bridge_dat"
    form := "hídnak"
    segments := ["h", "í", "d", "n", "a", "k"]
    comment := "dative of híd"
    source := [
      ⟨"siptar-torkenczy-2000", "(22c)"⟩
    ] }

def hidhoz : Form :=
  { id := "siptartorkenczy2000_hidhoz"
    languageId := "hung1274"
    parameterId := "bridge_all"
    form := "hídhoz"
    segments := ["h", "í", "d", "h", "o", "z"]
    comment := "allative of híd"
    source := [
      ⟨"siptar-torkenczy-2000", "(22d)"⟩
    ] }

def kodex : Form :=
  { id := "siptartorkenczy2000_kodex"
    languageId := "hung1274"
    parameterId := "codex"
    form := "kódex"
    segments := ["k", "ó", "d", "e", "x"]
    comment := "stem of Table 11 class IB-f"
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
    comment := "1pl of kódex"
    source := [
      ⟨"siptar-torkenczy-2000", "(23a)"⟩
    ] }

def kodextol : Form :=
  { id := "siptartorkenczy2000_kodextol"
    languageId := "hung1274"
    parameterId := "codex_abl"
    form := "kódextől"
    segments := ["k", "ó", "d", "e", "x", "t", "ő", "l"]
    comment := "ablative of kódex"
    source := [
      ⟨"siptar-torkenczy-2000", "(23b)"⟩
    ] }

def kodexnek : Form :=
  { id := "siptartorkenczy2000_kodexnek"
    languageId := "hung1274"
    parameterId := "codex_dat"
    form := "kódexnek"
    segments := ["k", "ó", "d", "e", "x", "n", "e", "k"]
    comment := "dative of kódex"
    source := [
      ⟨"siptar-torkenczy-2000", "(23c)"⟩
    ] }

def kodexhez : Form :=
  { id := "siptartorkenczy2000_kodexhez"
    languageId := "hung1274"
    parameterId := "codex_all"
    form := "kódexhez"
    segments := ["k", "ó", "d", "e", "x", "h", "e", "z"]
    comment := "allative of kódex"
    source := [
      ⟨"siptar-torkenczy-2000", "(23d)"⟩
    ] }

def dzsungel : Form :=
  { id := "siptartorkenczy2000_dzsungel"
    languageId := "hung1274"
    parameterId := "jungle"
    form := "dzsungel"
    segments := ["dzs", "u", "n", "g", "e", "l"]
    comment := "stem of Table 11 class IIB-b/IB-f"
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
    comment := "inessive of dzsungel, vacillating"
    source := [
      ⟨"siptar-torkenczy-2000", "section 3.2.3.1"⟩
    ] }

def dzsungelben : Form :=
  { id := "siptartorkenczy2000_dzsungelben"
    languageId := "hung1274"
    parameterId := "jungle_iness"
    form := "dzsungelben"
    segments := ["dzs", "u", "n", "g", "e", "l", "b", "e", "n"]
    comment := "inessive of dzsungel, vacillating"
    source := [
      ⟨"siptar-torkenczy-2000", "section 3.2.3.1"⟩
    ] }

def all : List Form := [haz, hazunk, haztol, haznak, hazhoz, tuz, tuzunk, tuztol, tuznek, tuzhoz, viz, vizunk, viztol, viznek, vizhez, piros, pirosunk, pirostol, pirosnak, piroshoz, nuansz, nuanszunk, nuansztol, nuansznak, nuanszhoz, oreg, oregunk, oregtol, oregnek, oreghez, szemolcs, szemolcsunk, szemolcstol, szemolcsnek, szemolcshoz, sofor, soforunk, sofortol, sofornek, soforhoz, papir, papirunk, papirtol, papirnak, papirhoz, hid, hidunk, hidtol, hidnak, hidhoz, kodex, kodexunk, kodextol, kodexnek, kodexhez, dzsungel, dzsungelban, dzsungelben]

def parameters : List Parameter := [
  { id := "house", name := "house", description := "" },
  { id := "house_1pl", name := "house (1pl)", description := "" },
  { id := "house_abl", name := "house (abl)", description := "" },
  { id := "house_dat", name := "house (dat)", description := "" },
  { id := "house_all", name := "house (all)", description := "" },
  { id := "fire", name := "fire", description := "" },
  { id := "fire_1pl", name := "fire (1pl)", description := "" },
  { id := "fire_abl", name := "fire (abl)", description := "" },
  { id := "fire_dat", name := "fire (dat)", description := "" },
  { id := "fire_all", name := "fire (all)", description := "" },
  { id := "water", name := "water", description := "" },
  { id := "water_1pl", name := "water (1pl)", description := "" },
  { id := "water_abl", name := "water (abl)", description := "" },
  { id := "water_dat", name := "water (dat)", description := "" },
  { id := "water_all", name := "water (all)", description := "" },
  { id := "red", name := "red", description := "" },
  { id := "red_1pl", name := "red (1pl)", description := "" },
  { id := "red_abl", name := "red (abl)", description := "" },
  { id := "red_dat", name := "red (dat)", description := "" },
  { id := "red_all", name := "red (all)", description := "" },
  { id := "nuance", name := "nuance", description := "" },
  { id := "nuance_1pl", name := "nuance (1pl)", description := "" },
  { id := "nuance_abl", name := "nuance (abl)", description := "" },
  { id := "nuance_dat", name := "nuance (dat)", description := "" },
  { id := "nuance_all", name := "nuance (all)", description := "" },
  { id := "old", name := "old", description := "" },
  { id := "old_1pl", name := "old (1pl)", description := "" },
  { id := "old_abl", name := "old (abl)", description := "" },
  { id := "old_dat", name := "old (dat)", description := "" },
  { id := "old_all", name := "old (all)", description := "" },
  { id := "wart", name := "wart", description := "" },
  { id := "wart_1pl", name := "wart (1pl)", description := "" },
  { id := "wart_abl", name := "wart (abl)", description := "" },
  { id := "wart_dat", name := "wart (dat)", description := "" },
  { id := "wart_all", name := "wart (all)", description := "" },
  { id := "driver", name := "driver", description := "" },
  { id := "driver_1pl", name := "driver (1pl)", description := "" },
  { id := "driver_abl", name := "driver (abl)", description := "" },
  { id := "driver_dat", name := "driver (dat)", description := "" },
  { id := "driver_all", name := "driver (all)", description := "" },
  { id := "paper", name := "paper", description := "" },
  { id := "paper_1pl", name := "paper (1pl)", description := "" },
  { id := "paper_abl", name := "paper (abl)", description := "" },
  { id := "paper_dat", name := "paper (dat)", description := "" },
  { id := "paper_all", name := "paper (all)", description := "" },
  { id := "bridge", name := "bridge", description := "" },
  { id := "bridge_1pl", name := "bridge (1pl)", description := "" },
  { id := "bridge_abl", name := "bridge (abl)", description := "" },
  { id := "bridge_dat", name := "bridge (dat)", description := "" },
  { id := "bridge_all", name := "bridge (all)", description := "" },
  { id := "codex", name := "codex", description := "" },
  { id := "codex_1pl", name := "codex (1pl)", description := "" },
  { id := "codex_abl", name := "codex (abl)", description := "" },
  { id := "codex_dat", name := "codex (dat)", description := "" },
  { id := "codex_all", name := "codex (all)", description := "" },
  { id := "jungle", name := "jungle", description := "" },
  { id := "jungle_iness", name := "jungle (iness)", description := "" }
]

def relations : List FormRelation := [
  { id := "siptartorkenczy2000_haz_siptartorkenczy2000_hazunk", formId := "siptartorkenczy2000_haz", targetId := "siptartorkenczy2000_hazunk", relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(13a)"⟩
    ] },
  { id := "siptartorkenczy2000_haz_siptartorkenczy2000_haztol", formId := "siptartorkenczy2000_haz", targetId := "siptartorkenczy2000_haztol", relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(13b)"⟩
    ] },
  { id := "siptartorkenczy2000_haz_siptartorkenczy2000_haznak", formId := "siptartorkenczy2000_haz", targetId := "siptartorkenczy2000_haznak", relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(13c)"⟩
    ] },
  { id := "siptartorkenczy2000_haz_siptartorkenczy2000_hazhoz", formId := "siptartorkenczy2000_haz", targetId := "siptartorkenczy2000_hazhoz", relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(13d)"⟩
    ] },
  { id := "siptartorkenczy2000_tuz_siptartorkenczy2000_tuzunk", formId := "siptartorkenczy2000_tuz", targetId := "siptartorkenczy2000_tuzunk", relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(14a)"⟩
    ] },
  { id := "siptartorkenczy2000_tuz_siptartorkenczy2000_tuztol", formId := "siptartorkenczy2000_tuz", targetId := "siptartorkenczy2000_tuztol", relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(14b)"⟩
    ] },
  { id := "siptartorkenczy2000_tuz_siptartorkenczy2000_tuznek", formId := "siptartorkenczy2000_tuz", targetId := "siptartorkenczy2000_tuznek", relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(14c)"⟩
    ] },
  { id := "siptartorkenczy2000_tuz_siptartorkenczy2000_tuzhoz", formId := "siptartorkenczy2000_tuz", targetId := "siptartorkenczy2000_tuzhoz", relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(14d)"⟩
    ] },
  { id := "siptartorkenczy2000_viz_siptartorkenczy2000_vizunk", formId := "siptartorkenczy2000_viz", targetId := "siptartorkenczy2000_vizunk", relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(15a)"⟩
    ] },
  { id := "siptartorkenczy2000_viz_siptartorkenczy2000_viztol", formId := "siptartorkenczy2000_viz", targetId := "siptartorkenczy2000_viztol", relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(15b)"⟩
    ] },
  { id := "siptartorkenczy2000_viz_siptartorkenczy2000_viznek", formId := "siptartorkenczy2000_viz", targetId := "siptartorkenczy2000_viznek", relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(15c)"⟩
    ] },
  { id := "siptartorkenczy2000_viz_siptartorkenczy2000_vizhez", formId := "siptartorkenczy2000_viz", targetId := "siptartorkenczy2000_vizhez", relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(15d)"⟩
    ] },
  { id := "siptartorkenczy2000_piros_siptartorkenczy2000_pirosunk", formId := "siptartorkenczy2000_piros", targetId := "siptartorkenczy2000_pirosunk", relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(16a)"⟩
    ] },
  { id := "siptartorkenczy2000_piros_siptartorkenczy2000_pirostol", formId := "siptartorkenczy2000_piros", targetId := "siptartorkenczy2000_pirostol", relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(16b)"⟩
    ] },
  { id := "siptartorkenczy2000_piros_siptartorkenczy2000_pirosnak", formId := "siptartorkenczy2000_piros", targetId := "siptartorkenczy2000_pirosnak", relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(16c)"⟩
    ] },
  { id := "siptartorkenczy2000_piros_siptartorkenczy2000_piroshoz", formId := "siptartorkenczy2000_piros", targetId := "siptartorkenczy2000_piroshoz", relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(16d)"⟩
    ] },
  { id := "siptartorkenczy2000_nuansz_siptartorkenczy2000_nuanszunk", formId := "siptartorkenczy2000_nuansz", targetId := "siptartorkenczy2000_nuanszunk", relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(17a)"⟩
    ] },
  { id := "siptartorkenczy2000_nuansz_siptartorkenczy2000_nuansztol", formId := "siptartorkenczy2000_nuansz", targetId := "siptartorkenczy2000_nuansztol", relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(17b)"⟩
    ] },
  { id := "siptartorkenczy2000_nuansz_siptartorkenczy2000_nuansznak", formId := "siptartorkenczy2000_nuansz", targetId := "siptartorkenczy2000_nuansznak", relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(17c)"⟩
    ] },
  { id := "siptartorkenczy2000_nuansz_siptartorkenczy2000_nuanszhoz", formId := "siptartorkenczy2000_nuansz", targetId := "siptartorkenczy2000_nuanszhoz", relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(17d)"⟩
    ] },
  { id := "siptartorkenczy2000_oreg_siptartorkenczy2000_oregunk", formId := "siptartorkenczy2000_oreg", targetId := "siptartorkenczy2000_oregunk", relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(18a)"⟩
    ] },
  { id := "siptartorkenczy2000_oreg_siptartorkenczy2000_oregtol", formId := "siptartorkenczy2000_oreg", targetId := "siptartorkenczy2000_oregtol", relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(18b)"⟩
    ] },
  { id := "siptartorkenczy2000_oreg_siptartorkenczy2000_oregnek", formId := "siptartorkenczy2000_oreg", targetId := "siptartorkenczy2000_oregnek", relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(18c)"⟩
    ] },
  { id := "siptartorkenczy2000_oreg_siptartorkenczy2000_oreghez", formId := "siptartorkenczy2000_oreg", targetId := "siptartorkenczy2000_oreghez", relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(18d)"⟩
    ] },
  { id := "siptartorkenczy2000_szemolcs_siptartorkenczy2000_szemolcsunk", formId := "siptartorkenczy2000_szemolcs", targetId := "siptartorkenczy2000_szemolcsunk", relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(19a)"⟩
    ] },
  { id := "siptartorkenczy2000_szemolcs_siptartorkenczy2000_szemolcstol", formId := "siptartorkenczy2000_szemolcs", targetId := "siptartorkenczy2000_szemolcstol", relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(19b)"⟩
    ] },
  { id := "siptartorkenczy2000_szemolcs_siptartorkenczy2000_szemolcsnek", formId := "siptartorkenczy2000_szemolcs", targetId := "siptartorkenczy2000_szemolcsnek", relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(19c)"⟩
    ] },
  { id := "siptartorkenczy2000_szemolcs_siptartorkenczy2000_szemolcshoz", formId := "siptartorkenczy2000_szemolcs", targetId := "siptartorkenczy2000_szemolcshoz", relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(19d)"⟩
    ] },
  { id := "siptartorkenczy2000_sofor_siptartorkenczy2000_soforunk", formId := "siptartorkenczy2000_sofor", targetId := "siptartorkenczy2000_soforunk", relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(20a)"⟩
    ] },
  { id := "siptartorkenczy2000_sofor_siptartorkenczy2000_sofortol", formId := "siptartorkenczy2000_sofor", targetId := "siptartorkenczy2000_sofortol", relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(20b)"⟩
    ] },
  { id := "siptartorkenczy2000_sofor_siptartorkenczy2000_sofornek", formId := "siptartorkenczy2000_sofor", targetId := "siptartorkenczy2000_sofornek", relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(20c)"⟩
    ] },
  { id := "siptartorkenczy2000_sofor_siptartorkenczy2000_soforhoz", formId := "siptartorkenczy2000_sofor", targetId := "siptartorkenczy2000_soforhoz", relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(20d)"⟩
    ] },
  { id := "siptartorkenczy2000_papir_siptartorkenczy2000_papirunk", formId := "siptartorkenczy2000_papir", targetId := "siptartorkenczy2000_papirunk", relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(21a)"⟩
    ] },
  { id := "siptartorkenczy2000_papir_siptartorkenczy2000_papirtol", formId := "siptartorkenczy2000_papir", targetId := "siptartorkenczy2000_papirtol", relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(21b)"⟩
    ] },
  { id := "siptartorkenczy2000_papir_siptartorkenczy2000_papirnak", formId := "siptartorkenczy2000_papir", targetId := "siptartorkenczy2000_papirnak", relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(21c)"⟩
    ] },
  { id := "siptartorkenczy2000_papir_siptartorkenczy2000_papirhoz", formId := "siptartorkenczy2000_papir", targetId := "siptartorkenczy2000_papirhoz", relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(21d)"⟩
    ] },
  { id := "siptartorkenczy2000_hid_siptartorkenczy2000_hidunk", formId := "siptartorkenczy2000_hid", targetId := "siptartorkenczy2000_hidunk", relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(22a)"⟩
    ] },
  { id := "siptartorkenczy2000_hid_siptartorkenczy2000_hidtol", formId := "siptartorkenczy2000_hid", targetId := "siptartorkenczy2000_hidtol", relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(22b)"⟩
    ] },
  { id := "siptartorkenczy2000_hid_siptartorkenczy2000_hidnak", formId := "siptartorkenczy2000_hid", targetId := "siptartorkenczy2000_hidnak", relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(22c)"⟩
    ] },
  { id := "siptartorkenczy2000_hid_siptartorkenczy2000_hidhoz", formId := "siptartorkenczy2000_hid", targetId := "siptartorkenczy2000_hidhoz", relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(22d)"⟩
    ] },
  { id := "siptartorkenczy2000_kodex_siptartorkenczy2000_kodexunk", formId := "siptartorkenczy2000_kodex", targetId := "siptartorkenczy2000_kodexunk", relation := "1pl", source := [
      ⟨"siptar-torkenczy-2000", "(23a)"⟩
    ] },
  { id := "siptartorkenczy2000_kodex_siptartorkenczy2000_kodextol", formId := "siptartorkenczy2000_kodex", targetId := "siptartorkenczy2000_kodextol", relation := "ablative", source := [
      ⟨"siptar-torkenczy-2000", "(23b)"⟩
    ] },
  { id := "siptartorkenczy2000_kodex_siptartorkenczy2000_kodexnek", formId := "siptartorkenczy2000_kodex", targetId := "siptartorkenczy2000_kodexnek", relation := "dative", source := [
      ⟨"siptar-torkenczy-2000", "(23c)"⟩
    ] },
  { id := "siptartorkenczy2000_kodex_siptartorkenczy2000_kodexhez", formId := "siptartorkenczy2000_kodex", targetId := "siptartorkenczy2000_kodexhez", relation := "allative", source := [
      ⟨"siptar-torkenczy-2000", "(23d)"⟩
    ] },
  { id := "siptartorkenczy2000_dzsungel_siptartorkenczy2000_dzsungelban", formId := "siptartorkenczy2000_dzsungel", targetId := "siptartorkenczy2000_dzsungelban", relation := "inessive", source := [
      ⟨"siptar-torkenczy-2000", "section 3.2.3.1"⟩
    ] },
  { id := "siptartorkenczy2000_dzsungel_siptartorkenczy2000_dzsungelben", formId := "siptartorkenczy2000_dzsungel", targetId := "siptartorkenczy2000_dzsungelben", relation := "inessive", source := [
      ⟨"siptar-torkenczy-2000", "section 3.2.3.1"⟩
    ] }
]

end SiptarTorkenczy2000.Forms
