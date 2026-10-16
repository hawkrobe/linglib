module

public import Linglib.Data.Forms.Schema

/-!
# `Lucy1994` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Lucy1994.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Lucy1994.Forms`.
-/

@[expose] public section

namespace Lucy1994.Forms

open Data.Forms

def AFCT : Form :=
  { id := "lucy1994_AFCT"
    languageId := "yuca1254"
    parameterId := "AFCT"
    form := "=t"
    segments := ["=t"]
    source := [
      ⟨"lucy-1994", "(1a)"⟩
    ] }

def ROOT : Form :=
  { id := "lucy1994_ROOT"
    languageId := "yuca1254"
    parameterId := "ROOT"
    form := "=∅"
    segments := ["=∅"]
    source := [
      ⟨"lucy-1994", "(1b)"⟩
    ] }

def CAUS : Form :=
  { id := "lucy1994_CAUS"
    languageId := "yuca1254"
    parameterId := "CAUS"
    form := "=s"
    segments := ["=s"]
    source := [
      ⟨"lucy-1994", "(1c)"⟩
    ] }

def POS : Form :=
  { id := "lucy1994_POS"
    languageId := "yuca1254"
    parameterId := "POS"
    form := "=lah"
    segments := ["=lah"]
    source := [
      ⟨"lucy-1994", "(5)"⟩
    ] }

def siit : Form :=
  { id := "lucy1994_siit"
    languageId := "yuca1254"
    parameterId := "jump"
    form := "síit'"
    segments := ["síit'"]
    source := [
      ⟨"lucy-1994", "(1a)"⟩
    ] }

def siit_t : Form :=
  { id := "lucy1994_siit_t"
    languageId := "yuca1254"
    parameterId := "jump-over"
    form := "síit'=t"
    segments := ["síit'", "=t"]
    source := [
      ⟨"lucy-1994", "(1a)"⟩
    ] }

def tziib : Form :=
  { id := "lucy1994_tziib"
    languageId := "yuca1254"
    parameterId := "write"
    form := "¢'iib'"
    segments := ["¢'iib'"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def miis : Form :=
  { id := "lucy1994_miis"
    languageId := "yuca1254"
    parameterId := "sweep"
    form := "mìis"
    segments := ["mìis"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def cheh : Form :=
  { id := "lucy1994_cheh"
    languageId := "yuca1254"
    parameterId := "smile"
    form := "čé'eh"
    segments := ["čé'eh"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def paak : Form :=
  { id := "lucy1994_paak"
    languageId := "yuca1254"
    parameterId := "weed"
    form := "páak"
    segments := ["páak"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def kuc : Form :=
  { id := "lucy1994_kuc"
    languageId := "yuca1254"
    parameterId := "carry"
    form := "kuč"
    segments := ["kuč"]
    source := [
      ⟨"lucy-1994", "(1b)"⟩
    ] }

def kuc_0 : Form :=
  { id := "lucy1994_kuc_0"
    languageId := "yuca1254"
    parameterId := "carry-tr"
    form := "kuč=∅"
    segments := ["kuč", "=∅"]
    source := [
      ⟨"lucy-1994", "(1b)"⟩
    ] }

def kos : Form :=
  { id := "lucy1994_kos"
    languageId := "yuca1254"
    parameterId := "cut"
    form := "k'os"
    segments := ["k'os"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def pis : Form :=
  { id := "lucy1994_pis"
    languageId := "yuca1254"
    parameterId := "measure"
    form := "p'is"
    segments := ["p'is"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def hats : Form :=
  { id := "lucy1994_hats"
    languageId := "yuca1254"
    parameterId := "whip"
    form := "ha¢"
    segments := ["ha¢"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def los : Form :=
  { id := "lucy1994_los"
    languageId := "yuca1254"
    parameterId := "punch"
    form := "loš"
    segments := ["loš"]
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def ah : Form :=
  { id := "lucy1994_ah"
    languageId := "yuca1254"
    parameterId := "awaken"
    form := "'ah"
    segments := ["'ah"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def ah_s : Form :=
  { id := "lucy1994_ah_s"
    languageId := "yuca1254"
    parameterId := "wake-someone"
    form := "'ah=s"
    segments := ["'ah", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def wen : Form :=
  { id := "lucy1994_wen"
    languageId := "yuca1254"
    parameterId := "fall-asleep"
    form := "wen"
    segments := ["wen"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def wen_s : Form :=
  { id := "lucy1994_wen_s"
    languageId := "yuca1254"
    parameterId := "put-to-sleep"
    form := "ween=s"
    segments := ["ween", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def siih : Form :=
  { id := "lucy1994_siih"
    languageId := "yuca1254"
    parameterId := "be-born"
    form := "siih"
    segments := ["siih"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def siih_s : Form :=
  { id := "lucy1994_siih_s"
    languageId := "yuca1254"
    parameterId := "give-birth"
    form := "siih=s"
    segments := ["siih", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def kiim : Form :=
  { id := "lucy1994_kiim"
    languageId := "yuca1254"
    parameterId := "die"
    form := "kíim"
    segments := ["kíim"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def kiim_s : Form :=
  { id := "lucy1994_kiim_s"
    languageId := "yuca1254"
    parameterId := "kill"
    form := "kíim=s"
    segments := ["kíim", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def tuub : Form :=
  { id := "lucy1994_tuub"
    languageId := "yuca1254"
    parameterId := "forget"
    form := "tú'ub'"
    segments := ["tú'ub'"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def tuub_s : Form :=
  { id := "lucy1994_tuub_s"
    languageId := "yuca1254"
    parameterId := "distract"
    form := "tú'ub'=s"
    segments := ["tú'ub'", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def kaah : Form :=
  { id := "lucy1994_kaah"
    languageId := "yuca1254"
    parameterId := "remember"
    form := "k'a'ah"
    segments := ["k'a'ah"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def kaah_s : Form :=
  { id := "lucy1994_kaah_s"
    languageId := "yuca1254"
    parameterId := "remind"
    form := "k'á'ah=s"
    segments := ["k'á'ah", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def chuun : Form :=
  { id := "lucy1994_chuun"
    languageId := "yuca1254"
    parameterId := "begin-activity"
    form := "ču'un"
    segments := ["ču'un"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def chuun_s : Form :=
  { id := "lucy1994_chuun_s"
    languageId := "yuca1254"
    parameterId := "cause-to-begin"
    form := "ču'un=s"
    segments := ["ču'un", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def chen : Form :=
  { id := "lucy1994_chen"
    languageId := "yuca1254"
    parameterId := "stop"
    form := "č'en"
    segments := ["č'en"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def chen_s : Form :=
  { id := "lucy1994_chen_s"
    languageId := "yuca1254"
    parameterId := "cause-to-stop"
    form := "č'en=s"
    segments := ["č'en", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def hoop : Form :=
  { id := "lucy1994_hoop"
    languageId := "yuca1254"
    parameterId := "begin"
    form := "hó'op'"
    segments := ["hó'op'"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def hoop_s : Form :=
  { id := "lucy1994_hoop_s"
    languageId := "yuca1254"
    parameterId := "cause-to-start"
    form := "hó'op'=s"
    segments := ["hó'op'", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def haaw : Form :=
  { id := "lucy1994_haaw"
    languageId := "yuca1254"
    parameterId := "cease"
    form := "háaw"
    segments := ["háaw"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def haaw_s : Form :=
  { id := "lucy1994_haaw_s"
    languageId := "yuca1254"
    parameterId := "revoke"
    form := "háaw=s"
    segments := ["háaw", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def heel : Form :=
  { id := "lucy1994_heel"
    languageId := "yuca1254"
    parameterId := "rest"
    form := "hé'el"
    segments := ["hé'el"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def heel_s : Form :=
  { id := "lucy1994_heel_s"
    languageId := "yuca1254"
    parameterId := "rest-tr"
    form := "hé'e(l)=s"
    segments := ["hé'e(l)", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def paat : Form :=
  { id := "lucy1994_paat"
    languageId := "yuca1254"
    parameterId := "remain"
    form := "p'át"
    segments := ["p'át"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def paat_s : Form :=
  { id := "lucy1994_paat_s"
    languageId := "yuca1254"
    parameterId := "abandon"
    form := "p'át=s"
    segments := ["p'át", "=s"]
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def maan : Form :=
  { id := "lucy1994_maan"
    languageId := "yuca1254"
    parameterId := "pass-by"
    form := "máan"
    segments := ["máan"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def maan_s : Form :=
  { id := "lucy1994_maan_s"
    languageId := "yuca1254"
    parameterId := "transport"
    form := "maan=s"
    segments := ["maan", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def peek : Form :=
  { id := "lucy1994_peek"
    languageId := "yuca1254"
    parameterId := "move"
    form := "péek"
    segments := ["péek"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def peek_s : Form :=
  { id := "lucy1994_peek_s"
    languageId := "yuca1254"
    parameterId := "cause-to-move"
    form := "pek=s"
    segments := ["pek", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def bin : Form :=
  { id := "lucy1994_bin"
    languageId := "yuca1254"
    parameterId := "go"
    form := "b'in"
    segments := ["b'in"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def bin_s : Form :=
  { id := "lucy1994_bin_s"
    languageId := "yuca1254"
    parameterId := "take"
    form := "bi(n)=s"
    segments := ["bi(n)", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def taal : Form :=
  { id := "lucy1994_taal"
    languageId := "yuca1254"
    parameterId := "come"
    form := "tàal"
    segments := ["tàal"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def taal_s : Form :=
  { id := "lucy1994_taal_s"
    languageId := "yuca1254"
    parameterId := "bring"
    form := "taa(l)=s"
    segments := ["taa(l)", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def uul : Form :=
  { id := "lucy1994_uul"
    languageId := "yuca1254"
    parameterId := "arrive-here"
    form := "'ú'ul"
    segments := ["'ú'ul"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def uul_s : Form :=
  { id := "lucy1994_uul_s"
    languageId := "yuca1254"
    parameterId := "bring-here"
    form := "'u'uh=s"
    segments := ["'u'uh", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def ok : Form :=
  { id := "lucy1994_ok"
    languageId := "yuca1254"
    parameterId := "enter"
    form := "'ok"
    segments := ["'ok"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def ok_s : Form :=
  { id := "lucy1994_ok_s"
    languageId := "yuca1254"
    parameterId := "move-in"
    form := "'ook=s"
    segments := ["'ook", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def luub : Form :=
  { id := "lucy1994_luub"
    languageId := "yuca1254"
    parameterId := "fall"
    form := "lúub'"
    segments := ["lúub'"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def luub_s : Form :=
  { id := "lucy1994_luub_s"
    languageId := "yuca1254"
    parameterId := "fell"
    form := "luub'=s"
    segments := ["luub'", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def liik : Form :=
  { id := "lucy1994_liik"
    languageId := "yuca1254"
    parameterId := "rise"
    form := "líik'"
    segments := ["líik'"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def liik_s : Form :=
  { id := "lucy1994_liik_s"
    languageId := "yuca1254"
    parameterId := "raise"
    form := "lii(k)'=s"
    segments := ["lii(k)'", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def naak : Form :=
  { id := "lucy1994_naak"
    languageId := "yuca1254"
    parameterId := "ascend"
    form := "ná'ak"
    segments := ["ná'ak"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def naak_s : Form :=
  { id := "lucy1994_naak_s"
    languageId := "yuca1254"
    parameterId := "raise-2"
    form := "na'ak=s"
    segments := ["na'ak", "=s"]
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def cin : Form :=
  { id := "lucy1994_cin"
    languageId := "yuca1254"
    parameterId := "bend"
    form := "čin"
    segments := ["čin"]
    source := [
      ⟨"lucy-1994", "(5)"⟩
    ] }

def cin_0 : Form :=
  { id := "lucy1994_cin_0"
    languageId := "yuca1254"
    parameterId := "bend-tr"
    form := "čin=∅"
    segments := ["čin", "=∅"]
    source := [
      ⟨"lucy-1994", "(6)"⟩
    ] }

def cin_lah : Form :=
  { id := "lucy1994_cin_lah"
    languageId := "yuca1254"
    parameterId := "become-bent"
    form := "čin=lah"
    segments := ["čin", "=lah"]
    source := [
      ⟨"lucy-1994", "(5c)"⟩
    ] }

def cil : Form :=
  { id := "lucy1994_cil"
    languageId := "yuca1254"
    parameterId := "lie-down"
    form := "čil"
    segments := ["čil"]
    source := [
      ⟨"lucy-1994", "(7)"⟩
    ] }

def all : List Form := [AFCT, ROOT, CAUS, POS, siit, siit_t, tziib, miis, cheh, paak, kuc, kuc_0, kos, pis, hats, los, ah, ah_s, wen, wen_s, siih, siih_s, kiim, kiim_s, tuub, tuub_s, kaah, kaah_s, chuun, chuun_s, chen, chen_s, hoop, hoop_s, haaw, haaw_s, heel, heel_s, paat, paat_s, maan, maan_s, peek, peek_s, bin, bin_s, taal, taal_s, uul, uul_s, ok, ok_s, luub, luub_s, liik, liik_s, naak, naak_s, cin, cin_0, cin_lah, cil]

def relations : List FormRelation := [
  { id := "lucy1994_siit_t", form := siit, target := siit_t, relation := "affective", source := [
      ⟨"lucy-1994", "(1a)"⟩
    ] },
  { id := "lucy1994_tziib_t", form := tziib, target := AFCT, relation := "affective", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_miis_t", form := miis, target := AFCT, relation := "affective", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_cheh_t", form := cheh, target := AFCT, relation := "affective", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_paak_t", form := paak, target := AFCT, relation := "affective", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_kuc_0", form := kuc, target := kuc_0, relation := "root", source := [
      ⟨"lucy-1994", "(1b)"⟩
    ] },
  { id := "lucy1994_kos_0", form := kos, target := ROOT, relation := "root", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_pis_0", form := pis, target := ROOT, relation := "root", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_hats_0", form := hats, target := ROOT, relation := "root", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_los_0", form := los, target := ROOT, relation := "root", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_ah_s", form := ah, target := ah_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_wen_s", form := wen, target := wen_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_siih_s", form := siih, target := siih_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_kiim_s", form := kiim, target := kiim_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_tuub_s", form := tuub, target := tuub_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_kaah_s", form := kaah, target := kaah_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_chuun_s", form := chuun, target := chuun_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_chen_s", form := chen, target := chen_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_hoop_s", form := hoop, target := hoop_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_haaw_s", form := haaw, target := haaw_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_heel_s", form := heel, target := heel_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_paat_s", form := paat, target := paat_s, relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_maan_s", form := maan, target := maan_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_peek_s", form := peek, target := peek_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_bin_s", form := bin, target := bin_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_taal_s", form := taal, target := taal_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_uul_s", form := uul, target := uul_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_ok_s", form := ok, target := ok_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_luub_s", form := luub, target := luub_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_liik_s", form := liik, target := liik_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_naak_s", form := naak, target := naak_s, relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_cin_0", form := cin, target := cin_0, relation := "root", source := [
      ⟨"lucy-1994", "(6)"⟩
    ] },
  { id := "lucy1994_cin_lah", form := cin, target := cin_lah, relation := "positional", source := [
      ⟨"lucy-1994", "(5c)"⟩
    ] },
  { id := "lucy1994_cil_lah", form := cil, target := POS, relation := "positional", source := [
      ⟨"lucy-1994", "(7)"⟩
    ] }
]

end Lucy1994.Forms
