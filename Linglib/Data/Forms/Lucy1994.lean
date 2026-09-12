import Linglib.Data.Forms.Schema

/-!
# `Lucy1994` — CLDF form data

Auto-generated from `Linglib/Data/Forms/Lucy1994.json` by
`scripts/gen_forms.py`. Do not edit by hand; edit the JSON and re-run the
generator. Consumers import this module; declarations live in
`namespace Lucy1994.Forms`.
-/

namespace Lucy1994.Forms

open Data.Forms

def AFCT : Form :=
  { id := "lucy1994_AFCT"
    languageId := "yuca1254"
    parameterId := "AFCT"
    form := "=t"
    segments := ["=t"]
    comment := "the affective suffix, transitivising an agent-salient root"
    source := [
      ⟨"lucy-1994", "(1a)"⟩
    ] }

def ROOT : Form :=
  { id := "lucy1994_ROOT"
    languageId := "yuca1254"
    parameterId := "ROOT"
    form := "=∅"
    segments := ["=∅"]
    comment := "zero derivation: the root alone supports a transitive stem"
    source := [
      ⟨"lucy-1994", "(1b)"⟩
    ] }

def CAUS : Form :=
  { id := "lucy1994_CAUS"
    languageId := "yuca1254"
    parameterId := "CAUS"
    form := "=s"
    segments := ["=s"]
    comment := "the causative suffix, transitivising a patient-salient root"
    source := [
      ⟨"lucy-1994", "(1c)"⟩
    ] }

def POS : Form :=
  { id := "lucy1994_POS"
    languageId := "yuca1254"
    parameterId := "POS"
    form := "=lah"
    segments := ["=lah"]
    comment := "the positional derivation, =tal in the imperfective"
    source := [
      ⟨"lucy-1994", "(5)"⟩
    ] }

def siit : Form :=
  { id := "lucy1994_siit"
    languageId := "yuca1254"
    parameterId := "jump"
    form := "síit'"
    segments := ["síit'"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(1a)"⟩
    ] }

def siit_t : Form :=
  { id := "lucy1994_siit_t"
    languageId := "yuca1254"
    parameterId := "jump-over"
    form := "síit'=t"
    segments := ["síit'", "=t"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(1a)"⟩
    ] }

def tziib : Form :=
  { id := "lucy1994_tziib"
    languageId := "yuca1254"
    parameterId := "write"
    form := "¢'iib'"
    segments := ["¢'iib'"]
    comment := ""
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def miis : Form :=
  { id := "lucy1994_miis"
    languageId := "yuca1254"
    parameterId := "sweep"
    form := "mìis"
    segments := ["mìis"]
    comment := ""
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def cheh : Form :=
  { id := "lucy1994_cheh"
    languageId := "yuca1254"
    parameterId := "smile"
    form := "čé'eh"
    segments := ["čé'eh"]
    comment := ""
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def paak : Form :=
  { id := "lucy1994_paak"
    languageId := "yuca1254"
    parameterId := "weed"
    form := "páak"
    segments := ["páak"]
    comment := ""
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def kuc : Form :=
  { id := "lucy1994_kuc"
    languageId := "yuca1254"
    parameterId := "carry"
    form := "kuč"
    segments := ["kuč"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(1b)"⟩
    ] }

def kuc_0 : Form :=
  { id := "lucy1994_kuc_0"
    languageId := "yuca1254"
    parameterId := "carry-tr"
    form := "kuč=∅"
    segments := ["kuč", "=∅"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(1b)"⟩
    ] }

def kos : Form :=
  { id := "lucy1994_kos"
    languageId := "yuca1254"
    parameterId := "cut"
    form := "k'os"
    segments := ["k'os"]
    comment := ""
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def pis : Form :=
  { id := "lucy1994_pis"
    languageId := "yuca1254"
    parameterId := "measure"
    form := "p'is"
    segments := ["p'is"]
    comment := ""
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def hats : Form :=
  { id := "lucy1994_hats"
    languageId := "yuca1254"
    parameterId := "whip"
    form := "ha¢"
    segments := ["ha¢"]
    comment := ""
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def los : Form :=
  { id := "lucy1994_los"
    languageId := "yuca1254"
    parameterId := "punch"
    form := "loš"
    segments := ["loš"]
    comment := ""
    source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] }

def ah : Form :=
  { id := "lucy1994_ah"
    languageId := "yuca1254"
    parameterId := "awaken"
    form := "'ah"
    segments := ["'ah"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def ah_s : Form :=
  { id := "lucy1994_ah_s"
    languageId := "yuca1254"
    parameterId := "wake-someone"
    form := "'ah=s"
    segments := ["'ah", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def wen : Form :=
  { id := "lucy1994_wen"
    languageId := "yuca1254"
    parameterId := "fall-asleep"
    form := "wen"
    segments := ["wen"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def wen_s : Form :=
  { id := "lucy1994_wen_s"
    languageId := "yuca1254"
    parameterId := "put-to-sleep"
    form := "ween=s"
    segments := ["ween", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def siih : Form :=
  { id := "lucy1994_siih"
    languageId := "yuca1254"
    parameterId := "be-born"
    form := "siih"
    segments := ["siih"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def siih_s : Form :=
  { id := "lucy1994_siih_s"
    languageId := "yuca1254"
    parameterId := "give-birth"
    form := "siih=s"
    segments := ["siih", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def kiim : Form :=
  { id := "lucy1994_kiim"
    languageId := "yuca1254"
    parameterId := "die"
    form := "kíim"
    segments := ["kíim"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def kiim_s : Form :=
  { id := "lucy1994_kiim_s"
    languageId := "yuca1254"
    parameterId := "kill"
    form := "kíim=s"
    segments := ["kíim", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def tuub : Form :=
  { id := "lucy1994_tuub"
    languageId := "yuca1254"
    parameterId := "forget"
    form := "tú'ub'"
    segments := ["tú'ub'"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def tuub_s : Form :=
  { id := "lucy1994_tuub_s"
    languageId := "yuca1254"
    parameterId := "distract"
    form := "tú'ub'=s"
    segments := ["tú'ub'", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def kaah : Form :=
  { id := "lucy1994_kaah"
    languageId := "yuca1254"
    parameterId := "remember"
    form := "k'a'ah"
    segments := ["k'a'ah"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def kaah_s : Form :=
  { id := "lucy1994_kaah_s"
    languageId := "yuca1254"
    parameterId := "remind"
    form := "k'á'ah=s"
    segments := ["k'á'ah", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def chuun : Form :=
  { id := "lucy1994_chuun"
    languageId := "yuca1254"
    parameterId := "begin-activity"
    form := "ču'un"
    segments := ["ču'un"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def chuun_s : Form :=
  { id := "lucy1994_chuun_s"
    languageId := "yuca1254"
    parameterId := "cause-to-begin"
    form := "ču'un=s"
    segments := ["ču'un", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def chen : Form :=
  { id := "lucy1994_chen"
    languageId := "yuca1254"
    parameterId := "stop"
    form := "č'en"
    segments := ["č'en"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def chen_s : Form :=
  { id := "lucy1994_chen_s"
    languageId := "yuca1254"
    parameterId := "cause-to-stop"
    form := "č'en=s"
    segments := ["č'en", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def hoop : Form :=
  { id := "lucy1994_hoop"
    languageId := "yuca1254"
    parameterId := "begin"
    form := "hó'op'"
    segments := ["hó'op'"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def hoop_s : Form :=
  { id := "lucy1994_hoop_s"
    languageId := "yuca1254"
    parameterId := "cause-to-start"
    form := "hó'op'=s"
    segments := ["hó'op'", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def haaw : Form :=
  { id := "lucy1994_haaw"
    languageId := "yuca1254"
    parameterId := "cease"
    form := "háaw"
    segments := ["háaw"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def haaw_s : Form :=
  { id := "lucy1994_haaw_s"
    languageId := "yuca1254"
    parameterId := "revoke"
    form := "háaw=s"
    segments := ["háaw", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def heel : Form :=
  { id := "lucy1994_heel"
    languageId := "yuca1254"
    parameterId := "rest"
    form := "hé'el"
    segments := ["hé'el"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def heel_s : Form :=
  { id := "lucy1994_heel_s"
    languageId := "yuca1254"
    parameterId := "rest-tr"
    form := "hé'e(l)=s"
    segments := ["hé'e(l)", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def paat : Form :=
  { id := "lucy1994_paat"
    languageId := "yuca1254"
    parameterId := "remain"
    form := "p'át"
    segments := ["p'át"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def paat_s : Form :=
  { id := "lucy1994_paat_s"
    languageId := "yuca1254"
    parameterId := "abandon"
    form := "p'át=s"
    segments := ["p'át", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(2)"⟩
    ] }

def maan : Form :=
  { id := "lucy1994_maan"
    languageId := "yuca1254"
    parameterId := "pass-by"
    form := "máan"
    segments := ["máan"]
    comment := "marked # in (4): lacks the -Vl imperfective"
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def maan_s : Form :=
  { id := "lucy1994_maan_s"
    languageId := "yuca1254"
    parameterId := "transport"
    form := "maan=s"
    segments := ["maan", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def peek : Form :=
  { id := "lucy1994_peek"
    languageId := "yuca1254"
    parameterId := "move"
    form := "péek"
    segments := ["péek"]
    comment := "marked # in (4): lacks the -Vl imperfective"
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def peek_s : Form :=
  { id := "lucy1994_peek_s"
    languageId := "yuca1254"
    parameterId := "cause-to-move"
    form := "pek=s"
    segments := ["pek", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def bin : Form :=
  { id := "lucy1994_bin"
    languageId := "yuca1254"
    parameterId := "go"
    form := "b'in"
    segments := ["b'in"]
    comment := "marked # in (4): lacks the -Vl imperfective"
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def bin_s : Form :=
  { id := "lucy1994_bin_s"
    languageId := "yuca1254"
    parameterId := "take"
    form := "bi(n)=s"
    segments := ["bi(n)", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def taal : Form :=
  { id := "lucy1994_taal"
    languageId := "yuca1254"
    parameterId := "come"
    form := "tàal"
    segments := ["tàal"]
    comment := "marked # in (4): lacks the -Vl imperfective"
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def taal_s : Form :=
  { id := "lucy1994_taal_s"
    languageId := "yuca1254"
    parameterId := "bring"
    form := "taa(l)=s"
    segments := ["taa(l)", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def uul : Form :=
  { id := "lucy1994_uul"
    languageId := "yuca1254"
    parameterId := "arrive-here"
    form := "'ú'ul"
    segments := ["'ú'ul"]
    comment := "marked # in (4): lacks the -Vl imperfective"
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def uul_s : Form :=
  { id := "lucy1994_uul_s"
    languageId := "yuca1254"
    parameterId := "bring-here"
    form := "'u'uh=s"
    segments := ["'u'uh", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def ok : Form :=
  { id := "lucy1994_ok"
    languageId := "yuca1254"
    parameterId := "enter"
    form := "'ok"
    segments := ["'ok"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def ok_s : Form :=
  { id := "lucy1994_ok_s"
    languageId := "yuca1254"
    parameterId := "move-in"
    form := "'ook=s"
    segments := ["'ook", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def luub : Form :=
  { id := "lucy1994_luub"
    languageId := "yuca1254"
    parameterId := "fall"
    form := "lúub'"
    segments := ["lúub'"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def luub_s : Form :=
  { id := "lucy1994_luub_s"
    languageId := "yuca1254"
    parameterId := "fell"
    form := "luub'=s"
    segments := ["luub'", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def liik : Form :=
  { id := "lucy1994_liik"
    languageId := "yuca1254"
    parameterId := "rise"
    form := "líik'"
    segments := ["líik'"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def liik_s : Form :=
  { id := "lucy1994_liik_s"
    languageId := "yuca1254"
    parameterId := "raise"
    form := "lii(k)'=s"
    segments := ["lii(k)'", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def naak : Form :=
  { id := "lucy1994_naak"
    languageId := "yuca1254"
    parameterId := "ascend"
    form := "ná'ak"
    segments := ["ná'ak"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def naak_s : Form :=
  { id := "lucy1994_naak_s"
    languageId := "yuca1254"
    parameterId := "raise-2"
    form := "na'ak=s"
    segments := ["na'ak", "=s"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(4)"⟩
    ] }

def cin : Form :=
  { id := "lucy1994_cin"
    languageId := "yuca1254"
    parameterId := "bend"
    form := "čin"
    segments := ["čin"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(5)"⟩
    ] }

def cin_0 : Form :=
  { id := "lucy1994_cin_0"
    languageId := "yuca1254"
    parameterId := "bend-tr"
    form := "čin=∅"
    segments := ["čin", "=∅"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(6)"⟩
    ] }

def cin_lah : Form :=
  { id := "lucy1994_cin_lah"
    languageId := "yuca1254"
    parameterId := "become-bent"
    form := "čin=lah"
    segments := ["čin", "=lah"]
    comment := "=tal in the imperfective (5a)"
    source := [
      ⟨"lucy-1994", "(5c)"⟩
    ] }

def cil : Form :=
  { id := "lucy1994_cil"
    languageId := "yuca1254"
    parameterId := "lie-down"
    form := "čil"
    segments := ["čil"]
    comment := ""
    source := [
      ⟨"lucy-1994", "(7)"⟩
    ] }

def all : List Form := [AFCT, ROOT, CAUS, POS, siit, siit_t, tziib, miis, cheh, paak, kuc, kuc_0, kos, pis, hats, los, ah, ah_s, wen, wen_s, siih, siih_s, kiim, kiim_s, tuub, tuub_s, kaah, kaah_s, chuun, chuun_s, chen, chen_s, hoop, hoop_s, haaw, haaw_s, heel, heel_s, paat, paat_s, maan, maan_s, peek, peek_s, bin, bin_s, taal, taal_s, uul, uul_s, ok, ok_s, luub, luub_s, liik, liik_s, naak, naak_s, cin, cin_0, cin_lah, cil]

def parameters : List Parameter := [
  { id := "AFCT", name := "affective derivation", description := "" },
  { id := "ROOT", name := "root transitive", description := "" },
  { id := "CAUS", name := "causative derivation", description := "" },
  { id := "POS", name := "positional derivation", description := "" },
  { id := "jump", name := "jump", description := "" },
  { id := "jump-over", name := "jump (over)", description := "" },
  { id := "write", name := "write", description := "" },
  { id := "sweep", name := "sweep", description := "" },
  { id := "smile", name := "smile", description := "" },
  { id := "weed", name := "weed", description := "" },
  { id := "carry", name := "carry", description := "" },
  { id := "carry-tr", name := "carry (someone)", description := "" },
  { id := "cut", name := "cut", description := "" },
  { id := "measure", name := "measure", description := "" },
  { id := "whip", name := "whip", description := "" },
  { id := "punch", name := "punch", description := "" },
  { id := "awaken", name := "(a)wake(n)", description := "" },
  { id := "wake-someone", name := "wake (someone)", description := "" },
  { id := "fall-asleep", name := "(fall a)sleep", description := "" },
  { id := "put-to-sleep", name := "put to sleep", description := "" },
  { id := "be-born", name := "be born", description := "" },
  { id := "give-birth", name := "give birth, bear", description := "" },
  { id := "die", name := "die", description := "" },
  { id := "kill", name := "kill", description := "" },
  { id := "forget", name := "forget", description := "" },
  { id := "distract", name := "distract, cause to forget", description := "" },
  { id := "remember", name := "remember", description := "" },
  { id := "remind", name := "remind, mention, invoke", description := "" },
  { id := "begin-activity", name := "begin activity", description := "" },
  { id := "cause-to-begin", name := "cause to begin", description := "" },
  { id := "stop", name := "stop, cease", description := "" },
  { id := "cause-to-stop", name := "cause to stop, suspend", description := "" },
  { id := "begin", name := "begin, start", description := "" },
  { id := "cause-to-start", name := "cause to begin", description := "" },
  { id := "cease", name := "stop, cease, heal", description := "" },
  { id := "revoke", name := "stop, revoke, medicate", description := "" },
  { id := "rest", name := "rest, stop at", description := "" },
  { id := "rest-tr", name := "rest", description := "" },
  { id := "remain", name := "remain", description := "" },
  { id := "abandon", name := "abandon", description := "" },
  { id := "pass-by", name := "pass by", description := "" },
  { id := "transport", name := "pass, transfer, transport", description := "" },
  { id := "move", name := "move, vibrate", description := "" },
  { id := "cause-to-move", name := "cause to move, vibrate", description := "" },
  { id := "go", name := "go", description := "" },
  { id := "take", name := "take", description := "" },
  { id := "come", name := "come (here)", description := "" },
  { id := "bring", name := "bring", description := "" },
  { id := "arrive-here", name := "arrive (here)", description := "" },
  { id := "bring-here", name := "bring it to here", description := "" },
  { id := "enter", name := "enter, intrude", description := "" },
  { id := "move-in", name := "move it in(to)", description := "" },
  { id := "fall", name := "fall", description := "" },
  { id := "fell", name := "fell", description := "" },
  { id := "rise", name := "(a)rise, ascend", description := "" },
  { id := "raise", name := "raise, lift, put away", description := "" },
  { id := "ascend", name := "(a)rise, ascend", description := "" },
  { id := "raise-2", name := "raise", description := "" },
  { id := "bend", name := "bow, bend down, bend over", description := "" },
  { id := "bend-tr", name := "bend (something)", description := "" },
  { id := "become-bent", name := "become bent down", description := "" },
  { id := "lie-down", name := "lie down, lying down", description := "" }
]

def relations : List FormRelation := [
  { id := "lucy1994_siit_t", formId := "lucy1994_siit", targetId := "lucy1994_siit_t", relation := "affective", source := [
      ⟨"lucy-1994", "(1a)"⟩
    ] },
  { id := "lucy1994_tziib_t", formId := "lucy1994_tziib", targetId := "lucy1994_AFCT", relation := "affective", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_miis_t", formId := "lucy1994_miis", targetId := "lucy1994_AFCT", relation := "affective", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_cheh_t", formId := "lucy1994_cheh", targetId := "lucy1994_AFCT", relation := "affective", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_paak_t", formId := "lucy1994_paak", targetId := "lucy1994_AFCT", relation := "affective", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_kuc_0", formId := "lucy1994_kuc", targetId := "lucy1994_kuc_0", relation := "root", source := [
      ⟨"lucy-1994", "(1b)"⟩
    ] },
  { id := "lucy1994_kos_0", formId := "lucy1994_kos", targetId := "lucy1994_ROOT", relation := "root", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_pis_0", formId := "lucy1994_pis", targetId := "lucy1994_ROOT", relation := "root", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_hats_0", formId := "lucy1994_hats", targetId := "lucy1994_ROOT", relation := "root", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_los_0", formId := "lucy1994_los", targetId := "lucy1994_ROOT", relation := "root", source := [
      ⟨"lucy-1994", "p. 629"⟩
    ] },
  { id := "lucy1994_ah_s", formId := "lucy1994_ah", targetId := "lucy1994_ah_s", relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_wen_s", formId := "lucy1994_wen", targetId := "lucy1994_wen_s", relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_siih_s", formId := "lucy1994_siih", targetId := "lucy1994_siih_s", relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_kiim_s", formId := "lucy1994_kiim", targetId := "lucy1994_kiim_s", relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_tuub_s", formId := "lucy1994_tuub", targetId := "lucy1994_tuub_s", relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_kaah_s", formId := "lucy1994_kaah", targetId := "lucy1994_kaah_s", relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_chuun_s", formId := "lucy1994_chuun", targetId := "lucy1994_chuun_s", relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_chen_s", formId := "lucy1994_chen", targetId := "lucy1994_chen_s", relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_hoop_s", formId := "lucy1994_hoop", targetId := "lucy1994_hoop_s", relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_haaw_s", formId := "lucy1994_haaw", targetId := "lucy1994_haaw_s", relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_heel_s", formId := "lucy1994_heel", targetId := "lucy1994_heel_s", relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_paat_s", formId := "lucy1994_paat", targetId := "lucy1994_paat_s", relation := "causative", source := [
      ⟨"lucy-1994", "(2)"⟩
    ] },
  { id := "lucy1994_maan_s", formId := "lucy1994_maan", targetId := "lucy1994_maan_s", relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_peek_s", formId := "lucy1994_peek", targetId := "lucy1994_peek_s", relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_bin_s", formId := "lucy1994_bin", targetId := "lucy1994_bin_s", relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_taal_s", formId := "lucy1994_taal", targetId := "lucy1994_taal_s", relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_uul_s", formId := "lucy1994_uul", targetId := "lucy1994_uul_s", relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_ok_s", formId := "lucy1994_ok", targetId := "lucy1994_ok_s", relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_luub_s", formId := "lucy1994_luub", targetId := "lucy1994_luub_s", relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_liik_s", formId := "lucy1994_liik", targetId := "lucy1994_liik_s", relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_naak_s", formId := "lucy1994_naak", targetId := "lucy1994_naak_s", relation := "causative", source := [
      ⟨"lucy-1994", "(4)"⟩
    ] },
  { id := "lucy1994_cin_0", formId := "lucy1994_cin", targetId := "lucy1994_cin_0", relation := "root", source := [
      ⟨"lucy-1994", "(6)"⟩
    ] },
  { id := "lucy1994_cin_lah", formId := "lucy1994_cin", targetId := "lucy1994_cin_lah", relation := "positional", source := [
      ⟨"lucy-1994", "(5c)"⟩
    ] },
  { id := "lucy1994_cil_lah", formId := "lucy1994_cil", targetId := "lucy1994_POS", relation := "positional", source := [
      ⟨"lucy-1994", "(7)"⟩
    ] }
]

end Lucy1994.Forms
