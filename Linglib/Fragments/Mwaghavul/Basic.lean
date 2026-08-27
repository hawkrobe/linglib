import Linglib.Phonology.Tone.Basic
import Linglib.Phonology.Tone.Grammatical

/-!
# Mwaghavul

Mwaghavul (A3 West Chadic, Plateau State, Nigeria; Glottocode mwag1236) contrasts H, M, and
L level tones and an LH rise on syllable TBUs. Verbs are derived from ideophones by two
segmentally null verbalisers whose sole exponents are tone: `verbM` overwrites every TBU
with M, `verbMH` every nonfinal TBU with M and the final one with H; pluractional verbs
reduplicate the ideophone and bear M on every TBU of the reduplicant and H on every TBU of
the base. Data from [akinbo-fwangwar-2026] (7)–(10) and [fwangwar-2018].

## Main definitions

* `Ideophone` — an ideophonic base with its lexical tones and, if it has one, the verbaliser
  of its singular verb.
* `ideophones` — the paper's dataset.
* `deriveVerb` / `derivePluractional` / `intensity` — the singular verb, the pluractional
  verb, and tone-preserving reduplication.
-/

namespace Mwaghavul

open Tone (TRN TBU Spec)

/-- Mwaghavul is a tone language with syllable TBUs. -/
def wordProsodicType : Tone.WordProsodicType := .toneBased
def tbuKind : Tone.TBUKind := .syllable

/-! ### Verbalisers -/

/-- The two lexically specific suppletive allomorphs of the verbaliser ((17)). -/
inductive Verbalizer where
  | m
  | mh
  deriving DecidableEq, Repr

/-- VBZ₁: M on every TBU of the host. -/
def verbM : Spec := { name := "VBZ₁", melody := [.M], window := .whole }

/-- VBZ₂ on a single host: M on every nonfinal TBU, H on the final one. -/
def verbMH : Spec := { name := "VBZ₂", melody := [.M, .H], window := .nonfinalFinal }

/-- The H of VBZ₂ on its own host, as in pluractional verbs. -/
def verbMHBase : Spec := { name := "VBZ₂", melody := [.H], window := .whole }

/-! ### Ideophones -/

/-- An ideophonic base: its form, gloss, the lexical tones of one copy, and the verbaliser of
its singular verb — `none` when only the reduplicated form is verbalised ((9), (10)). -/
structure Ideophone where
  form : String
  gloss : String
  tones : List TRN
  singular : Option Verbalizer
  /-- Inherently reduplicated ((10)): `form` shows both copies, `tones` one. -/
  frozen : Bool := false
  deriving DecidableEq, Repr

/-- A toned Mwaghavul syllable. -/
structure Syl where
  ipa : String
  deriving DecidableEq, Repr

/-- The host of an ideophone as toned TBUs. -/
def Ideophone.host (i : Ideophone) : List (TBU Syl) := i.tones.map fun t => ⟨⟨i.form⟩, t⟩

/-- The singular verb's tones, if the ideophone has a singular verb. -/
def deriveVerb (i : Ideophone) : Option (List TRN) :=
  i.singular.map fun v =>
    (Tone.tonalOverwrite i.host (match v with | .m => verbM | .mh => verbMH)).map (·.tone)

/-- The pluractional verb's tones: the M of VBZ₂ on every TBU of the reduplicant and its H
on every TBU of the base. -/
def derivePluractional (i : Ideophone) : List TRN :=
  (Tone.tonalOverwrite i.host verbM ++ Tone.tonalOverwrite i.host verbMHBase).map (·.tone)

/-- Reduplication without a tonal alternation, expressing intensity ((9)). -/
def intensity (i : Ideophone) : List TRN := i.tones ++ i.tones

theorem derivePluractional_eq (i : Ideophone) :
    derivePluractional i = i.tones.map (fun _ => .M) ++ i.tones.map (fun _ => .H) := by
  simp [derivePluractional, Ideophone.host, verbM, verbMHBase, Tone.tonalOverwrite,
    List.map_map, Function.comp_def]

/-! ### The dataset
[akinbo-fwangwar-2026] (7)–(10). -/

def zut : Ideophone := ⟨"zùt", "how solid substance ejects", [.L], some .m, false⟩
def diis : Ideophone := ⟨"ɗìːs", "sound of blood sucking", [.L], some .m, false⟩
def kwaj : Ideophone := ⟨"kwàj", "sound of bubbling hot water", [.L], some .m, false⟩
def vjar : Ideophone := ⟨"vjàr", "pouring of urine", [.L], some .m, false⟩
def shwer : Ideophone := ⟨"ʃwɛ̀r", "how water falls", [.L], some .m, false⟩
def shoghop : Ideophone := ⟨"ʃɔ̀ɣɔ̀p", "oily", [.L, .L], some .m, false⟩
def vjaghap : Ideophone := ⟨"vjàɣàp", "how liquid ejects from a fruit", [.L, .L], some .m, false⟩
def wulash : Ideophone := ⟨"wùlàʃ", "wide open", [.L, .L], some .m, false⟩
def lubuk : Ideophone := ⟨"lúɓúk", "smooth and soft", [.H, .H], some .m, false⟩
def wulashSmall : Ideophone := ⟨"wúláʃ", "wide open of small thing", [.H, .H], some .m, false⟩

def bishol : Ideophone := ⟨"bɨ̀ʃɔ̀l", "shabbily dressed", [.L, .L], some .mh, false⟩
def kitish : Ideophone := ⟨"kɨ̀tìʃ", "untidy", [.L, .L], some .mh, false⟩
def kodong : Ideophone := ⟨"kɔ̀ɗɔ̀ŋ", "walking effortfully", [.L, .L], some .mh, false⟩
def kitshor : Ideophone := ⟨"kɨ̀tʃɔ̀r", "old-sounding vehicle", [.L, .L], some .mh, false⟩
def korjong : Ideophone := ⟨"kɔ̀rjɔ̀ŋ", "crooked", [.L, .L], some .mh, false⟩
def mondos : Ideophone := ⟨"mɔ̀ndɔ̀s", "big nose", [.L, .L], some .mh, false⟩
def vwaplas : Ideophone := ⟨"vwàplàs", "oversized", [.L, .L], some .mh, false⟩
def jalpat : Ideophone := ⟨"jàlpàt", "hanging loose", [.L, .L], some .mh, false⟩
def hanlaghap : Ideophone := ⟨"háŋláɣáp", "light-weighted", [.H, .H, .H], some .mh, false⟩
def hamhoghosh : Ideophone :=
  ⟨"hámhɔ́ɣɔ́ʃ", "dryness of cracked feet", [.H, .H, .H], some .mh, false⟩
def jegherek : Ideophone := ⟨"dʒɛ́ɣɛ́rɛ́k", "thin, fragile", [.H, .H, .H], some .mh, false⟩
def gokshirok : Ideophone := ⟨"gɔ̀kʃìrɔ̀k", "old or abnormal", [.L, .L, .L], some .mh, false⟩
def zongilong : Ideophone := ⟨"zɔ̀ngɨ̀lɔ̀ŋ", "long and thin", [.L, .L, .L], some .mh, false⟩
def salmutat : Ideophone := ⟨"sàlmùtàt", "sluggish", [.L, .L, .L], some .mh, false⟩
def dighirik : Ideophone := ⟨"dɨ̀ɣɨ̀rɨ̀k", "being big and lazy", [.L, .L, .L], some .mh, false⟩

def jumHeavy : Ideophone := ⟨"dʒùm", "heavy water plop", [.L], none, false⟩
def kurashSlow : Ideophone := ⟨"kùràʃ", "slow scratching sound", [.L, .L], none, false⟩
def kwaasSlow : Ideophone := ⟨"kwàːs", "slow foot-dragging sound", [.L], none, false⟩
def tirat : Ideophone := ⟨"tɨ̀ràt", "sound of sipping", [.L, .L], none, false⟩
def jumLight : Ideophone := ⟨"dʒúm", "light water plop", [.H], none, false⟩
def kurashFast : Ideophone := ⟨"kúráʃ", "fast scratching sound", [.H, .H], none, false⟩
def kwaasFast : Ideophone := ⟨"kwáːs", "fast foot-dragging sound", [.H], none, false⟩
def weng : Ideophone := ⟨"wɛ́ŋ", "sound of buzzing", [.H], none, false⟩

def girgir : Ideophone := ⟨"gɨ̀r-gɨ̀r", "sound of a moving truck", [.L], none, true⟩
def wurwur : Ideophone := ⟨"wùr-wùr", "in a rush", [.L], none, true⟩
def tengteng : Ideophone := ⟨"tɛ̀ŋ-tɛ̀ŋ", "zigzag", [.L], none, true⟩
def zetzet : Ideophone := ⟨"zɛ̀t-zɛ̀t", "hurried walk", [.L], none, true⟩
def wuretwuret : Ideophone := ⟨"wùrɛ̀t-wùrɛ̀t", "fast walk", [.L, .L], none, true⟩
def shuretshuret : Ideophone := ⟨"ʃùrɛ̀t-ʃùrɛ̀t", "profusely crying", [.L, .L], none, true⟩
def kipetkipet : Ideophone := ⟨"kɨ́pɛ́t-kɨ́pɛ́t", "flip-flop sound", [.H, .H], none, true⟩
def wulengwuleng : Ideophone := ⟨"wúlɛ́ŋ-wúlɛ́ŋ", "smart look", [.H, .H], none, true⟩
def zonzon : Ideophone := ⟨"zɔ́n-zɔ́n", "aimless movement", [.H], none, true⟩

/-- The paper's dataset ((7)–(10)); (10c) *ram-ram*, printed without tone marks, is omitted. -/
def ideophones : List Ideophone :=
  [zut, diis, kwaj, vjar, shwer, shoghop, vjaghap, wulash, lubuk, wulashSmall,
    bishol, kitish, kodong, kitshor, korjong, mondos, vwaplas, jalpat, hanlaghap, hamhoghosh,
    jegherek, gokshirok, zongilong, salmutat, dighirik,
    jumHeavy, kurashSlow, kwaasSlow, tirat, jumLight, kurashFast, kwaasFast, weng,
    girgir, wurwur, tengteng, zetzet, wuretwuret, shuretshuret, kipetkipet, wulengwuleng,
    zonzon]

end Mwaghavul
