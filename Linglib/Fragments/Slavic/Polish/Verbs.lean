import Linglib.Morphology.Morph
import Linglib.Syntax.Category.Verb.Stem

/-!
# Polish Verbal Lexicon

Prefix morphs and verb-stem entries for the Polish verbal-prefix data
of [jablonska-2004] (and the Polish examples of [svenonius-2004]).
Prefixes carry only their form; the reading of *po-* per occurrence
(delimitative vs distributive vs inceptive) is [jablonska-2004]'s
central analytical question and lives in `Studies/Jablonska2004.lean`,
as does the assignment of stems to verbalizer classes. Aspect values are
the dictionary-consensus ones: simplex stems are imperfective except the
semelfactives.
-/

namespace Polish.Verbs

open Morphology
open Verb (Stem)

/-! ### Prefixes -/

/-- The prefix *po-*. -/
def po : Morph := .pref "po"

/-- The prefix *za-*. -/
def za : Morph := .pref "za"

/-- The prefix *w-* 'in'. -/
def w : Morph := .pref "w"

/-- The prefix *prze-* 'through'. -/
def prze : Morph := .pref "prze"

/-- The prefix *ob-* 'around'. -/
def ob : Morph := .pref "ob"

/-- The prefix *wy-* 'out'. -/
def wy : Morph := .pref "wy"

/-- The prefix *pod-* 'under'. -/
def pod : Morph := .pref "pod"

/-- The prefix *do-* 'to'. -/
def do_ : Morph := .pref "do"

/-- The prefix *z-*. -/
def z : Morph := .pref "z"

/-- The prefix *s-*, the voiceless allomorph of *z-*. -/
def s : Morph := .pref "s"

/-! ### Verb stems -/

/-- *siedzieć* 'sit' (imperfective, stative). -/
def siedziec : Stem := ⟨"siedzieć", .imperfective, "sit"⟩

/-- *kochać* 'love' (imperfective, stative). -/
def kochac : Stem := ⟨"kochać", .imperfective, "love"⟩

/-- *lubić* 'like' (imperfective, stative). -/
def lubic : Stem := ⟨"lubić", .imperfective, "like"⟩

/-- *jaśnieć* 'be bright' (imperfective, low -ej- verbalizer stem). -/
def jasniec : Stem := ⟨"jaśnieć", .imperfective, "be bright"⟩

/-- *siwieć* 'turn grey' (imperfective). -/
def siwiec : Stem := ⟨"siwieć", .imperfective, "turn grey"⟩

/-- *ciemnieć* 'get dark' (imperfective). -/
def ciemniec : Stem := ⟨"ciemnieć", .imperfective, "get dark"⟩

/-- *drożeć* 'get expensive' (imperfective). -/
def drozec : Stem := ⟨"drożeć", .imperfective, "get expensive"⟩

/-- *babieć* 'become effeminated' (imperfective). -/
def babiec : Stem := ⟨"babieć", .imperfective, "become effeminated"⟩

/-- *smutnieć* 'get sad' (imperfective). -/
def smutniec : Stem := ⟨"smutnieć", .imperfective, "get sad"⟩

/-- *dziczeć* 'go wild' (imperfective). -/
def dziczec : Stem := ⟨"dziczeć", .imperfective, "go wild"⟩

/-- *marznąć* 'freeze' (imperfective, inchoative). -/
def marznac : Stem := ⟨"marznąć", .imperfective, "freeze"⟩

/-- *głuchnąć* 'go deaf' (imperfective, inchoative). -/
def gluchnac : Stem := ⟨"głuchnąć", .imperfective, "go deaf"⟩

/-- *więdnąć* 'wither' (imperfective, inchoative). -/
def wiednac : Stem := ⟨"więdnąć", .imperfective, "wither"⟩

/-- *ślepnąć* 'go blind' (imperfective, inchoative). -/
def slepnac : Stem := ⟨"ślepnąć", .imperfective, "go blind"⟩

/-- *gasnąć* 'go out' (imperfective, inchoative). -/
def gasnac : Stem := ⟨"gasnąć", .imperfective, "go out"⟩

/-- *warknąć* 'snarl once' (perfective, semelfactive). -/
def warknac : Stem := ⟨"warknąć", .perfective, "snarl once"⟩

/-- *kopnąć* 'kick once' (perfective, semelfactive). -/
def kopnac : Stem := ⟨"kopnąć", .perfective, "kick once"⟩

/-- *machnąć* 'wave once' (perfective, semelfactive). -/
def machnac : Stem := ⟨"machnąć", .perfective, "wave once"⟩

/-- *miauknąć* 'meow once' (perfective, semelfactive). -/
def miauknac : Stem := ⟨"miauknąć", .perfective, "meow once"⟩

/-- *szepnąć* 'whisper once' (perfective, semelfactive). -/
def szepnac : Stem := ⟨"szepnąć", .perfective, "whisper once"⟩

/-- *czytać* 'read' (imperfective). -/
def czytac : Stem := ⟨"czytać", .imperfective, "read"⟩

/-- *grać* 'play' (imperfective). -/
def grac : Stem := ⟨"grać", .imperfective, "play"⟩

/-- *palić* 'smoke' (imperfective). -/
def palic : Stem := ⟨"palić", .imperfective, "smoke"⟩

/-- *chować* 'hide' (imperfective). -/
def chowac : Stem := ⟨"chować", .imperfective, "hide"⟩

/-- *pisać* 'write' (imperfective). -/
def pisac : Stem := ⟨"pisać", .imperfective, "write"⟩

/-- *śpiewać* 'sing' (imperfective). -/
def spiewac : Stem := ⟨"śpiewać", .imperfective, "sing"⟩

/-- *kopać* 'dig' (imperfective). -/
def kopac : Stem := ⟨"kopać", .imperfective, "dig"⟩

/-- *dmuchać* 'blow' (imperfective). -/
def dmuchac : Stem := ⟨"dmuchać", .imperfective, "blow"⟩

/-- *tracić* 'lose' (imperfective). -/
def tracic : Stem := ⟨"tracić", .imperfective, "lose"⟩

/-- *robić* 'make' (imperfective). -/
def robic : Stem := ⟨"robić", .imperfective, "make"⟩

/-- *brudzić* 'dirty' (imperfective). -/
def brudzic : Stem := ⟨"brudzić", .imperfective, "dirty"⟩

/-- *bić* 'beat' (imperfective). -/
def bic : Stem := ⟨"bić", .imperfective, "beat"⟩

/-- *chwalić* 'praise' (imperfective). -/
def chwalic : Stem := ⟨"chwalić", .imperfective, "praise"⟩

/-- *równać* 'level' (imperfective). -/
def rownac : Stem := ⟨"równać", .imperfective, "level"⟩

/-- *twierdzić* 'claim' (imperfective). -/
def twierdzic : Stem := ⟨"twierdzić", .imperfective, "claim"⟩

/-- *iść* 'go' (imperfective, directed motion). -/
def isc : Stem := ⟨"iść", .imperfective, "go"⟩

/-- *biec* 'run' (imperfective, directed motion). -/
def biec : Stem := ⟨"biec", .imperfective, "run"⟩

/-- *lecieć* 'fly' (imperfective, directed motion). -/
def leciec : Stem := ⟨"lecieć", .imperfective, "fly"⟩

/-- *ciągnąć* 'drag' (imperfective, directed motion). -/
def ciagnac : Stem := ⟨"ciągnąć", .imperfective, "drag"⟩

/-- *płynąć* 'swim' (imperfective, directed motion). -/
def plynac : Stem := ⟨"płynąć", .imperfective, "swim"⟩

/-- *chodzić* 'walk' (imperfective, non-directed motion). -/
def chodzic : Stem := ⟨"chodzić", .imperfective, "walk"⟩

/-- *biegać* 'run' (imperfective, non-directed motion). -/
def biegac : Stem := ⟨"biegać", .imperfective, "run"⟩

/-- *latać* 'fly' (imperfective, non-directed motion). -/
def latac : Stem := ⟨"latać", .imperfective, "fly"⟩

/-- *ciągać* 'drag' (imperfective, non-directed motion). -/
def ciagac : Stem := ⟨"ciągać", .imperfective, "drag"⟩

/-- *pływać* 'swim' (imperfective, non-directed motion). -/
def plywac : Stem := ⟨"pływać", .imperfective, "swim"⟩

end Polish.Verbs
