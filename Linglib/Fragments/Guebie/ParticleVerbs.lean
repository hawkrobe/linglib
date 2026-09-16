/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Segmental.Basic

/-!
# Guébie: vowels, ATR, and particle verbs

Lexical substrate for Guébie (Kru; Côte d'Ivoire): the ten-vowel ±ATR inventory
([sande-2022] §3.2, [sande-clem-dabkowski-2026] (1)) and the particle-verb
lexicon ([sande-clem-dabkowski-2026] (10)–(12)). Particle verbs are phrasal
idioms — a prefixing particle plus a verb, with noncompositional meaning; the
particle harmonizes with the verb root in ATR when both are spelled out in the
same phase, and carries its lexical value otherwise.

## Main definitions

* `Guebie.Vowel`, `Guebie.Vowel.segment`, `Guebie.inventory`: the ten vowels, their
  segments, and the inventory; `Vowel.atr` is the ±ATR split.
* `Guebie.Morpheme`: a transcription with vowel skeleton; `Morpheme.atr` is its
  lexical ATR value (morpheme-internal vowels agree, `Morpheme.ATRUniform`).
* `Guebie.ParticleVerb`, `Guebie.particleVerbs`: the (10) inventory plus the
  (11)–(12) /jɔkʊ/+/ni/ 'see' pair; `harmonizedParticleATR` is the SAuxOV
  surface value.
-/

namespace Guebie

open Phonology

/-- The ten Guébie vowels ([sande-2022] §3.2). Constructor names ASCII-ize the
    IPA (capital = lax −ATR counterpart): `schwa` = ə, `I` = ɪ, `E` = ɛ,
    `O` = ɔ, `U` = ʊ. -/
inductive Vowel where
  | i | e | schwa | o | u
  | I | E | a | O | U
  deriving DecidableEq, Repr, Fintype

/-- A vowel of the given height and backness, rounded or not, with its [ATR] value. -/
private def vowel (ht : Segment.Height) (bk : Segment.Backness) (round atr : Bool) :
    Segment :=
  ((Segment.vowel ht bk).setFeature .round round).setFeature .atr atr

/-- Each vowel's segment: the ±ATR pairs /i ɪ/, /e ɛ/, /o ɔ/, /u ʊ/ and /ə a/
    ([sande-clem-dabkowski-2026] (1)). -/
def Vowel.segment : Vowel → Segment
  | .i => vowel .high .front false true
  | .e => vowel .mid .front false true
  | .schwa => vowel .mid .central false true
  | .o => vowel .mid .back true true
  | .u => vowel .high .back true true
  | .I => vowel .high .front false false
  | .E => vowel .mid .front false false
  | .a => vowel .low .central false false
  | .O => vowel .mid .back true false
  | .U => vowel .high .back true false

/-- The vowel inventory. -/
def inventory : Finset Segment := Finset.univ.image Vowel.segment

/-- The ±ATR split, read off the segment. -/
def Vowel.atr (v : Vowel) : Bool := decide (v.segment.HasValue .atr true)

/-- A Guébie morpheme: transcription, vowel skeleton, optional gloss. -/
structure Morpheme where
  form   : String
  vowels : List Vowel
  gloss  : Option String := none
  deriving DecidableEq, Repr

/-- The lexical ATR value: the value of the morpheme's (agreeing) vowels. The
    rare vowelless morphemes are treated as `[−ATR]`; they neither trigger nor
    block (kɔ-ɲ 'give' surfaces −ATR, (10)). -/
def Morpheme.atr (m : Morpheme) : Bool :=
  (m.vowels.head?.map Vowel.atr).getD false

/-- Morpheme-internal vowels agree in ATR ([sande-clem-dabkowski-2026] §2.1). -/
def Morpheme.ATRUniform (m : Morpheme) : Prop :=
  ∀ v ∈ m.vowels, v.atr = m.atr

instance (m : Morpheme) : Decidable m.ATRUniform := by
  unfold Morpheme.ATRUniform; infer_instance

/-! ### Particles ([sande-clem-dabkowski-2026] (10)–(12))

Underlying forms; surface ATR alternates under harmony (e.g. /mɛ/ → [me] before
a +ATR root, /jɔkʊ/ → [joku]). `dakɔ` and `jɔkʊ` have no independent gloss. -/

def mE : Morpheme := ⟨"mɛ", [.E], some "in"⟩
def kO : Morpheme := ⟨"kɔ", [.O], some "at/to"⟩
def dakO : Morpheme := ⟨"dakɔ", [.a, .O], none⟩
def jOkU : Morpheme := ⟨"jɔkʊ", [.O, .U], none⟩

/-! ### Verbs appearing in the particle-verb inventory -/

def tE : Morpheme := ⟨"tɛ", [.E], some "be strong"⟩
def trO : Morpheme := ⟨"trɔ", [.O], some "be long/tall"⟩
def para : Morpheme := ⟨"para", [.a, .a], none⟩
def salI : Morpheme := ⟨"salɪ", [.a, .I], none⟩
def nu : Morpheme := ⟨"nu", [.u], some "hear"⟩
def silije : Morpheme := ⟨"silije", [.i, .i, .e], none⟩
def djE : Morpheme := ⟨"ɟɛ", [.E], none⟩
def pulo : Morpheme := ⟨"pulo", [.u, .o], some "be fast"⟩
def ny : Morpheme := ⟨"ɲ", [], none⟩
def ggO : Morpheme := ⟨"ggɔ", [.O], none⟩
def wa : Morpheme := ⟨"wa", [.a], none⟩
def ni : Morpheme := ⟨"ni", [.i], some "see"⟩
def ngwOsa : Morpheme := ⟨"ŋwɔsa", [.O, .a], some "scrape"⟩

/-! ### Particle verbs -/

/-- A particle-verb pair: a phrasal idiom with noncompositional meaning
    ([sande-clem-dabkowski-2026] (10)). -/
structure ParticleVerb where
  particle : Morpheme
  verb     : Morpheme
  gloss    : String
  deriving DecidableEq, Repr

/-- The particle's surface ATR in SAuxOV contexts: the verb root's value
    ([sande-clem-dabkowski-2026] (12)). -/
def ParticleVerb.harmonizedParticleATR (pv : ParticleVerb) : Bool :=
  pv.verb.atr

/-- The (10) inventory, plus the (11)–(12) /jɔkʊ/+/ni/ and /jɔkʊ/+/ŋwɔsa/ pairs. -/
def particleVerbs : List ParticleVerb :=
  [⟨mE, tE, "be strong"⟩, ⟨mE, trO, "be long"⟩, ⟨mE, para, "enter"⟩,
   ⟨mE, salI, "tell"⟩, ⟨mE, nu, "understand"⟩,
   ⟨kO, silije, "straighten"⟩, ⟨kO, trO, "be tall"⟩, ⟨kO, salI, "diminish"⟩,
   ⟨kO, djE, "take"⟩, ⟨kO, pulo, "hurry"⟩, ⟨kO, ny, "give"⟩,
   ⟨dakO, ggO, "move"⟩, ⟨dakO, wa, "hide"⟩,
   ⟨jOkU, ni, "see"⟩, ⟨jOkU, ngwOsa, "scrape"⟩]

/-- Every morpheme in the lexicon is ATR-uniform. -/
theorem particleVerbs_ATRUniform :
    ∀ pv ∈ particleVerbs, pv.particle.ATRUniform ∧ pv.verb.ATRUniform := by decide

/-- The (11)–(12) alternation: −ATR /jɔkʊ/ surfaces +ATR ([joku]) under harmony
    with the +ATR root /ni/ 'see'. -/
theorem joku_alternation :
    jOkU.atr = false ∧ (ParticleVerb.mk jOkU ni "see").harmonizedParticleATR = true := by
  decide

end Guebie
