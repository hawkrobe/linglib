/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Guébie: vowels, ATR, and particle verbs

Lexical substrate for Guébie (Kru; Côte d'Ivoire): the ten-vowel ±ATR inventory
([sande-2022] §3.2, [sande-clem-dabkowski-2026] (1)) and the particle-verb
lexicon ([sande-clem-dabkowski-2026] (10)–(12)). Particle verbs are phrasal
idioms — a prefixing particle plus a verb, with noncompositional meaning; the
particle harmonizes with the verb root in ATR when both are spelled out in the
same phase, and carries its lexical value otherwise.

## Main definitions

* `Guebie.Vowel`, `Guebie.Vowel.atr`: the ten-vowel inventory and its ±ATR split.
* `Guebie.Morpheme`: a transcription with vowel skeleton; `Morpheme.atr` is its
  lexical ATR value (morpheme-internal vowels agree, `Morpheme.ATRUniform`).
* `Guebie.ParticleVerb`, `Guebie.particleVerbs`: the (10) inventory plus the
  (11)–(12) /jɔkʊ/+/ni/ 'see' pair; `harmonizedParticleATR` is the SAuxOV
  surface value.
-/

namespace Guebie

/-- The ten Guébie vowels ([sande-2022] §3.2). Constructor names ASCII-ize the
    IPA (capital = lax −ATR counterpart): `schwa` = ə, `I` = ɪ, `E` = ɛ,
    `O` = ɔ, `U` = ʊ. -/
inductive Vowel where
  | i | e | schwa | o | u
  | I | E | a | O | U
  deriving DecidableEq, Repr

/-- The ±ATR split ([sande-clem-dabkowski-2026] (1)): `+ATR = true`. -/
def Vowel.atr : Vowel → Bool
  | .i | .e | .schwa | .o | .u => true
  | .I | .E | .a | .O | .U => false

/-- A Guébie morpheme: transcription, vowel skeleton, optional gloss. -/
structure Morpheme where
  form   : String
  vowels : List Vowel
  gloss  : Option String := none
  deriving DecidableEq, Repr

/-- The lexical ATR value: the value of the morpheme's (agreeing) vowels;
    `false` for the rare vowelless morphemes. -/
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

/-- The (10) inventory, plus the (11)–(12) /jɔkʊ/+/ni/ pair. -/
def particleVerbs : List ParticleVerb :=
  [⟨mE, tE, "be strong"⟩, ⟨mE, trO, "be long"⟩, ⟨mE, para, "enter"⟩,
   ⟨mE, salI, "tell"⟩, ⟨mE, nu, "understand"⟩,
   ⟨kO, silije, "straighten"⟩, ⟨kO, trO, "be tall"⟩, ⟨kO, salI, "diminish"⟩,
   ⟨kO, djE, "take"⟩, ⟨kO, pulo, "hurry"⟩, ⟨kO, ny, "give"⟩,
   ⟨dakO, ggO, "move"⟩, ⟨dakO, wa, "hide"⟩,
   ⟨jOkU, ni, "see"⟩]

/-- Every morpheme in the lexicon is ATR-uniform. -/
theorem particleVerbs_ATRUniform :
    ∀ pv ∈ particleVerbs, pv.particle.ATRUniform ∧ pv.verb.ATRUniform := by decide

/-- The (11)–(12) alternation: −ATR /jɔkʊ/ surfaces +ATR ([joku]) under harmony
    with the +ATR root /ni/ 'see'. -/
theorem joku_alternation :
    jOkU.atr = false ∧
    (ParticleVerb.mk jOkU ni "see").harmonizedParticleATR = true := by decide

end Guebie
