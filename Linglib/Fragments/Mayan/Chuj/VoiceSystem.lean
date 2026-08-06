import Linglib.Syntax.Voice.Basic

/-!
# Chuj Voice System Profile

Theory-neutral typological profile of the Chuj voice system: a voice
inventory any framework can consume via the `Voice.*` queries. Chuj is
four-way asymmetrical (Ø, -w, -ch, -j) — active transitive Ø is basic
(√TV roots form bare transitive stems), and each voice form is built
directly from root + v/Voice⁰ rather than derived from another
([coon-2019] p. 77), a caveat on the derivational reading of the
symmetry binary. The `promotes` field records which argument surfaces
as the sole absolutive argument of the derived stem, not movement to a
pivot position: unlike pivot systems (Toba Batak, Tagalog), Chuj voice
controls whether the external argument is overt, implicit, or absent.

## Main declarations

* `Chuj.VoiceSuffix`: the four voice suffixes (Ø, -ch, -j, -w).
* `Chuj.VoiceSystem.voices`: the four voice entries.
* `Chuj.VoiceSystem.symmetry`: the asymmetrical classification.
-/

namespace Chuj

/-- The four voice suffixes in Chuj (ex. (78), p. 76). -ch and -w are
    [coon-2019]'s decomposed morphemes: the attested stems are *-chaj*
    and *-waj*, analyzed as -ch and -w plus -aj (table (58), p. 66;
    §4.2). -/
inductive VoiceSuffix where
  /-- Ø: active transitive. -/
  | null
  /-- -ch: passive with implicit agent. -/
  | ch
  /-- -j: agentless passive. -/
  | j
  /-- -w: antipassive / verbalizer. -/
  | w
  deriving DecidableEq, Repr

namespace VoiceSystem

/-! ### Voice inventory -/

/-- The voices of Chuj: active (basic), agentive intransitive,
    passive, agentless passive. -/
def voices : List Voice.VoiceEntry :=
  [ ⟨"Active (Ø)", .agent⟩
  , ⟨"Agentive intransitive (-w)", .agent⟩
  , ⟨"Passive (-ch)", .patient⟩
  , ⟨"Agentless passive (-j)", .patient⟩ ]

/-- Chuj is asymmetrical — active transitive Ø is the basic voice. -/
def symmetry : Voice.VoiceSystemSymmetry := .asymmetrical

end VoiceSystem

theorem chuj_voice_system_asymmetrical :
    VoiceSystem.symmetry = .asymmetrical := rfl

theorem chuj_voice_count :
    Voice.voiceCount VoiceSystem.voices = 4 := rfl

/-- Chuj is NOT a simple active/passive: it has 4 voices, not 2. -/
theorem chuj_not_simple_active_passive :
    ¬ Voice.isActivePassive VoiceSystem.voices := by decide

theorem chuj_no_oblique_pivots :
    ¬ Voice.distinguishesObliques VoiceSystem.voices := by decide

end Chuj
