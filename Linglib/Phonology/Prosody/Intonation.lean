module

public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.DeriveFintype

/-!
# Intonation

The tonal vocabulary of autosegmental-metrical intonational phonology ([pierrehumbert-1980],
[beckman-pierrehumbert-1986]). A melody is a string of two level tones, H and L. A pitch accent
is a pitch shape associated with a syllable, which the association makes accented: a starred
tone, linked to that syllable, alone or with an unstarred tone just before or after it. The
phrase accent and the boundary tone are terminal tones of the intermediate phrase and the
intonation phrase.

## Main definitions

* `Prosody.LevelTone`: the two tones, H and L.
* `Prosody.PitchAccent`: a starred tone, alone (`T*`) or with a leading (`T+S*`) or trailing
  (`S*+T`) unstarred tone.
* `Prosody.PitchAccent.IsBitonal`: the accent has two tones.
* `Prosody.TerminalContour`: the phrase accent and boundary tone that close an intonation
  phrase.

## Implementation notes

`PitchAccent` has the ten members that [beckman-pierrehumbert-1986] §3.2 say their system
permits in principle: two single-tone accents and eight two-tone ones. Which of them a
language uses is a claim about that language and is stated by the study that makes it.
Unaccented material carries no pitch accent, so an accent slot is an `Option PitchAccent`.

## References

* [pierrehumbert-1980]
* [beckman-pierrehumbert-1986]
-/

@[expose] public section

namespace Prosody

/-- A level tone. [pierrehumbert-1980] analyses English melodies with H and L alone, and
[beckman-pierrehumbert-1986] analyse Japanese with the same two. -/
inductive LevelTone where
  | H
  | L
  deriving DecidableEq, Repr, Fintype

/-- A pitch accent: a starred tone, phonologically linked to the accented syllable, alone or
with an unstarred tone that precedes or follows it ([beckman-pierrehumbert-1986] §2.1). -/
inductive PitchAccent where
  /-- A single starred tone, `T*`. -/
  | mono (star : LevelTone)
  /-- An unstarred tone before the starred one, `T+S*`. -/
  | leading (lead star : LevelTone)
  /-- An unstarred tone after the starred one, `S*+T`. -/
  | trailing (star trail : LevelTone)
  deriving DecidableEq, Repr, Fintype

namespace PitchAccent

/-- The tones of the accent in temporal order. -/
def tones : PitchAccent → List LevelTone
  | mono s => [s]
  | leading t s => [t, s]
  | trailing s t => [s, t]

/-- A bitonal accent has two tones. In English and in Japanese it is the bitonal accents that
trigger catathesis ([beckman-pierrehumbert-1986] §3). -/
def IsBitonal (a : PitchAccent) : Prop := a.tones.length = 2

instance : DecidablePred IsBitonal := fun _ ↦ inferInstanceAs (Decidable (_ = _))

@[simp] theorem not_isBitonal_mono (s : LevelTone) : ¬(mono s).IsBitonal := by
  simp [IsBitonal, tones]

@[simp] theorem isBitonal_leading (t s : LevelTone) : (leading t s).IsBitonal := rfl

@[simp] theorem isBitonal_trailing (s t : LevelTone) : (trailing s t).IsBitonal := rfl

end PitchAccent

/-- The tones that close an intonation phrase: the phrase accent, terminal to its last
intermediate phrase, and the boundary tone, terminal to the intonation phrase itself
([beckman-pierrehumbert-1986] §4.3). Each is H or L, giving [pierrehumbert-1980]'s four
terminal configurations (§4.2). -/
structure TerminalContour where
  phraseAccent : LevelTone
  boundaryTone : LevelTone
  deriving DecidableEq, Repr, Fintype

end Prosody
