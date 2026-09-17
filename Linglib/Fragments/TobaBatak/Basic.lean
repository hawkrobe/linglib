import Linglib.Syntax.Voice.System

/-!
# Toba Batak: voice

Toba Batak (Austronesian; Lake Toba, Sumatra) is predicate-initial and has two voices, the actor
voice in *mang-* and the object voice in *di-*, each making one argument the pivot, the
clause-peripheral subject, and neither demoting the other core argument. Among the core
arguments only the pivot can be extracted, while obliques extract under either voice
([cole-hermon-2008]; the voice system is described by [schachter-1984] and analysed by
[erlewine-2018]): the restriction is the subject-only gap relativizer of `Relativization.lean`,
and the voice inventory says which argument the pivot is. The voice prefix surfaces in every
clause, so it is not a reflex of extraction. Neither voice is morphologically basic. Analyses
of the extraction restriction, and the examples that support them, live in the studies that
propose them.

## Main definitions

* `TobaBatak.Voice`, `Voice.affix`, `Voice.toVoice`: the two voices, their prefixes, and
  the voice of the typology each is.

## Main results

* `TobaBatak.voices`, `symmetrical`, `not_multiple`, `equipollent`: a binary symmetrical
  system with equipollent marking.

## References

* [cole-hermon-2008]
* [erlewine-2018]
* [schachter-1984]
-/

open Voice

namespace TobaBatak

/-- The two voices, each making one argument the pivot. -/
inductive Voice where
  /-- Actor voice: the agent is the pivot. -/
  | av
  /-- Object voice: the patient is the pivot. -/
  | ov
  deriving DecidableEq, Repr, Fintype

/-- The voice prefix, *mang-* (with its phonologically conditioned variants) or *di-*. -/
def Voice.affix : Voice → String
  | .av => "mang-"
  | .ov => "di-"

/-- The actor voice is the agent voice and the object voice the patient voice, each keeping
both core terms and selecting one as pivot; both prefixes are overt. -/
def Voice.toVoice : Voice → _root_.Voice
  | .av => agentVoice.synthetic
  | .ov => patientVoice.synthetic

/-- The two voices as the typology reads them. -/
def voices : Finset _root_.Voice := Finset.univ.image Voice.toVoice

theorem symmetrical : Symmetrical voices := by decide

theorem not_multiple : ¬ Multiple voices := by decide

theorem equipollent : Equipollent voices := by decide

end TobaBatak
