import Linglib.Syntax.Voice.Basic

/-!
# Toba Batak: voice

Toba Batak (Austronesian; Lake Toba, Sumatra) is predicate-initial and has two voices, the actor
voice in *mang-* and the object voice in *di-*, each making one argument the pivot, the
clause-peripheral subject. Only the pivot can be extracted ([schachter-1984]; [cole-hermon-2008];
[erlewine-2018]): the restriction is the subject-only gap relativizer of `Relativization.lean`,
and the voice inventory says which argument the pivot is. The voice prefix surfaces in every
clause, so it is not a reflex of extraction. Neither voice is morphologically basic. Analyses of
the extraction restriction, and the examples that support them, live in the studies that propose
them.

## Main definitions

* `TobaBatak.Voice`, `Voice.affix`, `Voice.promotes`: the two voices, their prefixes and the
  role each promotes to pivot.
* `TobaBatak.VoiceSystem.voices`, `VoiceSystem.symmetry`: the inventory as the voice typology
  reads it.
-/

open Voice (PivotTarget VoiceEntry VoiceSystemSymmetry)

namespace TobaBatak

/-! ### Voice -/

/-- The two voices, each making one argument the pivot. -/
inductive Voice where
  /-- Actor voice: the agent is the pivot. -/
  | av
  /-- Object voice: the patient is the pivot. -/
  | ov
  deriving DecidableEq, Repr

/-- The voice prefix, *mang-* (with its phonologically conditioned variants) or *di-*. -/
def Voice.affix : Voice → String
  | .av => "mang-"
  | .ov => "di-"

/-- The role the voice promotes to pivot. -/
def Voice.promotes : Voice → PivotTarget
  | .av => .agent
  | .ov => .patient

/-! ### The voice inventory -/

namespace VoiceSystem

/-- The two voices as the typology reads them. -/
def voices : List VoiceEntry :=
  [⟨"actor voice", Voice.av.promotes⟩, ⟨"object voice", Voice.ov.promotes⟩]

/-- Neither voice is morphologically basic. -/
def symmetry : VoiceSystemSymmetry := .symmetrical

end VoiceSystem

end TobaBatak
