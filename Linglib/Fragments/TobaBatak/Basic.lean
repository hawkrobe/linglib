import Linglib.Features.Reflex
import Linglib.Syntax.Extraction
import Linglib.Syntax.Voice.Basic

/-!
# Toba Batak: voice and extraction marking

Toba Batak (Austronesian; Lake Toba, Sumatra) is predicate-initial and has two voices, the actor
voice in *mang-* and the object voice in *di-*, each making one argument the pivot, the
clause-peripheral subject; only the pivot can be extracted, so the voice form on the verb is what
marks an extraction ([schachter-1984]; [cole-hermon-2008] §3; [erlewine-2018] §2). Neither voice
is morphologically basic. Analyses of the extraction restriction, and the examples that support
them, live in the studies that propose them.

## Main definitions

* `TobaBatak.Voice`, `Voice.affix`, `Voice.promotes`: the two voices, their prefixes and the
  role each promotes to pivot.
* `TobaBatak.Extraction.realize`, `Extraction.strategy`: extraction marked by the voice
  alternation on the verb.
* `TobaBatak.VoiceSystem.voices`, `VoiceSystem.symmetry`: the inventory as the voice typology
  reads it.
-/

open Extraction (ExtractionTarget ExtractionMarkingStrategy)
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

/-! ### Extraction marking -/

namespace Extraction

/-- The host of the extraction reflex. -/
inductive Site where
  | verb
  deriving DecidableEq, Repr

/-- Only the pivot, the subject, extracts, and the voice form on the verb says which argument
that is. -/
def realize : ExtractionTarget → List (Features.Reflex Site)
  | .subject => [.morpheme .verb]
  | _ => []

/-- The WALS-style label: voice alternation marks extraction. -/
def strategy : ExtractionMarkingStrategy := .voiceAlternation

end Extraction

/-! ### The voice inventory -/

namespace VoiceSystem

/-- The two voices as the typology reads them. -/
def voices : List VoiceEntry :=
  [⟨"actor voice", Voice.av.promotes⟩, ⟨"object voice", Voice.ov.promotes⟩]

/-- Neither voice is morphologically basic. -/
def symmetry : VoiceSystemSymmetry := .symmetrical

end VoiceSystem

end TobaBatak
