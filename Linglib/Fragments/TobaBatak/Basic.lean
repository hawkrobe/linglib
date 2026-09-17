import Linglib.Syntax.Voice.Pivot

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

* `TobaBatak.Voice`, `Voice.affix`, `Voice.selection`: the two voices, their prefixes, and
  what each does to the transitive construction and selects as pivot.

## Main results

* `TobaBatak.Voice.symmetrical`, `Voice.not_multiple`, `Voice.equipollent`: a binary
  symmetrical system with equipollent marking.

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

/-- Each voice keeps the agent and the patient core terms of the transitive construction and
selects one as pivot, the actor voice the agent and the object voice the patient; the two
prefixes are equipollent. -/
def Voice.selection : Voice → PivotSelection
  | .av => { ValencyAlternation.refl .np with pivot := .external }
  | .ov => { ValencyAlternation.refl .np with marking := .equipollent, pivot := .complement 0 }

theorem Voice.symmetrical : Symmetrical Voice.selection := by decide

theorem Voice.not_multiple : ¬ Multiple Voice.selection := by decide

theorem Voice.equipollent : Equipollent Voice.selection := by decide

end TobaBatak
