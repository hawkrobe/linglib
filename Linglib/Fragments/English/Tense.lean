import Linglib.Semantics.Tense.Evidential
import Linglib.Semantics.Tense.Decomposition

/-!
# English tense fragment
[cumming-2026] [winans-2016] [cumming-winans-2021] [kratzer-1998]

Paradigm cells for the English tense forms of [cumming-2026], the nonfuture and future
forms of its table (20) and the past- and present-directed *will* forms of its table (22),
each with its constraints on evidential and utterance perspective, followed by
[kratzer-1998]'s surface-tense decomposition of the simple past. The future cell of table
(20) and the bare *will* of table (22) are one cell.

| Form              | EP constraint | UP constraint | Nonfuture? |
|-------------------|---------------|---------------|------------|
| simple past       | T ≤ A         | T < S         | yes        |
| present prog      | T ≤ A         | T = S         | yes        |
| future (will)     | (none)        | S < T         | no         |
| will have V-ed    | A < T         | T < S         | no         |
| will now be V-ing | A < T         | T = S         | no         |

The printed table (22) gives *will have* the utterance perspective T > S; the text and the
example of the Fed's meeting require a past event, recorded here.
-/

open Tense

namespace English.Tense

open _root_.Tense.Evidential

/-! ### Nonfuture and future forms (table (20)) -/

/-- English simple past: evidence downstream of a past event. -/
def simplePast : TAMEEntry where
  label := "simple past"
  ep := .downstream
  up := .past

/-- English present progressive: evidence downstream of a present event. -/
def presentProg : TAMEEntry where
  label := "present progressive"
  ep := .downstream
  up := .present

/-- English future *will*: no evidential constraint on a future event. -/
def will : TAMEEntry where
  label := "future (will)"
  ep := .unconstrained
  up := .future

/-! ### The past- and present-directed *will* forms (table (22))

The restriction to inference from facts not causally downstream of the event is
[winans-2016]'s and [cumming-winans-2021]'s. -/

/-- The past-directed *will have V-ed*: prospective evidence for a past event. -/
def willHave : TAMEEntry where
  label := "will have V-ed"
  ep := .prospective
  up := .past

/-- The present-directed *will now be V-ing*: prospective evidence for a present event. -/
def willNow : TAMEEntry where
  label := "will now be V-ing"
  ep := .prospective
  up := .present

/-- The English paradigm cells. -/
def allEntries : List TAMEEntry :=
  [simplePast, presentProg, will, willHave, willNow]

/-! ### Surface tense ([kratzer-1998]) -/

open _root_.Tense.Decomposition
open _root_.Tense

/-- English simple past: surface-tense decomposition.
    Surface "V-ed" = PRESENT tense + PERFECT aspect.
    The tense head is present (indexical), so the form can be
    used deictically ("out of the blue"). -/
def simplePastSurface : SurfaceTense where
  tensePronoun := indexicalPresent
  hasPerfect := true

/-- English present perfect: no decomposition mismatch.
    Surface "have V-ed" = PRESENT tense + PERFECT aspect.
    Identical underlying structure to simple past — the difference
    is that the present perfect is morphologically transparent. -/
def presentPerfectSurface : SurfaceTense where
  tensePronoun := indexicalPresent
  hasPerfect := true

/-- English simple past can be deictic (from decomposition). -/
theorem simplePastSurface_deictic :
    simplePastSurface.canBeDeictic := by decide

/-- The underlying tense head is PRESENT, not PAST.
    Pastness comes from the PERF aspect head, not the tense. -/
theorem simplePastSurface_underlyingPresent :
    simplePastSurface.tensePronoun.constraint = _root_.Tense.present := rfl

/-- Simple past and present perfect share the same underlying decomposition:
    both are PRESENT + PERFECT. The difference is that simple past fuses
    the two morphemes while present perfect makes the PERF transparent
    via auxiliary "have". -/
theorem simplePast_presentPerfect_same_decomposition :
    simplePastSurface.tensePronoun = presentPerfectSurface.tensePronoun ∧
    simplePastSurface.hasPerfect = presentPerfectSurface.hasPerfect :=
  ⟨rfl, rfl⟩

end English.Tense
