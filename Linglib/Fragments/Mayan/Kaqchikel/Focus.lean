import Linglib.Fragments.Mayan.Kaqchikel.Agreement
import Linglib.Morphology.Realization

/-!
# Kaqchikel Focus Fragment

Realization data for the Kaqchikel focus construction, from the Patzún
variety described by [erlewine-2016]: a focused argument fronts to
immediately preverbal position marked by the particle *ja*, and a
focused transitive subject (A) additionally switches the verb to Agent
Focus (`Extraction.lean`) — the ergative split, since S
fronts like A but intransitive verbs have no AF form.

## Main declarations

* `Kaqchikel.focusRealize`: focus realization by focused argument
  position, as a `Morphology.Realization` reflex list.
* `Kaqchikel.af_reflex_iff`: the verb-hosted AF reflex appears exactly
  under transitive-subject (A) focus.
* `Kaqchikel.marked_subject_is_A_not_S`: the A-focus vs S-focus split
  that `Extraction.ExtractionTarget` cannot draw.

## Implementation notes

Focus fronting is one of four AF triggers ([erlewine-2016] §2.2); the
others (wh-questions, relative clauses, argument existentials) differ
only in the fronted phrase's own marking and are not separately
encoded. Preverbal subject-initial orders are topicalization, not
focus (no *ja*, no AF). Across Mayan, information focus stays in situ
and unmarked except for the transitive subject, which in AF-languages
must front and trigger AF ([aissen-2017]); Kaqchikel-specific in-situ
data are not in the sources here, so `focusRealize` covers the fronted
construction only and no `EveryFocusPerceptible` claim is made.
-/

namespace Kaqchikel

open Morphology

/-! ### Sites -/

/-- The constituents a Kaqchikel focus reflex attaches to: the fronted
    focus phrase itself (hosting *ja* and the fronting) or the verbal
    complex (hosting the AF morpheme). -/
inductive FocusSite where
  | focusPhrase
  | verb
  deriving DecidableEq, Repr

/-! ### Realization -/

/-- Focus realization by focused argument position ([erlewine-2016]
    §2.2): every focused argument fronts (VOS base order, so fronting is
    never string-vacuous) and hosts *ja*; a focused transitive subject
    (A) additionally switches the verb to AF — the ergative split, since
    S fronts like A but intransitive verbs have no AF form. Ditransitive
    R/T focus is unattested in the source and falls to the A-less
    default. -/
def focusRealize : ArgPosition → Realization FocusSite
  | .A => ⟨.focusPhrase,
           [.displacement .focusPhrase, .morpheme .focusPhrase, .morpheme .verb]⟩
  | _  => ⟨.focusPhrase, [.displacement .focusPhrase, .morpheme .focusPhrase]⟩

/-- The verb-hosted reflex (AF) appears under transitive-subject focus
    only. -/
theorem af_reflex_iff (p : ArgPosition) :
    Reflex.morpheme FocusSite.verb ∈ (focusRealize p).reflexes ↔ p = .A := by
  cases p <;> decide

/-- The ergative split in focus marking: A-focus switches the verb to AF
    while S-focus does not, although `Extraction.ExtractionTarget` maps
    both to `.subject` — the verb reflex of `Extraction.realize .subject`
    (`Extraction.lean`) marks transitive subjects only. -/
theorem marked_subject_is_A_not_S :
    Reflex.morpheme FocusSite.verb ∈ (focusRealize .A).reflexes ∧
    Reflex.morpheme FocusSite.verb ∉ (focusRealize .S).reflexes := by decide

end Kaqchikel
