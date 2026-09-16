import Linglib.Fragments.Mayan.Kaqchikel.Extraction

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
  role, the extraction reflexes plus the fronting and *ja*.
* `Kaqchikel.af_reflex_iff`: the verb-hosted AF reflex appears exactly
  under transitive-subject (A) focus.
* `Kaqchikel.marked_subject_is_A_not_S`: the A-focus vs S-focus split.

## Implementation notes

Focus fronting is one of four AF triggers ([erlewine-2016] §2.2); the
others (wh-questions, relative clauses, argument existentials) differ
only in the fronted phrase's own marking and are not separately
encoded. Preverbal subject-initial orders are topicalization, not
focus (no *ja*, no AF). Across Mayan, information focus stays in situ
and unmarked except for the transitive subject, which in AF-languages
must front and trigger AF ([aissen-2017]); Kaqchikel-specific in-situ
data are not in the sources here, so `focusRealize` covers the fronted
construction only and no `EveryTargetOvert` claim is made.
-/

namespace Kaqchikel

open Reflex

/-! ### Realization -/

/-- Focus realization by focused argument role ([erlewine-2016]): every
focused argument fronts (VOS base order, so fronting is never
string-vacuous) and hosts *ja*, on top of whatever extraction from its
role licenses — for a transitive subject (A), Agent Focus on the verb.
Ditransitive R/T focus is unattested in the source and falls to the
A-less default. -/
def focusRealize (r : ArgumentRole) : Finset (Reflex Extraction.Host) :=
  Extraction.realize (.core r) ∪ {.displacement .phrase, .morpheme .phrase}

/-- The verb-hosted reflex (AF) appears under transitive-subject focus
    only. -/
theorem af_reflex_iff (p : ArgumentRole) :
    Reflex.morpheme Extraction.Host.verb ∈ focusRealize p ↔ p = .A := by
  cases p <;> decide

/-- The ergative split in focus marking: A-focus switches the verb to AF
while S-focus does not. -/
theorem marked_subject_is_A_not_S :
    Reflex.morpheme Extraction.Host.verb ∈ focusRealize .A ∧
    Reflex.morpheme Extraction.Host.verb ∉ focusRealize .S := by decide

end Kaqchikel
