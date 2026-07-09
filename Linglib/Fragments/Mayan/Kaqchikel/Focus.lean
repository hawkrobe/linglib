import Linglib.Fragments.Mayan.Kaqchikel.Agreement
import Linglib.Semantics.Focus.Realization

/-!
# Kaqchikel Focus Fragment [erlewine-2016]

Theory-neutral realization data for the Kaqchikel focus construction:
a focused argument fronts to immediately preverbal position, marked by
the particle *ja*, and — when the focused argument is the transitive
subject — the verb switches to Agent Focus morphology (extraction
profile in `AgentFocus.lean`; AF's single agreement slot in
`Agreement.lean`). Realization uses the shared
`Semantics.Focus.Realization` vocabulary: multi-channel marking as a
reflex list — displacement, the *ja* particle, and (conditionally) the
verb-hosted AF reflex.

Focus fronting is one of four constructions targeting the same
preverbal position (wh-questions, relative clauses, focus, argument
existentials; [erlewine-2016] §2.2); the others differ only in the
fronted phrase's own marking (wh-word, relative *ri*, existential
*k'o*), sharing the verb-hosted AF conditioning encoded here.
Preverbal subject-initial word orders are topicalization, not focus —
no *ja*, no AF ([erlewine-2016] §4.4). Whether Kaqchikel also has
unmarked in-situ information focus is outside this fragment's data, so
no `EveryFocusPerceptible` claim for the language is made here.
-/

namespace Kaqchikel

open Semantics.Focus

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
    both to `.subject` — the extraction profile's `[.subject]`
    (`AgentFocus.lean`) means transitive subjects. -/
theorem marked_subject_is_A_not_S :
    Reflex.morpheme FocusSite.verb ∈ (focusRealize .A).reflexes ∧
    Reflex.morpheme FocusSite.verb ∉ (focusRealize .S).reflexes := by decide

end Kaqchikel
