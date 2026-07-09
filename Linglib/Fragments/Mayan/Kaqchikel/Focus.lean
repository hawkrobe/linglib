import Linglib.Fragments.Mayan.Kaqchikel.Agreement
import Linglib.Syntax.Extraction
import Linglib.Semantics.Focus.Realization

/-!
# Kaqchikel Focus and Agent Focus Fragment

Theory-neutral data for focus marking and Agent Focus (AF) in Kaqchikel
(K'ichean, Mayan), from the Patzún variety described by [erlewine-2016]:
the extraction-marking profile and the realization of the focus
construction.

AF marks the transitive verb whose subject has been Ā-extracted to its
immediately preverbal position — the suffix *-ö* or *-n*, with no Set A
slot. Despite the traditional Mayanist name, AF is not itself a focus
construction: it is extraction morphology, and focus fronting is one of
its four triggers alongside wh-questions, relative clauses, and
argument existentials. Patient extraction never triggers it,
long-distance subject extraction triggers it on the embedded verb only,
intervening preverbal material obviates it, and when both arguments
are 1st/2nd person the
full-agreement transitive appears even under subject extraction.
Intransitive verbs never undergo AF, so the marked "subject" is A, not
S. In the focus construction a focused argument fronts to the preverbal
position marked by the particle *ja*, with AF as the additional
verb-hosted reflex of A-focus.

## Main declarations

* `Kaqchikel.extractionStrategy`, `Kaqchikel.extractionMarkedPositions`,
  `Kaqchikel.extractionDistinguishesPosition`: the extraction profile.
* `Kaqchikel.focusRealize`: focus realization by focused argument
  position, as a `Semantics.Focus.Realization` reflex list.
* `Kaqchikel.af_reflex_iff`: the verb-hosted AF reflex appears exactly
  under transitive-subject (A) focus.
* `Kaqchikel.marked_subject_is_A_not_S`: the A-focus vs S-focus split
  that `Extraction.ExtractionTarget` cannot draw.

## Implementation notes

The verb form AF alternates on is the pan-Mayan `Mayan.VerbForm`
(`Fragments/Mayan/Params.lean`); the AF agreement paradigm is in
`Agreement.lean`; the interpreting OT and Voice analyses live in
`Studies/Erlewine2016.lean` and
`Studies/CoonMateoPedroPreminger2014.lean`. The three non-focus AF
triggers ([erlewine-2016] §2.2) differ from focus fronting only in the
fronted phrase's own marking and are not separately encoded. Preverbal
subject-initial
orders are topicalization, not focus (no *ja*, no AF). Whether
Kaqchikel has unmarked in-situ information focus is outside the
source's data, so no `EveryFocusPerceptible` claim is made.
-/

namespace Kaqchikel

open Semantics.Focus

/-! ### Extraction profile -/

/-- Kaqchikel marks transitive-subject extraction with dedicated AF
    morphology: the suffix *-ö* or *-n*, with Set A suppressed
    ([erlewine-2016]). -/
def extractionStrategy : Extraction.ExtractionMarkingStrategy := .dedicatedMorpheme
def extractionMarkedPositions : List Extraction.ExtractionTarget := [.subject]
def extractionDistinguishesPosition : Bool := true

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
    both to `.subject` — the extraction profile's
    `extractionMarkedPositions = [.subject]` means transitive
    subjects. -/
theorem marked_subject_is_A_not_S :
    Reflex.morpheme FocusSite.verb ∈ (focusRealize .A).reflexes ∧
    Reflex.morpheme FocusSite.verb ∉ (focusRealize .S).reflexes := by decide

end Kaqchikel
