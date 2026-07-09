import Linglib.Fragments.Mayan.Kaqchikel.Agreement
import Linglib.Syntax.Extraction
import Linglib.Semantics.Focus.Realization

/-!
# Kaqchikel Focus and Agent Focus Fragment [erlewine-2016]

Theory-neutral typological data for focus marking and Agent Focus (AF)
in Kaqchikel (K'ichean, Mayan), from the Patzún variety described by
[erlewine-2016]: the extraction-marking profile and the realization of
the focus construction. The verb-form distinction AF alternates on is
the pan-Mayan `Mayan.VerbForm` (`Fragments/Mayan/Params.lean`); the AF
agreement paradigm is in `Agreement.lean`.

The theory-laden apparatus that interprets this data lives in study
files per the project Fragment-discipline rule (CLAUDE.md):
- OT competing-derivations + SSAL/XRef/XRef-Participant constraints,
  rankings, and the cross-Mayan ranking typology →
  `Studies/Erlewine2016.lean`
- Minimalist Voice/ClauseSpine for Kaqchikel →
  `Studies/CoonMateoPedroPreminger2014.lean`

## The AF Paradigm

| Extracted arg      | Verb form            | Agreement     |
|--------------------|----------------------|---------------|
| None (declarative) | Transitive           | Set A + Set B |
| Patient/Abs        | Transitive           | Set A + Set B |
| Agent/Erg (local)  | AF (*-ö* or *-n*)    | Set B only    |
| Agent/Erg (long)   | embedded AF, matrix transitive | per verb |

AF marks the transitive verb whose subject has been Ā-extracted to its
immediately preverbal position: patient extraction never triggers it;
long-distance subject extraction triggers it on the *embedded* verb
only (the matrix verb, whose own subject has not moved, stays
transitive); and intervening preverbal material obviates it. Two
qualifications from the same source: the single AF agreement slot is
drawn from the Set B paradigm and targets the salience-higher argument
(see `Agreement.lean`), and when *both* arguments are 1st/2nd person
the full-agreement transitive appears even under subject extraction.
Intransitive verbs never undergo AF, so the marked "subject" below is
the transitive subject (A, not S) — the syntactic-ergativity pattern.

## The focus construction

A focused argument fronts to immediately preverbal position, marked by
the particle *ja*; a focused transitive subject additionally switches
the verb to AF. Realization uses the shared
`Semantics.Focus.Realization` vocabulary: multi-channel marking as a
reflex list — displacement, the *ja* particle, and (conditionally) the
verb-hosted AF reflex. Focus fronting is one of four constructions
targeting the same preverbal position (wh-questions, relative clauses,
focus, argument existentials; [erlewine-2016] §2.2); the others differ
only in the fronted phrase's own marking (wh-word, relative *ri*,
existential *k'o*), sharing the verb-hosted AF conditioning encoded
here. Preverbal subject-initial word orders are topicalization, not
focus — no *ja*, no AF ([erlewine-2016] §4.4). Whether Kaqchikel also
has unmarked in-situ information focus is outside this fragment's
data, so no `EveryFocusPerceptible` claim for the language is made
here.
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
