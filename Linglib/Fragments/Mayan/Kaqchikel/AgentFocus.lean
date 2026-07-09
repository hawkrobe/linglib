import Linglib.Syntax.Extraction

/-!
# Kaqchikel Agent Focus Fragment [erlewine-2016]

Theory-neutral typological data for Agent Focus (AF) in Kaqchikel
(K'ichean, Mayan): the extraction-marking profile of the Patzún
variety described by [erlewine-2016]. The verb-form distinction AF
alternates on is the pan-Mayan `Mayan.VerbForm`
(`Fragments/Mayan/Params.lean`); the AF agreement paradigm is in
`Agreement.lean`; focus-construction realization is in `Focus.lean`.

The theory-laden apparatus that interprets this data lives in study
files per the project Fragment-discipline rule (CLAUDE.md):
- OT competing-derivations + SSAL/XRef/XRef-Participant constraints,
  rankings, and the cross-Mayan ranking typology →
  `Studies/Erlewine2016.lean`
- Minimalist Voice/ClauseSpine for Kaqchikel →
  `Studies/CoonMateoPedroPreminger2014.lean`

## The Paradigm

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
-/

namespace Kaqchikel

/-! ### Extraction profile -/

/-- Kaqchikel marks transitive-subject extraction with dedicated AF
    morphology: the suffix *-ö* or *-n*, with Set A suppressed
    ([erlewine-2016]). -/
def extractionStrategy : Extraction.ExtractionMarkingStrategy := .dedicatedMorpheme
def extractionMarkedPositions : List Extraction.ExtractionTarget := [.subject]
def extractionDistinguishesPosition : Bool := true

end Kaqchikel
