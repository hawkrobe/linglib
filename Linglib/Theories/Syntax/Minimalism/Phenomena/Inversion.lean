/-
# Minimalist Analysis of Subject-Auxiliary Inversion

Inversion-specific constraints and licensing.
Builds on the general clause structure from Structure.lean.

## The Analysis

Matrix questions have [+Q] on C, which triggers T-to-C movement.
Embedded questions have [+Q] satisfied by the embedding verb or wh-movement,
so T-to-C doesn't occur.

This derives the word order asymmetry:
- Matrix: T-to-C → T precedes subject
- Embedded: no T-to-C → subject precedes T
-/

import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.FunctionWords
import Linglib.Theories.Syntax.Minimalism.Core.Structure
import Linglib.Phenomena.WordOrder.SubjectAuxInversion

namespace Minimalism

-- Clause Type Triggers (Inversion-Specific)

/-- Matrix questions trigger T-to-C movement (to check [+Q] on C) -/
def matrixTriggersTToC (ct : ClauseType) (tPos : TPosition) : Prop :=
  ct = .matrixQuestion → tPos = .inC

/-- Embedded questions don't trigger T-to-C (C's [+Q] is checked otherwise) -/
def embeddedNoTToC (ct : ClauseType) (tPos : TPosition) : Prop :=
  ct = .embeddedQuestion → tPos = .inT

-- Derived Word Order Predictions

/-- Matrix questions have T before subject (via T-to-C) -/
theorem matrix_has_t_before_subject (tPos : TPosition)
    (h : matrixTriggersTToC .matrixQuestion tPos) :
    tPrecedesSubject tPos = true := by
  have : tPos = .inC := h rfl
  simp [this, tPrecedesSubject, tPronouncedAt, structurallyPrecedes]

/-- Embedded questions have subject before T (no T-to-C) -/
theorem embedded_has_subject_before_t (tPos : TPosition)
    (h : embeddedNoTToC .embeddedQuestion tPos) :
    subjectPrecedesT tPos = true := by
  have : tPos = .inT := h rfl
  simp [this, subjectPrecedesT, tPronouncedAt, structurallyPrecedes]

-- Connecting to Word Lists

/-- Find auxiliary (T) position in word list -/
def findAuxInWords (ws : List Word) : Option Nat :=
  ws.findIdx? (·.cat == .AUX)

/-- Is this a nominal category that can be a subject? -/
def isSubjectCat (c : UD.UPOS) : Bool :=
  c == .PROPN || c == .NOUN || c == .PRON

/-- Find subject position in word list -/
def findSubjectInWords (ws : List Word) : Option Nat :=
  ws.findIdx? λ w => isSubjectCat w.cat && !w.features.wh

/-- Word list has T-before-subject order -/
def wordsHaveTBeforeSubject (ws : List Word) : Bool :=
  match findAuxInWords ws, findSubjectInWords ws with
  | some t, some s => t < s
  | _, _ => false

/-- Word list has subject-before-T order -/
def wordsHaveSubjectBeforeT (ws : List Word) : Bool :=
  match findAuxInWords ws, findSubjectInWords ws with
  | some t, some s => s < t
  | _, _ => false

-- Licensing

/-- A clause: words + structural info -/
structure Clause where
  words : List Word
  tPosition : TPosition
  clauseType : ClauseType

/-- Word order must match the structural prediction -/
def wordOrderMatchesStructure (c : Clause) : Prop :=
  (tPrecedesSubject c.tPosition = true → wordsHaveTBeforeSubject c.words = true) ∧
  (subjectPrecedesT c.tPosition = true → wordsHaveSubjectBeforeT c.words = true)

/-- Well-formed clause -/
def wellFormed (c : Clause) : Prop :=
  wordOrderMatchesStructure c ∧
  matrixTriggersTToC c.clauseType c.tPosition ∧
  embeddedNoTToC c.clauseType c.tPosition

/-- A word sequence is licensed for a clause type if some T-position works -/
def licenses (ws : List Word) (ct : ClauseType) : Prop :=
  ∃ tPos : TPosition, wellFormed ⟨ws, tPos, ct⟩

-- Licensing Theorems

/-- Matrix questions with T-first word order are licensed -/
theorem licenses_matrix_t_first (ws : List Word)
    (h : wordsHaveTBeforeSubject ws = true) :
    licenses ws .matrixQuestion := by
  refine ⟨.inC, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [tPrecedesSubject, tPronouncedAt, structurallyPrecedes]
    exact λ _ => h
  · simp only [subjectPrecedesT, tPronouncedAt, structurallyPrecedes]
    intro hf; cases hf
  · intro _; rfl
  · intro hct; cases hct

/-- Matrix questions with subject-first are NOT licensed -/
theorem not_licenses_matrix_subject_first (ws : List Word)
    (h : wordsHaveTBeforeSubject ws = false) :
    ¬ licenses ws .matrixQuestion := by
  intro ⟨tPos, wf⟩
  obtain ⟨⟨hword, _⟩, htrig, _⟩ := wf
  have hpos : tPos = .inC := htrig rfl
  have ht : tPrecedesSubject tPos = true := by
    simp [hpos, tPrecedesSubject, tPronouncedAt, structurallyPrecedes]
  have hws : wordsHaveTBeforeSubject ws = true := hword ht
  rw [h] at hws
  cases hws

/-- Embedded questions with subject-first are licensed -/
theorem licenses_embedded_subject_first (ws : List Word)
    (h : wordsHaveSubjectBeforeT ws = true) :
    licenses ws .embeddedQuestion := by
  refine ⟨.inT, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [tPrecedesSubject, tPronouncedAt, structurallyPrecedes]
    intro hf; cases hf
  · simp only [subjectPrecedesT, tPronouncedAt, structurallyPrecedes]
    exact λ _ => h
  · intro hct; cases hct
  · intro _; rfl

/-- Embedded questions with T-first are NOT licensed -/
theorem not_licenses_embedded_t_first (ws : List Word)
    (h : wordsHaveSubjectBeforeT ws = false) :
    ¬ licenses ws .embeddedQuestion := by
  intro ⟨tPos, wf⟩
  obtain ⟨⟨_, hword⟩, _, hemb⟩ := wf
  have hpos : tPos = .inT := hemb rfl
  have ht : subjectPrecedesT tPos = true := by
    simp [hpos, subjectPrecedesT, tPronouncedAt, structurallyPrecedes]
  have hws : wordsHaveSubjectBeforeT ws = true := hword ht
  rw [h] at hws
  cases hws

-- Verification

private abbrev what := Fragments.English.Pronouns.what.toWord
private abbrev can := Fragments.English.FunctionWords.can.toWord
private abbrev john := Fragments.English.Nouns.john.toWordSg
private abbrev eat := Fragments.English.Predicates.Verbal.eat.toWordPl

#eval wordsHaveTBeforeSubject [what, can, john, eat]   -- true
#eval wordsHaveTBeforeSubject [what, john, can, eat]   -- false
#eval wordsHaveSubjectBeforeT [john, can, eat]         -- true
#eval wordsHaveSubjectBeforeT [can, john, eat]         -- false

example : licenses [what, can, john, eat] .matrixQuestion :=
  licenses_matrix_t_first _ rfl

example : ¬ licenses [what, john, can, eat] .matrixQuestion :=
  not_licenses_matrix_subject_first _ rfl

example : licenses [john, can, eat] .embeddedQuestion :=
  licenses_embedded_subject_first _ rfl

example : ¬ licenses [can, john, eat] .embeddedQuestion :=
  not_licenses_embedded_t_first _ rfl

-- Comparison: HPSG vs Minimalism

/-
Both frameworks predict the same surface patterns:

| Sentence              | ClauseType     | HPSG           | Minimalism      |
|-----------------------|----------------|----------------|-----------------|
| What can John eat?    | matrixQuestion | INV+ → aux<subj| T-to-C → T<Subj |
| What John can eat?    | matrixQuestion | *needs INV+    | *needs T-to-C   |
| Can John eat pizza?   | matrixQuestion | INV+ → aux<subj| T-to-C → T<Subj |
| John can eat pizza?   | matrixQuestion | *needs INV+    | *needs T-to-C   |

The mechanisms differ:
- HPSG: [INV+] feature constrains word order directly (declarative)
- Minimalism: T-to-C movement derives word order (derivational)

But the predictions are identical for these cases.

Question for future work: Are there cases where the frameworks diverge?
(e.g., languages with different clause structures, or complex sentences)
-/

end Minimalism
