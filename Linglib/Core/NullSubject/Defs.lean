import Linglib.Core.Lexical.UD

/-!
# Subject-Context Vocabulary

Framework-agnostic vocabulary for the loci where a language makes a
null-vs-overt subject decision. The four orthogonal axes here suffice
to distinguish the empirical cases that 2026-era pro-drop literature
actually engages with:

- **Person** — partial pro-drop (Hebrew: 1/2 only; Brazilian Portuguese:
  3rd-person dependent).
- **Finiteness** — non-finite control vs finite matrix subject.
- **ClauseRole** — matrix vs embedded-finite vs control-subject locus.
- **ABarStatus** — anti-agreement effect (Tarifit, Fiorentino, Wolof:
  null subjects only available under Ā-extraction; @cite{baier-2018}).

A `SubjectContext` is a 4-tuple (one cell of the cross-classification)
and a `SubjectAssignment : SubjectContext → Exponent` (defined in
`Universals.lean`) is the abstract interface a syntactic theory must
provide to be evaluated against the universals in this directory.

Convenience constructors (`matrixFinite`, `embeddedFinite`,
`controlled`) cover the canonical 3rd-person in-situ loci that study
files reach for. `matrixExtracted` is the locus for anti-agreement
diagnostics.
-/

namespace Core.NullSubject

/-- Grammatical person. Aliased to `UD.Person` for cross-linguistic
    compatibility with the rest of linglib's morphological feature
    system; constructors are `.first`, `.second`, `.third`, `.zero`. -/
abbrev Person := UD.Person

/-- The thematic persons (1st, 2nd, 3rd). `.zero` (impersonal) is
    excluded because the typological universals here are about
    thematic-subject realization; impersonal subjects are governed by
    a separate parameter (cf. expletive vs null-expletive). -/
def thematicPersons : List Person := [.first, .second, .third]

/-- Finiteness of the clause hosting the subject locus. Coarser than
    @cite{landau-2004}'s scale — that finer-grained version belongs in
    a syntactic theory file, not here. -/
inductive Finiteness where
  /-- Finite clause (independent T, agreement morphology). -/
  | finite
  /-- Non-finite clause (control, raising, ECM, gerundive, ...). -/
  | nonfinite
  deriving DecidableEq, Repr, Inhabited

/-- The structural role of the clause hosting the subject locus. The
    three values exhaust the loci where the pro-drop / overt-PRO
    typology actually distinguishes languages. -/
inductive ClauseRole where
  /-- Matrix clause subject. -/
  | matrix
  /-- Subject of a finite embedded clause (relevant for
      embedded-pro-drop diagnostics). -/
  | embeddedFinite
  /-- Subject of an obligatory-control clause (PRO position). -/
  | controlSubject
  deriving DecidableEq, Repr, Inhabited

/-- Whether the subject is in situ or has undergone Ā-extraction.
    Distinguished here because anti-agreement effects (Tarifit,
    Fiorentino, Wolof; @cite{baier-2018}) license null subjects
    *only* under Ā-extraction. -/
inductive ABarStatus where
  /-- Subject in situ (no Ā-extraction). -/
  | insitu
  /-- Subject has undergone Ā-extraction (relativized, wh-fronted,
      focus-fronted, topicalized). -/
  | aBarExtracted
  deriving DecidableEq, Repr, Inhabited

/-- A cell of the four-way cross-classification: a single locus at
    which a language must decide between a null and an overt subject
    exponent. -/
structure SubjectContext where
  person     : Person
  finiteness : Finiteness
  clauseRole : ClauseRole
  aBarStatus : ABarStatus
  deriving DecidableEq, Repr

/-- The exponent decision at a `SubjectContext`: null vs overt. The
    typology this directory tracks reduces to a function
    `SubjectContext → Exponent`. -/
inductive Exponent where
  /-- Silent subject (pro / null PRO / dropped subject). -/
  | null
  /-- Overt subject (full pronoun, clitic, agreement-doubled
      pronoun, overt PRO). -/
  | overt
  deriving DecidableEq, Repr, Inhabited

namespace SubjectContext

/-- Matrix finite subject of person `p` (in situ). The canonical
    locus for "is this language pro-drop?". -/
def matrixFinite (p : Person) : SubjectContext :=
  { person := p, finiteness := .finite, clauseRole := .matrix,
    aBarStatus := .insitu }

/-- Embedded finite subject of person `p` (in situ). Distinguished
    from `matrixFinite` so that embedded-pro-drop asymmetries (some
    languages drop only embedded subjects) can be stated. -/
def embeddedFinite (p : Person) : SubjectContext :=
  { person := p, finiteness := .finite, clauseRole := .embeddedFinite,
    aBarStatus := .insitu }

/-- Subject of an obligatory-control clause (PRO position) of person
    `p`. The canonical locus for "does this language have overt
    PRO?". -/
def controlled (p : Person) : SubjectContext :=
  { person := p, finiteness := .nonfinite, clauseRole := .controlSubject,
    aBarStatus := .insitu }

/-- Ā-extracted matrix finite subject of person `p`. The canonical
    locus for the anti-agreement effect (@cite{baier-2018}). -/
def matrixExtracted (p : Person) : SubjectContext :=
  { person := p, finiteness := .finite, clauseRole := .matrix,
    aBarStatus := .aBarExtracted }

end SubjectContext

end Core.NullSubject
