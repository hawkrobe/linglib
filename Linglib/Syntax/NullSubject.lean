import Linglib.Data.UD.Basic

/-!
# Null-Subject Typology: Pro-Drop and Overt PRO

Framework-agnostic substrate for the pro-drop / overt-PRO typology
([ostrove-2026]): the loci where a language decides between null and
overt subjects, the coarse two-Boolean profile, and the implicational
universal stated over both the coarse profile and the fine per-context
`SubjectAssignment` interface. Anti-agreement loci follow [baier-2018].

Theory-laden *explanations* of the parameter (rich-agreement licensing,
the EPP, topic drop) belong in `Syntax/<framework>/`; theory-laden
*bridges* (e.g. deriving `hasOvertPRO` from a Minimalist minimal-pronoun
inventory) live with the theory they presuppose
(`Syntax/Minimalist/MinimalPronoun.lean`).

## Main declarations

* `SubjectContext` — a cell of the person × finiteness × clause-role ×
  Ā-status cross-classification.
* `ProDropProfile` — the coarse two-Boolean typological observable;
  `ProDropProfile.Satisfies` is [ostrove-2026]'s universal (overt PRO →
  no pro-drop).
* `Typology` — the four cells; `overtPROProDrop` is predicted absent.
* `SubjectAssignment` — the fine interface (`SubjectContext → Exponent`)
  a syntactic theory must provide; its `Satisfies` is defined via the
  projection `toProDropProfile`, so the universal is singly authored.

Per-person predicates (`allowsProDropAt`, `hasOvertPROAt`,
`licensesAntiAgreementAt`) expose the grain that partial-pro-drop
(Hebrew, Brazilian Portuguese, Finnish) and anti-agreement languages
require.
-/

namespace NullSubject

/-! ### Subject-context vocabulary -/

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
    [landau-2004]'s scale — that finer-grained version belongs in
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
    Fiorentino, Wolof; [baier-2018]) license null subjects
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
    typology this file tracks reduces to a function
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
    locus for the anti-agreement effect ([baier-2018]). -/
def matrixExtracted (p : Person) : SubjectContext :=
  { person := p, finiteness := .finite, clauseRole := .matrix,
    aBarStatus := .aBarExtracted }

end SubjectContext

/-! ### The coarse profile and the implicational universal -/

/-- A language's pro-drop / overt-PRO profile. The two Booleans are the
    typological observables; [ostrove-2026]'s implicational
    universal is a constraint on which combinations are predicted to
    occur. -/
structure ProDropProfile where
  /-- Whether the language permits null thematic subjects in finite
      clauses (*pro*-drop). -/
  allowsProDrop : Bool
  /-- Whether the subject of an obligatory-control clause must be
      realized overtly (overt PRO). -/
  hasOvertPRO   : Bool
  deriving DecidableEq, Repr

namespace ProDropProfile

/-- [ostrove-2026]'s implicational universal as a `Prop`: overt
    PRO entails non-*pro*-drop. Stated as a Prop so it composes with
    other logical predicates; `Decidable` instance below makes it
    evaluable by `decide`. -/
def Satisfies (p : ProDropProfile) : Prop :=
  p.hasOvertPRO = true → p.allowsProDrop = false

instance (p : ProDropProfile) : Decidable p.Satisfies := by
  unfold Satisfies; infer_instance

/-- If PRO is null, the universal is satisfied vacuously (its
    antecedent is false). -/
theorem satisfies_of_not_overt_pro (p : ProDropProfile)
    (h : p.hasOvertPRO = false) : p.Satisfies := by
  intro h'; exact absurd (h ▸ h') (by decide)

/-- If PRO is overt and the language is non-*pro*-drop, the
    universal's consequent already holds, so the implication does too. -/
theorem satisfies_of_overt_pro_no_prodrop (p : ProDropProfile)
    (hD : p.allowsProDrop = false) : p.Satisfies := fun _ => hD

/-- Contrapositive: a *pro*-drop language cannot have overt PRO. This
    is the practically useful direction of the universal — given that
    a language is *pro*-drop, it predicts the absence of overt PRO. -/
theorem prodrop_excludes_overt_pro (p : ProDropProfile)
    (h : p.Satisfies) (hD : p.allowsProDrop = true) :
    p.hasOvertPRO = false := by
  cases hO : p.hasOvertPRO with
  | false => rfl
  | true  => exact absurd (h hO) (hD ▸ by decide)

end ProDropProfile

/-- The four cells of the typology. The fourth (overt PRO + *pro*-drop)
    is predicted absent by [ostrove-2026]'s universal. Names use
    mathlib-style camelCase. -/
inductive Typology where
  /-- Null PRO + non-*pro*-drop (e.g., English). -/
  | nullPRONoProDrop
  /-- Null PRO + *pro*-drop (e.g., Italian). -/
  | nullPROProDrop
  /-- Overt PRO + non-*pro*-drop (e.g., SMPM, Gã, Büli). -/
  | overtPRONoProDrop
  /-- Overt PRO + *pro*-drop — predicted absent. -/
  | overtPROProDrop
  deriving DecidableEq, Repr

/-- Whether a typological cell is attested under the universal. The
    only forbidden cell is `overtPROProDrop`. -/
def Typology.isAttested : Typology → Prop
  | .overtPROProDrop => False
  | _                => True

instance (t : Typology) : Decidable t.isAttested := by
  cases t <;> unfold Typology.isAttested <;> infer_instance

namespace ProDropProfile

/-- Classify a profile into one of the four typological cells. -/
def classify (p : ProDropProfile) : Typology :=
  match p.hasOvertPRO, p.allowsProDrop with
  | false, false => .nullPRONoProDrop
  | false, true  => .nullPROProDrop
  | true,  false => .overtPRONoProDrop
  | true,  true  => .overtPROProDrop

/-- A profile satisfies the universal iff its typological cell is
    attested. This is the typology-as-finite-enumeration restatement
    of `Satisfies`. -/
theorem satisfies_iff_attested (p : ProDropProfile) :
    p.Satisfies ↔ p.classify.isAttested := by
  cases hO : p.hasOvertPRO <;> cases hD : p.allowsProDrop <;>
    simp [Satisfies, classify, Typology.isAttested, hO, hD]

end ProDropProfile

/-! ### Universals over subject assignments -/

/-- A language's null-vs-overt decision at every cell of the
    cross-classification. The abstract interface against which
    pro-drop / overt-PRO universals are stated: each framework
    provides its own projection from its inventory type to a
    `SubjectAssignment`, and the universals apply to all of them
    uniformly. -/
abbrev SubjectAssignment := SubjectContext → Exponent

namespace SubjectAssignment

/-- Per-person controlled-subject (PRO) overtness. -/
def hasOvertPROAt (a : SubjectAssignment) (p : Person) : Prop :=
  a (.controlled p) = .overt

instance (a : SubjectAssignment) (p : Person) : Decidable (a.hasOvertPROAt p) :=
  inferInstanceAs (Decidable (_ = _))

/-- Per-person pro-drop: the language drops a matrix finite subject
    of person `p`. -/
def allowsProDropAt (a : SubjectAssignment) (p : Person) : Prop :=
  a (.matrixFinite p) = .null

instance (a : SubjectAssignment) (p : Person) : Decidable (a.allowsProDropAt p) :=
  inferInstanceAs (Decidable (_ = _))

/-- Per-person anti-agreement licensing: the language drops a matrix
    finite subject of person `p` *under Ā-extraction* even when it
    cannot drop the same subject in situ ([baier-2018]). -/
def licensesAntiAgreementAt (a : SubjectAssignment) (p : Person) : Prop :=
  a (.matrixExtracted p) = .null ∧ a (.matrixFinite p) = .overt

instance (a : SubjectAssignment) (p : Person) :
    Decidable (a.licensesAntiAgreementAt p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The language has overt PRO iff EVERY thematic person realizes
    controlled-subject position overtly. The honest quantified
    version of [ostrove-2026]'s "overt PRO" parameter. -/
def hasOvertPRO (a : SubjectAssignment) : Prop :=
  ∀ p ∈ thematicPersons, a.hasOvertPROAt p

instance (a : SubjectAssignment) : Decidable a.hasOvertPRO :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The language allows pro-drop iff SOME thematic person can be
    dropped in matrix finite position. -/
def allowsProDrop (a : SubjectAssignment) : Prop :=
  ∃ p ∈ thematicPersons, a.allowsProDropAt p

instance (a : SubjectAssignment) : Decidable a.allowsProDrop :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The language is *partially* pro-drop: it drops some thematic
    persons but not all. Hebrew (1/2 only), Brazilian Portuguese
    (3rd-person dependent), Finnish (1/2 only). -/
def isPartialProDrop (a : SubjectAssignment) : Prop :=
  a.allowsProDrop ∧ ¬ ∀ p ∈ thematicPersons, a.allowsProDropAt p

instance (a : SubjectAssignment) : Decidable a.isPartialProDrop :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The language exhibits the anti-agreement effect: SOME thematic
    person triggers null subjects only under Ā-extraction. -/
def licensesAntiAgreement (a : SubjectAssignment) : Prop :=
  ∃ p ∈ thematicPersons, a.licensesAntiAgreementAt p

instance (a : SubjectAssignment) : Decidable a.licensesAntiAgreement :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Project the fine assignment down to the coarse two-Boolean profile.
    The Bool fields of `ProDropProfile` are typological observables
    (the data); the abstract `SubjectAssignment` predicates are Prop,
    so we project via `decide`. -/
def toProDropProfile (a : SubjectAssignment) : ProDropProfile :=
  { allowsProDrop := decide a.allowsProDrop,
    hasOvertPRO   := decide a.hasOvertPRO }

/-- [ostrove-2026]'s implicational universal applied to the
    abstract assignment. Defined via the projection so there is one
    canonical `Satisfies` definition (`ProDropProfile.Satisfies`) and
    the assignment-level form is its lift. -/
abbrev Satisfies (a : SubjectAssignment) : Prop :=
  a.toProDropProfile.Satisfies

instance (a : SubjectAssignment) : Decidable a.Satisfies :=
  inferInstanceAs (Decidable (a.toProDropProfile.Satisfies))

end SubjectAssignment

end NullSubject
