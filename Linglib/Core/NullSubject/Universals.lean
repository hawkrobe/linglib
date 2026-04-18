import Linglib.Core.NullSubject.Basic
import Linglib.Core.NullSubject.Defs

/-!
# Universals over Subject Assignments

A `SubjectAssignment` is the abstract interface a syntactic theory
must provide to be evaluated against pro-drop / overt-PRO universals:
a function from a `SubjectContext` (locus of decision) to an
`Exponent` (null vs overt).

Stating the universals over this abstract function type — rather than
over a particular framework's inventory structure (DM vocabulary
items, HPSG `pro-form` lexical entries, LFG f-structure features) —
keeps the typological claims framework-neutral. Each framework
provides its own projection from its inventory type to a
`SubjectAssignment`; the universals here apply to all of them
uniformly.

## Honest quantification

`hasOvertPRO` is `∀ p ∈ thematicPersons, a (.controlled p) = .overt`
(decidable by `decide`). `allowsProDrop` is `∃ p ∈ thematicPersons,
a (.matrixFinite p) = .null`. The Ostrove universal then has its
strongest content: if EVERY thematic person is overt in PRO position,
NO thematic person can be dropped in matrix position.

Per-person predicates `allowsProDropAt`/`hasOvertPROAt` expose the
finer grain that partial-pro-drop languages (Hebrew: 1/2 only;
Brazilian Portuguese: 3rd-person dependent; Finnish: 1/2 only) and
anti-agreement languages (overt only when in situ) require.

## The `Satisfies` predicate is defined exactly once

The two-Boolean `ProDropProfile` (in `Basic.lean`) is the projected
view; `SubjectAssignment.Satisfies` is defined as
`(toProDropProfile a).Satisfies` rather than re-stipulated. The bridge
is then a real reduction (loss of per-person information), not the
identity.
-/

namespace Core.NullSubject

/-- A language's null-vs-overt decision at every cell of the
    cross-classification. The abstract interface against which
    pro-drop / overt-PRO universals are stated. -/
abbrev SubjectAssignment := SubjectContext → Exponent

namespace SubjectAssignment

/-- Per-person controlled-subject (PRO) overtness. -/
def hasOvertPROAt (a : SubjectAssignment) (p : Person) : Bool :=
  a (.controlled p) == .overt

/-- Per-person pro-drop: the language drops a matrix finite subject
    of person `p`. -/
def allowsProDropAt (a : SubjectAssignment) (p : Person) : Bool :=
  a (.matrixFinite p) == .null

/-- Per-person anti-agreement licensing: the language drops a matrix
    finite subject of person `p` *under Ā-extraction* even when it
    cannot drop the same subject in situ (@cite{baier-2018}). -/
def licensesAntiAgreementAt (a : SubjectAssignment) (p : Person) : Bool :=
  (a (.matrixExtracted p) == .null) && (a (.matrixFinite p) == .overt)

/-- The language has overt PRO iff EVERY thematic person realizes
    controlled-subject position overtly. The honest quantified
    version of @cite{ostrove-2026}'s "overt PRO" parameter. -/
def hasOvertPRO (a : SubjectAssignment) : Bool :=
  thematicPersons.all (hasOvertPROAt a)

/-- The language allows pro-drop iff SOME thematic person can be
    dropped in matrix finite position. -/
def allowsProDrop (a : SubjectAssignment) : Bool :=
  thematicPersons.any (allowsProDropAt a)

/-- The language is *partially* pro-drop: it drops some thematic
    persons but not all. Hebrew (1/2 only), Brazilian Portuguese
    (3rd-person dependent), Finnish (1/2 only). -/
def isPartialProDrop (a : SubjectAssignment) : Bool :=
  a.allowsProDrop && !thematicPersons.all (allowsProDropAt a)

/-- The language exhibits the anti-agreement effect: SOME thematic
    person triggers null subjects only under Ā-extraction. -/
def licensesAntiAgreement (a : SubjectAssignment) : Bool :=
  thematicPersons.any (licensesAntiAgreementAt a)

/-- Bridge to the legacy two-Boolean profile in `Basic.lean`. -/
def toProDropProfile (a : SubjectAssignment) : ProDropProfile :=
  { allowsProDrop := a.allowsProDrop, hasOvertPRO := a.hasOvertPRO }

/-- @cite{ostrove-2026}'s implicational universal applied to the
    abstract assignment. Defined via the projection so there is one
    canonical `Satisfies` definition (`ProDropProfile.Satisfies`) and
    the assignment-level form is its lift. -/
abbrev Satisfies (a : SubjectAssignment) : Prop :=
  a.toProDropProfile.Satisfies

instance (a : SubjectAssignment) : Decidable a.Satisfies :=
  inferInstanceAs (Decidable (a.toProDropProfile.Satisfies))

end SubjectAssignment

end Core.NullSubject
