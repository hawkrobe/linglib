import Linglib.Syntax.Case.Alignment
import Linglib.Fragments.Mayan.Params

/-!
# Imanishi (2014): Default Ergative

This file formalizes Chapter 3 of [imanishi-2014], the explanation of the alignment puzzle in
the nominative-accusative side of Mayan ergative splits: the non-perfective sentence of
Kaqchikel and of Chol and Q'anjob'al is a non-verbal predicate embedding a nominalized clause,
yet Kaqchikel aligns the transitive object with the ergative morpheme, (87), where Chol and
Q'anjob'al align every subject with it, (88). The Unaccusative Requirement on Nominalization
(90), that nominalized verbs lack an external argument, is parameterized (`URN`); phase head
ergative Case goes to the highest Case-less DP of the nominalized clause when it is spelled
out, absolutive to the matrix-generated subject from Infl and to the object from a nominalized
verb able to assign it (`Nominalization`, `caseOf`). Where the requirement holds the subject
is base-generated in the matrix and the object, left Case-less by the intransitivized verb, is
the highest Case-less DP; where it need not apply the subject stays inside and is that DP,
(141). The two alignments of the summary (178) are the outputs (`caseOf_kaqchikel`,
`caseOf_chol`, `caseOf_qanjobal`), they are the library's `Alignment.invertedErgative` and
`Alignment.extendedErgative`, and the typological gaps (179) and (180), an all-absolutive and
an all-ergative alignment, are underivable (`not_all_abs`, `not_all_erg`).

## Implementation notes

* `S` is treated with `A`, as in the paper's tables; the internal argument of an unaccusative
  is not modelled separately. Ergative from the phase head D is `Case.gen`, as in the
  library's alignments, ERG and GEN being homophonous in Mayan.
* A nominalized verb assigns absolutive to its object when the requirement does not apply and
  either Voice of a low absolutive language or the special suffix of Q'anjob'al, Chuj and
  Jakaltek supplies the Case (Section 3.4.3); a high absolutive language without the suffix
  leaves the object Case-less. Mam's double ergative (181)–(183) and the transitive embedding
  verb *chäp* 'begin' of (94) are outside the model.

## References

* [imanishi-2014]
* [coon-mateo-pedro-preminger-2014]
-/

namespace Imanishi2014

open Alignment

/-- The Unaccusative Requirement on Nominalization, (90): whether nominalized verbs must lack
an external argument, as in Kaqchikel, or need not, as in Chol and Q'anjob'al, (141). -/
inductive URN
  | required
  | optional
  deriving DecidableEq

/-- A language's nominalization on the accusative side of its split: the requirement, the
locus of absolutive Case (`Mayan.ABSPosition`, the Mayan Absolutive Parameter of
[coon-mateo-pedro-preminger-2014]), and whether the nominalized verb carries the suffix that
lets a high absolutive language assign absolutive to its object (Section 3.4.3). -/
structure Nominalization where
  urn : URN
  absPos : Mayan.ABSPosition
  suffix : Prop
  [decSuffix : Decidable suffix]

attribute [instance] Nominalization.decSuffix

namespace Nominalization

variable (L : Nominalization)

/-- The nominalized verb assigns absolutive Case to its object: the requirement does not
intransitivize it, and either Voice of a low absolutive language or the suffix provides the
Case. -/
def VerbAssignsAbs : Prop := L.urn = .optional ∧ (L.absPos = .low ∨ L.suffix)

instance : Decidable L.VerbAssignsAbs := by unfold VerbAssignsAbs; infer_instance

/-- The Case-less DPs of the transitive nominalized clause, highest first: the external
argument when the requirement lets it stay inside, and the object unless the verb assigns
it Case. -/
def caseless : List ArgumentRole :=
  (if L.urn = .optional then [.A] else []) ++ (if L.VerbAssignsAbs then [] else [.P])

/-- Phase head ergative Case: the highest Case-less DP receives ergative from D when the
nominalized clause is spelled out (Section 3.3). -/
def phaseHead (r : ArgumentRole) : Option Case :=
  if L.caseless.head? = some r then some .gen else none

/-- The Case of each core argument on the accusative side: a subject base-generated in the
matrix under the requirement receives absolutive from Infl, an object from a nominalized verb
able to assign it, and otherwise phase head ergative Case or nothing. -/
def caseOf : ArgumentRole → Option Case
  | .A | .S => if L.urn = .required then some .abs else L.phaseHead .A
  | .P => if L.VerbAssignsAbs then some .abs else L.phaseHead .P
  | .R | .T => none

/-- Kaqchikel: the requirement holds, high absolutive, no suffix. -/
def kaqchikel : Nominalization := ⟨.required, .high, False⟩

/-- Chol: the requirement need not apply, low absolutive. -/
def chol : Nominalization := ⟨.optional, .low, False⟩

/-- Q'anjob'al: the requirement need not apply, high absolutive, the suffix *-on* supplying
object Case. -/
def qanjobal : Nominalization := ⟨.optional, .high, True⟩

/-- Tojolabal, (178): low absolutive but subject to the requirement, so Kaqchikel-type. -/
def tojolabal : Nominalization := ⟨.required, .low, False⟩

/-- Kaqchikel's accusative side is the library's inverted ergative alignment, (87): subjects
absolutive, the object ergative. -/
theorem caseOf_kaqchikel :
    ∀ r ∈ [ArgumentRole.A, .S, .P], kaqchikel.caseOf r = some (invertedErgative.assignCase r) := by
  decide

/-- Chol's accusative side is the extended ergative alignment, (88). -/
theorem caseOf_chol :
    ∀ r ∈ [ArgumentRole.A, .S, .P], chol.caseOf r = some (extendedErgative.assignCase r) := by
  decide

/-- Q'anjob'al's accusative side is the extended ergative alignment, its object Case coming
from the suffix rather than from Voice. -/
theorem caseOf_qanjobal :
    ∀ r ∈ [ArgumentRole.A, .S, .P], qanjobal.caseOf r = some (extendedErgative.assignCase r) := by
  decide

/-- Tojolabal patterns with Kaqchikel: the requirement, not the absolutive parameter,
decides the type, (178). -/
theorem caseOf_tojolabal :
    ∀ r ∈ [ArgumentRole.A, .S, .P], tojolabal.caseOf r = some (invertedErgative.assignCase r) := by
  decide

/-- The fragment's progressive entries are the mechanism's outputs. -/
theorem caseKaqchikel_prog (r : ArgumentRole) (h : r ∈ [ArgumentRole.A, .S, .P]) :
    kaqchikel.caseOf r = some (Mayan.caseKaqchikel .Prog r) :=
  caseOf_kaqchikel r h

/-- (178): the subject is absolutive exactly when the requirement holds. -/
theorem caseOf_A_eq_abs_iff : L.caseOf .A = some .abs ↔ L.urn = .required := by
  unfold caseOf phaseHead
  split <;> simp_all

/-- (178): the object is ergative exactly when the requirement holds. -/
theorem caseOf_P_eq_gen_iff : L.caseOf .P = some .gen ↔ L.urn = .required := by
  rcases L with ⟨urn, absPos, suffix⟩
  cases urn <;> simp [caseOf, phaseHead, caseless, VerbAssignsAbs]

/-- Without the requirement the object needs a Case assigner: a high absolutive language
lacking the suffix leaves it Case-less. -/
theorem caseOf_P_eq_none_iff :
    L.caseOf .P = none ↔ L.urn = .optional ∧ L.absPos = .high ∧ ¬ L.suffix := by
  rcases L with ⟨urn, absPos, suffix⟩
  cases urn <;> cases absPos <;> simp [caseOf, phaseHead, caseless, VerbAssignsAbs]

/-- (179): no language aligns both the subject and the object with the absolutive. An
absolutive subject means the requirement holds, so the nominalized verb is intransitivized and
cannot assign the object Case. -/
theorem not_all_abs : ¬ (L.caseOf .A = some .abs ∧ L.caseOf .P = some .abs) := by
  rcases L with ⟨urn, absPos, suffix⟩
  cases urn <;> simp [caseOf, phaseHead, caseless, VerbAssignsAbs]

/-- (180): no language aligns both with the ergative. An ergative subject sits inside the
nominalized clause as its highest Case-less DP, so the object is not the highest. -/
theorem not_all_erg : ¬ (L.caseOf .A = some .gen ∧ L.caseOf .P = some .gen) := by
  rcases L with ⟨urn, absPos, suffix⟩
  cases urn <;> simp [caseOf, phaseHead, caseless, VerbAssignsAbs]

end Nominalization

end Imanishi2014
