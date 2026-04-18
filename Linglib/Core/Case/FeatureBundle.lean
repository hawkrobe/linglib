import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.DeriveFintype
import Linglib.Core.Case.Basic
/-!
# Anderson's Case Features
@cite{anderson-jm-2006}

Three first-order case features `[abs, src, loc]`, the 8 case relations
that arise as their feature bundles, the subject-selection hierarchy over
those bundles, predicate scenarios (argument-structure tuples of
relations), and the morphological-case → relation map.

A `CaseRelation` is just a `Finset CaseFeature` — containment, the empty
bundle, the full bundle, and meet/join all come from `Finset`'s
`BooleanAlgebra` instance.
-/

namespace Core

/-- Anderson's three first-order case features (@cite{anderson-jm-2006},
    Ch. 6). -/
inductive CaseFeature where
  | abs
  | src
  | loc
  deriving DecidableEq, Repr, Fintype

/-- An argument's case specification: a bundle of first-order features
    (@cite{anderson-jm-2006}, Ch. 6).

    A `CaseRelation` is a `Finset CaseFeature` — the powerset of the three
    primitive features. The 8 possible bundles are exactly `Finset.powerset`
    of `Finset.univ`. Containment (`⊆`), the empty bundle (`∅`), the full
    bundle (`Finset.univ`), and meet/join are inherited from `Finset`'s
    `BooleanAlgebra` instance. -/
abbrev CaseRelation := Finset CaseFeature

namespace CaseRelation

@[reducible] def neutral    : CaseRelation := ∅
@[reducible] def absolutive : CaseRelation := {.abs}
@[reducible] def ergative   : CaseRelation := {.src}
@[reducible] def locative   : CaseRelation := {.loc}
@[reducible] def srcAbs     : CaseRelation := {.abs, .src}
@[reducible] def srcLoc     : CaseRelation := {.src, .loc}
@[reducible] def absLoc     : CaseRelation := {.abs, .loc}
@[reducible] def absSrcLoc  : CaseRelation := {.abs, .src, .loc}

/-- The full feature set is `Finset.univ` and equals the 3-feature top. -/
theorem absSrcLoc_eq_univ :
    absSrcLoc = (Finset.univ : Finset CaseFeature) := by decide

/-- Convenience accessors for the three features. -/
@[reducible] def abs (cr : CaseRelation) : Prop := .abs ∈ cr
@[reducible] def src (cr : CaseRelation) : Prop := .src ∈ cr
@[reducible] def loc (cr : CaseRelation) : Prop := .loc ∈ cr

end CaseRelation

/-- The subject selection rank (@cite{anderson-jm-2006}, eq. 38').
    src (agent) outranks abs (patient) outranks loc (spatial).

    Codomain `Fin 3` — three tiers, type-level boundedness. -/
def CaseRelation.subjectRank (cr : CaseRelation) : Fin 3 :=
  if .src ∈ cr then 2 else if .abs ∈ cr then 1 else 0

/-- The `src` feature alone determines subject rank 2 — regardless of other
    features. This is why ergative, experiencer (srcLoc), and self-mover
    (srcAbs) all tie for highest subject rank. -/
theorem src_determines_subject_rank (cr : CaseRelation) (h : .src ∈ cr) :
    cr.subjectRank = 2 := by simp [CaseRelation.subjectRank, h]

/-- Without `src`, the `abs` feature determines rank 1. This is why
    absolutive and contactive (absLoc) tie at the second tier. -/
theorem abs_without_src_rank (cr : CaseRelation)
    (h1 : .src ∉ cr) (h2 : .abs ∈ cr) :
    cr.subjectRank = 1 := by simp [CaseRelation.subjectRank, h1, h2]

/-- Anderson's `absSrcLoc` is the top of the feature lattice. -/
theorem absSrcLoc_is_top (cr : CaseRelation) :
    cr ⊆ CaseRelation.absSrcLoc := by
  rw [CaseRelation.absSrcLoc_eq_univ]; exact Finset.subset_univ cr

/-- Anderson's `neutral` (the empty bundle) is the bottom of the feature
    lattice. -/
theorem neutral_is_bottom (cr : CaseRelation) : CaseRelation.neutral ⊆ cr :=
  Finset.empty_subset cr

/-- The 8 possible case relations are exactly
    `(Finset.univ : Finset CaseFeature).powerset`.
    Cardinality follows from `Finset.card_powerset`. -/
theorem CaseRelation.card_all :
    (Finset.univ : Finset CaseFeature).powerset.card = 8 := by decide

/-- A predicate's **scenario** (@cite{anderson-jm-2006}, Ch. 6): the case
    relations assigned to its arguments. -/
structure Scenario where
  relations : List CaseRelation

def Scenario.arity (s : Scenario) : Nat := s.relations.length

def Scenario.subjectRelation (s : Scenario) : Option CaseRelation :=
  s.relations.head?

def Scenario.objectRelation (s : Scenario) : Option CaseRelation :=
  match s.relations with
  | _ :: cr :: _ => some cr
  | _ => none

def Scenario.transitive   : Scenario := ⟨[.ergative, .absolutive]⟩
def Scenario.unergative   : Scenario := ⟨[.ergative]⟩
def Scenario.unaccusative : Scenario := ⟨[.absolutive, .locative]⟩
def Scenario.selfMoving   : Scenario := ⟨[.srcAbs, .locative]⟩
def Scenario.experiencer  : Scenario := ⟨[.srcLoc, .absolutive]⟩

theorem transitive_subject_object :
    Scenario.transitive.subjectRelation = some .ergative ∧
    Scenario.transitive.objectRelation = some .absolutive := ⟨rfl, rfl⟩

theorem unergative_subject_only :
    Scenario.unergative.subjectRelation = some .ergative ∧
    Scenario.unergative.objectRelation = none := ⟨rfl, rfl⟩

theorem unaccusative_subject_loc :
    Scenario.unaccusative.subjectRelation = some .absolutive ∧
    Scenario.unaccusative.objectRelation = some .locative := ⟨rfl, rfl⟩

theorem selfMoving_subject :
    Scenario.selfMoving.subjectRelation = some .srcAbs ∧
    Scenario.selfMoving.objectRelation = some .locative := ⟨rfl, rfl⟩

theorem experiencer_subject_object :
    Scenario.experiencer.subjectRelation = some .srcLoc ∧
    Scenario.experiencer.objectRelation = some .absolutive := ⟨rfl, rfl⟩

theorem transitive_subject_outranks_object :
    CaseRelation.ergative.subjectRank > CaseRelation.absolutive.subjectRank := by
  decide

theorem unergative_unaccusative_differ :
    Scenario.unergative.subjectRelation ≠
    Scenario.unaccusative.subjectRelation := by decide

/-- Canonical mapping from Blake's morphological cases to Anderson's
    case-feature bundles (@cite{anderson-jm-2006}, Ch. 6). -/
def Case.toCaseRelation : Case → Option CaseRelation
  | .nom  => some .srcAbs
  | .acc  => some .absolutive
  | .erg  => some .srcAbs
  | .abs  => some .absolutive
  | .abl  => some .locative
  | .loc  => some .locative
  | .inst => some .ergative
  | _     => none

theorem Case.nom_erg_same_relation :
    Case.toCaseRelation .nom = Case.toCaseRelation .erg := rfl

theorem Case.acc_abs_same_relation :
    Case.toCaseRelation .acc = Case.toCaseRelation .abs := rfl

end Core
