import Linglib.Core.Prominence

/-!
# Georgian Agreement Fragment @cite{just-2024}

Georgian (Kartvelian) has a polypersonal agreement system where the finite
verb indexes both subject and object. Object agreement is
**person-conditioned**: indirect objects (dative-marked) are cross-referenced
on the verb for 1st/2nd person but not for 3rd person (Harris 1981,
Just 2024, Table 1).

This is **differential P indexing** conditioned by person prominence.

## Agreement Paradigm Overview

Georgian has two sets of verbal agreement markers:

| Set | Position | Function |
|-----|----------|----------|
| Subject markers | prefix/suffix | Always present |
| Object markers | prefix | SAP objects only (differential) |

The object markers are prefixed to the verb stem:
- *m-* 1sg object ("me")
- *g-* 2sg object ("you")
- No marker for 3rd person objects

## Split-Ergative Case

Georgian has a tense/aspect-conditioned split ergative system (Harris 1981):
- Present series: NOM-DAT alignment
- Aorist series: ERG-NOM alignment
- Evidential series: DAT-NOM (inversion)

The agreement split is orthogonal to the case split — object agreement
is person-conditioned regardless of the case frame.

## References

- Harris, A. C. (1981). Georgian Syntax: A Study in Relational Grammar.
  Cambridge University Press.
- Just, E. (2024). A structural and functional comparison of differential A
  and P indexing. Linguistics 62(2): 295–321.
-/

namespace Fragments.Georgian.Agreement

open Core.Prominence

-- ============================================================================
-- § 1: Person-Number Values
-- ============================================================================

/-- Person-number combinations in the Georgian agreement paradigm. -/
inductive PersonNumber where
  | p1sg | p2sg | p3sg | p1pl | p2pl | p3pl
  deriving DecidableEq, BEq, Repr

/-- All person-number values. -/
def allPersonNumbers : List PersonNumber :=
  [.p1sg, .p2sg, .p3sg, .p1pl, .p2pl, .p3pl]

/-- Person value (1, 2, or 3). -/
def PersonNumber.person : PersonNumber → Nat
  | .p1sg | .p1pl => 1
  | .p2sg | .p2pl => 2
  | .p3sg | .p3pl => 3

/-- Is this a SAP (speech act participant)? -/
def PersonNumber.isSAP (pn : PersonNumber) : Bool :=
  pn.person == 1 || pn.person == 2

-- ============================================================================
-- § 2: Object Agreement Markers
-- ============================================================================

/-- Object agreement prefix on the verb (Harris 1981).
    SAP objects receive an overt marker; 3rd person objects receive none. -/
def objectPrefix : PersonNumber → Option String
  | .p1sg => some "m-"
  | .p2sg => some "g-"
  | .p1pl => some "gv-"
  | .p2pl => some "g-"
  | .p3sg => none
  | .p3pl => none

-- ============================================================================
-- § 3: Differential P Indexing
-- ============================================================================

/-- Whether a P/R argument at a given person-number is indexed (triggers
    an object prefix on the verb).

    Derived from `objectPrefix`: a person-number is indexed iff it has
    a non-none object prefix. -/
def pIsIndexed (pn : PersonNumber) : Bool := (objectPrefix pn).isSome

/-- Subject agreement is always present (not differential). -/
def subjectIsIndexed (_ : PersonNumber) : Bool := true

-- ============================================================================
-- § 4: Verification
-- ============================================================================

/-- SAP objects are indexed (receive an overt prefix). -/
theorem sap_objects_indexed :
    pIsIndexed .p1sg = true ∧ pIsIndexed .p2sg = true ∧
    pIsIndexed .p1pl = true ∧ pIsIndexed .p2pl = true := ⟨rfl, rfl, rfl, rfl⟩

/-- 3rd person objects are NOT indexed (no prefix). -/
theorem third_objects_not_indexed :
    pIsIndexed .p3sg = false ∧ pIsIndexed .p3pl = false := ⟨rfl, rfl⟩

/-- P indexing is differential. -/
theorem p_indexing_differential :
    allPersonNumbers.any pIsIndexed = true ∧
    !(allPersonNumbers.all pIsIndexed) = true := ⟨by native_decide, by native_decide⟩

/-- P indexing is grounded in the presence of an object prefix:
    indexed ↔ has overt prefix. -/
theorem indexed_iff_has_prefix :
    allPersonNumbers.all (λ pn =>
      pIsIndexed pn == (objectPrefix pn).isSome) = true := by native_decide

/-- The indexed/not-indexed split aligns with SAP vs 3rd. -/
theorem indexed_iff_sap :
    allPersonNumbers.all (λ pn => pIsIndexed pn == pn.isSAP) = true := by
  native_decide

end Fragments.Georgian.Agreement
