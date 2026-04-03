import Linglib.Core.Case

/-!
# Case Containment and Syncretism
@cite{caha-2009} @cite{mcfadden-2018} @cite{bobaljik-2012} @cite{blake-1994}


## Containment

@cite{caha-2009} proposes that the morphosyntactic representation of each
case on the hierarchy literally *contains* the representations of all
cases below it:

    [[[[[ NOM ] ACC ] GEN ] DAT ] P ]

This means ACC's representation includes NOM's; GEN's includes both
ACC's and NOM's; etc. A Vocabulary Insertion rule conditioned on feature
F therefore matches every case whose representation contains F. A rule
conditioned on ACC matches ACC, GEN, DAT, and P — the set of all
nonnominative cases — explaining the widespread NOM vs. oblique split in
stem allomorphy (@cite{mcfadden-2018}).

## The *ABA Constraint

@cite{bobaljik-2012} and @cite{caha-2009} observe that case-conditioned
suppletion obeys a *contiguity* restriction: if two cases X and Z
(with X ⊂ Y ⊂ Z on the hierarchy) share a suppletive form A, then
the case Y between them must also have form A. The pattern A–B–A
(with B ≠ A) is systematically unattested. This is the **\*ABA
constraint**.

The constraint falls out from containment: if a VI rule inserts form B
in the context of feature F, and Y's representation contains F, then
so does Z's (since Z ⊃ Y ⊃ X). There is no way for Z to "skip" B and
revert to A.

## Syncretism

Syncretism is the systematic neutralization of case distinctions: two or more
cases share a single morphological exponent in some paradigm cells.
@cite{blake-1994} documents syncretism patterns in Latin, Greek, and
other IE languages. He observes that syncretisms cluster into groups
(NOM+ACC vs. DAT+ABL) that are "significant on other grounds" (p. 22).

The **adjacency constraint** — that syncretic cases must be adjacent on the
case hierarchy — is a generalization from the Nanosyntax tradition, not an
explicit claim by Blake. Blake's data is consistent with it.

## Connection to Blake

`Core.Case.Hierarchy` formalizes Blake's *typological* hierarchy — an
implicational tendency about which cases languages tend to have.
Caha's containment hierarchy is a different object: a *syntactic*
claim about the internal structure of case representations. The two
are complementary, not competing.
-/

namespace Theories.Morphology.CaseContainment

open Core

-- ============================================================================
-- § 1: Containment Rank
-- ============================================================================

/-- Caha's containment rank (@cite{caha-2009}). Cases higher on the
    containment hierarchy have representations that include all lower cases.

    [[[[[ NOM ] ACC ] GEN ] DAT ] P ]

    The P(ostpositional) layer includes LOC and other spatial cases whose
    representations contain the full case spine.

    Returns `none` for cases not on the containment hierarchy
    (e.g., ERG/ABS in ergative systems, or minor cases whose containment
    structure is less well established). -/
def containmentRank : Case → Option Nat
  | .nom => some 0
  | .acc => some 1
  | .gen => some 2
  | .dat => some 3
  | .loc => some 4
  | _ => none

/-- Does case `inner` have a representation contained within case `outer`?
    True when `inner.containmentRank ≤ outer.containmentRank`. -/
def containedIn (inner outer : Case) : Bool :=
  match containmentRank inner, containmentRank outer with
  | some ri, some ro => ri ≤ ro
  | _, _ => false

-- ============================================================================
-- § 2: Containment Theorems
-- ============================================================================

/-- NOM is contained in every case on the hierarchy. -/
theorem nom_contained_in_acc : containedIn .nom .acc = true := rfl
theorem nom_contained_in_gen : containedIn .nom .gen = true := rfl
theorem nom_contained_in_dat : containedIn .nom .dat = true := rfl
theorem nom_contained_in_loc : containedIn .nom .loc = true := rfl

/-- ACC is contained in GEN, DAT, and LOC but not NOM. -/
theorem acc_contained_in_gen : containedIn .acc .gen = true := rfl
theorem acc_contained_in_dat : containedIn .acc .dat = true := rfl
theorem acc_contained_in_loc : containedIn .acc .loc = true := rfl
theorem acc_not_in_nom : containedIn .acc .nom = false := rfl

/-- Every case contains itself. -/
theorem containment_reflexive (c : Case) (h : (containmentRank c).isSome = true) :
    containedIn c c = true := by
  simp only [containedIn]
  cases c <;> simp_all [containmentRank, Option.isSome]

/-- Containment is transitive. -/
theorem containment_transitive (a b c : Case)
    (hab : containedIn a b = true)
    (hbc : containedIn b c = true) :
    containedIn a c = true := by
  simp only [containedIn] at *
  cases a <;> cases b <;> cases c <;> simp_all [containmentRank]

-- ============================================================================
-- § 3: Nonnominative as a Natural Class
-- ============================================================================

/-- The set of nonnominative cases on the containment hierarchy:
    those whose representation contains ACC.

    @cite{mcfadden-2018} argues this is the key natural class for stem
    allomorphy: a VI rule conditioned on [ACC] captures the
    NOM-vs-oblique split found cross-linguistically. -/
def isNonnom (c : Case) : Bool :=
  containedIn .acc c

theorem acc_is_nonnom : isNonnom .acc = true := rfl
theorem gen_is_nonnom : isNonnom .gen = true := rfl
theorem dat_is_nonnom : isNonnom .dat = true := rfl
theorem loc_is_nonnom : isNonnom .loc = true := rfl
theorem nom_not_nonnom : isNonnom .nom = false := rfl

-- ============================================================================
-- § 4: The *ABA Constraint
-- ============================================================================

/-- An allomorphy pattern over the four core cases (NOM, ACC, GEN, DAT),
    represented as a form-class index for each case. -/
structure AllomorphyPattern where
  nom : Nat
  acc : Nat
  gen : Nat
  dat : Nat
  deriving DecidableEq, Repr

/-- Does a pattern contain an ABA subsequence? An ABA violation occurs
    when two non-adjacent cases on the containment hierarchy share a form
    that the intervening case does not. -/
def AllomorphyPattern.violatesABA (p : AllomorphyPattern) : Bool :=
  (p.nom == p.gen && p.nom != p.acc) ||
  (p.nom == p.dat && p.nom != p.acc) ||
  (p.nom == p.dat && p.nom != p.gen) ||
  (p.acc == p.dat && p.acc != p.gen)

/-- Is a pattern contiguous? Each form class occupies a contiguous
    span on the containment hierarchy. Equivalent to ¬violatesABA. -/
def AllomorphyPattern.isContiguous (p : AllomorphyPattern) : Bool :=
  !p.violatesABA

-- ============================================================================
-- § 5: *ABA Verification
-- ============================================================================

def abbPattern : AllomorphyPattern := ⟨0, 1, 1, 1⟩
theorem abb_contiguous : abbPattern.isContiguous = true := by native_decide
theorem abb_no_aba : abbPattern.violatesABA = false := by native_decide

def aabPattern : AllomorphyPattern := ⟨0, 0, 0, 1⟩
theorem aab_contiguous : aabPattern.isContiguous = true := by native_decide

def aabbPattern : AllomorphyPattern := ⟨0, 0, 1, 1⟩
theorem aabb_contiguous : aabbPattern.isContiguous = true := by native_decide

def ababPattern : AllomorphyPattern := ⟨0, 1, 0, 1⟩
theorem abab_violates_aba : ababPattern.violatesABA = true := by native_decide
theorem abab_not_contiguous : ababPattern.isContiguous = false := by native_decide

def abaPattern : AllomorphyPattern := ⟨0, 1, 0, 0⟩
theorem aba_violates : abaPattern.violatesABA = true := by native_decide

def babPattern : AllomorphyPattern := ⟨1, 0, 1, 0⟩
theorem bab_violates : babPattern.violatesABA = true := by native_decide

def uniformPattern : AllomorphyPattern := ⟨0, 0, 0, 0⟩
theorem uniform_contiguous : uniformPattern.isContiguous = true := by native_decide

-- ============================================================================
-- § 6: Containment vs. Typological Hierarchy
-- ============================================================================

/-- Containment rank preserves Blake's typological ordering on the core
    cases (NOM, ACC, GEN, DAT): the orderings are *inverses*. Blake ranks
    by "how likely a language is to have it" (NOM most common → highest),
    while containment ranks by "how much structure it contains"
    (NOM least complex → lowest). -/
theorem containment_refines_blake :
    Case.hierarchyRank .nom ≥ Case.hierarchyRank .acc ∧
    Case.hierarchyRank .acc ≥ Case.hierarchyRank .gen ∧
    Case.hierarchyRank .gen ≥ Case.hierarchyRank .dat := by decide

-- ============================================================================
-- § 7: Syncretism
-- ============================================================================

/-- A syncretism pattern: two cases share a morphological exponent. -/
structure Syncretism where
  case1 : Case
  case2 : Case
  neq : case1 ≠ case2
  deriving Repr

/-- Are two cases adjacent on the hierarchy (same rank or ranks differ by 1)? -/
def hierarchyAdjacent (c1 c2 : Case) : Bool :=
  let r1 := c1.hierarchyRank
  let r2 := c2.hierarchyRank
  r1 == r2 || r1 + 1 == r2 || r2 + 1 == r1

/-- Relaxed adjacency: no case in the inventory falls strictly between
    the two syncretic cases on the hierarchy. -/
def inventoryAdjacent (inv : List Case) (c1 c2 : Case) : Bool :=
  let lo := min c1.hierarchyRank c2.hierarchyRank
  let hi := max c1.hierarchyRank c2.hierarchyRank
  !inv.any fun c =>
    c != c1 && c != c2 && c.hierarchyRank > lo && c.hierarchyRank < hi

-- ============================================================================
-- § 8: Well-Known Syncretism Patterns
-- ============================================================================

def nomAccSyncretism : Syncretism :=
  ⟨.nom, .acc, by decide⟩

def comInstSyncretism : Syncretism :=
  ⟨.com, .inst, by decide⟩

-- ============================================================================
-- § 9: Adjacency Theorems
-- ============================================================================

theorem nom_acc_adjacent : hierarchyAdjacent .nom .acc = true := by native_decide
theorem com_inst_adjacent : hierarchyAdjacent .com .inst = true := by native_decide
theorem dat_loc_adjacent : hierarchyAdjacent .dat .loc = true := by native_decide
theorem gen_dat_adjacent : hierarchyAdjacent .gen .dat = true := by native_decide

/-- ERG/INST syncretism does NOT satisfy strict adjacency (ranks 6, 2) —
    this is Blake's known exception, explained by historical derivation. -/
theorem erg_inst_not_strictly_adjacent :
    hierarchyAdjacent .erg .inst = false := by native_decide

/-- But ERG/INST IS inventory-adjacent in a system with only {ERG, ABS, INST}. -/
theorem erg_inst_inv_adjacent :
    inventoryAdjacent [.erg, .abs, .inst] .erg .inst = true := by native_decide

/-- Same-tier cases are always strictly adjacent. -/
theorem same_tier_adjacent (c1 c2 : Case)
    (h : c1.hierarchyRank = c2.hierarchyRank) :
    hierarchyAdjacent c1 c2 = true := by
  simp [hierarchyAdjacent, h]

-- ============================================================================
-- § 10: *ABA and Syncretism
-- ============================================================================

theorem neuter_syncretism_contiguous :
    (AllomorphyPattern.mk 0 0 1 1).isContiguous = true := by native_decide

theorem nom_gen_without_acc_violates_aba :
    (AllomorphyPattern.mk 0 1 0 1).violatesABA = true := by native_decide

theorem acc_gen_syncretism_contiguous :
    (AllomorphyPattern.mk 0 1 1 2).isContiguous = true := by native_decide

theorem gen_dat_syncretism_contiguous :
    (AllomorphyPattern.mk 0 1 2 2).isContiguous = true := by native_decide

theorem nom_dat_syncretism_violates_aba :
    (AllomorphyPattern.mk 0 1 1 0).violatesABA = true := by native_decide

-- ============================================================================
-- § 11: Anderson's Features Explain Syncretism
-- ============================================================================

/-- ERG/INST syncretism: both share the {src} feature despite hierarchy
    non-adjacency. -/
theorem erg_inst_share_src :
    (Case.toCaseRelation .erg).map CaseRelation.src = some true ∧
    (Case.toCaseRelation .inst).map CaseRelation.src = some true ∧
    hierarchyAdjacent .erg .inst = false :=
  ⟨rfl, rfl, by native_decide⟩

/-- NOM/ACC syncretism (neuter nouns): both contain the abs feature. -/
theorem nom_acc_share_abs :
    (Case.toCaseRelation .nom).map CaseRelation.abs = some true ∧
    (Case.toCaseRelation .acc).map CaseRelation.abs = some true :=
  ⟨rfl, rfl⟩

/-- ABL/LOC syncretism: both map to {loc}. -/
theorem abl_loc_same_case_relation :
    Case.toCaseRelation .abl = Case.toCaseRelation .loc := rfl

end Theories.Morphology.CaseContainment
