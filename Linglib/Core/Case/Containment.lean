import Linglib.Core.Case.Hierarchy

/-!
# Case Containment and the *ABA Constraint
@cite{caha-2009} @cite{mcfadden-2018} @cite{bobaljik-2012}

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

## Connection to Blake

`Core.Case.Hierarchy` formalizes Blake's *typological* hierarchy — an
implicational tendency about which cases languages tend to have.
Caha's containment hierarchy is a different object: a *syntactic*
claim about the internal structure of case representations. The two
are complementary, not competing.
-/

namespace Core

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
def Case.containmentRank : Case → Option Nat
  | .nom => some 0
  | .acc => some 1
  | .gen => some 2
  | .dat => some 3
  | .loc => some 4   -- P layer (postpositions), from the full hierarchy
  | _ => none

/-- Does case `inner` have a representation contained within case `outer`?
    True when `inner.containmentRank ≤ outer.containmentRank`. -/
def Case.containedIn (inner outer : Case) : Bool :=
  match inner.containmentRank, outer.containmentRank with
  | some ri, some ro => ri ≤ ro
  | _, _ => false

-- ============================================================================
-- § 2: Containment Theorems
-- ============================================================================

/-- NOM is contained in every case on the hierarchy. -/
theorem nom_contained_in_acc : Case.containedIn .nom .acc = true := rfl
theorem nom_contained_in_gen : Case.containedIn .nom .gen = true := rfl
theorem nom_contained_in_dat : Case.containedIn .nom .dat = true := rfl

/-- NOM is contained in LOC (postpositional layer). -/
theorem nom_contained_in_loc : Case.containedIn .nom .loc = true := rfl

/-- ACC is contained in GEN, DAT, and LOC but not NOM. -/
theorem acc_contained_in_gen : Case.containedIn .acc .gen = true := rfl
theorem acc_contained_in_dat : Case.containedIn .acc .dat = true := rfl
theorem acc_contained_in_loc : Case.containedIn .acc .loc = true := rfl
theorem acc_not_in_nom : Case.containedIn .acc .nom = false := rfl

/-- Every case contains itself. -/
theorem containment_reflexive (c : Case) (h : c.containmentRank.isSome = true) :
    Case.containedIn c c = true := by
  simp only [Case.containedIn]
  cases c <;> simp_all [Case.containmentRank, Option.isSome]

/-- Containment is transitive. -/
theorem containment_transitive (a b c : Case)
    (hab : Case.containedIn a b = true)
    (hbc : Case.containedIn b c = true) :
    Case.containedIn a c = true := by
  simp only [Case.containedIn] at *
  cases a <;> cases b <;> cases c <;> simp_all [Case.containmentRank]

-- ============================================================================
-- § 3: Nonnominative as a Natural Class
-- ============================================================================

/-- The set of nonnominative cases on the containment hierarchy:
    those whose representation contains ACC.

    @cite{mcfadden-2018} argues this is the key natural class for stem
    allomorphy: a VI rule conditioned on [ACC] captures the
    NOM-vs-oblique split found cross-linguistically. -/
def Case.isNonnom (c : Case) : Bool :=
  Case.containedIn .acc c

theorem acc_is_nonnom : Case.isNonnom .acc = true := rfl
theorem gen_is_nonnom : Case.isNonnom .gen = true := rfl
theorem dat_is_nonnom : Case.isNonnom .dat = true := rfl
theorem loc_is_nonnom : Case.isNonnom .loc = true := rfl
theorem nom_not_nonnom : Case.isNonnom .nom = false := rfl

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
  deriving DecidableEq, BEq, Repr

/-- Does a pattern contain an ABA subsequence? An ABA violation occurs
    when two non-adjacent cases on the containment hierarchy share a form
    that the intervening case does not.

    We check all triples (i, j, k) where i < j < k on the hierarchy
    NOM(0) < ACC(1) < GEN(2) < DAT(3):
    if pattern(i) = pattern(k) ≠ pattern(j), the pattern is ABA. -/
def AllomorphyPattern.violatesABA (p : AllomorphyPattern) : Bool :=
  -- (NOM, ACC, GEN): NOM = GEN ≠ ACC?
  (p.nom == p.gen && p.nom != p.acc) ||
  -- (NOM, ACC, DAT): NOM = DAT ≠ ACC?
  (p.nom == p.dat && p.nom != p.acc) ||
  -- (NOM, GEN, DAT): NOM = DAT ≠ GEN?
  (p.nom == p.dat && p.nom != p.gen) ||
  -- (ACC, GEN, DAT): ACC = DAT ≠ GEN?
  (p.acc == p.dat && p.acc != p.gen)

/-- Is a pattern contiguous? Each form class occupies a contiguous
    span on the containment hierarchy. Equivalent to ¬violatesABA. -/
def AllomorphyPattern.isContiguous (p : AllomorphyPattern) : Bool :=
  !p.violatesABA

-- ============================================================================
-- § 5: *ABA Verification
-- ============================================================================

/-- ABB pattern (NOM vs oblique): the Telugu strong alternation.
    NOM gets form 0, all oblique cases get form 1. Contiguous. -/
def abbPattern : AllomorphyPattern := ⟨0, 1, 1, 1⟩

theorem abb_contiguous : abbPattern.isContiguous = true := by native_decide
theorem abb_no_aba : abbPattern.violatesABA = false := by native_decide

/-- AAB pattern (core vs dative): contiguous. -/
def aabPattern : AllomorphyPattern := ⟨0, 0, 0, 1⟩

theorem aab_contiguous : aabPattern.isContiguous = true := by native_decide

/-- AABB pattern: contiguous (NOM+ACC share form 0, GEN+DAT share form 1). -/
def aabbPattern : AllomorphyPattern := ⟨0, 0, 1, 1⟩

theorem aabb_contiguous : aabbPattern.isContiguous = true := by native_decide

/-- ABAB pattern: the Telugu weak alternation.
    NOM = short (0), ACC = long (1), GEN = short (0), DAT = long (1).
    Violates *ABA — this is the pattern @cite{aitha-2026} argues cannot
    be case-conditioned contextual allomorphy. -/
def ababPattern : AllomorphyPattern := ⟨0, 1, 0, 1⟩

theorem abab_violates_aba : ababPattern.violatesABA = true := by native_decide
theorem abab_not_contiguous : ababPattern.isContiguous = false := by native_decide

/-- ABA pattern (NOM=GEN, ACC different): violates *ABA. -/
def abaPattern : AllomorphyPattern := ⟨0, 1, 0, 0⟩

theorem aba_violates : abaPattern.violatesABA = true := by native_decide

/-- BAB pattern: violates *ABA. -/
def babPattern : AllomorphyPattern := ⟨1, 0, 1, 0⟩

theorem bab_violates : babPattern.violatesABA = true := by native_decide

/-- Uniform pattern (all same form): trivially contiguous. -/
def uniformPattern : AllomorphyPattern := ⟨0, 0, 0, 0⟩

theorem uniform_contiguous : uniformPattern.isContiguous = true := by native_decide

-- ============================================================================
-- § 6: Containment vs. Typological Hierarchy
-- ============================================================================

/-- Containment rank preserves Blake's typological ordering on the core
    cases (NOM, ACC, GEN, DAT): the containment hierarchy is a refinement
    of the typological hierarchy's ordering on these cases.

    Blake's hierarchy: NOM(6) > GEN(5) > DAT(4) > LOC(3) > ...
    Containment:       NOM(0) < ACC(1) < GEN(2) < DAT(3)

    The orderings are *inverses* on the shared cases: Blake ranks by
    "how likely a language is to have it" (NOM most common → highest),
    while containment ranks by "how much structure it contains"
    (NOM least complex → lowest).

    For any two cases with containment ranks r₁ < r₂, their Blake
    ranks satisfy h₁ ≥ h₂ (weakly, since NOM and ACC share Blake rank 6). -/
theorem containment_refines_blake :
    Case.hierarchyRank .nom ≥ Case.hierarchyRank .acc ∧
    Case.hierarchyRank .acc ≥ Case.hierarchyRank .gen ∧
    Case.hierarchyRank .gen ≥ Case.hierarchyRank .dat := by decide

end Core
