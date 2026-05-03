import Linglib.Core.Morphology.Containment

/-!
# Degree Containment — Substrate
@cite{bobaljik-2012}

Framework-neutral substrate for the three-grade degree hierarchy
(positive, comparative, superlative) and the *ABA generalization that
applies to it. Mirrors the structure of `Core.Case.Allomorphy` for
case morphology: an `AllomorphyPattern`-style record + decidable
contiguity predicates derived from the generic
`Morphology.Containment` substrate.

The empirical generalization @cite{bobaljik-2012} surveys: across
languages, suppletion in adjectival comparison patterns as `tall–
taller–tallest` (AAA), `good–better–best` (ABB), or `bonus–melior–
optimus` (ABC); the configuration `*good–better–goodest` (ABA) is
unattested. This file supplies the pattern type and the *ABA
detector. What *explains* the generalization (Containment Hypothesis +
late insertion + Elsewhere ordering) is theory-laden and lives
elsewhere — see `Theories/Morphology/DegreeContainment.lean` for the
DM-flavored VI account and `Phenomena/Comparison/Studies/Bobaljik2012.lean`
for the bundle of CSG predictions and attested-pattern theorems.

Scope restriction (cf. @cite{bobaljik-2012} on relative vs. absolute
superlatives): the contiguity claim concerns *relative* superlatives.
Absolute / elatival superlatives (e.g., Italian *bellissimo*) are a
distinct morphological category whose internal structure need not
contain CMPR.
-/

namespace Core.Morphology.DegreeContainment

-- ============================================================================
-- § 1: Degree Grade
-- ============================================================================

/-- The three morphological grades of adjectival degree. Structural
    layers: each higher grade's morphosyntactic representation contains
    the lower ones. -/
inductive DegreeGrade where
  | pos   -- positive: the bare adjective
  | cmpr  -- comparative: ADJ + CMPR
  | sprl  -- superlative: ADJ + CMPR + SPRL
  deriving DecidableEq, Repr

/-- Containment rank: POS < CMPR < SPRL. -/
def DegreeGrade.rank : DegreeGrade → Nat
  | .pos  => 0
  | .cmpr => 1
  | .sprl => 2

/-- Does grade `inner` have a representation contained within `outer`?
    True when `inner.rank ≤ outer.rank`. -/
def containedIn (inner outer : DegreeGrade) : Bool :=
  inner.rank ≤ outer.rank

/-- POS is contained in every grade. -/
theorem pos_contained_in_cmpr : containedIn .pos .cmpr = true := rfl
theorem pos_contained_in_sprl : containedIn .pos .sprl = true := rfl

/-- CMPR is contained in SPRL but not POS. -/
theorem cmpr_contained_in_sprl : containedIn .cmpr .sprl = true := rfl
theorem cmpr_not_in_pos : containedIn .cmpr .pos = false := rfl

/-- SPRL is not contained in CMPR or POS. -/
theorem sprl_not_in_cmpr : containedIn .sprl .cmpr = false := rfl
theorem sprl_not_in_pos : containedIn .sprl .pos = false := rfl

/-- Every grade contains itself. -/
theorem containment_reflexive (g : DegreeGrade) :
    containedIn g g = true := by
  cases g <;> rfl

/-- Containment is transitive. -/
theorem containment_transitive (a b c : DegreeGrade)
    (hab : containedIn a b = true) (hbc : containedIn b c = true) :
    containedIn a c = true := by
  cases a <;> cases b <;> cases c <;> first | rfl | (simp_all [containedIn, DegreeGrade.rank])

-- ============================================================================
-- § 2: DegreePattern + *ABA
-- ============================================================================

/-- A suppletive pattern over the three grades, indexed by form-class.
    Two grades share a root iff they have the same index.

    Examples:
    - AAA (0,0,0): `tall – taller – tallest`
    - ABB (0,1,1): `good – better – best`
    - ABC (0,1,2): `bonus – melior – optimus`
    - *ABA (0,1,0): unattested. -/
structure DegreePattern where
  pos  : Nat
  cmpr : Nat
  sprl : Nat
  deriving DecidableEq, Repr

/-- Bool decision: does a pattern violate *ABA? Defined as the generic
    contiguity predicate applied to the 3-position projection. -/
def DegreePattern.violatesABA (p : DegreePattern) : Bool :=
  Morphology.Containment.violatesABA [p.pos, p.cmpr, p.sprl]

/-- Bool decision: is a pattern contiguous? Equivalent to ¬violatesABA. -/
def DegreePattern.isContiguous (p : DegreePattern) : Bool :=
  !p.violatesABA

/-- Prop wrapper: a pattern violates *ABA. By construction reduces by
    `rfl` to the generic `Morphology.Containment.ViolatesABA`. -/
def DegreePattern.ViolatesABA (p : DegreePattern) : Prop :=
  Morphology.Containment.ViolatesABA [p.pos, p.cmpr, p.sprl]

instance (p : DegreePattern) : Decidable p.ViolatesABA :=
  inferInstanceAs (Decidable (Morphology.Containment.ViolatesABA _))

/-- Prop wrapper: a pattern is contiguous. -/
def DegreePattern.IsContiguous (p : DegreePattern) : Prop :=
  ¬ p.ViolatesABA

instance (p : DegreePattern) : Decidable p.IsContiguous :=
  inferInstanceAs (Decidable (¬ _))

/-- Bridge: the degree-specific `violatesABA` is the generic predicate
    applied to the 3-position projection. Holds by definition. -/
theorem degree_violatesABA_eq_generic (p : DegreePattern) :
    p.violatesABA =
      Morphology.Containment.violatesABA [p.pos, p.cmpr, p.sprl] := rfl

-- ============================================================================
-- § 3: Pattern Classification
-- ============================================================================

/-- All three grades share the same root (regular paradigm). -/
def DegreePattern.isRegular (p : DegreePattern) : Bool :=
  p.pos == p.cmpr && p.cmpr == p.sprl

/-- Comparative is suppletive (root differs from positive). -/
def DegreePattern.cmprSuppletive (p : DegreePattern) : Bool :=
  p.pos != p.cmpr

/-- Superlative is suppletive (root differs from positive). -/
def DegreePattern.sprlSuppletive (p : DegreePattern) : Bool :=
  p.pos != p.sprl

-- ============================================================================
-- § 4: Concrete Pattern Constants + Verification
-- ============================================================================

/-- AAA: regular throughout. -/
def aaa : DegreePattern := ⟨0, 0, 0⟩
theorem aaa_contiguous : aaa.isContiguous = true := by decide
theorem aaa_regular : aaa.isRegular = true := by decide

/-- ABB: suppletive comparative; superlative shares comparative root.
    English `good – better – best`. -/
def abb : DegreePattern := ⟨0, 1, 1⟩
theorem abb_contiguous : abb.isContiguous = true := by decide
theorem abb_cmpr_suppletive : abb.cmprSuppletive = true := by decide
theorem abb_sprl_suppletive : abb.sprlSuppletive = true := by decide

/-- ABC: three distinct roots. Latin `bonus – melior – optimus`. -/
def abc : DegreePattern := ⟨0, 1, 2⟩
theorem abc_contiguous : abc.isContiguous = true := by decide

/-- *ABA: the unattested pattern (`*good – better – goodest`). -/
def aba : DegreePattern := ⟨0, 1, 0⟩
theorem aba_violates : aba.violatesABA = true := by decide
theorem aba_not_contiguous : aba.isContiguous = false := by decide

/-- *AAB: contiguous by the generic ABA checker, but excluded by VI
    locality in the DM analysis (see `Theories/Morphology/DegreeContainment.lean`). -/
def aab : DegreePattern := ⟨0, 0, 1⟩
theorem aab_contiguous : aab.isContiguous = true := by decide

-- ============================================================================
-- § 5: CSG Part I (from Contiguity Alone)
-- ============================================================================

/-- **Comparative-Superlative Generalization, Part I** (@cite{bobaljik-2012}):
    if the comparative is suppletive, then the superlative is also
    suppletive (with respect to the positive). Follows from contiguity
    alone — if POS ≠ CMPR, then a contiguous pattern cannot have
    POS = SPRL (that would be ABA). -/
theorem csg_part1 (p : DegreePattern)
    (h_contig : p.isContiguous = true)
    (h_cmpr_suppl : p.cmprSuppletive = true) :
    p.sprlSuppletive = true := by
  simp only [DegreePattern.isContiguous, DegreePattern.violatesABA,
    DegreePattern.cmprSuppletive, DegreePattern.sprlSuppletive,
    Morphology.Containment.violatesABA_three] at *
  cases h : (p.pos != p.sprl) <;> simp_all

-- ============================================================================
-- § 6: Deriving a Pattern from Surface Forms
-- ============================================================================

/-- Derive a `DegreePattern` from three surface forms by grouping
    identical strings. Convention: positive root gets index 0; new
    roots get fresh indices. -/
def patternFromForms (pos cmpr sprl : String) : DegreePattern :=
  let posIdx := 0
  let cmprIdx := if cmpr == pos then 0 else 1
  let sprlIdx :=
    if sprl == pos then 0
    else if sprl == cmpr then cmprIdx
    else if cmprIdx == 1 then 2 else 1
  ⟨posIdx, cmprIdx, sprlIdx⟩

theorem patternFromForms_aaa :
    patternFromForms "tall" "tall" "tall" = aaa := by decide

/-- ABB: comparative and superlative share the same suppletive root. -/
theorem patternFromForms_abb :
    patternFromForms "A" "B" "B" = abb := by decide

/-- ABC: three distinct roots (Latin bonus–melior–optimus). -/
theorem patternFromForms_abc :
    patternFromForms "A" "B" "C" = abc := by decide

end Core.Morphology.DegreeContainment
