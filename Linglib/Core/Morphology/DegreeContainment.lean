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
elsewhere — see `Theories/Morphology/DM/ContainmentVI.lean` for the
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

/-- Containment rank: POS < CMPR < SPRL. The "containment" relation
    reduces to `rank ≤ rank` on `DegreeGrade`; we don't introduce a
    named `containedIn` wrapper, since `Nat.le_refl` and `Nat.le_trans`
    already provide the algebraic content. -/
def DegreeGrade.rank : DegreeGrade → Nat
  | .pos  => 0
  | .cmpr => 1
  | .sprl => 2

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

/-- A pattern violates the *ABA constraint. By construction the
    case-projection of the generic predicate `Morphology.Containment.ViolatesABA`. -/
def DegreePattern.ViolatesABA (p : DegreePattern) : Prop :=
  Morphology.Containment.ViolatesABA [p.pos, p.cmpr, p.sprl]

instance (p : DegreePattern) : Decidable p.ViolatesABA :=
  inferInstanceAs (Decidable (Morphology.Containment.ViolatesABA _))

/-- A pattern is contiguous: each form class occupies a contiguous span
    on the hierarchy. Equivalent to `¬ ViolatesABA`. -/
def DegreePattern.IsContiguous (p : DegreePattern) : Prop :=
  ¬ p.ViolatesABA

instance (p : DegreePattern) : Decidable p.IsContiguous :=
  inferInstanceAs (Decidable (¬ _))

-- ============================================================================
-- § 3: Pattern Classification
-- ============================================================================

/-- All three grades share the same root (regular paradigm). -/
def DegreePattern.IsRegular (p : DegreePattern) : Prop :=
  p.pos = p.cmpr ∧ p.cmpr = p.sprl

instance (p : DegreePattern) : Decidable p.IsRegular :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Comparative is suppletive (root differs from positive). -/
def DegreePattern.CmprSuppletive (p : DegreePattern) : Prop :=
  p.pos ≠ p.cmpr

instance (p : DegreePattern) : Decidable p.CmprSuppletive :=
  inferInstanceAs (Decidable (_ ≠ _))

/-- Superlative is suppletive (root differs from positive). -/
def DegreePattern.SprlSuppletive (p : DegreePattern) : Prop :=
  p.pos ≠ p.sprl

instance (p : DegreePattern) : Decidable p.SprlSuppletive :=
  inferInstanceAs (Decidable (_ ≠ _))

-- ============================================================================
-- § 4: Concrete Pattern Constants + Verification
-- ============================================================================

/-- AAA: regular throughout. -/
def aaa : DegreePattern := ⟨0, 0, 0⟩

/-- ABB: suppletive comparative; superlative shares comparative root.
    English `good – better – best`. -/
def abb : DegreePattern := ⟨0, 1, 1⟩

/-- ABC: three distinct roots. Latin `bonus – melior – optimus`. -/
def abc : DegreePattern := ⟨0, 1, 2⟩

/-- *ABA: the unattested pattern (`*good – better – goodest`). -/
def aba : DegreePattern := ⟨0, 1, 0⟩

/-- *AAB: contiguous by the generic ABA checker, but excluded by VI
    locality in the DM analysis (see `Theories/Morphology/DM/ContainmentVI.lean`). -/
def aab : DegreePattern := ⟨0, 0, 1⟩

/-! Smoke tests confirming each named pattern resolves correctly.
    Demoted from `theorem` to `example` because nothing in the
    codebase references them by name. -/

example : aaa.IsContiguous := by decide
example : aaa.IsRegular := by decide
example : abb.IsContiguous := by decide
example : abb.CmprSuppletive := by decide
example : abb.SprlSuppletive := by decide
example : abc.IsContiguous := by decide
example : aba.ViolatesABA := by decide
example : ¬ aba.IsContiguous := by decide
example : aab.IsContiguous := by decide

-- ============================================================================
-- § 5: CSG Part I (from Contiguity Alone)
-- ============================================================================

/-- **Comparative-Superlative Generalization, Part I** (@cite{bobaljik-2012}):
    if the comparative is suppletive, then the superlative is also
    suppletive (with respect to the positive). Follows from contiguity
    alone — if POS ≠ CMPR, then a contiguous pattern cannot have
    POS = SPRL (that would be ABA). -/
theorem csg_part1 (p : DegreePattern)
    (h_contig : p.IsContiguous) (h_cmpr_suppl : p.CmprSuppletive) :
    p.SprlSuppletive := by
  intro h_pos_eq_sprl
  apply h_contig
  show Morphology.Containment.ViolatesABA [p.pos, p.cmpr, p.sprl]
  unfold Morphology.Containment.ViolatesABA
  rw [Morphology.Containment.violatesABA_three]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
  exact ⟨h_pos_eq_sprl, h_cmpr_suppl⟩

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

/-! Smoke tests for `patternFromForms` covering the three attested
    pattern types. -/

example : patternFromForms "tall" "tall" "tall" = aaa := by decide
example : patternFromForms "A" "B" "B" = abb := by decide
example : patternFromForms "A" "B" "C" = abc := by decide

end Core.Morphology.DegreeContainment
