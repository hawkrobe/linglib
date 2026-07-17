import Linglib.Morphology.Paradigm.Contiguity

/-!
# Degree Containment — Substrate
[bobaljik-2012]

Framework-neutral substrate for the three-grade degree hierarchy
(positive, comparative, superlative) and the *ABA generalization over
it: the n = 3 specialization of `Morphology.Paradigm`,
mirroring `Morphology.Case.Allomorphy` for case. `DegreePattern` is the
ergonomic record form; `DegreePattern.toParadigm` connects it to the
general substrate, and all predicates are defined through that
projection, so the generic theory applies by construction.

The empirical generalization [bobaljik-2012] surveys: across languages,
suppletion in adjectival comparison patterns as `tall – taller –
tallest` (AAA), `good – better – best` (ABB), or `bonus – melior –
optimus` (ABC); both `*good – better – goodest` (ABA) and `*good –
gooder – best` (AAB) are unattested. Contiguity excludes only ABA; the
AAB exclusion and the derivations live in the realizational engine
(`Morphology/Containment/Vocabulary.lean`) and are instantiated in
`Studies/Bobaljik2012.lean`.

Scope restriction (cf. [bobaljik-2012] pp. 2, 28): the contiguity claim
concerns *relative* superlatives. Absolute / elatival superlatives
(e.g., Italian *bellissimo*) lack the comparative meaning component and
hence the containment structure.
-/

namespace Morphology.DegreeContainment


/-! ### Degree grades -/

/-- The three morphological grades of adjectival degree. Structural
layers: each higher grade's morphosyntactic representation contains the
lower ones. -/
inductive DegreeGrade where
  | pos   -- positive: the bare adjective
  | cmpr  -- comparative: ADJ + CMPR
  | sprl  -- superlative: ADJ + CMPR + SPRL
  deriving DecidableEq, Repr

/-- The degree grade as a position in the 3-grade hierarchy, for
indexing `Morphology.Containment` machinery. -/
def DegreeGrade.toFin : DegreeGrade → Fin 3
  | .pos  => 0
  | .cmpr => 1
  | .sprl => 2

/-- Containment rank: POS < CMPR < SPRL. Derived from `toFin`. -/
def DegreeGrade.rank (g : DegreeGrade) : Nat := g.toFin

/-! ### DegreePattern -/

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

/-- The general-substrate form of a degree pattern. -/
def DegreePattern.toParadigm (p : DegreePattern) : Paradigm 3 ℕ :=
  ![p.pos, p.cmpr, p.sprl]

@[simp] theorem DegreePattern.toParadigm_zero (p : DegreePattern) :
    p.toParadigm 0 = p.pos := rfl

@[simp] theorem DegreePattern.toParadigm_one (p : DegreePattern) :
    p.toParadigm 1 = p.cmpr := rfl

@[simp] theorem DegreePattern.toParadigm_two (p : DegreePattern) :
    p.toParadigm 2 = p.sprl := rfl

/-- A pattern is contiguous: each form class occupies an interval of
grades. The generic `Morphology.IsContiguous`, by
construction. -/
def DegreePattern.IsContiguous (p : DegreePattern) : Prop :=
  Morphology.IsContiguous p.toParadigm

instance (p : DegreePattern) : Decidable p.IsContiguous :=
  inferInstanceAs (Decidable (Morphology.IsContiguous _))

/-- A pattern violates the *ABA constraint. -/
def DegreePattern.ViolatesABA (p : DegreePattern) : Prop :=
  ¬ p.IsContiguous

instance (p : DegreePattern) : Decidable p.ViolatesABA :=
  inferInstanceAs (Decidable (¬ _))

/-! ### Paradigm classification -/

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

/-! ### Paradigm constants -/

/-- AAA: regular throughout. -/
def aaa : DegreePattern := ⟨0, 0, 0⟩

/-- ABB: suppletive comparative; superlative shares comparative root.
English `good – better – best`. -/
def abb : DegreePattern := ⟨0, 1, 1⟩

/-- ABC: three distinct roots. Latin `bonus – melior – optimus`. -/
def abc : DegreePattern := ⟨0, 1, 2⟩

/-- *ABA: the unattested pattern (`*good – better – goodest`). -/
def aba : DegreePattern := ⟨0, 1, 0⟩

/-- *AAB: contiguous, but unattested — excluded by the vocabulary-level
conditions of `Morphology/Containment/Vocabulary.lean` (`csg2`), not by
contiguity. -/
def aab : DegreePattern := ⟨0, 0, 1⟩

/-! Smoke tests confirming each named pattern resolves correctly. -/

example : aaa.IsContiguous := by decide
example : aaa.IsRegular := by decide
example : abb.IsContiguous := by decide
example : abb.CmprSuppletive := by decide
example : abb.SprlSuppletive := by decide
example : abc.IsContiguous := by decide
example : aba.ViolatesABA := by decide
example : ¬ aba.IsContiguous := by decide
example : aab.IsContiguous := by decide

/-! ### CSG Part I from contiguity alone -/

/-- **Comparative-Superlative Generalization, Part I** ([bobaljik-2012]):
if the comparative is suppletive, the superlative is also suppletive
(with respect to the positive). Follows from contiguity alone — if
POS ≠ CMPR, a contiguous pattern cannot have POS = SPRL (that would be
ABA). -/
theorem csg_part1 (p : DegreePattern)
    (h_contig : p.IsContiguous) (h_cmpr_suppl : p.CmprSuppletive) :
    p.SprlSuppletive := λ heq =>
  h_cmpr_suppl (h_contig (i := 0) (j := 1) (k := 2) (by decide) (by decide) heq)

/-! ### Reading a pattern off realized cells -/

/-- Classify a 3-grade realization into a `DegreePattern` by grouping
identical cells: positive root is index 0, fresh roots get fresh
indices. Connects the realizational engine's output
(`Morphology.Containment.realize`) to the fragment-level pattern
vocabulary; see `Studies/Bobaljik2012.lean` for the worked instances. -/
def degreeShape {F : Type*} [DecidableEq F] (p : Paradigm 3 F) : DegreePattern :=
  let c : Nat := if p 1 = p 0 then 0 else 1
  ⟨0, c, if p 2 = p 0 then 0 else if p 2 = p 1 then c else c + 1⟩

/-- Derive a `DegreePattern` from three surface forms — `degreeShape`
on the form triple. Caveat ([bobaljik-2012] ch. 5 fn. 4): surface-form
identity cannot distinguish suppletion from readjustment (German
*hoch – höher – höchst* would misread as ABA), so fragment entries
record curated patterns rather than applying this to orthography. -/
def patternFromForms (pos cmpr sprl : String) : DegreePattern :=
  degreeShape ![pos, cmpr, sprl]

/-! Smoke tests for `degreeShape` and `patternFromForms` covering the
attested pattern types. -/

example : patternFromForms "tall" "tall" "tall" = aaa := by decide
example : patternFromForms "A" "B" "B" = abb := by decide
example : patternFromForms "A" "B" "C" = abc := by decide
example : degreeShape ![0, 1, 0] = aba := by decide
example : degreeShape ![0, 0, 1] = aab := by decide

end Morphology.DegreeContainment
