import Linglib.Theories.Morphology.Containment

/-!
# Degree Containment and the *ABA Constraint
@cite{bobaljik-2012} @cite{caha-2009}

## The Containment Hypothesis

@cite{bobaljik-2012} argues that the representation of the superlative
properly contains that of the comparative:

    [[[ ADJ ] CMPR ] SPRL ]

The impossible structure is `*[[ ADJ ] SPRL ]` — there is no superlative
morpheme that attaches directly to adjectival roots. Even in languages
like English where `-est` appears to attach directly, a phonologically
null allomorph of CMPR intervenes.

## The *ABA Constraint

Combined with the **Elsewhere Condition** on Vocabulary Insertion
(@cite{halle-marantz-1993}), containment derives the
**Comparative-Superlative Generalization** (CSG): no language has a
pattern `*good – better – goodest` (ABA). If a VI rule inserts
suppletive root B in the CMPR context, and SPRL's representation
contains CMPR's, then B must also win in the SPRL context. There is
no way for the positive root A to "skip" the comparative and resurface
in the superlative.

The attested patterns are:
- **AAA**: regular throughout (`tall – taller – tallest`)
- **ABB**: suppletive CMPR+SPRL (`good – better – best`)
- **ABC**: three distinct roots (`bonus – melior – optimus`)

## Scope Restriction

The CSG as stated by @cite{bobaljik-2012} (p. 2, p. 28) applies to
**relative superlatives** — those involving comparison to a contextual
set. **Absolute superlatives / elatives** (e.g., Italian *bellissimo*
'very beautiful') are a different morphological category whose internal
structure need not contain CMPR, and are therefore not subject to the
containment-based analysis.

## Parallel to Case Containment

This is structurally isomorphic to the *ABA constraint on case
syncretism formalized in `CaseContainment.lean` (@cite{caha-2009}):
`NOM ⊂ ACC ⊂ GEN ⊂ DAT` parallels `POS ⊂ CMPR ⊂ SPRL`. Both are
instances of a hierarchical containment structure where VI + Elsewhere
ordering forces contiguity of suppletive forms. The generic
contiguity predicate shared by both domains is in `Containment.lean`.
-/

namespace Theories.Morphology.DegreeContainment

-- ============================================================================
-- § 1: Degree Grade
-- ============================================================================

/-- The three morphological grades of adjectival degree.
    These are structural layers, not semantic primitives: each higher
    grade's morphosyntactic representation contains the lower ones. -/
inductive DegreeGrade where
  | pos   -- positive: the bare adjective
  | cmpr  -- comparative: ADJ + CMPR
  | sprl  -- superlative: ADJ + CMPR + SPRL
  deriving DecidableEq, Repr, BEq, Hashable

/-- Containment rank: POS < CMPR < SPRL.
    The superlative representation contains three layers, the
    comparative two, and the positive one. -/
def DegreeGrade.rank : DegreeGrade → Nat
  | .pos  => 0
  | .cmpr => 1
  | .sprl => 2

/-- Does grade `inner` have a representation contained within `outer`?
    True when `inner.rank ≤ outer.rank`. -/
def containedIn (inner outer : DegreeGrade) : Bool :=
  inner.rank ≤ outer.rank

-- ============================================================================
-- § 2: Containment Theorems
-- ============================================================================

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
  cases a <;> cases b <;> cases c <;> simp_all [containedIn, DegreeGrade.rank]

-- ============================================================================
-- § 3: Suppletive Degree Patterns
-- ============================================================================

/-- A suppletive pattern over the three grades, represented as
    form-class indices. Two grades share a root iff they have the
    same index.

    Examples:
    - AAA (0,0,0): `tall – taller – tallest`
    - ABB (0,1,1): `good – better – best`
    - ABC (0,1,2): `bonus – melior – optimus`
    - *ABA (0,1,0): `*good – better – goodest` (unattested) -/
structure DegreePattern where
  pos  : Nat
  cmpr : Nat
  sprl : Nat
  deriving DecidableEq, Repr, BEq

/-- Does a pattern violate the *ABA constraint?
    ABA occurs when POS and SPRL share a form that CMPR does not. -/
def DegreePattern.violatesABA (p : DegreePattern) : Bool :=
  p.pos == p.sprl && p.pos != p.cmpr

/-- Is a pattern contiguous? Equivalent to ¬violatesABA.
    Every form class must occupy a contiguous span on the hierarchy. -/
def DegreePattern.isContiguous (p : DegreePattern) : Bool :=
  !p.violatesABA

-- ============================================================================
-- § 4: Pattern Classification
-- ============================================================================

/-- Is this a regular (non-suppletive) paradigm? All three grades
    share the same root. -/
def DegreePattern.isRegular (p : DegreePattern) : Bool :=
  p.pos == p.cmpr && p.cmpr == p.sprl

/-- Is the comparative suppletive (root differs from positive)? -/
def DegreePattern.cmprSuppletive (p : DegreePattern) : Bool :=
  p.pos != p.cmpr

/-- Is the superlative suppletive (root differs from positive)? -/
def DegreePattern.sprlSuppletive (p : DegreePattern) : Bool :=
  p.pos != p.sprl

-- ============================================================================
-- § 5: *ABA Verification
-- ============================================================================

/-- AAA: regular throughout. -/
def aaa : DegreePattern := ⟨0, 0, 0⟩
theorem aaa_contiguous : aaa.isContiguous = true := by native_decide
theorem aaa_regular : aaa.isRegular = true := by native_decide

/-- ABB: suppletive comparative, superlative shares comparative root.
    English `good – better – best`. -/
def abb : DegreePattern := ⟨0, 1, 1⟩
theorem abb_contiguous : abb.isContiguous = true := by native_decide
theorem abb_cmpr_suppletive : abb.cmprSuppletive = true := by native_decide
theorem abb_sprl_suppletive : abb.sprlSuppletive = true := by native_decide

/-- ABC: three distinct roots.
    Latin `bonus – melior – optimus`. -/
def abc : DegreePattern := ⟨0, 1, 2⟩
theorem abc_contiguous : abc.isContiguous = true := by native_decide

/-- *ABA: the unattested pattern. `*good – better – goodest`. -/
def aba : DegreePattern := ⟨0, 1, 0⟩
theorem aba_violates : aba.violatesABA = true := by native_decide
theorem aba_not_contiguous : aba.isContiguous = false := by native_decide

/-- *AAB: unattested. Contiguous by the ABA checker, but excluded
    by VI locality (see § 9). -/
def aab : DegreePattern := ⟨0, 0, 1⟩
theorem aab_contiguous : aab.isContiguous = true := by native_decide

-- ============================================================================
-- § 6: CSG Part I (from Contiguity)
-- ============================================================================

/-- **Comparative-Superlative Generalization, Part I** (@cite{bobaljik-2012}):
    If the comparative is suppletive, then the superlative is also
    suppletive (with respect to the positive).

    This follows from contiguity: if POS ≠ CMPR, then a contiguous
    pattern cannot have POS = SPRL (that would be ABA). -/
theorem csg_part1 (p : DegreePattern)
    (h_contig : p.isContiguous = true)
    (h_cmpr_suppl : p.cmprSuppletive = true) :
    p.sprlSuppletive = true := by
  simp only [DegreePattern.isContiguous, DegreePattern.violatesABA,
    DegreePattern.cmprSuppletive, DegreePattern.sprlSuppletive] at *
  cases h : (p.pos != p.sprl) <;> simp_all

-- ============================================================================
-- § 7: Exhaustive Pattern Check
-- ============================================================================

/-- All logically possible 3-cell patterns with indices 0,1,2.
    There are 27 patterns; exactly 6 violate *ABA. -/
def allPatterns3 : List DegreePattern :=
  (List.map (λ a =>
    (List.map (λ b =>
      List.map (λ c => DegreePattern.mk a b c) [0, 1, 2]
    ) [0, 1, 2]).flatten
  ) [0, 1, 2]).flatten

/-- Exactly 6 of the 27 patterns violate *ABA.
    (3 form-class labels × 2 non-self comparatives each.) -/
theorem six_aba_violations :
    (allPatterns3.filter DegreePattern.violatesABA).length = 6 := by native_decide

/-- No ABA pattern is contiguous. -/
theorem no_aba_contiguous :
    (allPatterns3.filter (λ p => p.violatesABA && p.isContiguous)).length = 0 := by
  native_decide

-- ============================================================================
-- § 8: Deriving a Pattern from Forms
-- ============================================================================

/-- Derive a `DegreePattern` from three surface forms by grouping
    identical strings. Uses the convention that the positive root
    gets index 0, and new roots get fresh indices. -/
def patternFromForms (pos cmpr sprl : String) : DegreePattern :=
  let posIdx := 0
  let cmprIdx := if cmpr == pos then 0 else 1
  let sprlIdx :=
    if sprl == pos then 0
    else if sprl == cmpr then cmprIdx
    else if cmprIdx == 1 then 2 else 1
  ⟨posIdx, cmprIdx, sprlIdx⟩

theorem patternFromForms_aaa :
    patternFromForms "tall" "tall" "tall" = aaa := by native_decide

/-- ABB: comparative and superlative share the same (suppletive) root. -/
theorem patternFromForms_abb :
    patternFromForms "A" "B" "B" = abb := by native_decide

/-- ABC: three distinct roots (Latin bonus–melior–optimus). -/
theorem patternFromForms_abc :
    patternFromForms "A" "B" "C" = abc := by native_decide

-- ============================================================================
-- § 9: CSG Part II from VI Locality
-- ============================================================================

/-- A locality-constrained VI rule for root morphemes in degree
    contexts (@cite{bobaljik-2012}, @cite{bobaljik-2000}).

    Root-out insertion (@cite{bobaljik-2000}) means root VI rules can
    only be conditioned on features in the root's local domain — the
    CMPR head that immediately contains the root. The SPRL head is
    outside CMPR and invisible to root VI.

    `condGrade` is the highest grade whose features the rule checks.
    Locality constrains this to at most CMPR. -/
structure LocalVIRule where
  /-- The form-class index this rule inserts. -/
  formClass : Nat
  /-- The grade whose features condition the rule. -/
  condGrade : DegreeGrade
  /-- Specificity for Elsewhere ordering. -/
  specificity : Nat
  /-- Locality: root VI rules see at most the CMPR layer. -/
  locality : condGrade.rank ≤ DegreeGrade.cmpr.rank

/-- Does a local VI rule match at a given grade? True when the
    conditioning grade's features are present (containment). -/
def LocalVIRule.matches (r : LocalVIRule) (g : DegreeGrade) : Bool :=
  containedIn r.condGrade g

/-- Under locality, a root VI rule that matches at one of CMPR/SPRL
    matches at both — because both representations contain the CMPR
    layer, and the rule is conditioned on ≤ CMPR features. -/
theorem matches_cmpr_eq_sprl (r : LocalVIRule) :
    r.matches .cmpr = r.matches .sprl := by
  simp only [LocalVIRule.matches, containedIn]
  cases h : r.condGrade
  · simp [DegreeGrade.rank]   -- pos: 0 ≤ 1 ↔ 0 ≤ 2
  · simp [DegreeGrade.rank]   -- cmpr: 1 ≤ 1 ↔ 1 ≤ 2
  · exfalso; have := r.locality; simp [h, DegreeGrade.rank] at this

/-- The filter of local VI rules that match CMPR equals the filter
    that match SPRL — the same rules compete at both grades. -/
theorem vi_filter_cmpr_eq_sprl (rules : List LocalVIRule) :
    rules.filter (·.matches .cmpr) = rules.filter (·.matches .sprl) := by
  induction rules with
  | nil => rfl
  | cons r rs ih => simp [List.filter, matches_cmpr_eq_sprl r, ih]

/-- Select the root form at a grade by VI competition: pick the
    highest-specificity matching rule, or the default. -/
def viWinner (rules : List LocalVIRule) (defaultForm : Nat)
    (g : DegreeGrade) : Nat :=
  let matching := rules.filter (·.matches g)
  let sorted := matching.mergeSort (λ a b => a.specificity ≥ b.specificity)
  match sorted.head? with
  | some r => r.formClass
  | none => defaultForm

/-- The degree pattern generated by a VI competition. -/
def viPattern (rules : List LocalVIRule) (defaultForm : Nat) : DegreePattern :=
  ⟨viWinner rules defaultForm .pos,
   viWinner rules defaultForm .cmpr,
   viWinner rules defaultForm .sprl⟩

/-- **Core result**: under locality, VI selects the same root form at
    CMPR and SPRL. The matching rule sets are identical (by
    `vi_filter_cmpr_eq_sprl`), so the Elsewhere winner is the same.

    This is the formal content of @cite{bobaljik-2012}'s containment
    argument: root suppletion at SPRL necessarily entails root suppletion
    at CMPR, and vice versa. -/
theorem vi_cmpr_eq_sprl (rules : List LocalVIRule) (defaultForm : Nat) :
    viWinner rules defaultForm .cmpr = viWinner rules defaultForm .sprl := by
  unfold viWinner
  rw [vi_filter_cmpr_eq_sprl]

/-- **CSG Part I from VI**: if the root is suppletive at CMPR, it is
    also suppletive at SPRL. (Immediate from CMPR cell = SPRL cell.) -/
theorem csg_part1_vi (rules : List LocalVIRule) (defaultForm : Nat)
    (h : (viPattern rules defaultForm).cmprSuppletive = true) :
    (viPattern rules defaultForm).sprlSuppletive = true := by
  simp only [viPattern, DegreePattern.cmprSuppletive, DegreePattern.sprlSuppletive] at *
  rwa [← vi_cmpr_eq_sprl]

/-- **CSG Part II from VI**: if the root is suppletive at SPRL, it is
    also suppletive at CMPR.

    This is the generalization that *cannot* be derived from contiguity
    alone (*AAB is contiguous — see `aab_contiguous`). It requires the
    VI locality argument: since the same rules compete at both CMPR and
    SPRL, the same root wins at both. -/
theorem csg_part2_vi (rules : List LocalVIRule) (defaultForm : Nat)
    (h : (viPattern rules defaultForm).sprlSuppletive = true) :
    (viPattern rules defaultForm).cmprSuppletive = true := by
  simp only [viPattern, DegreePattern.cmprSuppletive, DegreePattern.sprlSuppletive] at *
  rwa [vi_cmpr_eq_sprl]

/-- VI-generated root suppletion patterns can only be AAA or ABB.
    *ABA is excluded by contiguity; *AAB and ABC (for root suppletion)
    are excluded by VI locality. -/
theorem vi_pattern_abb_or_aaa (rules : List LocalVIRule) (defaultForm : Nat) :
    (viPattern rules defaultForm).cmpr = (viPattern rules defaultForm).sprl :=
  vi_cmpr_eq_sprl rules defaultForm

-- ============================================================================
-- § 10: Bridge to Generic Containment
-- ============================================================================

/-- Degree-specific `violatesABA` is the generic contiguity checker
    applied to the 3-position list [pos, cmpr, sprl].

    This makes the isomorphism with case containment structural:
    both `DegreePattern.violatesABA` and `AllomorphyPattern.violatesABA`
    (in `CaseContainment.lean`) reduce to the same generic predicate
    from `Containment.lean`. -/
theorem degree_violatesABA_eq_generic (p : DegreePattern) :
    p.violatesABA =
      Theories.Morphology.Containment.violatesABA [p.pos, p.cmpr, p.sprl] := by
  simp only [DegreePattern.violatesABA,
    Theories.Morphology.Containment.violatesABA_three]

-- ============================================================================
-- § 11: VI Consistency and Attestedness
-- ============================================================================

/-- Is a pattern consistent with VI locality? Under root-out insertion
    (@cite{bobaljik-2000}), the same VI rules compete at CMPR and SPRL,
    so the same root must win at both. This excludes *AAB and restricts
    root suppletion patterns to AAA and ABB. -/
def DegreePattern.isVIConsistent (p : DegreePattern) : Bool :=
  p.cmpr == p.sprl

/-- A pattern is **attested** for root suppletion if it satisfies both
    contiguity (no *ABA) and VI locality (CMPR = SPRL). The conjunction
    restricts root suppletion patterns to exactly AAA and ABB.

    Note: ABC (three distinct roots, e.g., Latin *bonus – melior –
    optimus*) involves affix suppletion, not root suppletion, and is
    attested. Use `isContiguous` alone for the broader generalization
    that includes affix suppletion. -/
def DegreePattern.isAttested (p : DegreePattern) : Bool :=
  p.isContiguous && p.isVIConsistent

/-- VI consistency implies contiguity: if CMPR = SPRL, then trivially
    POS ≠ SPRL → POS ≠ CMPR, so the ABA configuration is impossible. -/
theorem viConsistent_implies_contiguous (p : DegreePattern)
    (h : p.isVIConsistent = true) :
    p.isContiguous = true := by
  simp only [DegreePattern.isVIConsistent, DegreePattern.isContiguous,
    DegreePattern.violatesABA] at *
  cases hps : (p.pos == p.sprl) <;> simp_all

/-- Any VI-generated pattern is VI-consistent (from `vi_cmpr_eq_sprl`). -/
theorem vi_generates_viConsistent (rules : List LocalVIRule) (defaultForm : Nat) :
    (viPattern rules defaultForm).isVIConsistent = true := by
  simp only [DegreePattern.isVIConsistent, viPattern]
  rw [vi_cmpr_eq_sprl]; simp [BEq.beq]

/-- AAA is attested. -/
theorem aaa_attested : aaa.isAttested = true := by native_decide

/-- ABB is attested. -/
theorem abb_attested : abb.isAttested = true := by native_decide

/-- ABC is contiguous but NOT VI-consistent (distinct roots at CMPR
    and SPRL). This is correct: ABC involves affix suppletion, which
    is not constrained by root VI locality. -/
theorem abc_not_viConsistent : abc.isVIConsistent = false := by native_decide
theorem abc_not_attested_root : abc.isAttested = false := by native_decide

/-- *ABA is not attested (fails contiguity). -/
theorem aba_not_attested : aba.isAttested = false := by native_decide

/-- *AAB is not attested (fails VI consistency). -/
theorem aab_not_attested : aab.isAttested = false := by native_decide

end Theories.Morphology.DegreeContainment
