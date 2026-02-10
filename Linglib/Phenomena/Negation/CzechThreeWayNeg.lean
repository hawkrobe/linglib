/-!
# Czech Three-Way Negation in Polar Questions

Core empirical data for Staňková (2026), who proposes that negation in Czech
occupies three distinct LF positions in polar questions:

| Position | LF site | Scope   | ne- > PPI | NCI | náhodou | ještě | fakt |
|----------|---------|---------|-----------|-----|---------|-------|------|
| inner    | TP      | narrow  | ✗         | ✓   | ✗       | ✓     | ✓    |
| medial   | ModP    | wide    | ✓         | ✗   | ✗       | ✗     | ✓    |
| outer    | PolP    | widest  | ✓         | ✗   | ✓       | ✗     | ✗    |

The three readings differ in (i) licensing conditions on polarity/concord items,
(ii) compatibility with particles *náhodou* 'by chance', *ještě* 'yet', *fakt*
'really', (iii) scope relative to the evidential bias modal □_ev, and (iv)
syntactic/prosodic encoding (word order and focus).

## Module Structure

This file contains the core three-way distinction: `NegPosition`, `Diagnostic`,
`licenses`, per-cell verification, and scope generalizations. Cross-linguistic
bridges to Romero (2024), Šimík (2024), verb position, and bias profiles are
in `CzechThreeWayNeg.Typology`.

## References

- Staňková, V. (2026). A three-way distinction of negation interpretation in Czech.
- Zeijlstra, H. (2004). Sentential Negation and Negative Concord. LOT.
-/

namespace Phenomena.Negation.CzechThreeWayNeg

-- ============================================================================
-- §1: Three-Way Negation Position
-- ============================================================================

/-- The three LF positions for negation in Czech PQs (Staňková 2026 §3, ex. 16).

  [CP ... [PolP ne-    [ModP ne-     [TP ne-    ]]]]
              OUTER          MEDIAL       INNER
-/
inductive NegPosition where
  /-- Inner negation: in TP, propositional ¬p. Narrow scope.
      Licenses NCIs by Agree, licenses NPIs. Standard sentential negation. -/
  | inner
  /-- Medial negation: in ModP, scopes over □_ev. Wide scope but syntactically low.
      Non-propositional: part of evidential bias presupposition. -/
  | medial
  /-- Outer negation: in PolP, FALSUM operator. Widest scope.
      Maps to high negation (VSO word order). Obligatorily focused. -/
  | outer
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §2: Diagnostic Items
-- ============================================================================

/-- Diagnostics that distinguish the three negation readings (Table 1). -/
inductive Diagnostic where
  /-- ne- outscopes a PPI like *nějaký* 'some.DET.PPI' -/
  | ppiOutscoping
  /-- Negative concord item like *žádný* 'no.DET.NCI' is licensed -/
  | nciLicensed
  /-- Particle *náhodou* 'by chance' is compatible -/
  | nahodou
  /-- Particle *ještě* 'yet/still' is compatible (with telic predicates + neg) -/
  | jeste
  /-- Particle *fakt* 'really' is compatible -/
  | fakt
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- §3: Table 1 — Compatibility Matrix
-- ============================================================================

/-- Table 1 from Staňková (2026 §3): compatibility of each negation reading
with polarity items and particles.

This is the core empirical fingerprint: each negation position has a unique
Boolean signature across the five diagnostics. -/
def licenses : NegPosition → Diagnostic → Bool
  | .outer,  .ppiOutscoping => true
  | .outer,  .nciLicensed   => false
  | .outer,  .nahodou       => true
  | .outer,  .jeste         => false
  | .outer,  .fakt          => false
  | .medial, .ppiOutscoping => true
  | .medial, .nciLicensed   => false
  | .medial, .nahodou       => false
  | .medial, .jeste         => false
  | .medial, .fakt          => true
  | .inner,  .ppiOutscoping => false
  | .inner,  .nciLicensed   => true
  | .inner,  .nahodou       => false
  | .inner,  .jeste         => true
  | .inner,  .fakt          => true

-- ============================================================================
-- §4: Per-Cell Verification Theorems
-- ============================================================================

/-! Each cell of Table 1 gets its own theorem. Changing any single entry in
`licenses` breaks exactly one theorem — maximum interconnection density. -/

-- Outer negation
theorem outer_licenses_ppi     : licenses .outer .ppiOutscoping = true  := rfl
theorem outer_blocks_nci       : licenses .outer .nciLicensed   = false := rfl
theorem outer_licenses_nahodou : licenses .outer .nahodou       = true  := rfl
theorem outer_blocks_jeste     : licenses .outer .jeste         = false := rfl
theorem outer_blocks_fakt      : licenses .outer .fakt          = false := rfl

-- Medial negation
theorem medial_licenses_ppi     : licenses .medial .ppiOutscoping = true  := rfl
theorem medial_blocks_nci       : licenses .medial .nciLicensed   = false := rfl
theorem medial_blocks_nahodou   : licenses .medial .nahodou       = false := rfl
theorem medial_blocks_jeste     : licenses .medial .jeste         = false := rfl
theorem medial_licenses_fakt    : licenses .medial .fakt          = true  := rfl

-- Inner negation
theorem inner_blocks_ppi       : licenses .inner .ppiOutscoping = false := rfl
theorem inner_licenses_nci     : licenses .inner .nciLicensed   = true  := rfl
theorem inner_blocks_nahodou   : licenses .inner .nahodou       = false := rfl
theorem inner_licenses_jeste   : licenses .inner .jeste         = true  := rfl
theorem inner_licenses_fakt    : licenses .inner .fakt          = true  := rfl

-- ============================================================================
-- §5: Uniqueness of Fingerprints
-- ============================================================================

/-- The Boolean signature of a negation position across all five diagnostics. -/
def signature (pos : NegPosition) : List Bool :=
  [ licenses pos .ppiOutscoping
  , licenses pos .nciLicensed
  , licenses pos .nahodou
  , licenses pos .jeste
  , licenses pos .fakt ]

/-- Each negation position has a unique diagnostic signature.
This is the empirical basis for the three-way distinction. -/
theorem signatures_distinct :
    signature .outer ≠ signature .medial ∧
    signature .outer ≠ signature .inner ∧
    signature .medial ≠ signature .inner := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold signature licenses; decide)

/-- The three positions exhaust all negation readings in Czech PQs. -/
theorem positions_exhaustive : ∀ p : NegPosition,
    p = .inner ∨ p = .medial ∨ p = .outer := by
  intro p; cases p <;> simp

-- ============================================================================
-- §6: Scope Generalizations
-- ============================================================================

/-- Only inner negation licenses NCIs — because only inner negation is in the
scope domain of the Agree relation (Zeijlstra 2004). NCIs must be c-commanded
by ¬ at LF. Medial and outer negation are too high. -/
theorem only_inner_licenses_nci :
    (∀ p : NegPosition, licenses p .nciLicensed = true → p = .inner) := by
  intro p h; cases p <;> simp_all [licenses]

/-- Only outer negation licenses *náhodou* — because *náhodou* modifies the
ordering source of the epistemic possibility contributed by FALSUM,
including less stereotypical worlds (Staňková §2.2.1). -/
theorem only_outer_licenses_nahodou :
    (∀ p : NegPosition, licenses p .nahodou = true → p = .outer) := by
  intro p h; cases p <;> simp_all [licenses]

/-- Inner negation does not outscope PPIs — PPIs like *nějaký* must outscope
¬, but inner negation has narrow scope (within TP). So PPIs in the scope of
inner negation yield infelicity. -/
theorem inner_neg_cannot_outscope_ppi :
    licenses .inner .ppiOutscoping = false := rfl

/-- Both medial and outer license PPIs outscoping negation. -/
theorem noninner_licenses_ppi :
    licenses .medial .ppiOutscoping = true ∧
    licenses .outer .ppiOutscoping = true := ⟨rfl, rfl⟩

end Phenomena.Negation.CzechThreeWayNeg
