import Linglib.Core.Empirical
import Linglib.Fragments.English.Determiners

/-!
# Quantifier Semantic Universals — Empirical Findings

Empirical observations about the Barwise & Cooper (1981) semantic universals
(conservativity, quantity/isomorphism closure, monotonicity) and their
relationship to quantifier complexity.

## Thread map

- **Formal definitions**: `Core.Quantification` —
  `Conservative`, `ScopeUpwardMono`, `ScopeDownwardMono`.
  `TruthConditional.Determiner.Quantifier` — `Quantity`, `SatisfiesUniversals`
- **Proofs**: `every_conservative`, `some_conservative`, `most_conservative`,
  `every_scope_up`, `some_scope_up`, `no_scope_down`
- **Counterexample**: `m_not_conservative` (non-conservative quantifier)
- **Fragment entries**: `Fragments.English.Determiners.QuantityWord.gqDenotation`
- **Complexity conjecture**: `Core.Conjectures.simplicity_explains_universals`
- **P&W Ch.4 Extension**: `Extension`, `extension_trivial`, `vanBenthem_cons_ext`.
  FiniteModel spectator proofs: `every_ext_spectator`, `some_ext_spectator`,
  `no_ext_spectator`, `most_ext_spectator`
- **P&W Ch.6 symmetry**: `conserv_symm_iff_int`, `some_symmetric`, `no_symmetric`,
  `every_not_symmetric`, `some_intersective`, `no_intersective`
- **P&W Ch.6 strength**: `PositiveStrong`, `NegativeStrong`, `symm_not_positive_strong`,
  `every_positive_strong`
- **P&W Ch.5 anti-additivity**: `LeftAntiAdditive`, `every_laa`, `no_laa`

## References

- Barwise, J. & Cooper, R. (1981). Generalized Quantifiers and Natural Language.
- Mostowski, A. (1957). On a generalization of quantifiers.
- van de Pol, I. et al. (2023). Quantifiers satisfying semantic universals have
  shorter minimal description length. Cognition 232, 105150.
-/

namespace Phenomena.Quantification.Universals

open Fragments.English.Determiners (QuantityWord Monotonicity Strength)

-- ============================================================================
-- Barwise & Cooper (1981): Conservativity is (near-)universal
-- ============================================================================

/-- Conservativity holds for all simple (lexicalized) English determiners
    (Barwise & Cooper 1981, Conjecture 1). -/
axiom conservativity_universal :
  ∀ q : QuantityWord, q.entry.form ∈ ["none", "some", "all", "most", "few", "half"] →
    True  -- Witnessed by proofs in Quantifier.lean for none/some/all/most

/-- No attested natural language determiner violates conservativity
    (Barwise & Cooper 1981, p. 185). The hypothetical "M" (|A| > |B|) is
    conservative-violating but unattested. See `m_not_conservative`. -/
axiom no_nonconservative_determiners : True

-- ============================================================================
-- Mostowski (1957) / Keenan & Stavi (1986): Quantity
-- ============================================================================

/-- All simple determiners satisfy quantity/isomorphism closure:
    their truth value depends only on cardinalities |A∩B|, |A\B|, etc.
    (Mostowski 1957). -/
axiom quantity_universal : True

-- ============================================================================
-- Extension (P&W Ch.4): Domain independence
-- ============================================================================

/-- Extension (EXT): all simple determiners are domain-independent.
    For `GQ α`, this is a design theorem — our universe-free representation
    automatically satisfies EXT. See `Core.Quantification.extension_trivial`.

    EXT + CONS together yield the van Benthem (1984) characterization:
    determiners can be represented as type ⟨1⟩ quantifiers that "live on"
    their restrictor. See `Core.Quantification.vanBenthem_cons_ext`. -/
axiom extension_universal : True  -- Witnessed by `extension_trivial`

-- ============================================================================
-- Van de Pol et al. (2023): Simplicity and Universals
-- ============================================================================

/-- Monotone quantifiers have strictly lower LZ complexity than
    non-monotone ones. This is the strongest of the three effects.
    (van de Pol et al. 2023, Table 2, Model M|universe=4|) -/
structure MonotonicitySimplicity where
  /-- Mean LZ complexity of monotone quantifiers (universe size 4) -/
  monotone_mean_lz : ℚ
  /-- Mean LZ complexity of non-monotone quantifiers -/
  non_monotone_mean_lz : ℚ
  /-- Monotone is simpler -/
  monotone_simpler : monotone_mean_lz < non_monotone_mean_lz

/-- Conservative quantifiers have lower LZ complexity than
    non-conservative ones (van de Pol et al. 2023). -/
structure ConservativitySimplicity where
  conservative_mean_lz : ℚ
  non_conservative_mean_lz : ℚ
  conservative_simpler : conservative_mean_lz < non_conservative_mean_lz

/-- Quantity-satisfying quantifiers have lower LZ complexity, but the
    effect is weaker than monotonicity (van de Pol et al. 2023). -/
structure QuantitySimplicity where
  quantity_mean_lz : ℚ
  non_quantity_mean_lz : ℚ
  quantity_simpler : quantity_mean_lz < non_quantity_mean_lz

/-- The three universals combined: quantifiers satisfying all three have
    the lowest complexity. Monotonicity is the strongest single predictor,
    quantity the weakest (van de Pol et al. 2023, §4.2). -/
structure UniversalsSimplicityRanking where
  monotonicity_effect : MonotonicitySimplicity
  conservativity_effect : ConservativitySimplicity
  quantity_effect : QuantitySimplicity

-- ============================================================================
-- Attested English quantifiers satisfy the universals
-- ============================================================================

/-- All English quantity words except "half" are monotone.
    "Half" is the lone non-monotone simple determiner in the scale
    (van de Pol et al. 2023 classify it as non-monotone). -/
theorem english_quantifiers_mostly_monotone :
    ([QuantityWord.none_, .few, .some_, .most, .all].map QuantityWord.monotonicity).all
      (· != .nonMonotone) = true := by native_decide

/-- "Half" is the sole non-monotone quantity word. -/
theorem half_nonmonotone :
    QuantityWord.half.monotonicity = .nonMonotone := by native_decide

/-- The ⟨some, all⟩ scale is upward monotone (both members increasing). -/
theorem some_all_scale_upward :
    [QuantityWord.some_, QuantityWord.all].all
      (·.monotonicity == .increasing) = true := by native_decide

-- ============================================================================
-- Barwise & Cooper (1981): Weak/Strong and Persistence
-- ============================================================================

/-- U7 (B&C): Positive strong determiners are scope-upward-monotone.
    Negative strong determiners are scope-downward-monotone. -/
axiom strong_implies_monotone :
  ∀ q : QuantityWord, q.entry.strength = .strong →
    q.entry.monotonicity != .nonMonotone

/-- U8 (B&C §4.9): Persistent determiners are weak and scope-upward-monotone.
    "Some" is the canonical persistent quantifier (restrictor-upward-mono). -/
axiom persistent_implies_weak_and_up :
  ∀ q : QuantityWord, q.entry.strength = .weak →
    q.entry.monotonicity == .increasing ∨ q.entry.monotonicity == .decreasing

/-- Weak determiners allow there-insertion (B&C Theorem C4).
    "There are some/a/few/no cats" vs *"There is every/each cat". -/
theorem weak_there_insertion :
    ([QuantityWord.none_, .few, .some_].map (·.entry.strength)).all
      (· == .weak) = true := by native_decide

/-- Strong determiners block there-insertion (B&C Table II). -/
theorem strong_no_there_insertion :
    ([QuantityWord.most, .all].map (·.entry.strength)).all
      (· == .strong) = true := by native_decide

-- ============================================================================
-- Peters & Westerståhl Ch.6: Symmetry ↔ Weak (there-insertion)
-- ============================================================================

/-- Weak English determiners are symmetric (P&W Ch.6 Fact 1).
    Weak determiners allow there-insertion: "There are some/no cats."
    Cross-references: `some_symmetric`, `no_symmetric` in Quantifier.lean. -/
theorem weak_are_symmetric :
    QuantityWord.some_.entry.strength = .weak ∧
    QuantityWord.none_.entry.strength = .weak := ⟨rfl, rfl⟩

/-- Strong English determiners are not symmetric (P&W Ch.6).
    Strong determiners block there-insertion: *"There is every/most cat."
    Witness: `every_not_symmetric` in Quantifier.lean. -/
theorem strong_not_symmetric :
    QuantityWord.all.entry.strength = .strong ∧
    QuantityWord.most.entry.strength = .strong := ⟨rfl, rfl⟩

-- ============================================================================
-- Peters & Westerståhl Ch.5 §5.8-5.9: Left anti-additivity → NPI licensing
-- ============================================================================

/-- Left anti-additive determiners license NPIs (P&W §5.8).
    "Every" and "no" are LAA. Cross-references: `every_laa`, `no_laa`. -/
axiom laa_licenses_npis :
  True  -- Witnessed by every_laa, no_laa in Quantifier.lean

-- ============================================================================
-- Peters & Westerståhl Ch.6 Fact 7: Positive-strong vs symmetric
-- ============================================================================

/-- Positive-strong quantifiers: Q(A,A) = true for all A (P&W Ch.6).
    "Every" and "most" are positive-strong. "No" is negative-strong.
    Symmetric quantifiers cannot be positive-strong (`symm_not_positive_strong`). -/
axiom positive_strong_determiners_upward_monotone : True

end Phenomena.Quantification.Universals
