import Linglib.Theories.Semantics.Tense.TemporalConnectives
import Linglib.Fragments.English.TemporalExpressions

/-!
# Before/After Semantics: Four-Theory Comparison

Compares four theories of English temporal connectives at different
levels of semantic representation:

1. **Level 1 — Under-specification (Anscombe 1964; Krifka 2010b)**: Point-level.
   Single lexical entry per connective. Multiple readings from under-specification
   + pragmatic strengthening. No covert aspectual operators.

2. **Level 2 — Ambiguity (Rett 2020)**: Interval-set-level. Strong defaults
   (before-start, after-finish). Non-default readings require covert
   **INCHOAT** or **COMPLET** operators that incur measurable processing cost.

3. **Level 3 — Quantificational Event (Ogihara & Steinert-Threlkeld 2024)**:
   Event-level. Derives the veridicality asymmetry from quantificational
   structure (∃∃ for *after*, ∃∀ for *before*).

4. **Level 4 — Intensional Uniform (Beaver & Condoravdi 2003)**: World–time pairs
   with historical alternatives. Uniform `earliest` operator for both connectives.
   Derives veridicality from branching time (initial branch point condition).

## Empirical Discriminators

The theories make identical truth-conditional predictions for all 6
scenario/connective combinations (Table 1 of Rett 2020). They diverge on:

1. **Processing cost**: Rett predicts coercion costs; Anscombe/O&ST/B&C do not
2. **Cross-linguistic morphology**: Rett's covert operators have overt reflexes
   (Tagalog PFV.NEUT/AIA, Serbo-Croatian PFV/IMPF)
3. **NPI licensing mechanism**: Anscombe/O&ST from ∀; Rett from Strawson-entailment;
   B&C from the `earliest` operator's universal force
4. **Veridicality derivation**: O&ST and B&C derive it; Anscombe and Rett stipulate it

## References

- Anscombe, E. (1964). Before and after.
- Rett, J. (2020). Eliminating EARLIEST. *Sinn und Bedeutung* 24.
- Ogihara, T. & Steinert-Threlkeld, S. (2024). An interval-based semantics for
  *before* and *after*.
- Beaver, D. & Condoravdi, C. (2003). A uniform analysis of *before* and *after*.
- Alstott, A. & Aravind, A. (2026). Aspectual coercion in *before*/*after*-clauses.
- Krifka, M. (2010b). *Before* and *after* without coercion.
-/

namespace Phenomena.TenseAspect.Compare

open Semantics.Tense.TemporalConnectives
open Fragments.English.TemporalExpressions

-- ============================================================================
-- § 1: Theory Classification
-- ============================================================================

/-- Theories of temporal connective semantics. -/
inductive BeforeAfterTheory where
  | underspecification     -- Anscombe 1964, Krifka 2010b
  | ambiguity              -- Rett 2020
  | quantificationalEvent  -- Ogihara & Steinert-Threlkeld 2024
  | intensionalUniform     -- Beaver & Condoravdi 2003
  deriving DecidableEq, Repr, BEq

/-- Theory profile: what each theory posits and predicts. -/
structure TheoryProfile where
  theory : BeforeAfterTheory
  /-- Single lexical entry per connective (vs. default + coerced pair)? -/
  singleLexicalEntry : Bool
  /-- Does the theory posit covert aspectual coercion operators? -/
  positsCoercion : Bool
  /-- Does the theory predict measurable processing cost for non-default readings? -/
  predictsProcessingCost : Bool
  /-- Mechanism for NPI licensing in *before*-clauses -/
  npiMechanism : String
  /-- Does the theory derive the veridicality asymmetry from its semantics? -/
  derivesVeridicality : Bool := false
  /-- Level of semantic representation (1 = point, 2 = interval, 3 = event, 4 = intensional) -/
  level : Nat := 0
  deriving Repr

-- ============================================================================
-- § 2: Theory Profiles
-- ============================================================================

/-- Anscombe/Krifka: single entry, no coercion, NPIs from ∀ + strong alternatives. -/
def anscombeProfile : TheoryProfile :=
  { theory := .underspecification
  , singleLexicalEntry := true
  , positsCoercion := false
  , predictsProcessingCost := false
  , npiMechanism := "downward entailment from universal quantifier over times"
  , derivesVeridicality := false
  , level := 1 }

/-- Rett: dual entries via coercion, processing cost predicted, NPIs from
    Strawson-entailment of the strong default reading. -/
def rettProfile : TheoryProfile :=
  { theory := .ambiguity
  , singleLexicalEntry := false
  , positsCoercion := true
  , predictsProcessingCost := true
  , npiMechanism := "Strawson-entailment of strong default (before-start)"
  , derivesVeridicality := false
  , level := 2 }

/-- O&ST: event-level quantificational asymmetry derives the veridicality contrast
    directly from the semantics (∃∃ for after, ∃∀ for before). -/
def ostProfile : TheoryProfile :=
  { theory := .quantificationalEvent
  , singleLexicalEntry := true
  , positsCoercion := false
  , predictsProcessingCost := false
  , npiMechanism := "universal quantifier over complement events (∀e₂)"
  , derivesVeridicality := true
  , level := 3 }

/-- B&C: uniform analysis with `earliest` across historical alternatives.
    Veridicality derived from branching time (initial branch point condition),
    not from quantificational asymmetry. Single lexical entry per connective. -/
def bcProfile : TheoryProfile :=
  { theory := .intensionalUniform
  , singleLexicalEntry := true
  , positsCoercion := false
  , predictsProcessingCost := false
  , npiMechanism := "downward entailment from universal quantifier (earliest operator)"
  , derivesVeridicality := true
  , level := 4 }

-- ============================================================================
-- § 3: Empirical Discriminators
-- ============================================================================

/-- Rett predicts processing cost for non-default readings; Anscombe does not.
    This is the core empirical discriminator tested by Alstott & Aravind (2026).
    Completive coercion (Exps 1b, 2), inchoative in after-clauses (Exp 4), and
    cross-linguistic morphology all support the coercion account. -/
def rettPredictsCoercionCost : Bool :=
  rettProfile.predictsProcessingCost && !anscombeProfile.predictsProcessingCost

/-- Rett posits covert operators with cross-linguistic morphological reflexes
    (Tagalog PFV.NEUT/AIA, Serbo-Croatian PFV/IMPF). Anscombe does not. -/
def rettPredictsOvertMorphology : Bool :=
  rettProfile.positsCoercion && !anscombeProfile.positsCoercion

theorem coercion_cost_discriminates : rettPredictsCoercionCost = true := rfl
theorem morphology_discriminates : rettPredictsOvertMorphology = true := rfl
theorem theories_distinct : anscombeProfile.theory ≠ rettProfile.theory := by decide

/-- O&ST and B&C both derive veridicality; Anscombe and Rett do not.
    O&ST derives it from quantificational asymmetry (∃∃ vs ∃∀);
    B&C derives it from branching time (initial branch point condition). -/
theorem veridicality_derivation :
    ostProfile.derivesVeridicality = true ∧
    bcProfile.derivesVeridicality = true ∧
    anscombeProfile.derivesVeridicality = false ∧
    rettProfile.derivesVeridicality = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The four theories form a strict level hierarchy:
    Anscombe (1) < Rett (2) < O&ST (3) < B&C (4). -/
theorem level_hierarchy :
    anscombeProfile.level < rettProfile.level ∧
    rettProfile.level < ostProfile.level ∧
    ostProfile.level < bcProfile.level :=
  ⟨by decide, by decide, by decide⟩

/-- All four theories are distinct. -/
theorem all_theories_distinct :
    anscombeProfile.theory ≠ rettProfile.theory ∧
    anscombeProfile.theory ≠ ostProfile.theory ∧
    anscombeProfile.theory ≠ bcProfile.theory ∧
    rettProfile.theory ≠ ostProfile.theory ∧
    rettProfile.theory ≠ bcProfile.theory ∧
    ostProfile.theory ≠ bcProfile.theory := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

-- ============================================================================
-- § 4: Truth-Conditional Agreement
-- ============================================================================

/-- Both theories make identical truth-conditional predictions for all 6
    scenario types in Rett's (2020) Table 1. They diverge *only* on
    processing predictions and cross-linguistic morphology.

    The 6 scenarios (Rett 2020, Table 1):
    1. process EE + *before* → ≺ initial
    2. culmination EE + *before* → ≺ initial OR ≺ final
    3. process EE + *after* → ≻ initial OR ≻ final
    4. culmination EE + *after* → ≻ final
    5. Stative EE + *before* → ≺ initial
    6. Stative EE + *after* → ≻ initial OR ≻ final

    The theory-level agreement proofs for the unambiguous cases (scenarios 1, 4)
    are in `TemporalConnectives.anscombe_rett_agree_stative_before_start` and
    `rett_implies_anscombe_telic_after_finish` (one-directional: the ↔ is
    false because Anscombe only requires some B-time to precede A, while
    Rett requires A after B's finish). -/
theorem stative_before_default_is_start :
    before_.defaultReading = .beforeStart := rfl

theorem telic_after_default_is_finish :
    after_.defaultReading = .afterFinish := rfl

-- ============================================================================
-- § 5: Fragment Consistency
-- ============================================================================

/-- The Fragment entries correctly reflect the universal NPI asymmetry
    (Heinamäki 1974; Rett 2020, §2.2): *before* licenses NPIs, *after* does not. -/
theorem npi_asymmetry :
    before_.licensesNPI = true ∧ after_.licensesNPI = false :=
  ⟨rfl, rfl⟩

/-- Both connectives are cross-linguistically basic (attested in all 17 languages
    of Rett's typological survey). -/
theorem both_universal :
    before_.crossLinguisticBasic = true ∧ after_.crossLinguisticBasic = true :=
  ⟨rfl, rfl⟩

/-- The *before*/*after* asymmetry is reflected in telicity sensitivity:
    both are sensitive to embedded clause telicity. -/
theorem both_telicity_sensitive :
    before_.embeddedTelicityEffect = true ∧ after_.embeddedTelicityEffect = true :=
  ⟨rfl, rfl⟩

end Phenomena.TenseAspect.Compare
