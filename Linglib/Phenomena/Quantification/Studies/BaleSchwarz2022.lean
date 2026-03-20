import Linglib.Core.Empirical
import Linglib.Theories.Semantics.Probabilistic.Measurement.Basic
import Linglib.Fragments.English.MeasurePhrases

/-!
# @cite{bale-schwarz-2022} — Measurements from *per* without complex dimensions
@cite{bale-schwarz-2022} @cite{coppock-2021}

Proceedings of SALT 32: 543--560.

## Key Claims

1. **Against the division theory**: @cite{coppock-2021}'s lexical entry
   ⟦per⟧ = λr. λq. q/r (eq. 1) forms quotient quantities (e.g., 0.9 g/mL).
   This theory both **undergenerates** (fails for measurement verbs, §3)
   and **overgenerates** (predicts unit insensitivity in pseudo-partitives, §6).

2. **Free relatives against polysemy** (exx. 10-14): The division theory's
   escape — making measurement verbs polysemous (eq. 8) — is ruled out
   because *weigh* only admits weight readings, never density.

3. **Anaphoric theory** (eq. 16): ⟦per⟧ = λq. λx. μ_{dim(q)}(x)/q — *per*
   derives measure functions mapping entities to pure numbers via a covert
   pronoun *pro* in the *per*-PP's specifier (eq. 17).

4. **MUCH** (eq. 25): A covert element ⟦MUCH⟧ = λq. λx. μ(x) = q mediates
   pseudo-partitives, with μ underspecified and resolved contextually.

5. **Unit sensitivity** (exx. 37-40, 44-45): The per-unit sets a lower bound
   on the entity's measure. Revised entry (eq. 43) adds a presupposition:
   μ_{dim(q)}(x) ≥ q.

6. **Copular puzzle** (§8): An acknowledged open problem where the anaphoric
   theory assigns density copular sentences a dimension mismatch.

## Connection to @cite{bale-schwarz-2026}

This SALT paper is the precursor to the L&P paper. The anaphoric theory
of *per* originates here. The 2026 paper extends it with:
- The **No Division Hypothesis** (grammar composes via × and +, not ÷)
- The **math speak** analysis (quotient-dimension *per* = mixed quotation)
- The substitution and sub-extraction diagnostics

The 2022 paper uses division explicitly in its lexical entry (eq. 16);
the 2026 paper shows this is reformulable using multiplication only.
-/

namespace Phenomena.Quantification.BaleSchwarz2022

open Semantics.Probabilistic.Measurement
open Fragments.English.MeasurePhrases (gram kilo milliliter liter MeasureTermEntry)
open Core.Empirical (Acceptability)

-- ============================================================================
-- § 1. The Two Theories of *per*
-- ============================================================================

/-- **Division theory** (@cite{coppock-2021}, eq. 1): ⟦per⟧ = λr. λq. q/r.

Takes a denominator quantity r and a numerator quantity q, outputs their
ratio — a quotient quantity in a complex dimension (e.g., g/mL in WT/VOL). -/
def perDivision (r q : ℚ) : ℚ := q / r

/-- **Anaphoric theory** (@cite{bale-schwarz-2022}, eq. 16):
⟦per⟧ = λq. λx. μ_{dim(q)}(x) / q.

Takes a unit quantity q and an entity x, returns a pure number:
the entity's measure in q's dimension, divided by q. The entity
argument is supplied by a covert pronoun *pro* (eq. 17). -/
def perAnaphoric {E : Type*} (μ : MeasureFn E) (q : ℚ) (x : E) : ℚ :=
  μ.apply x / q

-- ============================================================================
-- § 2. Measurement Verb Semantics (eq. 5)
-- ============================================================================

/-- Measurement verb semantics (eq. 5): ⟦weigh⟧ = λq. λx. μ_WT(x) = q.

A measurement verb maps a quantity to a predicate over entities. The verb's
measure function determines which simplex dimension is measured:
μ_WT for *weigh*, μ_VOL for *contain* (in measure readings). -/
def measureVerbSem {E : Type*} (μ : MeasureFn E) (q : ℚ) (x : E) : Bool :=
  decide (μ.apply x = q)

-- ============================================================================
-- § 3. Undergeneration: Dimension Mismatch (§3, exx. 3-9)
-- ============================================================================

/-! ### The dimension mismatch argument

Under the division theory, "The sample weighs 0.9 grams per milliliter"
(ex. 6) assigns the complement the denotation 0.9 g/mL — a quantity in
dimension WT/VOL. But *weigh* outputs quantities in dimension WT (eq. 5).
The predicted truth conditions (eq. 7) are:

    μ_WT(the sample) = 0.9 g/mL

This is a dimension contradiction: μ_WT outputs WT-quantities, but
0.9 g/mL is a WT/VOL-quantity.

The division theory could escape by making *weigh* polysemous: adding
⟦weigh⟧' = λq. λx. μ_{WT/VOL}(x) = q (eq. 8). This would give the
non-contradictory truth conditions μ_{WT/VOL}(sample) = 0.9 g/mL (eq. 9).
But free relatives rule out this polysemy (§4 below). -/

/-- Fragment entries confirm the dimensions involved in the undergeneration:
grams measure mass, milliliters measure volume. -/
theorem undergen_dimensions :
    gram.dimension = .mass ∧ milliliter.dimension = .volume := ⟨rfl, rfl⟩

/-- Density is the quotient of the gram and milliliter dimensions. Under the
division theory, "grams per milliliter" denotes a quantity in this quotient
dimension — incompatible with *weigh*'s simplex mass dimension. -/
theorem density_is_mass_over_volume :
    QuotientDimension.density.components = (.mass, .volume) := rfl

/-- Quotient components are always distinct simplex dimensions. -/
theorem quotient_dimension_differs_from_components (q : QuotientDimension) :
    q.components.1 ≠ q.components.2 :=
  quotient_components_distinct q

-- ============================================================================
-- § 4. Free Relatives Against Polysemy (§3, exx. 10-14)
-- ============================================================================

/-! ### The free relative argument

The division theory's only escape from undergeneration is to make *weigh*
polysemous: the basic meaning (eq. 5) plus a density meaning (eq. 8).
Free relatives rule this out.

(10) "This cube weighs what that cube weighs."
Under the basic meaning: μ_WT(this cube) = μ_WT(that cube) — same WEIGHT ✓
If eq. 8 existed: μ_{WT/VOL}(this cube) = μ_{WT/VOL}(that cube) — same DENSITY

But (10) can ONLY be understood as same weight, not same density: a 1kg cube
and a 2kg cube may have the same density but (10) is clearly false of them.
This extends to comparatives (14a) and wh-interrogatives (14b).

The crucial feature of (10), setting it apart from (3) and (6), is that the
complement of *weigh* does not constrain the dimension — so if the density
meaning existed, nothing would block it. -/

/-- Readings of *weigh*: only weight is attested. The division theory
would need density (eq. 8), but free relatives rule it out. -/
inductive WeighReading where
  | weight   -- μ_WT(x) = q  (eq. 5, attested)
  | density  -- μ_{WT/VOL}(x) = q  (eq. 8, hypothetical, ruled out)
  deriving Repr, DecidableEq, BEq

/-- Free relative data: *weigh* admits only weight readings. -/
structure FreeRelativeDatum where
  surface : String
  reading : WeighReading
  judgment : Acceptability
  deriving Repr, BEq

def ex10_weight : FreeRelativeDatum :=
  { surface := "This cube weighs what that cube weighs"
    reading := .weight, judgment := .ok }

def ex10_density : FreeRelativeDatum :=
  { surface := "This cube weighs what that cube weighs"
    reading := .density, judgment := .unacceptable }

def ex14a : FreeRelativeDatum :=
  { surface := "This cube weighs more than that cube weighs"
    reading := .weight, judgment := .ok }

def ex14b : FreeRelativeDatum :=
  { surface := "What does this cube weigh?"
    reading := .weight, judgment := .ok }

def allFreeRelativeData : List FreeRelativeDatum :=
  [ex10_weight, ex10_density, ex14a, ex14b]

/-- Weight readings are always acceptable; density readings never are.
This rules out the polysemous entry for *weigh* that the division
theory would need — confirming the undergeneration is genuine. -/
theorem free_relatives_rule_out_density :
    ∀ d ∈ allFreeRelativeData,
      (d.reading = .weight → d.judgment = .ok) ∧
      (d.reading = .density → d.judgment = .unacceptable) := by
  simp [allFreeRelativeData]; decide

-- ============================================================================
-- § 5. Compositional Derivation Under the Anaphoric Theory (§4-5, exx. 17-22)
-- ============================================================================

/-! ### Compositional derivation

The anaphoric theory derives truth conditions for (6) "The sample weighs
0.9 grams per milliliter" via the following steps:

1. Parse (eq. 20): [sample] weighs [_MP [_MP 0.9 grams] [_PP pro [per mL]]]
2. ⟦per milliliter⟧ = λx. μ_VOL(x) / mL  (eq. 15, instance of eq. 16)
3. ⟦per milliliter⟧(pro) = μ_VOL(sample) / mL  — a pure number
4. ⟦[MP 0.9 grams] [PP pro per mL]⟧ = (0.9 * μ_VOL(sample)/mL) g  (eq. 19)
5. ⟦weigh⟧(⟦fullMP⟧)(sample): μ_WT(sample) = (0.9 * μ_VOL(sample)/mL) g  (eq. 22)

The final quantity is in dimension WT (mass), matching *weigh*'s selection.
No dimension mismatch arises. -/

/-- Truth conditions under the anaphoric theory (eq. 22):
μ_WT(sample) = numeral * (μ_VOL(sample) / perUnit). -/
def anaphoricTC {E : Type*} (μ_wt μ_vol : MeasureFn E)
    (sample : E) (numeral perUnit : ℚ) : Prop :=
  μ_wt.apply sample = numeral * perAnaphoric μ_vol perUnit sample

/-- The anaphoric theory derives truth conditions for pseudo-partitives
(ex. 27 "The mixture contains 0.1 grams per milliliter of salt") that are
equivalent under the quantity calculus to the division theory's (eq. 32).

Both theories yield: ∃x[salt(x) ∧ μ_WT(x) = (0.1 * μ_VOL(mixture)/mL) g ∧ contain(mixture, x)]

The key difference is structural: the anaphoric theory reaches these truth
conditions without ever forming a quotient quantity (0.1 g/mL), keeping all
composed values in simplex dimensions. This matters because the anaphoric
theory can then add the unit sensitivity presupposition (eq. 43), while the
division theory cannot (the per-unit is structurally inaccessible). -/
theorem anaphoric_tc_equivalent {E : Type*}
    (μ_wt μ_vol : MeasureFn E) (sample : E) (numeral perUnit : ℚ) :
    -- The anaphoric TC unfolds to: μ_wt(sample) = numeral * (μ_vol(sample) / perUnit)
    anaphoricTC μ_wt μ_vol sample numeral perUnit ↔
      μ_wt.apply sample = numeral * (μ_vol.apply sample / perUnit) := by
  simp [anaphoricTC, perAnaphoric]

/-- Both the gram and kilo Fragment entries measure mass — connecting the
truth conditions' μ_wt to the Fragment's lexical data. -/
theorem verb_dimension_matches_fragment :
    gram.dimension = .mass ∧ kilo.dimension = .mass := ⟨rfl, rfl⟩

-- ============================================================================
-- § 6. MUCH and Pseudo-Partitives (§6, exx. 23-32)
-- ============================================================================

/-! ### MUCH: a covert measure term

@cite{bale-schwarz-2022} adopt @cite{nakanishi-2007}'s analysis where a covert
element MUCH mediates pseudo-partitives (eq. 24). MUCH's denotation (eq. 25):

    ⟦MUCH⟧ = λq. λx. μ(x) = q

This is identical to `MeasureTermSem.applyNumeral` — MUCH IS a measure term,
but with an underspecified measure function μ resolved contextually:
- μ_WT in "0.9 grams of salt" (eq. 24a)
- μ_VOL in "0.8 milliliters of salt" (eq. 24b)
- An anaphorically determined function in *per*-phrases (eq. 30) -/

/-- MUCH as a `MeasureTermSem` (eq. 25). The measure function μ is
underspecified — resolved contextually to the appropriate dimension. -/
def MUCH {E : Type*} (μ : MeasureFn E) : MeasureTermSem E :=
  { measureFn := μ }

/-- MUCH's denotation matches measure term semantics by construction:
⟦MUCH⟧(q)(x) = (μ(x) == q) = MeasureTermSem.applyNumeral(q)(x). -/
theorem MUCH_is_measureTerm {E : Type*} (μ : MeasureFn E) (n : ℚ) (x : E) :
    (MUCH μ).applyNumeral n x = (μ.apply x == n) := rfl

/-- The measure verb semantics (eq. 5) is used in the anaphoric derivation:
the truth conditions are stated as measureVerbSem μ_wt q sample = true,
where q is the composed quantity from the anaphoric per-phrase. -/
theorem measureVerb_applied {E : Type*} (μ_wt : MeasureFn E) (q : ℚ) (x : E) :
    measureVerbSem μ_wt q x = decide (μ_wt.apply x = q) := rfl

-- ============================================================================
-- § 7. Unit Sensitivity: Division Theory Overgenerates (§6, exx. 27, 36)
-- ============================================================================

/-! ### Unit insensitivity prediction

The division theory predicts that different unit pairs yielding the same
quotient are interchangeable. Since kg = 1000g and L = 1000mL:

    g/mL = kg/L

So "0.1 grams per milliliter of salt" (ex. 27) should have identical
truth conditions to "0.1 kilograms per liter of salt" (ex. 36a). But
speakers distinguish them: *per liter* implies volume ≥ 1L, while
*per milliliter* implies volume ≥ 1mL only. -/

/-- Quantity division is invariant under uniform scaling: for any
nonzero scaling factor k, q/r = (kq)/(kr). This is why the division
theory cannot distinguish "per milliliter" from "per liter" — they
are related by k = 1000. -/
theorem division_scaling_invariant (r q k : ℚ) (hk : k ≠ 0) :
    perDivision r q = perDivision (k * r) (k * q) := by
  simp only [perDivision, mul_div_mul_left _ _ hk]

/-- Concrete instance: g/mL = kg/L (k = 1000). The division theory
therefore cannot distinguish (27) from (36a). -/
theorem division_unit_insensitive :
    perDivision (1 : ℚ) (1 : ℚ) = perDivision (1000 : ℚ) (1000 : ℚ) := by
  simp [perDivision]

/-- Gram and kilo share the mass dimension; milliliter and liter share volume.
The unit sensitivity argument relies on same-dimension units that differ
in magnitude, not dimension. -/
theorem unit_pairs_share_dimensions :
    gram.dimension = kilo.dimension ∧
    milliliter.dimension = liter.dimension := ⟨rfl, rfl⟩

-- ============================================================================
-- § 8. Unit Sensitivity Data (§6-7, exx. 37-40, 44-45)
-- ============================================================================

/-- Unit sensitivity datum: felicity depends on whether the entity's measure
in the *per*-unit's dimension is at least as large as the unit quantity. -/
structure UnitSensitivityDatum where
  surface : String
  /-- Volume of the entity (in mL). -/
  entityVolume_mL : ℚ
  /-- The *per*-unit quantity (in mL). -/
  perUnit_mL : ℚ
  /-- Is the entity's volume ≥ the per-unit? -/
  presupSatisfied : Bool
  judgment : Acceptability
  deriving Repr, BEq

-- Pseudo-partitive examples (§6, exx. 37-38)

/-- (37) ✓ The 5mL sample contained 0.1 grams of salt per milliliter. -/
def ex37 : UnitSensitivityDatum where
  surface := "The 5 milliliter sample of mixture contained 0.1 grams of salt per milliliter"
  entityVolume_mL := 5; perUnit_mL := 1
  presupSatisfied := true; judgment := .ok

/-- (38a) # The 5mL sample contained 0.1 grams of salt per liter. -/
def ex38a : UnitSensitivityDatum where
  surface := "The 5 milliliter sample of mixture contained 0.1 grams of salt per liter"
  entityVolume_mL := 5; perUnit_mL := 1000
  presupSatisfied := false; judgment := .anomalous

/-- (38b) # The 0.1mL sample contained 0.1 grams of salt per milliliter. -/
def ex38b : UnitSensitivityDatum where
  surface := "The 0.1 milliliter sample of mixture contained 0.1 grams of salt per milliliter"
  entityVolume_mL := (1 : ℚ) / 10; perUnit_mL := 1
  presupSatisfied := false; judgment := .anomalous

-- Measurement verb examples (§7, exx. 44-45)

/-- (44) ✓ The 5mL portion weighed 0.9 grams per milliliter. -/
def ex44 : UnitSensitivityDatum where
  surface := "The 5 milliliter portion of solution weighed 0.9 grams per milliliter"
  entityVolume_mL := 5; perUnit_mL := 1
  presupSatisfied := true; judgment := .ok

/-- (45a) # The 5mL portion weighed 0.9 kilograms per liter. -/
def ex45a : UnitSensitivityDatum where
  surface := "The 5 milliliter portion of solution weighed 0.9 kilograms per liter"
  entityVolume_mL := 5; perUnit_mL := 1000
  presupSatisfied := false; judgment := .anomalous

/-- (45b) # The 0.1mL portion weighed 0.9 grams per milliliter. -/
def ex45b : UnitSensitivityDatum where
  surface := "The 0.1 milliliter portion of solution weighed 0.9 grams per milliliter"
  entityVolume_mL := (1 : ℚ) / 10; perUnit_mL := 1
  presupSatisfied := false; judgment := .anomalous

def allUnitSensitivityData : List UnitSensitivityDatum :=
  [ex37, ex38a, ex38b, ex44, ex45a, ex45b]

-- ============================================================================
-- § 9. Unit Sensitivity Beyond Chemistry (exx. 39-40)
-- ============================================================================

/-! ### Typos per page: unit sensitivity generalizes

Unit sensitivity extends beyond chemistry to any *per*-phrase. Exx. (39-40)
show that text-length units exhibit the same pattern:
- A monograph has at least one page → "per page" OK (39a)
- A paragraph has at least one line → "per line" OK (39b)
- A paragraph has less than a page → "#per page" anomalous (40) -/

/-- Text-domain unit sensitivity data (exx. 39-40). -/
structure TextUnitDatum where
  surface : String
  presupSatisfied : Bool
  judgment : Acceptability
  deriving Repr, BEq

/-- (39a) ✓ The monograph by Dole contained more than 3 typos per page. -/
def ex39a : TextUnitDatum :=
  { surface := "The monograph by Dole contained more than 3 typos per page"
    presupSatisfied := true, judgment := .ok }

/-- (39b) ✓ The paragraph by Dole contained more than 3 typos per line. -/
def ex39b : TextUnitDatum :=
  { surface := "The paragraph by Dole contained more than 3 typos per line"
    presupSatisfied := true, judgment := .ok }

/-- (40) # The paragraph by Dole contained more than 3 typos per page. -/
def ex40 : TextUnitDatum :=
  { surface := "The paragraph by Dole contained more than 3 typos per page"
    presupSatisfied := false, judgment := .anomalous }

def allTextUnitData : List TextUnitDatum := [ex39a, ex39b, ex40]

/-- Unit sensitivity in the text domain matches the presupposition prediction:
presup satisfied → ok, presup violated → anomalous. -/
theorem text_unit_sensitivity :
    ∀ d ∈ allTextUnitData,
      (d.presupSatisfied = true → d.judgment = .ok) ∧
      (d.presupSatisfied = false → d.judgment = .anomalous) := by
  simp [allTextUnitData]; decide

-- ============================================================================
-- § 10. Unit Sensitivity Presupposition (§7, eq. 43)
-- ============================================================================

/-- The presupposition from eq. (43): μ_{dim(q)}(x) ≥ q.

The entity's measure in the per-unit's dimension must be at least the
unit quantity. This is the only addition eq. (43) makes over eq. (16) —
the at-issue content (the pure number μ(x)/q) is unchanged, i.e., it
is still `perAnaphoric μ q x`.

Note: `PrProp` (from `Core.Presupposition`) is not used here because
*per*'s at-issue content is a pure number (ℚ), not a truth value (Bool).
`PrProp` models presupposed propositions; eq. (43) is a presupposed value. -/
def perPresup {E : Type*} (μ : MeasureFn E) (q : ℚ) (x : E) : Bool :=
  decide (μ.apply x ≥ q)

/-- The presupposition is satisfied iff the entity's measure ≥ the unit. -/
theorem presup_satisfied_iff {E : Type*} (μ : MeasureFn E) (q : ℚ) (x : E) :
    perPresup μ q x = true ↔ μ.apply x ≥ q := by
  simp [perPresup, decide_eq_true_eq]

/-- The `presupSatisfied` field in each datum correctly reflects the
entity volume ≥ per-unit comparison. -/
theorem presup_matches_data :
    ∀ d ∈ allUnitSensitivityData,
      d.presupSatisfied = decide (d.entityVolume_mL ≥ d.perUnit_mL) := by
  simp [allUnitSensitivityData]; native_decide

/-- Presupposition satisfaction predicts acceptability: satisfied → ok,
not satisfied → anomalous. -/
theorem presup_predicts_felicity :
    ∀ d ∈ allUnitSensitivityData,
      (d.presupSatisfied = true → d.judgment = .ok) ∧
      (d.presupSatisfied = false → d.judgment = .anomalous) := by
  simp [allUnitSensitivityData]; decide

/-- The anaphoric theory distinguishes "per milliliter" from "per liter"
via different presuppositions, even when the ratios are numerically equal. -/
theorem anaphoric_distinguishes_units {E : Type*} (μ : MeasureFn E) (x : E)
    (h : μ.apply x = 5) :
    -- per milliliter: presup μ(x) ≥ 1 — satisfied (5 ≥ 1)
    decide (μ.apply x ≥ 1) = true ∧
    -- per liter: presup μ(x) ≥ 1000 — NOT satisfied (5 < 1000)
    decide (μ.apply x ≥ 1000) = false := by
  simp [h]; decide

-- ============================================================================
-- § 11. Copular Puzzle (§8, exx. 46-49)
-- ============================================================================

/-! ### Open problem: copular density sentences

"The sample's density is 0.9 grams per milliliter" (ex. 46) is problematic
for the anaphoric theory. The *per*-PP denotes a pure number, so the MP
"0.9 grams per milliliter" denotes a weight quantity (dimension WT). But
the copular sentence equates the sample's density (dimension WT/VOL) with
a weight quantity — a dimension mismatch.

Under the division theory, (46) is straightforward: the MP denotes 0.9 g/mL,
a quotient quantity matching the density dimension.

@cite{bale-schwarz-2022} note that *for every* paraphrases (ex. 48: "0.9 grams
for every cubic centimeter") and naturally occurring density expressions
(ex. 49: "968 people for every km²") suggest that density copular sentences
may not require quantity division. This remains an open question. -/

/-- Under the anaphoric theory, the MP's dimension is determined by its
head noun. "Grams" → mass (a simplex `Dimension`). But density predicates
expect WT/VOL (a `QuotientDimension`). These are structurally incompatible:
`Dimension` and `QuotientDimension` are different types in the formalization,
and the MP is typed as mass, not as mass/volume. -/
theorem copular_anaphoric_mismatch :
    gram.dimension = .mass ∧
    QuotientDimension.density.components = (.mass, .volume) := ⟨rfl, rfl⟩

/-- Under the division theory, the copular sentence works: the MP denotes
a quotient quantity whose numerator and denominator match the Fragment
entries for "gram" (mass) and "milliliter" (volume) — precisely the
components of the density dimension. -/
theorem copular_division_matches :
    QuotientDimension.density.components =
      (gram.dimension, milliliter.dimension) := rfl

/-- Copular density examples (exx. 46-49). -/
structure CopularDatum where
  surface : String
  /-- Does the sentence use *per* (quantity-division vocabulary)? -/
  usesPer : Bool
  judgment : Acceptability
  deriving Repr, BEq

/-- (46) The sample's density is 0.9 grams per milliliter. -/
def ex46 : CopularDatum :=
  { surface := "The sample's density is 0.9 grams per milliliter"
    usesPer := true, judgment := .ok }

/-- (47) #The sample's density is 0.9 grams.
Without *per*, the MP denotes a WT quantity — dimension mismatch
with density (WT/VOL) regardless of theory. -/
def ex47 : CopularDatum :=
  { surface := "The sample's density is 0.9 grams"
    usesPer := false, judgment := .anomalous }

/-- (48) The sample's density is 0.9 grams for every cubic centimeter.
*For every* paraphrase — expresses density WITHOUT quantity-division
vocabulary. Challenges the assumption that copular density requires *per*. -/
def ex48 : CopularDatum :=
  { surface := "The sample's density is 0.9 grams for every cubic centimeter"
    usesPer := false, judgment := .ok }

/-- (49) London's population density is 968 people for every km².
Naturally occurring density expression without *per*. -/
def ex49 : CopularDatum :=
  { surface := "London's population density is 968 people for every km²"
    usesPer := false, judgment := .ok }

def allCopularData : List CopularDatum := [ex46, ex47, ex48, ex49]

/-- Density copular sentences are felicitous with *per* (46) and with
*for every* (48, 49), but not with bare measure phrases (47). The
*for every* paraphrases show that density can be expressed without
quantity-division vocabulary — undermining the division theory's
advantage on copular data. -/
theorem copular_without_per :
    ex48.usesPer = false ∧ ex48.judgment = .ok ∧
    ex49.usesPer = false ∧ ex49.judgment = .ok := ⟨rfl, rfl, rfl, rfl⟩

/-- The only anomalous copular datum is the bare MP (47). -/
theorem copular_bare_mp_anomalous :
    ex47.usesPer = false ∧ ex47.judgment = .anomalous := ⟨rfl, rfl⟩

-- ============================================================================
-- § 12. End-to-End Compositional Derivation (§4-5, exx. 15-22)
-- ============================================================================

/-! ### Dimension-tracking derivation for ex. (6) / eq. (20)

"The sample weighs 0.9 grams per milliliter"

Tree structure (eq. 20):
```
        S
       / \
   the    VP
  sample / \
      weighs  MP
             / \
          MP     PP
         / \   / \
       0.9 g pro  P'
                 / \
              per   mL
```

The paper's derivation uses dimensioned quantities throughout.
The central insight of the anaphoric theory is that **no quotient
dimension is ever composed**: `per` outputs a pure number (dimension
ID), multiplication preserves the original dimension (WT), and
`weigh` receives a WT quantity — dimensions match at every step.

We track dimensions explicitly via `Quantity` to verify this. -/

section Derivation

variable {E : Type*}

/-- A dimensioned quantity: a rational value tagged with its dimension.
This is the paper's notation "0.9g" = ⟨0.9, .mass⟩. -/
structure Quantity where
  value : ℚ
  dim : Dimension
  deriving Repr, BEq, DecidableEq

/-- A unit quantity: 1 in a given dimension (e.g., g = ⟨1, .mass⟩). -/
def unitQuantity (d : Dimension) : Quantity := ⟨1, d⟩

/-- Numeral × unit = quantity (e.g., 0.9 * g = 0.9g).
The dimension comes from the unit. -/
def numeralTimesUnit (n : ℚ) (unit : Quantity) : Quantity :=
  ⟨n * unit.value, unit.dim⟩

/-- Quantity × pure number = quantity, preserving dimension (eq. 18).
This is the multiplication that combines "0.9 grams" with the pure
number from the *per*-PP. The dimension is preserved — NO quotient
dimension is formed. -/
def quantityTimesNumber (q : Quantity) (n : ℚ) : Quantity :=
  ⟨q.value * n, q.dim⟩

-- Step-by-step derivation matching eqs. (15)-(22)

/-- ⟦per milliliter⟧ = λx. μ_VOL(x) / mL (eq. 15).
Instance of eq. (16): ⟦per⟧ = λq. λx. μ_{dim(q)}(x) / q.
Output type: E → ℚ (entity to **pure number**). -/
def step_perMilliliter (μ_vol : MeasureFn E) (mL : Quantity) : E → ℚ :=
  fun x => μ_vol.apply x / mL.value

/-- ⟦[PP pro [per milliliter]]⟧ = μ_VOL(pro) / mL (FA).
*pro* is resolved to the subject. Result: a **pure number**. -/
def step_PP (μ_vol : MeasureFn E) (mL : Quantity) (pro : E) : ℚ :=
  step_perMilliliter μ_vol mL pro

/-- ⟦[MP 0.9 grams]⟧ = 0.9 * g = 0.9g.
A **quantity in dimension WT** (mass). -/
def step_innerMP (numeral : ℚ) (unit : Quantity) : Quantity :=
  numeralTimesUnit numeral unit

/-- ⟦[MP [MP 0.9 grams] [PP pro per mL]]⟧ = 0.9g * (μ_VOL(pro)/mL) (eq. 18).
Quantity × pure number → **quantity in dimension WT** (eq. 19).
The dimension is STILL .mass — no quotient dimension arises. -/
def step_fullMP (μ_vol : MeasureFn E) (pro : E) (numeral : ℚ)
    (unit mL : Quantity) : Quantity :=
  quantityTimesNumber (step_innerMP numeral unit) (step_PP μ_vol mL pro)

/-- ⟦weighs⟧ = λq. λx. μ_WT(x) = q (eq. 5).
Takes a **quantity** and returns a predicate. The verb's measure
function must match the quantity's dimension. -/
def step_weighs (μ_wt : MeasureFn E) (q : Quantity) (x : E) : Bool :=
  decide (μ_wt.apply x = q.value)

/-- ⟦[S [the sample] [VP weighs [MP]]]⟧ — the full sentence (eq. 22).
Applies the VP to the subject entity. -/
def step_sentence (μ_wt μ_vol : MeasureFn E) (sample : E)
    (numeral : ℚ) (unit mL : Quantity) : Bool :=
  step_weighs μ_wt (step_fullMP μ_vol sample numeral unit mL) sample

-- ════════════════════════════════════════════════════
-- Dimension-tracking verification
-- ════════════════════════════════════════════════════

/-- The gram unit quantity. -/
def gram_unit : Quantity := unitQuantity .mass

/-- The milliliter unit quantity. -/
def mL_unit : Quantity := unitQuantity .volume

/-- The inner MP "0.9 grams" is in dimension WT (mass). -/
theorem innerMP_dimension :
    (step_innerMP (9/10) gram_unit).dim = .mass := rfl

/-- The full MP "0.9 grams per milliliter" is STILL in dimension WT.
This is the paper's key claim: the anaphoric theory never forms a
quotient dimension. The *per*-PP contributes a dimensionless scalar,
and multiplication preserves the original dimension. -/
theorem fullMP_dimension (μ_vol : MeasureFn E) (pro : E) :
    (step_fullMP μ_vol pro (9/10) gram_unit mL_unit).dim = .mass := rfl

/-- `weigh`'s measure function is in dimension WT. When the composed
quantity is also in WT, dimensions match — no type error. -/
theorem dimensions_match (μ_wt : MeasureFn E) (hwt : μ_wt.dimension = .mass)
    (μ_vol : MeasureFn E) (pro : E) :
    μ_wt.dimension = (step_fullMP μ_vol pro (9/10) gram_unit mL_unit).dim :=
  hwt

/-- Under the division theory, the MP would be in WT/VOL — a quotient
dimension. The verb's WT dimension would NOT match. -/
theorem division_theory_mismatch :
    QuotientDimension.density.components.1 = .mass ∧
    QuotientDimension.density.components ≠ (.mass, .mass) :=
  ⟨rfl, by decide⟩

-- ════════════════════════════════════════════════════
-- Truth-condition verification
-- ════════════════════════════════════════════════════

/-- The derivation yields eq. (22): μ_WT(sample) = (0.9 * μ_VOL(sample)/mL) g.
The numerical content is: μ_WT(sample) = 0.9 * 1 * (μ_VOL(sample) / 1),
which simplifies to μ_WT(sample) = 0.9 * μ_VOL(sample). -/
theorem derivation_eq22 (μ_wt μ_vol : MeasureFn E) (sample : E) :
    step_sentence μ_wt μ_vol sample (9/10) gram_unit mL_unit =
      decide (μ_wt.apply sample = 9 / 10 * 1 * (μ_vol.apply sample / 1)) := rfl

/-- The derivation matches `anaphoricTC` (modulo unit normalization). -/
theorem derivation_matches_tc (μ_wt μ_vol : MeasureFn E) (sample : E)
    (numeral : ℚ) :
    (step_sentence μ_wt μ_vol sample numeral gram_unit mL_unit = true) ↔
      anaphoricTC μ_wt μ_vol sample numeral 1 := by
  simp only [step_sentence, step_weighs, step_fullMP, quantityTimesNumber,
    step_innerMP, numeralTimesUnit, step_PP, step_perMilliliter,
    gram_unit, mL_unit, unitQuantity, anaphoricTC, perAnaphoric,
    decide_eq_true_eq, mul_one]

-- ════════════════════════════════════════════════════
-- Concrete verification
-- ════════════════════════════════════════════════════

private def μ_wt_concrete : MeasureFn Unit where
  dimension := .mass; apply := fun _ => 9; nonneg := fun _ => by norm_num

private def μ_vol_concrete : MeasureFn Unit where
  dimension := .volume; apply := fun _ => 10; nonneg := fun _ => by norm_num

/-- A sample with μ_WT = 9g, μ_VOL = 10mL: "weighs 0.9 grams per
milliliter" is TRUE. 9 = 0.9 * 1 * (10 / 1) = 9 ✓ -/
theorem concrete_derivation :
    step_sentence μ_wt_concrete μ_vol_concrete () (9/10) gram_unit mL_unit
      = true := by native_decide

/-- The same sample does NOT weigh "0.9 grams per liter".
A liter = 1000mL, so liter_unit has value 1000.
9 ≠ 0.9 * 1 * (10 / 1000) = 0.009 -/
def liter_unit : Quantity := ⟨1000, .volume⟩

theorem concrete_per_liter :
    step_sentence μ_wt_concrete μ_vol_concrete () (9/10)
      gram_unit liter_unit = false := by native_decide

-- ════════════════════════════════════════════════════
-- Pseudo-partitive derivation (§7, exx. 41-42, eq. 32)
-- ════════════════════════════════════════════════════

/-! The anaphoric theory derives pseudo-partitive truth conditions via
the same mechanism. For (27) "The mixture contains 0.1 grams per
milliliter of salt":

Parse (eq. 41): [the mixt.] contains [DP ∃ [AP [MP 0.1 grams]
  [PP pro [per milliliter]]] MUCH] of salt]

1. ⟦[MP 0.1 grams] [PP pro per mL]⟧ = (0.1 * μ_VOL(mixture)/mL) g  (eq. 42)
2. ⟦MUCH⟧(⟦fullMP⟧)(x) = μ_WT(x) = (0.1 * μ_VOL(mixture)/mL) g  (eq. 25)
3. ⟦sentence⟧ = ∃x[salt(x) ∧ μ_WT(x) = (0.1 * μ_VOL(mixture)/mL) g
   ∧ contain(mixture, x)]  (eq. 32)

The MP denotation (step 1) is identical to the measurement verb case —
`step_fullMP` produces the same dimensioned quantity. The only difference
is that MUCH applies this quantity as a predicate, rather than *weigh*. -/

/-- MUCH applied to the composed quantity (eq. 25 + eq. 42).
⟦MUCH⟧(q)(x) = (μ(x) = q.value), where μ is contextually resolved
to μ_WT for "grams of salt". -/
def step_MUCH (μ : MeasureFn E) (q : Quantity) (x : E) : Bool :=
  decide (μ.apply x = q.value)

/-- Pseudo-partitive truth conditions (eq. 32):
∃x[salt(x) ∧ μ_WT(x) = (0.1 * μ_VOL(mixture)/mL) g ∧ contain(mixture, x)].

We represent the existential as a check over a domain list, matching the
paper's eq. (26). -/
def step_pseudoPartitive (salt : E → Bool) (contain : E → E → Bool)
    (μ_wt μ_vol : MeasureFn E) (mixture : E)
    (numeral : ℚ) (unit mL : Quantity) (domain : List E) : Bool :=
  domain.any fun x =>
    salt x && step_MUCH μ_wt (step_fullMP μ_vol mixture numeral unit mL) x
      && contain mixture x

/-- The pseudo-partitive MP has the same dimension as the measurement
verb MP — mass in both cases. This confirms that the anaphoric theory
uses the same derivation mechanism for both environments. -/
theorem pseudoPartitive_same_dimension (μ_vol : MeasureFn E) (mixture : E) :
    (step_fullMP μ_vol mixture (1/10) gram_unit mL_unit).dim =
    (step_fullMP μ_vol mixture (9/10) gram_unit mL_unit).dim := rfl

/-- Pseudo-partitive truth conditions (eq. 32). MUCH equates μ_WT(x)
with the composed quantity, where `x` is the salt entity and `mixture`
is the container (pro's referent). These are DIFFERENT entities — unlike
the measurement verb case where the same entity is both subject and
pro's referent. -/
theorem pseudoPartitive_eq32 (μ_wt μ_vol : MeasureFn E) (mixture x : E) :
    step_MUCH μ_wt (step_fullMP μ_vol mixture (1/10) gram_unit mL_unit) x =
      decide (μ_wt.apply x = 1 / 10 * 1 * (μ_vol.apply mixture / 1)) := rfl

/-- In the measurement verb case, pro = subject, so the pseudo-partitive
machinery specializes to `anaphoricTC` when we set mixture = x. -/
theorem pseudoPartitive_specializes_to_measureVerb (μ_wt μ_vol : MeasureFn E)
    (sample : E) (numeral : ℚ) :
    (step_MUCH μ_wt (step_fullMP μ_vol sample numeral gram_unit mL_unit)
      sample = true) ↔ anaphoricTC μ_wt μ_vol sample numeral 1 := by
  simp only [step_MUCH, step_fullMP, quantityTimesNumber, step_innerMP,
    numeralTimesUnit, step_PP, step_perMilliliter, gram_unit, mL_unit,
    unitQuantity, anaphoricTC, perAnaphoric, decide_eq_true_eq, mul_one]

end Derivation

-- ============================================================================
-- § 13. Cross-reference to @cite{bale-schwarz-2026}
-- ============================================================================

/-! ### Connection to the 2026 L&P paper

The measurement verb examples formalized here (ex. 6: "The sample weighs
0.9 grams per milliliter") are simplex-dimension uses of *per* with
compositional interpretation — exactly the class that
`Phenomena.Quantification.BaleSchwarz2026.PerPhraseExample` classifies as
`dimType := .simplex` and `source := .compositional`.

The 2026 paper extends the anaphoric theory with:
- The No Division Hypothesis (compositional semantics uses × and +, not ÷)
- The math-speak analysis for quotient-dimension *per*-phrases
- Substitution and sub-extraction diagnostics

The unit sensitivity presupposition (eq. 43) originates in this 2022 paper
and is carried forward into the 2026 analysis. -/

end Phenomena.Quantification.BaleSchwarz2022
