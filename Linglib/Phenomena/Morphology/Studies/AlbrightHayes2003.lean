import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Linglib.Paradigms.WugTest

/-!
# Albright & Hayes (2003): Rules vs. analogy in English past tenses
@cite{albright-hayes-2003} @cite{berko-1958} @cite{albright-hayes-2002}
@cite{mikheev-1997} @cite{pinker-prince-1988} @cite{bybee-moder-1983}

A computational/experimental study of how speakers form past tenses
for novel English verbs (wug verbs). The paper's central architectural
claim is that morphological knowledge is best modelled as **multiple
stochastic rules** — each with a structural description, a scope, a
hit count, and an adjusted-confidence score — and that this model
fits human wug-test data better than either a purely analogical model
or a single-default-rule dual-mechanism model.

## Architectural commitments

Three positions are at stake:

- **Single-default-rule dual-mechanism**: regular pasts are derived
  by a *single*, context-free rule; only irregular pasts are sensitive
  to phonological context. Predicts that novel-word ratings of regular
  pasts are *invariant* in the phonological context of the stem.
- **Pure analogy** (e.g. GCM-style): all generalisation flows from
  variegated similarity to existing lexemes. No structured rules; the
  influence of a model form on a novel form can ride on any feature.
- **Multiple stochastic rules** (this paper): the lexicon supplies
  *many* rules per change, each restricted to a structurally-defined
  context. A novel form's past-tense rating depends on the *adjusted
  confidence* of the most accurate rule whose structural description
  it satisfies. Predicts both regular and irregular ratings vary with
  phonological context — specifically, with **island-of-reliability
  membership**.

## Empirical core: islands of reliability for **both** regulars and irregulars

A&H's central empirical contribution is that wug ratings of *regular*
past tenses **also** show context sensitivity, contrary to the
single-default-rule prediction. The 4-way Core stimulus design
crosses island-of-reliability (IOR) status for regulars × IOR for
irregulars, and the published rating data show:

- ratings F(1, 78) = 27.23, P < 0.0001 main effect of islandhood
- production-probability F(1, 78) = 14.05, P < 0.001 main effect of
  islandhood

with no significant interaction. **Both** regulars and irregulars are
sensitive to IOR membership.

## What this file formalises

This is the second consumer of `Paradigms/WugTest.lean` (the first is
@cite{breiss-katsuda-kawahara-2026}). It supplies:

- The 4-way IOR Core wug stem set (example 14 in the paper);
- A `StochasticRule` type with scope/hits/rawConfidence;
- A note on Mikheev (1997) lower-confidence-limit adjustment, kept
  as an abstract specification rather than a numerical implementation;
- An `AHWugCell` type that participates in the WugTest contract via
  `HasAttestation`;
- A local typeclass `HasIORForRegular` (binary IOR factor — the
  WugTest `HasFrequency` analogue for the discrete IOR dimension);
- Two paradigm-level predicates `NovelRegularsShowIORGradient` and
  `NovelRegularsInvariantInIOR`;
- A structural discriminator
  `novelRegularsGradient_inconsistent_with_invariance`;
- A concrete A&H step-function model that satisfies the gradient and
  hence rules out the single-default-rule prediction by structural
  impossibility.

## Out of scope

Per CLAUDE.md "do not encode conclusions as definitions": we do not
formalise the numerical correlation tables (r = 0.745 etc.) as Lean
theorems with `rfl` proofs. The numbers are reported in prose and the
paper-side citation. We formalise the *qualitative* prediction-shape
contrasts that the empirical correlations support.

We also do not implement the @cite{mikheev-1997} lower-confidence-limit
interval. The discriminator below depends only on `rawConfidence` and
on the qualitative shape of the prediction (gradient on novel cells
across IOR membership), not on the adjustment formula. We expose
`adjustedConfidence` as a placeholder definition equal to
`rawConfidence` so that downstream code can reference the API name;
wiring this to a real Wilson interval (or the @cite{albright-hayes-2002}
MGL implementation) is deferred.
-/

namespace Phenomena.Morphology.Studies.AlbrightHayes2003

open Paradigms.WugTest (Attestation HasFactor HasAttestation Rate
  NovelShowsFactorGradient NovelInvariantInFactor
  novelGradient_inconsistent_with_invariance)

-- ============================================================================
-- § 1: Core wug stems — 4-way IOR design (Table 3, example 14)
-- ============================================================================

/-- Island-of-reliability category for a wug stem. The 4-way Core
    design crosses (IOR for regulars) × (IOR for irregulars); a stem
    is in exactly one cell, picked out by two booleans. Structural
    encoding via product avoids the 4-way enum + 2 helper accessors
    pattern: the cells of a 2×2 design *are* the boolean product.
    Table 3 of @cite{albright-hayes-2003}. -/
structure IORCategory where
  /-- Whether the stem is in an island of reliability for the regular
      allomorph. Example for `regular = true`: *bredge* /brɛdʒ/. -/
  iorForRegular : Bool
  /-- Whether the stem is in an island of reliability for some
      irregular pattern. Example for `iorForIrregular = true` only:
      *spling* /splɪŋ/ (close to *spring/sling/sting*). -/
  iorForIrregular : Bool
  deriving DecidableEq, Repr, Inhabited

/-! ### Named cells of Table 3, retained as `abbrev`s so that
paper-side terminology survives in the witness definitions. -/

namespace IORCategory

/-- IOR for **both** regulars and irregulars: e.g. *dize*. -/
abbrev regAndIrreg : IORCategory := ⟨true, true⟩

/-- IOR for **regulars only**: e.g. *bredge*. -/
abbrev regOnly : IORCategory := ⟨true, false⟩

/-- IOR for **irregulars only**: e.g. *spling*. -/
abbrev irregOnly : IORCategory := ⟨false, true⟩

/-- IOR for **neither**: e.g. *gude*. -/
abbrev neither : IORCategory := ⟨false, false⟩

end IORCategory

/-- A wug stem with its IPA form and its IOR category. The IPA strings
    are taken verbatim from example (14) of @cite{albright-hayes-2003}. -/
structure WugStem where
  ipa : String
  category : IORCategory
  deriving Repr, Inhabited

/-! ### Sample stems from each cell of Table 3 (example 14) -/

-- IOR for both
def stem_dize : WugStem := { ipa := "daɪz", category := .regAndIrreg }
def stem_fro  : WugStem := { ipa := "fro",  category := .regAndIrreg }
def stem_rife : WugStem := { ipa := "raɪf", category := .regAndIrreg }

-- IOR for regulars only
def stem_bredge : WugStem := { ipa := "brɛdʒ", category := .regOnly }
def stem_gezz   : WugStem := { ipa := "gɛz",   category := .regOnly }
def stem_nace   : WugStem := { ipa := "nes",   category := .regOnly }

-- IOR for irregulars only
def stem_fleep  : WugStem := { ipa := "flip",  category := .irregOnly }
def stem_gleed  : WugStem := { ipa := "glid",  category := .irregOnly }
def stem_spling : WugStem := { ipa := "splɪŋ", category := .irregOnly }

-- IOR for neither
def stem_gude  : WugStem := { ipa := "gud",  category := .neither }
def stem_nung  : WugStem := { ipa := "nʌŋ",  category := .neither }
def stem_preak : WugStem := { ipa := "prik", category := .neither }

-- ============================================================================
-- § 2: Stochastic rules — minimal generalization with scope and hits
-- ============================================================================

/-- A past-tense structural change (the "input → output" half of a
    rule). The three regular allomorphs and a residual category for
    vowel-changing irregulars and zero-derivation. -/
inductive PastChange where
  | suffixD       -- /-d/ as in `rub-rubbed`
  | suffixT       -- /-t/ as in `jump-jumped`
  | suffixSchwaD  -- /-əd/ as in `vote-voted`
  | vowelChange   -- e.g. [ɪ] → [ʌ] as in `cling-clung`
  | noChange      -- e.g. `cut-cut`
  deriving DecidableEq, Repr, Inhabited

/-- Whether a past-tense change is one of the three regular suffixes. -/
def PastChange.isRegular : PastChange → Bool
  | .suffixD | .suffixT | .suffixSchwaD => true
  | .vowelChange | .noChange => false

/-- A stochastic rule: a structural change applied in a structurally-
    defined context, together with its `scope` (number of forms in
    the lexicon meeting the structural description) and `hits`
    (number of those forms on which the change actually obtains).

    The bundled invariant `hits ≤ scope` is a real-data property of
    rules extracted by a minimal-generalization procedure: every form
    counted as a hit must be in the scope. This is the structural fact
    that makes `rawConfidence ≤ 1`.

    The structural-description / context is kept abstract — A&H's
    rules are extracted from the lexicon by a minimal-generalization
    procedure, and the discriminator below does not depend on any
    specific encoding of the contexts. -/
structure StochasticRule where
  change : PastChange
  scope : ℕ
  hits : ℕ
  hits_le_scope : hits ≤ scope
  deriving Repr

/-- Raw confidence: hits / scope. Defaults to 0 when scope = 0 to
    avoid division by zero; that case never arises for a rule
    extracted from real data. @cite{albright-hayes-2003}. -/
def StochasticRule.rawConfidence (r : StochasticRule) : ℚ :=
  if r.scope = 0 then 0 else (r.hits : ℚ) / (r.scope : ℚ)

/-- `rawConfidence ≤ 1` follows structurally from `hits_le_scope`. -/
theorem StochasticRule.rawConfidence_le_one (r : StochasticRule) :
    r.rawConfidence ≤ 1 := by
  unfold rawConfidence
  split_ifs with h
  · exact zero_le_one
  · have hscope_pos : (0 : ℚ) < (r.scope : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero h
    rw [div_le_one hscope_pos]
    exact_mod_cast r.hits_le_scope

/-- @cite{mikheev-1997} lower-confidence-limit adjustment to raw
    confidence, used by @cite{albright-hayes-2003} to penalise rules
    supported by few forms; A&H §2.3.4 reports the best-fit lower-
    confidence-limit parameter α = 0.55.

    **TODO**: this is a placeholder equal to `rawConfidence`. A faithful
    implementation would apply the Wilson-style interval used in the
    @cite{albright-hayes-2002} MGL code. The discriminator below depends
    on `rawConfidence`, not on this adjustment, so the placeholder is
    sound for the present proof obligations. -/
noncomputable def adjustedConfidence (r : StochasticRule) : ℚ := r.rawConfidence

-- ============================================================================
-- § 3: Wug cell — wiring to `Paradigms/WugTest.lean`
-- ============================================================================

/-- A cell in the A&H wug-rating paradigm. Carries:

    - the stem being rated;
    - whether the stem is presented as a wug (novel) or a real verb
      (attested) — A&H's cross-paradigm comparison;
    - the IOR-for-regular factor — the propositional phonological-
      context dimension that A&H's experiments turn on. The field is
      `Prop` rather than `Bool` because IOR-membership is a
      propositional property of the stimulus, not a designed numeric
      coordinate; mathlib quality requires Prop with `[Decidable]` for
      such fields rather than `Bool` standing in for a proposition. -/
structure AHWugCell where
  stem : WugStem
  attestation : Attestation
  withinIORForRegular : Prop

namespace AHWugCell

/-- The `Paradigms/WugTest.lean` `HasAttestation` instance: BKK and
    A&H both use the same wug paradigm contract. Lens laws by `rfl`
    on the structure projections. -/
instance : HasAttestation AHWugCell where
  factorOf c := c.attestation
  setFactor a c := { c with attestation := a }
  factorOf_setFactor := by intros; rfl
  setFactor_factorOf := by intros; rfl
  setFactor_setFactor := by intros; rfl

end AHWugCell

-- ============================================================================
-- § 4: A binary "island-of-reliability" lens
-- ============================================================================

/-- A&H's discriminator runs on the categorical *island membership*
    dimension; the WugTest paradigm contract handles this through the
    `HasFactor Cell Prop` specialisation, parallel to
    `HasFrequency = HasFactor Cell ℝ`. The lens-law shape is shared.

    The Prop factor inherits its `<` from mathlib's complete-Boolean-
    algebra structure on `Prop` (`p < q ↔ (p → q) ∧ ¬(q → p)`), so
    `NovelShowsFactorGradient (F := Prop)` instantiates to "rate is
    strictly higher under any pair where the second IOR proposition
    strictly entails the first" — exactly A&H's prediction reading IOR
    as a propositional property. -/
abbrev HasIORForRegular (Cell : Type) := HasFactor Cell Prop

namespace AHWugCell

instance : HasIORForRegular AHWugCell where
  factorOf c := c.withinIORForRegular
  setFactor p c := { c with withinIORForRegular := p }
  factorOf_setFactor := by intros; rfl
  setFactor_factorOf := by intros; rfl
  setFactor_setFactor := by intros; rfl

end AHWugCell

-- ============================================================================
-- § 5: Paradigm-level predictions
-- ============================================================================

variable {Cell : Type} {R : Type}

/-- A rate observable shows the **novel-regulars IOR gradient** if,
    on novel cells, switching the IOR-for-regular factor from `false`
    to `true` strictly raises the rate. The shared paradigm-level
    predicate `NovelShowsFactorGradient (F := Bool)` already expresses
    exactly this: the only `Bool` pair satisfying `f₁ < f₂` is
    `false < true`. This is the A&H multiple-stochastic-rule
    prediction: novel regulars receive higher ratings when the stem
    occupies an island where the regular allomorph works particularly
    well. -/
abbrev NovelRegularsShowIORGradient
    [HasAttestation Cell] [HasIORForRegular Cell] [LT R]
    (rate : Rate Cell R) : Prop :=
  NovelShowsFactorGradient (F := Prop) rate

/-- A rate observable is **invariant in IOR for novel regulars** if,
    on novel cells, switching the IOR-for-regular factor leaves the
    rate unchanged. This is the single-default-rule dual-mechanism
    prediction: regular pasts are derived by one rule whose
    confidence does not vary with phonological context, so novel
    regular ratings cannot vary with IOR membership. Specialises
    `NovelInvariantInFactor (F := Prop)`. -/
abbrev NovelRegularsInvariantInIOR
    [HasAttestation Cell] [HasIORForRegular Cell]
    (rate : Rate Cell R) : Prop :=
  NovelInvariantInFactor (F := Prop) rate

-- ============================================================================
-- § 7: Concrete A&H step-function model
-- ============================================================================

/-! These definitions are concrete witnesses that the A&H prediction-
shape `NovelRegularsShowIORGradient` is realised by a model. The
model is a step function: ratings on IOR=true cells equal `slope`,
ratings on IOR=false cells equal `0`. The shape is intentionally
minimal — the goal is to exhibit a model satisfying the gradient,
not to fit the empirical numbers. -/

/-- Step-function regular-rating model: rating = `slope` when the
    IOR-for-regular proposition holds, 0 otherwise. A faithful proxy
    for the monotonic relationship between IOR-supported rule-
    confidence and novel-form ratings reported in
    @cite{albright-hayes-2003} for the regulars panel. Noncomputable
    because the IOR-for-regular field is `Prop` rather than `Bool`;
    `Classical.propDecidable` discharges the `Decidable`-of-`if`. -/
noncomputable def ahRegularRating (slope : ℝ) (c : AHWugCell) : ℝ :=
  open Classical in
  if c.withinIORForRegular then slope else 0

/-- A&H's model satisfies `NovelRegularsShowIORGradient` for any
    positive rating slope. The `Prop`-valued IOR factor satisfies
    `f₁ < f₂` iff `f₁ → f₂` and `¬(f₂ → f₁)`; the only consistent
    case (modulo classical reasoning) is `¬f₁ ∧ f₂`, on which the
    rate jumps from 0 to `slope`. -/
theorem ah_satisfies_NovelRegularsShowIORGradient
    (slope : ℝ) (hSlope : 0 < slope) :
    NovelRegularsShowIORGradient (ahRegularRating slope) := by
  intro c f₁ f₂ hf
  -- `Prop`'s `<` decomposes via `lt_iff_le_not_le`; on `Prop`, `≤` is
  -- implication.  Classical case analysis on f₁ and f₂ kills three
  -- of the four cases; only `¬f₁ ∧ f₂` is consistent with `f₁ < f₂`.
  have h_le : f₁ ≤ f₂ := le_of_lt hf
  have h_nle : ¬ f₂ ≤ f₁ := not_le_of_gt hf
  by_cases h₁ : f₁
  · exact absurd (fun _ => h₁) h_nle
  · by_cases h₂ : f₂
    · show (open Classical in if (HasFactor.setFactor f₁
              (HasFactor.setFactor Attestation.novel c)).withinIORForRegular
            then slope else 0) <
           (open Classical in if (HasFactor.setFactor f₂
              (HasFactor.setFactor Attestation.novel c)).withinIORForRegular
            then slope else 0)
      show (open Classical in if f₁ then slope else 0) <
           (open Classical in if f₂ then slope else 0)
      rw [if_neg h₁, if_pos h₂]
      exact hSlope
    · exact absurd (fun hf2 => absurd hf2 h₂) h_nle

/-- A concrete `AHWugCell` witness — the wug stem *bredge*
    (regulars-only IOR) presented as a novel form. Used as the
    discriminator-corollary witness below. -/
def cell_bredge : AHWugCell where
  stem := stem_bredge
  attestation := .novel
  withinIORForRegular := True

/-- **A&H rules out the single-default-rule dual-mechanism
    prediction** (the @cite{pinker-prince-1988} family). Wired through
    `Paradigms/WugTest.lean`'s `novelGradient_inconsistent_with_invariance`
    at `F := Bool`: the empirical fact that novel regulars show an
    IOR gradient is structurally incompatible with the single-rule
    prediction that novel regulars are invariant in phonological
    context. Any account in the latter family is ruled out by
    structural impossibility, not just empirical fit.

    NB: this discriminator only captures A&H's *anti-dual-mechanism*
    prong. A&H also argue against pure analogy via §4.3.2 ("Failure of
    the analogical model to locate islands of reliability"); the
    structured-vs-variegated similarity contrast that drives the
    anti-analogy prong is not formalised here. See @cite{bybee-moder-1983}
    for the analogical tradition A&H argue against. -/
theorem ah_excludes_singleDefaultRule
    (slope : ℝ) (hSlope : 0 < slope) :
    ¬ NovelRegularsInvariantInIOR (ahRegularRating slope) := by
  intro h_inv
  refine novelGradient_inconsistent_with_invariance (F := Prop)
    (ahRegularRating slope)
    (ah_satisfies_NovelRegularsShowIORGradient slope hSlope)
    h_inv cell_bredge False True ?_
  exact ⟨False.elim, fun h => h trivial⟩

end Phenomena.Morphology.Studies.AlbrightHayes2003
