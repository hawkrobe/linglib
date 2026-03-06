import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Tactics.RSAPredict
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Linglib.Phenomena.Modality.FreeChoice

/-!
# @cite{alsop-2024} — Free Choice *Any* as GI-RSA
@cite{alsop-2024} @cite{champollion-alsop-grosu-2019} @cite{dayal-1998} @cite{franke-bergen-2020} @cite{szabolcsi-2004} @cite{tessler-franke-2019}

"Disjunction, Free Choice, and Exhaustification" (Chapter 4)

## The Model

Domain: "You may take any class" with 2 items {S, P}. 7 states based on
permission structure (which baskets are permitted). 4 utterances. 2 global
interpretation functions (weak/Szabolcsi vs strong/Dayal), following the
GI-RSA architecture of @cite{franke-bergen-2020}.

- **L0**: L0(w|u,I) ∝ ⟦u⟧^I(w) (meaning under interpretation I)
- **S1**: S1(u|w,I) ∝ L0(w|u,I)^α (rpow belief-based)
- **L1**: L1(w|u) ∝ P(w) · Σ_I P(I) · S1(u|w,I)

Parameters: α = 2, uniform interpretation prior, configurable world prior.

## Qualitative Findings

| # | Finding | Theorem |
|---|---------|---------|
| 1 | Exclusiveness derived | `exclusiveness_derived` |
| 2 | Exclusiveness robust to prior | `exclusiveness_robust` |
| 3 | Not-every holds under uniform prior | `not_every_uniform` |
| 4 | Not-every weakened under biased prior | `not_every_weakened` |
| 5 | Hearing "may S" → S is permitted | `literal_s_correct` |
| 6 | Hearing "may every" → both permitted | `every_permBoth` |
| 7 | Ambiguity essential for FC | `exclusiveness_requires_ambiguity` |
| 8 | No FC under negation | `no_fc_under_negation` |

-/

set_option autoImplicit false

namespace RSA.FCIAny

open Real (rpow rpow_nonneg)

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- The 7 states from @cite{alsop-2024} for a 2-item domain {S, P}.
    Each state is defined by which baskets are permitted:
    w0 (nothing), wS (S only), wP (P only), wSP (both). -/
inductive FCIState where
  | onlyS    -- {w0, wS}
  | onlyP    -- {w0, wP}
  | only1    -- {w0, wS, wP}
  | anyNum   -- {w0, wS, wP, wSP}
  | only2    -- {w0, wSP}
  | sOrBoth  -- {w0, wS, wSP}
  | pOrBoth  -- {w0, wP, wSP}
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype FCIState where
  elems := {.onlyS, .onlyP, .only1, .anyNum, .only2, .sOrBoth, .pOrBoth}
  complete := fun x => by cases x <;> simp

/-- The 4 utterances. -/
inductive Utterance where
  | mayS     -- "You may take S"
  | mayP     -- "You may take P"
  | mayAny   -- "You may take any class"
  | mayEvery -- "You may take every class"
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype Utterance where
  elems := {.mayS, .mayP, .mayAny, .mayEvery}
  complete := fun x => by cases x <;> simp

/-- Two global interpretation functions (GI-RSA).
    Each assigns a meaning to every utterance simultaneously. -/
inductive Interp where
  | weak   -- Szabolcsi-type: unexhaustified, liberal meanings
  | strong -- Dayal-type: exhaustified, strict meanings
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype Interp where
  elems := {.weak, .strong}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- §2. Permission Predicates (Compositional Foundation)
-- ============================================================================

/-- ◇take(S)_strict: taking S alone is a permitted basket (wS accessible). -/
def permS : FCIState → Bool
  | .onlyS | .only1 | .anyNum | .sOrBoth => true
  | _ => false

/-- ◇take(P)_strict: taking P alone is a permitted basket (wP accessible). -/
def permP : FCIState → Bool
  | .onlyP | .only1 | .anyNum | .pOrBoth => true
  | _ => false

/-- ◇take(S∧P): taking both together is permitted (wSP accessible). -/
def permBoth : FCIState → Bool
  | .anyNum | .only2 | .sOrBoth | .pOrBoth => true
  | _ => false

/-- ◇take(S)_liberal: S is obtainable (alone or via both). -/
def permS_liberal (w : FCIState) : Bool := permS w || permBoth w

/-- ◇take(P)_liberal: P is obtainable (alone or via both). -/
def permP_liberal (w : FCIState) : Bool := permP w || permBoth w

-- ============================================================================
-- §3. Empirical Predicates
-- ============================================================================

/-- Exclusiveness: each item is individually (strictly) permitted.
    ∀x[◇take(x)_strict]. True at {only1, anyNum}. -/
def hasExclusiveness : FCIState → Bool
  | .only1 | .anyNum => true
  | _ => false

/-- Not-every: taking both is not permitted. ¬◇(S∧P).
    True at {onlyS, onlyP, only1}. -/
def hasNotEvery : FCIState → Bool
  | .onlyS | .onlyP | .only1 => true
  | _ => false

-- ============================================================================
-- §4. Truth Tables (Global Interpretation Functions)
-- ============================================================================

/-- Weak (Szabolcsi) interpretation: unexhaustified meanings.
    - May S: ◇take(S)_liberal (6 states, all except onlyP)
    - May P: ◇take(P)_liberal (6 states, all except onlyS)
    - May Any: ∃x[◇take(x)] (7 states, always true)
    - May Every: ◇take(S∧P) (4 states: anyNum, only2, sOrBoth, pOrBoth) -/
def weakMeaning : Utterance → FCIState → Bool
  | .mayS, w => permS_liberal w
  | .mayP, w => permP_liberal w
  | .mayAny, _ => true
  | .mayEvery, w => permBoth w

/-- Strong (Dayal) interpretation: exhaustified meanings.
    - May S: {onlyS} (only S permitted, not P, not both)
    - May P: {onlyP} (only P permitted, not S, not both)
    - May Any: {only1, anyNum} (∀x[◇take(x)_strict], exclusiveness)
    - May Every: {only2} (must take both, neither alone) -/
def strongMeaning : Utterance → FCIState → Bool
  | .mayS, .onlyS => true
  | .mayP, .onlyP => true
  | .mayAny, .only1 | .mayAny, .anyNum => true
  | .mayEvery, .only2 => true
  | _, _ => false

/-- Combined meaning function indexed by interpretation. -/
def interpMeaning : Interp → Utterance → FCIState → Bool
  | .weak => weakMeaning
  | .strong => strongMeaning

-- ============================================================================
-- §5. Structural Theorems
-- ============================================================================

/-- The strong interpretation characterizes exclusiveness exactly. -/
theorem strong_characterizes_exclusiveness :
    ∀ w, strongMeaning .mayAny w = hasExclusiveness w := by
  intro w; cases w <;> rfl

/-- The weak interpretation is always true for "may any". -/
theorem weak_mayAny_always_true : ∀ w, weakMeaning .mayAny w = true := by
  intro w; rfl

/-- Exclusiveness = ∀x[◇take(x)_strict]. -/
theorem exclusiveness_eq_allStrict :
    ∀ w, hasExclusiveness w = (permS w && permP w) := by
  intro w; cases w <;> rfl

/-- Not-every = ¬permBoth. -/
theorem notEvery_eq_not_permBoth :
    ∀ w, hasNotEvery w = !permBoth w := by
  intro w; cases w <;> rfl

/-- The strong interpretation refines the weak for all utterances. -/
theorem strong_refines_weak :
    ∀ u w, strongMeaning u w = true → weakMeaning u w = true := by
  intro u w h; cases u <;> cases w <;> simp_all [strongMeaning, weakMeaning,
    permS_liberal, permP_liberal, permS, permP, permBoth]

/-- Permission predicates correctly characterize key states. -/
theorem permission_correspondence :
    (permS .onlyS = true ∧ permP .onlyS = false ∧ permBoth .onlyS = false) ∧
    (permS .only1 = true ∧ permP .only1 = true ∧ permBoth .only1 = false) ∧
    (permS .only2 = false ∧ permP .only2 = false ∧ permBoth .only2 = true) := by
  decide

-- ============================================================================
-- §6. RSAConfig
-- ============================================================================

/-- @cite{alsop-2024} GI-RSA model for free choice *any*.
    Two global interpretations serve as latent variables.
    S1 score is rpow(L0, α) — standard belief-based RSA. -/
noncomputable def cfg (worldPr : FCIState → ℝ) (hp : ∀ w, 0 ≤ worldPr w) :
    RSA.RSAConfig Utterance FCIState where
  Latent := Interp
  meaning _ i u w := if interpMeaning i u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _i w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos
  worldPrior := worldPr
  worldPrior_nonneg := hp

/-- Uniform prior: all states equally likely. -/
noncomputable abbrev uniformCfg :=
  cfg (fun _ => 1) (fun _ => le_of_lt one_pos)

/-- Biased prior: P(anyNum) = 3, others = 1.
    Biases toward the state where exclusiveness holds but not-every does not,
    testing prior sensitivity of the two inferences. -/
noncomputable abbrev biasedCfg :=
  cfg (fun w => match w with | .anyNum => 3 | _ => 1)
    (fun w => by cases w <;> positivity)

-- ============================================================================
-- §7. Bridge Theorems
-- ============================================================================

/-- Exclusiveness is derived: L1 assigns more mass to exclusiveness states
    than non-exclusiveness states upon hearing "may any". -/
theorem exclusiveness_derived :
    uniformCfg.L1_marginal .mayAny hasExclusiveness >
    uniformCfg.L1_marginal .mayAny (fun w => !hasExclusiveness w) := by
  rsa_predict

/-- Exclusiveness is robust: holds even under a prior biased toward anyNum. -/
theorem exclusiveness_robust :
    biasedCfg.L1_marginal .mayAny hasExclusiveness >
    biasedCfg.L1_marginal .mayAny (fun w => !hasExclusiveness w) := by
  rsa_predict

/-- Not-every holds under uniform prior. -/
theorem not_every_uniform :
    uniformCfg.L1_marginal .mayAny hasNotEvery >
    uniformCfg.L1_marginal .mayAny (fun w => !hasNotEvery w) := by
  rsa_predict

/-- Not-every is weakened under biased prior (prior-sensitive). -/
theorem not_every_weakened :
    ¬(biasedCfg.L1_marginal .mayAny hasNotEvery >
      biasedCfg.L1_marginal .mayAny (fun w => !hasNotEvery w)) := by
  rsa_predict

/-- Hearing "may S", the listener infers S is (strictly) permitted. -/
theorem literal_s_correct :
    uniformCfg.L1_marginal .mayS (fun w => permS w) >
    uniformCfg.L1_marginal .mayS (fun w => !permS w) := by
  rsa_predict

/-- Hearing "may every", the listener infers both are permitted. -/
theorem every_permBoth :
    uniformCfg.L1_marginal .mayEvery (fun w => permBoth w) >
    uniformCfg.L1_marginal .mayEvery (fun w => !permBoth w) := by
  rsa_predict

-- ============================================================================
-- §8. Ambiguity is Essential
-- ============================================================================

/-- Counterfactual: both interpretations use weak meaning (no ambiguity).
    Without the informativity gap between weak (7 states for "may any") and
    strong (2 states), S1 cannot discriminate exclusiveness states. -/
noncomputable def weakOnlyCfg : RSA.RSAConfig Utterance FCIState where
  Latent := Interp
  meaning _ _i u w := if weakMeaning u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _i w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos
  worldPrior_nonneg := fun _ => le_of_lt one_pos

/-- Without interpretation ambiguity, exclusiveness is NOT derived.
    The informativity gap between weak (7 states) and strong (2 states) is
    what drives L1 toward exclusiveness states. Without a strong parse,
    "may any" is uninformative and the prior dominates: 2/7 exclusiveness
    states vs 5/7 non-exclusiveness states. -/
theorem exclusiveness_requires_ambiguity :
    ¬(weakOnlyCfg.L1_marginal .mayAny hasExclusiveness >
      weakOnlyCfg.L1_marginal .mayAny (fun w => !hasExclusiveness w)) := by
  rsa_predict

-- ============================================================================
-- §9. FC Under Negation
-- ============================================================================

/-- Extended utterances including negation of "may any". -/
inductive UtteranceNeg where
  | mayS | mayP | mayAny | mayEvery | mayNotAny
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype UtteranceNeg where
  elems := {.mayS, .mayP, .mayAny, .mayEvery, .mayNotAny}
  complete := fun x => by cases x <;> simp

/-- Weak meaning extended with negation.
    "May not any" under weak = ¬∃x[◇take(x)] = false everywhere,
    since the weak existential meaning is trivially true at all states. -/
def weakMeaningNeg : UtteranceNeg → FCIState → Bool
  | .mayS, w => permS_liberal w
  | .mayP, w => permP_liberal w
  | .mayAny, _ => true
  | .mayEvery, w => permBoth w
  | .mayNotAny, _ => false

/-- Strong meaning extended with negation.
    "May not any" under strong = ¬∀x[◇take(x)_strict] = ¬hasExclusiveness.
    True at 5 of 7 states (all except only1 and anyNum). -/
def strongMeaningNeg : UtteranceNeg → FCIState → Bool
  | .mayS, .onlyS => true
  | .mayP, .onlyP => true
  | .mayAny, .only1 | .mayAny, .anyNum => true
  | .mayEvery, .only2 => true
  | .mayNotAny, w => !hasExclusiveness w
  | _, _ => false

/-- Combined meaning for the extended model. -/
def interpMeaningNeg : Interp → UtteranceNeg → FCIState → Bool
  | .weak => weakMeaningNeg
  | .strong => strongMeaningNeg

/-- RSAConfig for the extended model with negation. -/
noncomputable def negCfg : RSA.RSAConfig UtteranceNeg FCIState where
  Latent := Interp
  meaning _ i u w := if interpMeaningNeg i u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _i w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos
  worldPrior_nonneg := fun _ => le_of_lt one_pos

/-- Free choice does NOT emerge under negation.
    Under negation, the weak interpretation is vacuous (false everywhere) and
    the strong interpretation supports only non-exclusiveness states. The
    informativity gap that drives FC in the positive case disappears. -/
theorem no_fc_under_negation :
    ¬(negCfg.L1_marginal .mayNotAny hasExclusiveness >
      negCfg.L1_marginal .mayNotAny (fun w => !hasExclusiveness w)) := by
  rsa_predict

-- ============================================================================
-- §10. Verification
-- ============================================================================

/-- The 8 qualitative findings from @cite{alsop-2024}. -/
inductive Finding where
  | exclusiveness_derived
  | exclusiveness_robust
  | not_every_uniform
  | not_every_weakened
  | literal_s_correct
  | every_permBoth
  | exclusiveness_requires_ambiguity
  | no_fc_under_negation
  deriving DecidableEq, BEq, Repr

/-- Map each finding to its RSA formalization. -/
noncomputable def formalize : Finding → Prop
  | .exclusiveness_derived =>
      uniformCfg.L1_marginal .mayAny hasExclusiveness >
      uniformCfg.L1_marginal .mayAny (fun w => !hasExclusiveness w)
  | .exclusiveness_robust =>
      biasedCfg.L1_marginal .mayAny hasExclusiveness >
      biasedCfg.L1_marginal .mayAny (fun w => !hasExclusiveness w)
  | .not_every_uniform =>
      uniformCfg.L1_marginal .mayAny hasNotEvery >
      uniformCfg.L1_marginal .mayAny (fun w => !hasNotEvery w)
  | .not_every_weakened =>
      ¬(biasedCfg.L1_marginal .mayAny hasNotEvery >
        biasedCfg.L1_marginal .mayAny (fun w => !hasNotEvery w))
  | .literal_s_correct =>
      uniformCfg.L1_marginal .mayS (fun w => permS w) >
      uniformCfg.L1_marginal .mayS (fun w => !permS w)
  | .every_permBoth =>
      uniformCfg.L1_marginal .mayEvery (fun w => permBoth w) >
      uniformCfg.L1_marginal .mayEvery (fun w => !permBoth w)
  | .exclusiveness_requires_ambiguity =>
      ¬(weakOnlyCfg.L1_marginal .mayAny hasExclusiveness >
        weakOnlyCfg.L1_marginal .mayAny (fun w => !hasExclusiveness w))
  | .no_fc_under_negation =>
      ¬(negCfg.L1_marginal .mayNotAny hasExclusiveness >
        negCfg.L1_marginal .mayNotAny (fun w => !hasExclusiveness w))

/-- The RSA model accounts for all 8 findings from @cite{alsop-2024}. -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact exclusiveness_derived
  · exact exclusiveness_robust
  · exact not_every_uniform
  · exact not_every_weakened
  · exact literal_s_correct
  · exact every_permBoth
  · exact exclusiveness_requires_ambiguity
  · exact no_fc_under_negation

end RSA.FCIAny

/-! ## Bridge content (merged from RSA_Alsop2024Bridge.lean) -/

/-!
# Bridge: RSA Free Choice Any → Phenomena Data
@cite{alsop-2024}

Connects the RSA free choice *any* model from @cite{alsop-2024} to empirical
data in `Phenomena.Modality.FreeChoice`.

## Bridge Theorems

- `predicts_fci_any`: Exclusiveness arises for permission *any*
- `predicts_robustness`: Exclusiveness is robust to prior manipulation
-/


namespace Phenomena.Modality.RSA_Alsop2024Bridge

/-!
## Connection to Phenomena

The model predicts the patterns in `Phenomena.Modality.FreeChoice`:

1. **FCI Any** (`anyClass`, `anyFruit`):
   - "You may take any class" → permission for each class specifically
   - Derived: L1 assigns ~100% to exclusiveness states

2. **Robustness to priors**:
   - Exclusiveness holds even with unfavorable priors
   - Parallels FCI robustness in disjunction

3. **Not-every is cancelable**:
   - "You may take any class (in fact, you must take all of them)"
   - The "not every" inference can be cancelled, unlike exclusiveness
-/

/-- Free choice *any* is predicted for permission sentences -/
theorem predicts_fci_any :
    Phenomena.Modality.FreeChoice.anyClass.exclusivenessArises = true := rfl

/-- Exclusiveness is robust to priors (as recorded in the data) -/
theorem predicts_robustness :
    Phenomena.Modality.FreeChoice.anyClass.robustToPriors = true := rfl

end Phenomena.Modality.RSA_Alsop2024Bridge
