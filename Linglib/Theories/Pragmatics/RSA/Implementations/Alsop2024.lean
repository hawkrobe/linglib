import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Tactics.RSAPredict
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Alsop (2024) — Free Choice *Any* as GI-RSA

"Disjunction, Free Choice, and Exhaustification" (Chapter 4)

## The Model

Domain: "You may take any class" with 2 items {S, P}. 7 states based on
permission structure (which baskets are permitted). 4 utterances. 2 global
interpretation functions (weak/Szabolcsi vs strong/Dayal), following the
GI-RSA architecture of Franke & Bergen (2020).

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

## References

- Alsop, S. (2024). Disjunction, Free Choice, and Exhaustification.
- Champollion, L., Alsop, S. & Grosu, A. (2019). Free choice disjunction
  as a rational speech act. SALT 29: 238-257.
- Franke, M. & Bergen, L. (2020). Theory-driven statistical modeling.
- Dayal, V. (1998). Any as Inherently Modal. L&P.
- Szabolcsi, A. (2004). Positive polarity — negative polarity. NLLT.
-/

set_option autoImplicit false

namespace RSA.FCIAny

open Real (rpow rpow_nonneg)

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- The 7 states from Alsop (2024) for a 2-item domain {S, P}.
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

/-- Alsop (2024) GI-RSA model for free choice *any*.
    Two global interpretations serve as latent variables (Franke & Bergen 2020).
    S1 score is rpow(L0, α) — standard belief-based RSA. -/
noncomputable def cfg (worldPr : FCIState → ℝ) (hp : ∀ w, 0 ≤ worldPr w) :
    RSA.RSAConfig Utterance FCIState where
  Latent := Interp
  meaning i u w := if interpMeaning i u w then 1 else 0
  meaning_nonneg _ _ _ := by split <;> positivity
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

-- ============================================================================
-- §8. Verification
-- ============================================================================

/-- The 4 qualitative findings from Alsop (2024). -/
inductive Finding where
  | exclusiveness_derived
  | exclusiveness_robust
  | not_every_uniform
  | not_every_weakened
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

/-- The RSA model accounts for all 4 findings from Alsop (2024). -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact exclusiveness_derived
  · exact exclusiveness_robust
  · exact not_every_uniform
  · exact not_every_weakened

end RSA.FCIAny
