import Linglib.Tactics.RSAPredict
import Linglib.Theories.Sociolinguistics.EckertMontague
import Linglib.Phenomena.SocialMeaning.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# @cite{burnett-2019} — Signalling Games, Sociolinguistic Variation, and
the Construction of Style

Linguistics and Philosophy 42: 419–450.

## Overview

Social Meaning Games (SMGs) model how sociolinguistic variant choice
conveys social information. A speaker's use of *-ing* vs *-in'* induces
listener inferences about persona traits (competent, friendly, etc.).
The framework combines @cite{lewis-1969}'s signalling games with RSA-style
Bayesian reasoning to derive both style shifting (intra-speaker variation
across contexts) and social stratification (inter-speaker variation across
classes) from the same principles.

## Architecture

The meaning function is **grounded** in the Eckert–Montague lift from
`EckertMontague.emMeaningMI`: each variant's Eckert field (a set of
indexed properties) is lifted to persona compatibility via intersection
semantics. The grounding theorem `ingMeaning_eq_emMeaningMI` verifies
that the study's meaning function matches the theory-layer derivation.

Each context is an `RSAConfig INGVariant Persona` with beliefBased S1
scoring (S1(v|π) ∝ L0(π|v)^α, α=6) and context-specific worldPrior.
All predictions are verified by `rsa_predict`.

## Key predictions

1. **Per-persona variant preference**: cool-guy prefers *-in'* ~69%
2. **Style shifting**: casual→careful flips the cool-guy's preference
3. **Stern-leader exclusion**: -in' is incompatible with stern leader
4. **Listener interpretation**: Rice/Pelosi/Bush /t/ release predictions
5. **Bulletproofing**: strong prior overwhelms variant effects (Bush)
6. **Cross-reference**: model predictions close to @cite{labov-2012} data
-/

set_option autoImplicit false

namespace Phenomena.SocialMeaning.Studies.Burnett2019

open Sociolinguistics
open Sociolinguistics.EckertMontague
open RSA

-- ============================================================================
-- §1. Types
-- ============================================================================

/-- Social properties (Burnett example (5)). Two bipolar dimensions:
    competence (competent/incompetent) and warmth (friendly/aloof). -/
inductive PersonaTrait where
  | competent | incompetent | friendly | aloof
  deriving DecidableEq, BEq, Repr

instance : Fintype PersonaTrait where
  elems := {.competent, .incompetent, .friendly, .aloof}
  complete := by intro x; cases x <;> simp

/-- The four personae: maximally consistent subsets (Burnett example (6)).
    Each selects one pole per dimension. -/
inductive Persona where
  | coolGuy      -- {competent, friendly}: the cool guy
  | sternLeader  -- {competent, aloof}: the stern leader
  | doofus       -- {incompetent, friendly}: the doofus
  | asshole      -- {incompetent, aloof}: the arrogant asshole
  deriving DecidableEq, BEq, Repr

instance : Fintype Persona where
  elems := {.coolGuy, .sternLeader, .doofus, .asshole}
  complete := by intro x; cases x <;> simp

/-- ING variants (Burnett example (8)). -/
inductive INGVariant where
  | ing  -- *-ing* [ɪŋ]
  | in'  -- *-in'* [ɪn]
  deriving DecidableEq, BEq, Repr

instance : Fintype INGVariant where
  elems := {.ing, .in'}
  complete := by intro x; cases x <;> simp

-- ============================================================================
-- §2. Meaning: grounded in Eckert–Montague lift
-- ============================================================================

/-! Eckert fields (Burnett example (10)):
- [*-ing*] = {competent, aloof}
- [*-in'*] = {incompetent, friendly}

The meaning function is derived via the Montagovian Individual /
intersection semantics (Burnett footnote 14, Table 1): persona p is
compatible with variant v iff p shares at least one property with v's
Eckert field. -/

/-- The property space for Burnett's simplified example. -/
def burnettSpace : PropertySpace where
  Property := PersonaTrait
  incompatible
    | .competent, .incompetent | .incompetent, .competent => true
    | .friendly, .aloof | .aloof, .friendly => true
    | _, _ => false
  incomp_symm := by intro p q; cases p <;> cases q <;> simp
  incomp_irrefl := by intro p; cases p <;> rfl

/-- Persona membership as a `Finset`. -/
def Persona.toFinset : Persona → Finset PersonaTrait
  | .coolGuy     => {.competent, .friendly}
  | .sternLeader => {.competent, .aloof}
  | .doofus      => {.incompetent, .friendly}
  | .asshole     => {.incompetent, .aloof}

/-- Eckert fields for (ING) (Burnett example (10)). -/
def ingEckertField : INGVariant → Finset PersonaTrait
  | .ing => {.competent, .aloof}
  | .in' => {.incompetent, .friendly}

/-- The ING grounded field: both Eckert fields are consistent. -/
def ingField : GroundedField INGVariant burnettSpace where
  indexedProperties := ingEckertField
  indexed_consistent := by intro v; cases v <;> native_decide

/-- Meaning via the EM intersection lift: persona p is compatible with
    variant v iff p shares ≥1 property with v's Eckert field. -/
def ingMeaning : INGVariant → Persona → Bool
  | .ing, .coolGuy     => true   -- coolGuy has competent ∈ {comp, aloof}
  | .ing, .sternLeader => true   -- sternLeader has comp AND aloof
  | .ing, .asshole     => true   -- asshole has aloof ∈ {comp, aloof}
  | .ing, .doofus      => false  -- doofus has neither comp nor aloof
  | .in', .coolGuy     => true   -- coolGuy has friendly ∈ {incomp, friendly}
  | .in', .sternLeader => false  -- sternLeader has neither incomp nor friendly
  | .in', .asshole     => true   -- asshole has incomp ∈ {incomp, friendly}
  | .in', .doofus      => true   -- doofus has incomp AND friendly

/-- **Grounding theorem**: the inline meaning function equals the
    theory-layer `emMeaningMI` applied to the ING Eckert fields. -/
theorem ingMeaning_eq_emMeaningMI (v : INGVariant) (p : Persona) :
    ingMeaning v p = emMeaningMI ingField v p.toFinset := by
  cases v <;> cases p <;> native_decide

/-- *-ing* is compatible with 3 personae (Table 1: excludes doofus). -/
theorem ing_compat_count :
    (Finset.univ.filter (fun p => ingMeaning .ing p = true)).card = 3 := by
  native_decide

/-- *-in'* is compatible with 3 personae (Table 1: excludes stern leader). -/
theorem in'_compat_count :
    (Finset.univ.filter (fun p => ingMeaning .in' p = true)).card = 3 := by
  native_decide

-- ============================================================================
-- §3. RSAConfig: SMG as belief-based RSA
-- ============================================================================

/-! Each social context is an `RSAConfig INGVariant Persona`:
- Worlds = personae (what the listener infers)
- Utterances = variants (what the speaker chooses)
- Meaning = EM intersection lift
- S1 scoring = beliefBased: S1(v|p) ∝ L0(p|v)^α
- α = 6 (Burnett p. 435)
- worldPrior = context-dependent belief about the speaker -/

/-- Construct an SMG as an RSAConfig with context-specific prior.

    The meaning function incorporates the prior so that L0 matches Burnett's
    naive listener: L₀(π|v) ∝ Pr(π) · ⟦v⟧(π). Without the prior in meaning,
    L0 would be uniform over compatible personae (1/3 for all), erasing the
    context-dependence that drives style shifting. -/
noncomputable abbrev mkSMG (prior : Persona → ℚ) (h : ∀ p, (0 : ℚ) ≤ prior p) :
    RSAConfig INGVariant Persona where
  meaning _ _ v p := if ingMeaning v p then ↑(prior p) else 0
  meaning_nonneg _ _ _ _ := by
    split
    · exact_mod_cast h _
    · exact le_refl 0
  s1Score l0 α _ p v :=
    if l0 v p = 0 then 0
    else Real.exp (α * Real.log (l0 v p))
  s1Score_nonneg _ _ _ _ _ _ _ := by
    split
    · exact le_refl 0
    · exact le_of_lt (Real.exp_pos _)
  α := 6
  α_pos := by norm_num
  worldPrior p := ↑(prior p)
  worldPrior_nonneg p := by exact_mod_cast h p
  latentPrior_nonneg _ _ := by norm_num

-- ============================================================================
-- §3a. Context-specific configurations
-- ============================================================================

/-- Casual-context prior (Burnett Table 2): voters at the barbecue
    think Obama is aloof (personae with aloof get more weight). -/
def casualPrior : Persona → ℚ
  | .sternLeader => 3/10
  | .coolGuy     => 2/10
  | .asshole     => 3/10
  | .doofus      => 2/10

noncomputable abbrev casualCfg : RSAConfig INGVariant Persona :=
  mkSMG casualPrior (by intro p; cases p <;> norm_num [casualPrior])

/-- Careful-context prior (Burnett Table 5): journalists think Obama
    is incompetent (incompetent personae get more weight). -/
def carefulPrior : Persona → ℚ
  | .sternLeader => 2/10
  | .coolGuy     => 2/10
  | .asshole     => 3/10
  | .doofus      => 3/10

noncomputable abbrev carefulCfg : RSAConfig INGVariant Persona :=
  mkSMG carefulPrior (by intro p; cases p <;> norm_num [carefulPrior])

/-- Rice: uniform prior — unfamiliar politician (Burnett Table 10). -/
def ricePrior : Persona → ℚ
  | _ => 1/4

noncomputable abbrev riceCfg : RSAConfig INGVariant Persona :=
  mkSMG ricePrior (by intro p; cases p <;> norm_num [ricePrior])

/-- Pelosi: listeners believe she is inarticulate (Burnett Table 13). -/
def pelosiPrior : Persona → ℚ
  | .sternLeader => 5/100
  | .coolGuy     => 5/100
  | .asshole     => 45/100
  | .doofus      => 45/100

noncomputable abbrev pelosiCfg : RSAConfig INGVariant Persona :=
  mkSMG pelosiPrior (by intro p; cases p <;> norm_num [pelosiPrior])

/-- Bush: listeners almost certain he is {inarticulate, aloof}
    (Burnett Table 15). -/
def bushPrior : Persona → ℚ
  | .sternLeader => 1/100
  | .coolGuy     => 1/100
  | .asshole     => 97/100
  | .doofus      => 1/100

noncomputable abbrev bushCfg : RSAConfig INGVariant Persona :=
  mkSMG bushPrior (by intro p; cases p <;> norm_num [bushPrior])

-- ============================================================================
-- §4. Speaker predictions (casual context)
-- ============================================================================

section casual

/-- Cool-guy at the barbecue prefers *-in'* over *-ing* (~69% vs ~31%).
    Burnett (p. 435): "we predict that Obama will use -in' around **69%**
    of the time [...] which is close to what Labov found" (72%). -/
theorem casual_coolGuy_prefers_in' :
    casualCfg.S1 () .coolGuy .in' > casualCfg.S1 () .coolGuy .ing := by
  rsa_predict

/-- Stern leader only uses *-ing*: *-in'* is incompatible (Table 1).
    This predicts ~0% *-in'* in formal contexts where Obama constructs
    the stern leader. -/
theorem casual_sternLeader_prefers_ing :
    casualCfg.S1 () .sternLeader .ing > casualCfg.S1 () .sternLeader .in' := by
  rsa_predict

/-- The doofus only uses *-in'*: *-ing* is incompatible (Table 1). -/
theorem casual_doofus_prefers_in' :
    casualCfg.S1 () .doofus .in' > casualCfg.S1 () .doofus .ing := by
  rsa_predict

end casual

-- ============================================================================
-- §5. Style shifting: casual → careful
-- ============================================================================

section styleShifting

/-- In the careful context, the cool-guy now prefers *-ing* over *-in'*.
    The prior shift reverses the informativity ranking. -/
theorem careful_coolGuy_prefers_ing :
    carefulCfg.S1 () .coolGuy .ing > carefulCfg.S1 () .coolGuy .in' := by
  rsa_predict

end styleShifting

-- ============================================================================
-- §6. /t/ release: listener interpretation (@cite{podesva-etal-2015})
-- ============================================================================

/-! The /t/ release variable has the same mathematical structure as (ING).
Relabeling: articulate↔competent, inarticulate↔incompetent (same friendly/aloof).
Variants: released [tʰ]↔*-ing*, flapped [ɾ]↔*-in'*.
The Eckert fields are structurally identical (Burnett example (19)):
  [tʰ] = {articulate, aloof},  [ɾ] = {inarticulate, friendly}.

We reuse the same types and meaning function, since the math is isomorphic.
The personae reinterpret as:
  coolGuy ↔ {articulate, friendly},
  sternLeader ↔ {articulate, aloof},
  doofus ↔ {inarticulate, friendly},
  asshole ↔ {inarticulate, aloof}. -/

/-- The asshole prefers *-in'* in the casual context (both variants are
    compatible, but *-in'* is more informative given the prior). -/
theorem casual_asshole_prefers_in' :
    casualCfg.S1 () .asshole .in' > casualCfg.S1 () .asshole .ing := by
  rsa_predict

section tRelease

/-- Rice: released /t/ triggers {articulate, aloof} = stern leader
    (Burnett Table 11). With uniform prior, the exclusive variant
    (only *-ing* compatible) gets double the L1 weight. -/
theorem rice_released_sternLeader :
    riceCfg.L1 .ing .sternLeader > riceCfg.L1 .ing .coolGuy := by
  rsa_predict

/-- Rice: flapped /t/ triggers {inarticulate, friendly} = doofus
    (Burnett Table 11). Symmetric to the released case. -/
theorem rice_flapped_doofus :
    riceCfg.L1 .in' .doofus > riceCfg.L1 .in' .coolGuy := by
  rsa_predict

/-- Pelosi: released /t/ predominantly triggers {inarticulate, aloof} —
    the strong prior that she is inarticulate overwhelms the released /t/
    association with articulateness (Burnett Table 14). -/
theorem pelosi_released_inarticAloof :
    pelosiCfg.L1 .ing .asshole > pelosiCfg.L1 .ing .sternLeader := by
  rsa_predict

/-- Pelosi: flapped /t/ triggers {inarticulate, friendly} (Table 14). -/
theorem pelosi_flapped_friendly :
    pelosiCfg.L1 .in' .doofus > pelosiCfg.L1 .in' .asshole := by
  rsa_predict

/-- Bush "bulletproofing" (Burnett p. 444, Table 16): the prior is so
    extreme that variant choice has no practical effect. Both released and
    flapped /t/ yield >90% {inarticulate, aloof}. -/
theorem bush_bulletproofing :
    bushCfg.L1 .ing .asshole > 9/10 ∧
    bushCfg.L1 .in' .asshole > 9/10 := by
  exact ⟨by rsa_predict, by rsa_predict⟩

end tRelease

end Phenomena.SocialMeaning.Studies.Burnett2019
