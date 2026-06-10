import Linglib.Tactics.RSAPredict
import Linglib.Pragmatics.SocialMeaning.EckertMontague
import Linglib.Pragmatics.IBR.Basic
import Linglib.Phenomena.SocialMeaning.IndexicalField
import Linglib.Phenomena.SocialMeaning.ING
import Linglib.Studies.Labov2012
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# [burnett-2019] — Signalling Games, Sociolinguistic Variation, and
the Construction of Style

Linguistics and Philosophy 42: 419–450.

## Overview

Social Meaning Games (SMGs) model how sociolinguistic variant choice
conveys social information. A speaker's use of *-ing* vs *-in'* induces
listener inferences about persona traits (competent, friendly, etc.).
The framework combines [lewis-1969]'s signalling games with RSA-style
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
6. **Cross-reference**: model predictions close to [labov-2012] data
-/

set_option autoImplicit false

namespace Burnett2019

open SocialMeaning
open SocialMeaning.EckertMontague
open Phenomena.SocialMeaning.ING
open RSA

-- ============================================================================
-- §1. Types
-- ============================================================================

/-- Social properties (Burnett example (5)). Two bipolar dimensions:
    competence (competent/incompetent) and warmth (friendly/aloof). -/
inductive PersonaTrait where
  | competent | incompetent | friendly | aloof
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

instance : Fintype Persona where
  elems := {.coolGuy, .sternLeader, .doofus, .asshole}
  complete := by intro x; cases x <;> simp

-- INGVariant is imported from Phenomena.SocialMeaning.ING
-- Burnett's *-ing* = .velar, *-in'* = .apical

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
  | .velar => {.competent, .aloof}
  | .apical => {.incompetent, .friendly}

/-- The ING grounded field: both Eckert fields are consistent. -/
def ingField : GroundedField INGVariant burnettSpace where
  indexedProperties := ingEckertField
  indexed_consistent := by intro v; cases v <;> native_decide

/-- Meaning via the EM intersection lift: persona p is compatible with
    variant v iff p shares ≥1 property with v's Eckert field. -/
def ingMeaning : INGVariant → Persona → Bool
  | .velar,.coolGuy     => true   -- coolGuy has competent ∈ {comp, aloof}
  | .velar,.sternLeader => true   -- sternLeader has comp AND aloof
  | .velar,.asshole     => true   -- asshole has aloof ∈ {comp, aloof}
  | .velar,.doofus      => false  -- doofus has neither comp nor aloof
  | .apical,.coolGuy     => true   -- coolGuy has friendly ∈ {incomp, friendly}
  | .apical,.sternLeader => false  -- sternLeader has neither incomp nor friendly
  | .apical,.asshole     => true   -- asshole has incomp ∈ {incomp, friendly}
  | .apical,.doofus      => true   -- doofus has incomp AND friendly

/-- **Grounding theorem**: the inline meaning function equals the
    theory-layer `emMeaningMI` applied to the ING Eckert fields. -/
theorem ingMeaning_eq_emMeaningMI (v : INGVariant) (p : Persona) :
    ingMeaning v p = emMeaningMI ingField v p.toFinset := by
  cases v <;> cases p <;> native_decide

/-- *-ing* is compatible with 3 personae (Table 1: excludes doofus). -/
theorem ing_compat_count :
    (Finset.univ.filter (fun p => ingMeaning .velar p = true)).card = 3 := by
  native_decide

/-- *-in'* is compatible with 3 personae (Table 1: excludes stern leader). -/
theorem in'_compat_count :
    (Finset.univ.filter (fun p => ingMeaning .apical p = true)).card = 3 := by
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
    casualCfg.S1 () .coolGuy .apical > casualCfg.S1 () .coolGuy .velar := by
  rsa_predict

/-- Stern leader only uses *-ing*: *-in'* is incompatible (Table 1).
    This predicts ~0% *-in'* in formal contexts where Obama constructs
    the stern leader. -/
theorem casual_sternLeader_prefers_ing :
    casualCfg.S1 () .sternLeader .velar > casualCfg.S1 () .sternLeader .apical := by
  rsa_predict

/-- The doofus only uses *-in'*: *-ing* is incompatible (Table 1). -/
theorem casual_doofus_prefers_in' :
    casualCfg.S1 () .doofus .apical > casualCfg.S1 () .doofus .velar := by
  rsa_predict

end casual

-- ============================================================================
-- §5. Style shifting: casual → careful
-- ============================================================================

section styleShifting

/-- In the careful context, the cool-guy now prefers *-ing* over *-in'*.
    The prior shift reverses the informativity ranking. -/
theorem careful_coolGuy_prefers_ing :
    carefulCfg.S1 () .coolGuy .velar > carefulCfg.S1 () .coolGuy .apical := by
  rsa_predict

end styleShifting

-- ============================================================================
-- §6. /t/ release: listener interpretation ([podesva-etal-2015])
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
    casualCfg.S1 () .asshole .apical > casualCfg.S1 () .asshole .velar := by
  rsa_predict

section tRelease

/-- Rice: released /t/ triggers {articulate, aloof} = stern leader
    (Burnett Table 11). With uniform prior, the exclusive variant
    (only *-ing* compatible) gets double the L1 weight. -/
theorem rice_released_sternLeader :
    riceCfg.L1 .velar .sternLeader > riceCfg.L1 .velar .coolGuy := by
  rsa_predict

/-- Rice: flapped /t/ triggers {inarticulate, friendly} = doofus
    (Burnett Table 11). Symmetric to the released case. -/
theorem rice_flapped_doofus :
    riceCfg.L1 .apical .doofus > riceCfg.L1 .apical .coolGuy := by
  rsa_predict

/-- Pelosi: released /t/ predominantly triggers {inarticulate, aloof} —
    the strong prior that she is inarticulate overwhelms the released /t/
    association with articulateness (Burnett Table 14). -/
theorem pelosi_released_inarticAloof :
    pelosiCfg.L1 .velar .asshole > pelosiCfg.L1 .velar .sternLeader := by
  rsa_predict

/-- Pelosi: flapped /t/ triggers {inarticulate, friendly} (Table 14). -/
theorem pelosi_flapped_friendly :
    pelosiCfg.L1 .apical .doofus > pelosiCfg.L1 .apical .asshole := by
  rsa_predict

/-- Bush "bulletproofing" (Burnett p. 444, Table 16): the prior is so
    extreme that variant choice has no practical effect. Both released and
    flapped /t/ yield >90% {inarticulate, aloof}. -/
theorem bush_bulletproofing :
    bushCfg.L1 .velar .asshole > 9/10 ∧
    bushCfg.L1 .apical .asshole > 9/10 := by
  exact ⟨by rsa_predict, by rsa_predict⟩

end tRelease

-- ============================================================================
-- §7. Cross-study bridge: Labov 2012 data ↔ SMG predictions
-- ============================================================================

/-- Cross-reference: the SMG model's qualitative predictions match the
    directional pattern observed in [labov-2012]'s data on Obama's
    (ING) rates. The model predicts the cool-guy persona prefers *-in'*
    in casual context and *-ing* in careful context; the data shows
    Obama's *-in'* rate decreasing monotonically from casual (72%)
    through careful (33%) to formal (3%). -/
theorem smg_matches_labov_direction :
    -- SMG: cool-guy prefers -in' in casual context
    casualCfg.S1 () .coolGuy .apical > casualCfg.S1 () .coolGuy .velar ∧
    -- SMG: cool-guy prefers -ing in careful context
    carefulCfg.S1 () .coolGuy .velar > carefulCfg.S1 () .coolGuy .apical ∧
    -- Observed: casual > careful > formal
    Labov2012.obama_ING.casual > Labov2012.obama_ING.careful ∧
    Labov2012.obama_ING.careful > Labov2012.obama_ING.formal :=
  ⟨casual_coolGuy_prefers_in', careful_coolGuy_prefers_ing,
   by native_decide, by native_decide⟩

-- ============================================================================
-- §8. Social Meaning Games (Definitions 4.1–4.4)
-- ============================================================================

/-! Burnett's Social Meaning Game (SMG): a signalling game in which a
speaker's variant choice conveys social information about their persona.
The SMG reuses [franke-2011]'s IBR machinery — the naive listener,
strategic speaker, and uncovering listener are all instances of IBR
reasoning applied to a social-meaning interpretation game.

The key design choice: `toInterpGame` converts any SMG into Franke's
`InterpGame`, so SMG agents reuse the existing IBR iteration machinery.
The grounding theorem `naiveListener_eq_L0` verifies that this reuse
is semantically correct: the SMG L₀ definition produces the same
results as running Franke's L₀ on the converted game. -/

section smgDefs

open RSA.IBR

/-- A Social Meaning Game (Burnett Def. 4.1): a signalling game where
    variant choice conveys social information.

    - `P`: persona types (social categories the listener is trying to infer)
    - `V`: variant types (linguistic forms the speaker chooses)
    - `prior`: probability distribution over personae
    - `meaning`: whether a variant is compatible with a persona
      (derived from the EM field: `v` means `t` iff the EM lift of `v`
      includes persona `t`)
    - `socialEval`: the speaker's utility μ(t, v) — how much persona `t`
      values being associated with variant `v` -/
structure SocialMeaningGame (P V : Type)
    [Fintype P] [Fintype V]
    [DecidableEq P] [DecidableEq V] where
  /-- Prior probability over personae. -/
  prior : P → ℚ
  /-- Prior is non-negative. -/
  prior_nonneg : ∀ (t : P), 0 ≤ prior t
  /-- Semantic meaning: is variant `v` compatible with persona `t`? -/
  meaning : V → P → Bool
  /-- Social evaluation: how much persona `t` values variant `v`. -/
  socialEval : P → V → ℚ

/-- Convert a Social Meaning Game to Franke's interpretation game.

    This is the key architectural bridge: SMG analysis reuses the
    existing IBR machinery from [franke-2011] rather than reimplementing
    iterated best response.

    The mapping:
    - States = Personae (what the listener tries to infer)
    - Messages = Variants (what the speaker chooses)
    - meaning = SMG meaning (EM field compatibility)
    - prior = SMG prior over personae -/
def SocialMeaningGame.toInterpGame {P V : Type}
    [Fintype P] [Fintype V]
    [DecidableEq P] [DecidableEq V]
    (smg : SocialMeaningGame P V) : InterpGame :=
  { State := P
    Message := V
    meaning := smg.meaning
    prior := smg.prior }

/-- The naive listener (Burnett Def. 4.2): L₀(t | v) = 1/|⟦v⟧| if
    ⟦v⟧(t), 0 otherwise.

    This is Franke's literal L₀ — uniform over compatible types, NOT
    Bayesian conditioning on the prior. The prior is passed through to
    `toInterpGame` but Franke's `HearerStrategy.literal` ignores it,
    distributing probability uniformly over `trueStates`.

    The Bayesian L₀ (L₀(t | v) ∝ Pr(t) · ⟦v⟧(t)) is what Burnett's
    RSA model uses (eq. 11). That prior-weighted version lives in the
    `RSAConfig` meaning function of §3, not here. -/
def naiveListener {P V : Type}
    [Fintype P] [Fintype V]
    [DecidableEq P] [DecidableEq V]
    (smg : SocialMeaningGame P V)
    (v : V) (t : P) : ℚ :=
  (L0 smg.toInterpGame).respond v t

/-- **Grounding theorem**: The SMG naive listener IS Franke's L₀
    applied to the converted game. True by construction. -/
theorem naiveListener_eq_L0 {P V : Type}
    [Fintype P] [Fintype V]
    [DecidableEq P] [DecidableEq V]
    (smg : SocialMeaningGame P V) :
    naiveListener smg = fun v t => (L0 smg.toInterpGame).respond v t := rfl

/-- The strategic speaker (simplified): S₁(v | t) ∝ μ(t, v) · ⟦v⟧(t).

    This normalizes raw social evaluation scores over compatible variants,
    producing a closed-form rational speaker. This is a simplification of
    Burnett's Def. 4.3 / eq. (13), which uses soft-max over log-L₀:
    P_S(v | π) ∝ exp(α · ln(L₀(π | v))). The full RSA formulation with
    belief-based S₁ scoring lives in the `RSAConfig` of §3, not here.

    Unlike Franke's best-response speaker (which maximizes hearer success),
    the SMG speaker maximizes *social* utility: a persona chooses variants
    that make the listener more likely to infer a desirable persona. -/
def strategicSpeaker {P V : Type}
    [Fintype P] [Fintype V]
    [DecidableEq P] [DecidableEq V]
    (smg : SocialMeaningGame P V)
    (t : P) (v : V) : ℚ :=
  if smg.meaning v t then
    let numerator := smg.socialEval t v
    let denominator := Finset.univ.sum fun v' =>
      if smg.meaning v' t then smg.socialEval t v' else 0
    if denominator == 0 then 0 else numerator / denominator
  else 0

/-- The uncovering listener (Burnett Def. 4.4): L₁(t | v) ∝ Pr(t) · S₁(v | t).

    The listener uses Bayes' rule to infer the speaker's persona from
    the observed variant choice, using the strategic speaker's production
    probabilities as the likelihood. -/
def uncoveringListener {P V : Type}
    [Fintype P] [Fintype V]
    [DecidableEq P] [DecidableEq V]
    (smg : SocialMeaningGame P V)
    (v : V) (t : P) : ℚ :=
  let numerator := strategicSpeaker smg t v * smg.prior t
  let denominator := Finset.univ.sum fun t' => strategicSpeaker smg t' v * smg.prior t'
  if denominator == 0 then 0 else numerator / denominator

/-- Construct a Social Meaning Game from a grounded field, prior, and
    social evaluation function.

    The meaning function is derived from the EM field: variant `v`
    is compatible with a persona set `p` iff `v`'s indexed properties
    are a subset of `p`'s properties. -/
def fromGroundedField {V : Type} [Fintype V] [DecidableEq V]
    (ps : PropertySpace)
    (gf : GroundedField V ps)
    (personaeSets : Finset (Finset ps.Property))
    [Fintype personaeSets] [DecidableEq personaeSets]
    (prior : personaeSets → ℚ)
    (prior_nonneg : ∀ (t : personaeSets), 0 ≤ prior t)
    (socialEval : personaeSets → V → ℚ) :
    SocialMeaningGame personaeSets V :=
  { prior := prior
    prior_nonneg := prior_nonneg
    meaning := fun v t => gf.indexedProperties v ⊆ t.val
    socialEval := socialEval }

end smgDefs

/-! The SMG's `naiveListener` is Franke's literal L₀ — *uniform* over
compatible personae. This captures the exclusion structure (which
personae are ruled out by each variant) but not the prior-weighted
refinement. The *quantitative* predictions (69% -in' for cool guy,
style shifting) use the RSAConfig's belief-based S₁ (Burnett eq. 13:
P_S(m|π) ∝ L₀(π|m)^α), which incorporates the context-specific prior
into the meaning function to recover Bayesian conditioning. We
construct an SMG from the study's types and prove structural
properties. -/

section smgBridge

/-- Obama's social value function μ at the barbecue
    ([burnett-2019], Table 6, p. 438).

    Cool guy ({competent, friendly}) is most valued (μ = 2);
    asshole ({incompetent, aloof}) is least (μ = 0).
    The μ function reflects what the speaker (Obama) most wants
    the listener to infer about him in this context. -/
def obamaValues : Persona → ℚ
  | .coolGuy     => 2
  | .sternLeader => 1
  | .doofus      => 1
  | .asshole     => 0

/-- The (ING) Social Meaning Game for the casual context
    ([burnett-2019], Def. 4.1 + Table 2 + Table 6).

    This connects the study's types to the §8 game structure,
    exercising `SocialMeaningGame`, `naiveListener`, and
    `toInterpGame`. -/
def casualSMG : SocialMeaningGame Persona INGVariant where
  prior := casualPrior
  prior_nonneg := by intro p; cases p <;> norm_num [casualPrior]
  meaning := ingMeaning
  socialEval := fun p _ => obamaValues p

/-- The SMG meaning is grounded in the Eckert–Montague intersection
    lift — connecting the game structure to the compositional
    semantics layer via `ingMeaning_eq_emMeaningMI`. -/
theorem smg_meaning_grounded (v : INGVariant) (p : Persona) :
    casualSMG.meaning v p = emMeaningMI ingField v p.toFinset :=
  ingMeaning_eq_emMeaningMI v p

/-- The naive listener excludes stern leader after hearing *-in'*
    (incompatible: stern leader = {competent, aloof} shares no
    property with [-in'] = {incompetent, friendly}). -/
theorem smg_L0_in'_excludes_sternLeader :
    naiveListener casualSMG .apical .sternLeader = 0 := by
  native_decide

/-- The naive listener excludes doofus after hearing *-ing*
    (incompatible: doofus = {incompetent, friendly} shares no
    property with [-ing] = {competent, aloof}). -/
theorem smg_L0_ing_excludes_doofus :
    naiveListener casualSMG .velar .doofus = 0 := by
  native_decide

/-- The naive listener assigns equal probability (1/3) to all
    compatible personae. Franke's literal L₀ is uniform over ⟦v⟧:
    since 3 personae are compatible with each variant, each gets 1/3.

    This is the structural content of the meaning function: each variant
    partitions personae into compatible (1/3) and incompatible (0). -/
theorem smg_L0_uniform_compatible :
    naiveListener casualSMG .velar .coolGuy = 1/3 ∧
    naiveListener casualSMG .velar .sternLeader = 1/3 ∧
    naiveListener casualSMG .velar .asshole = 1/3 ∧
    naiveListener casualSMG .apical .coolGuy = 1/3 ∧
    naiveListener casualSMG .apical .asshole = 1/3 ∧
    naiveListener casualSMG .apical .doofus = 1/3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end smgBridge

end Burnett2019
