import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Semantics.Exhaustification.Operators
import Linglib.Phenomena.ScalarImplicatures.Basic

/-!
# @cite{potts-levy-2015}: Negotiating Lexical Uncertainty and Speaker Expertise with Disjunction
@cite{potts-levy-2015}

"Negotiating Lexical Uncertainty and Speaker Expertise with Disjunction."
Proceedings of the 41st Annual Meeting of the Berkeley Linguistics Society, 417–445.

## The Puzzle

Hurford-violating disjunctions like "X or A" (where A ⊆ X semantically) are
predicted to be redundant, yet they are felicitous and carry **ignorance
implicatures**: the listener infers that the speaker is uncertain which
disjunct holds.

@cite{potts-levy-2015} show that an RSA model with **lexical uncertainty**
derives this: L1 infers that the speaker might be using a lexicon under which
the disjuncts are non-overlapping, and the disjunction signals the speaker's
uncertainty about the world.

## The Model

Three worlds:
- `w₁`: only A-worlds (speaker knows A)
- `w₂`: only B-worlds (speaker knows B, where B ⊆ X \ A)
- `w₁₂`: both A- and B-worlds possible (speaker uncertain)

Three lexica for X:
- `base`: X = A ∪ B (unrefined, overlapping with A)
- `excl`: X = B only (exhaustified, disjoint from A)
- `syn`: X = A (synonymous with A)

Five utterances: A, B, X, AorX, null.

Key insight: under `syn`, "A or X" and "A" are equivalent (Hurford violation).
Under `excl`, "A or X" partitions {w₁, w₂} cleanly. L1 marginalizes over
lexica, and `excl` dominates for "A or X" — deriving the prediction that
disjunction implies speaker uncertainty (w₁₂ > w₁ > w₂).

## Join Closure

The join state w₁₂ represents speaker uncertainty. Following the paper's
convention, an utterance m is true at w₁₂ iff m is true at BOTH w₁ and w₂
(the "must" reading: the speaker can assert m only if m holds across all
worlds compatible with their knowledge).

## Expertise Model (S2)

The paper's key contribution is the **expertise parameter β**: a level-2
speaker who cares not only about informativity (L1 inferring the correct
world) but also about **lexicon signaling** (L1 inferring the correct
lexicon). The S2 utility:

    U_S2(m, w, L; β) = ln L₁(w|m) + β · ln L₁(L|m)

When β > 0, the speaker has extra incentive to use utterances that signal
the `excl` lexicon — precisely the Hurford-violating disjunction "A or X".
Following the @cite{yoon-etal-2020} pattern, we define S2 utility directly
from L1 marginals and prove comparative predictions.

## Verification Against Paper

Our model operates in the **Hurfordian parameter regime** (α > β) with α = 2,
β = 0, C = 0. The paper's Hurfordian worked example (Figure 10) uses α = 2,
β = 1, C(or) = 1. All 10 qualitative predictions match the paper:

- **L1 world inference** (§6): w₁₂ > w₁ > w₂ given "A or X"
  (paper Figure 10 L2: .91 > .09 > 0)
- **L1 lexicon inference** (§7): excl > base > syn given "A or X"
  (paper Figure 10 L2: .49 > .34 > .17)
- **S1 speaker** (§8): prefers AorX at w₁₂, prefers A at w₁ (under excl)
  (paper Figure 7(b), p. 436)
- **S2 endorsement** (§10): prefers AorX at w₁₂, A at w₁
  (paper p. 436: "S₂'s preferred message given observed state w₁∨w₂
  and lexicon L₁ is A or X")
- **Lexicon signaling** (§10): AorX signals excl more than A
  (paper Section 5.2)

### Two Implementations

1. **RSAConfig (§4–§10)**: L₁-level predictions via `rsa_predict`, zero costs,
   structural correspondence with linglib's RSA infrastructure.
2. **Full ℚ model (§12)**: L₂-level predictions via `native_decide`, with
   the paper's Hurfordian parameters (α = 2, β = 1, C(or) ≈ 1).

The paper's **definitional reading** (where syn dominates, e.g., "wine lover
or oenophile") requires β > α (paper Section 5.4, Figures 13–14) and is
not modeled here.

## Connection to @cite{potts-etal-2016}

Both papers use lexical uncertainty (Latent := Lexicon). @cite{potts-etal-2016}
applies it to embedded scalar implicatures; this paper applies it to
Hurford-violating disjunctions and speaker expertise. The mechanism is
identical — only the domain and lexica differ.
-/

set_option autoImplicit false

namespace PottsLevy2015

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- World states. w₁ = only A-state, w₂ = only B-state,
    w₁₂ = speaker uncertain (both A and B possible). -/
inductive World where
  | w₁ | w₂ | w₁₂
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Utterances: A, B, X (the ambiguous term), "A or X", and null. -/
inductive Utterance where
  | A | B | X | AorX | null
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Lexica for X.
    - base: X = A ∪ B (unrefined)
    - excl: X = B only (exhaustified, disjoint from A)
    - syn:  X = A (synonymous with A) -/
inductive Lex where
  | base | excl | syn
  deriving DecidableEq, Repr, Inhabited, Fintype

-- ============================================================================
-- §2. Truth Conditions
-- ============================================================================

/-- Truth of atomic (non-disjunctive) utterances at atomic worlds. -/
def atomicTruth : Lex → Utterance → World → Bool
  -- A is true at w₁ only
  | _, .A, .w₁ => true
  -- B is true at w₂ only
  | _, .B, .w₂ => true
  -- X depends on lexicon:
  | .base, .X, .w₁ => true   -- base: X = {w₁, w₂}
  | .base, .X, .w₂ => true
  | .excl, .X, .w₂ => true   -- excl: X = {w₂} only
  | .syn,  .X, .w₁ => true   -- syn:  X = {w₁} only
  -- null is always true
  | _, .null, _ => true
  | _, _, _ => false

/-- Truth at all worlds including the join state w₁₂.
    AorX is computed compositionally: A ∨ X.
    At w₁₂, an utterance is true iff true at BOTH w₁ and w₂
    (speaker can only assert what holds across all epistemically
    accessible worlds — the "must" reading). -/
def truth (l : Lex) (u : Utterance) (w : World) : Bool :=
  let base (w' : World) :=
    match u with
    | .AorX => atomicTruth l .A w' || atomicTruth l .X w'
    | other => atomicTruth l other w'
  match w with
  | .w₁ => base .w₁
  | .w₂ => base .w₂
  | .w₁₂ => base .w₁ && base .w₂

-- ============================================================================
-- §3. Exhaustification Grounding
-- ============================================================================

/-! The `excl` lexicon is the exhaustified reading of X relative to
alternatives {A, X}. We prove this structurally: at every atomic world,
excl(X) = base(X) ∧ ¬A, which is what `exh_mw({A, X}, X)` yields
when there are exactly two alternatives with A ⊂ X. -/

/-- excl(X) = base(X) ∧ ¬base(A): X minus A. -/
theorem excl_is_base_minus_A :
    ∀ w, atomicTruth .excl .X w =
      (atomicTruth .base .X w && !atomicTruth .base .A w) := by
  native_decide

/-- syn(X) = base(A): X narrowed to overlap with A. -/
theorem syn_is_base_A :
    ∀ w, atomicTruth .syn .X w = atomicTruth .base .A w := by
  native_decide

/-- Base X strictly entails excl X (excl is a proper refinement). -/
theorem base_entails_excl :
    (∀ w, atomicTruth .excl .X w = true → atomicTruth .base .X w = true) ∧
    ∃ w, atomicTruth .base .X w = true ∧ atomicTruth .excl .X w = false := by
  native_decide

-- ============================================================================
-- §4. RSAConfig
-- ============================================================================

open RSA Real in
/-- @cite{potts-levy-2015} lexical uncertainty model for Hurford disjunctions.

    Latent variable = Lex (base vs excl vs syn).
    L0: literal listener under lexicon l.
    S1: belief-based scoring, rpow(L0(w|u), α).
    L1: marginalizes over lexica with uniform prior.

    α = 2 to sharpen speaker preferences. -/
noncomputable def cfg : RSAConfig Utterance World where
  Latent := Lex
  meaning _ lex u w := if truth lex u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> norm_num
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ _ hl0 _ := rpow_nonneg (hl0 _ _) _
  α := 2
  α_pos := two_pos
  latentPrior_nonneg _ _ := by norm_num
  worldPrior_nonneg _ := by norm_num

-- ============================================================================
-- §5. Structural Properties
-- ============================================================================

/-- Under syn lexicon, "A or X" has the same extension as "A" alone.
    This is the Hurford violation: the disjunction is redundant. -/
theorem syn_AorX_eq_A :
    ∀ w, truth .syn .AorX w = truth .syn .A w := by native_decide

/-- Under excl lexicon, A and X are semantically disjoint.
    This is the exhaustified reading that rescues the disjunction. -/
theorem excl_disjoint :
    ¬∃ w, truth .excl .A w = true ∧ truth .excl .X w = true := by native_decide

/-- Under excl, "A or X" is true at w₁₂ and is the only non-null
    utterance true there. A, B, X alone each fail at w₁₂ because
    they cannot cover both atomic states. -/
theorem excl_w12_AorX_unique :
    truth .excl .AorX .w₁₂ = true ∧
    truth .excl .A .w₁₂ = false ∧
    truth .excl .B .w₁₂ = false ∧
    truth .excl .X .w₁₂ = false := by native_decide

/-- Under syn, "A or X" is FALSE at w₁₂ (syn X = A, so AorX = A,
    and A fails the "must" check because A is false at w₂). -/
theorem syn_w12_AorX_false :
    truth .syn .AorX .w₁₂ = false := by native_decide

/-- Under base, "A or X" is true at w₁₂ (base X covers both w₁
    and w₂, so the disjunction holds at both atomic states). -/
theorem base_w12_AorX_true :
    truth .base .AorX .w₁₂ = true := by native_decide

-- ============================================================================
-- §6. L1 Predictions: Uncertainty Implicature
-- ============================================================================

/-! The key prediction: hearing "A or X", L1 infers the speaker is
uncertain (w₁₂), not that the speaker knows A (w₁) or knows B (w₂).

This is the ignorance/uncertainty implicature. The speaker could have
said just "A" if they knew w₁, or just "X" if they knew w₂ (under the
excl lexicon). By choosing the disjunction, the speaker signals that
they cannot commit to either disjunct — i.e., they are in w₁₂. -/

/-- Uncertainty implicature: w₁₂ > w₁ given "A or X". -/
theorem uncertainty_w12_vs_w1 :
    cfg.L1 .AorX .w₁₂ > cfg.L1 .AorX .w₁ := by
  rsa_predict

/-- Uncertainty implicature: w₁₂ > w₂ given "A or X". -/
theorem uncertainty_w12_vs_w2 :
    cfg.L1 .AorX .w₁₂ > cfg.L1 .AorX .w₂ := by
  rsa_predict

/-- Complete uncertainty ordering: w₁ > w₂. The listener assigns
    higher posterior to w₁ than w₂ because under excl, "A or X"
    at w₁ has A as the operative disjunct (a natural reading),
    while at w₂ only excl-X contributes (a refined reading). -/
theorem uncertainty_w1_vs_w2 :
    cfg.L1 .AorX .w₁ > cfg.L1 .AorX .w₂ := by
  rsa_predict

-- ============================================================================
-- §7. L1 Predictions: Lexicon Inference
-- ============================================================================

/-! L1 also infers which lexicon the speaker is using. For "A or X",
the excl lexicon dominates: it makes the disjunction maximally
informative (A and X partition the space). The syn lexicon makes the
disjunction redundant (Hurford violation), so L1 disprefers it. -/

/-- Lexicon inference: excl preferred over base for "A or X". -/
theorem lexicon_excl_vs_base :
    cfg.L1_latent .AorX .excl > cfg.L1_latent .AorX .base := by
  rsa_predict

/-- Lexicon inference: excl preferred over syn for "A or X". -/
theorem lexicon_excl_vs_syn :
    cfg.L1_latent .AorX .excl > cfg.L1_latent .AorX .syn := by
  rsa_predict

/-- Lexicon inference: base preferred over syn for "A or X".
    Completes the full ordering: excl > base > syn.
    The syn lexicon makes "A or X" redundant (= "A"),
    so it gets the least support from L1. -/
theorem lexicon_base_vs_syn :
    cfg.L1_latent .AorX .base > cfg.L1_latent .AorX .syn := by
  rsa_predict

-- ============================================================================
-- §8. S1 Predictions: Speaker Rationality
-- ============================================================================

/-! The paper argues that a rational speaker at w₁₂ (uncertain)
should prefer the disjunction "A or X" over simpler utterances.
This is the production-side counterpart to the L1 uncertainty
implicature: the speaker KNOWS they're in w₁₂ and chooses AorX
because it is the most informative utterance at that world. -/

/-- Speaker at w₁₂ prefers "A or X" over "A" (under excl lexicon).
    If the speaker only said "A", the listener would infer w₁
    (since A is only true at w₁ under excl). The disjunction
    conveys the uncertainty. -/
theorem s1_w12_AorX_vs_A :
    cfg.S1 .excl .w₁₂ .AorX > cfg.S1 .excl .w₁₂ .A := by
  rsa_predict

/-- Speaker at w₁₂ prefers "A or X" over "X" (under excl lexicon).
    "X" alone would lead to inference of w₂. -/
theorem s1_w12_AorX_vs_X :
    cfg.S1 .excl .w₁₂ .AorX > cfg.S1 .excl .w₁₂ .X := by
  rsa_predict

/-- Speaker at w₁ prefers "A" over "A or X" (under excl lexicon).
    When the speaker KNOWS w₁, saying just "A" is more informative
    than the disjunction. -/
theorem s1_w1_A_vs_AorX :
    cfg.S1 .excl .w₁ .A > cfg.S1 .excl .w₁ .AorX := by
  rsa_predict

-- ============================================================================
-- §9. Bridge to Hurford Data
-- ============================================================================

/-! The Hurford data in `Phenomena.ScalarImplicatures.Basic` records
that "some or all" is felicitous, rescued by exhaustification.
This is exactly the phenomenon @cite{potts-levy-2015} models: the
`excl` lexicon plays the role of exhaustification, making the
disjuncts non-overlapping and the sentence informative.

The connection: `someOrAll.rescueMethod = some "exh(some) = some but
not all"` corresponds to our `excl_is_base_minus_A` theorem, which
shows excl(X) = base(X) ∧ ¬A — the same operation as exh. -/

open Phenomena.ScalarImplicatures in
/-- The Hurford datum "some or all" is felicitous. Our model
    explains WHY: the excl lexicon makes the disjunction informative
    (proved by `excl_disjoint` and the L1 predictions above). -/
theorem matches_someOrAll_felicitous :
    someOrAll.felicitous = true := rfl

open Phenomena.ScalarImplicatures in
/-- The rescue method is exhaustification — matching our `excl` lexicon. -/
theorem matches_someOrAll_rescue :
    someOrAll.rescueMethod = some "exh(some) = some but not all" := rfl

-- ============================================================================
-- §10. Expertise Model (S2-level)
-- ============================================================================

/-! The paper's key contribution: the **expertise parameter β**.

@cite{potts-levy-2015}'s distinctive insight beyond generic LU-RSA is that
speakers of Hurford-violating disjunctions signal their **expertise** about
the meaning of the broader term. This is modeled as an S2-level speaker who
cares not only about informativity (L1 inferring the correct world) but
also about **lexicon signaling** (L1 inferring the speaker's lexicon).

The paper's expertise speaker utility (eq 15):

    U_Sk(m, w, L) = α · ln Lk₋₁(w|m,L) + β · ln Lk₋₁(L|m) − C(m)

- **Informativity** (α term): world-inference
- **Expertise** (β term): lexicon-inference
- **Cost** (C(m) term): message complexity

When β = 0, this reduces to standard RSA (pure informativity).
When β > 0, the speaker has extra incentive to choose utterances that
cause L1 to infer the `excl` lexicon. "A or X" is the uniquely effective
signal because it is maximally informative only under `excl` (§5, §7).

We decompose the expertise model into two independently verifiable
components using `cfg.S2` (RSA endorsement: S2(u|w) ∝ L₁(w|u)) for
informativity and `cfg.L1_latent` for lexicon signaling.

### Two Components

1. **Informativity (S2 endorsement)**: `S2(AorX|w₁₂) > S2(A|w₁₂)`,
   i.e. L1 assigns higher posterior to w₁₂ given AorX than given A.
2. **Lexicon signaling (L1_latent, §7)**: L1_latent(excl|AorX) >
   L1_latent(base|AorX) > L1_latent(syn|AorX) — AorX causes L1 to
   infer the excl lexicon.

When β > 0, the speaker cares about BOTH, and the lexicon-signaling
term provides extra motivation beyond pure informativity to use the
disjunction. -/

/-- S2 endorsement at w₁₂: the pragmatic speaker prefers "A or X" over "A".

    S2(u|w) ∝ L₁(w|u): L1 assigns higher posterior to w₁₂ given AorX
    (the disjunction is informative about uncertainty) than given A
    (which is false at w₁₂ under all lexica, so L₁(w₁₂|A) ≈ 0).

    This is the informativity component of the expertise model. -/
theorem s2_w12_AorX_vs_A :
    cfg.S2 .w₁₂ .AorX > cfg.S2 .w₁₂ .A := by
  rsa_predict

/-- S2 endorsement at w₁: the pragmatic speaker prefers "A" over "A or X".

    When the speaker knows w₁, "A" is the most informative utterance.
    The expertise model does not override this — even with β > 0,
    an expert at w₁ prefers the direct utterance. -/
theorem s2_w1_A_vs_AorX :
    cfg.S2 .w₁ .A > cfg.S2 .w₁ .AorX := by
  rsa_predict

/-- "A or X" signals the excl lexicon more strongly than "A" does.

    Under "A", all three lexica agree on truth conditions (A is true at
    w₁ only), so L1_latent is approximately uniform. Under "A or X",
    the excl lexicon dominates because it makes the disjunction maximally
    informative (§5). This asymmetry is the mechanism by which β > 0
    amplifies the speaker's preference for the disjunction.

    Combined with `s2_w12_AorX_vs_A`, this shows that an expert speaker
    at w₁₂ has TWO reasons to use "A or X": informativity (S2) and
    lexicon signaling (this theorem). -/
theorem AorX_signals_excl_vs_A :
    cfg.L1_latent .AorX .excl > cfg.L1_latent .A .excl := by
  rsa_predict

-- ============================================================================
-- §11. Full Expertise Model (Stacked RSA, eq 15)
-- ============================================================================

/-! The paper's distinctive contribution is the **expertise parameter β**
in the S₂ speaker utility (eq 15):

  `S₂(m|w,L) ∝ l₁(w|m,L)^α · L₁(L|m)^β · exp(-C(m))`

The expertise speaker simultaneously signals world knowledge (informativity
via l₁) and lexicon knowledge (expertise via L₁). We implement this as a
**stacked RSAConfig**: the base config's per-lexicon listener l₁ becomes
the upper level's L0 meaning, with the expertise bonus `L₁(L|m)` and
disjunction cost `exp(-C(m))` entering via `stack`'s `bonus` and
`costFactor` parameters.

Since `exp(-1) ∉ ℚ`, the cost penalty is approximated as `37/100 ≈ 0.37`
(close to `exp(-1) ≈ 0.368`). Qualitative predictions are robust to the
exact value (paper Section 5.4). -/

/-- Disjunction cost penalty: `exp(-C(m))`. The paper uses `C(or) = 1`,
    giving `exp(-1) ≈ 0.368`. We use `37/100` as a rational approximation. -/
noncomputable def disjCost : Utterance → ℝ
  | .AorX => 37/100
  | _ => 1

theorem disjCost_nonneg (u : Utterance) : 0 ≤ disjCost u := by
  cases u <;> simp [disjCost] <;> norm_num

open RSA in
/-- Expertise model: `cfg.stack` with α₂ = 2, β = 1.

`S₂(m|w,L) ∝ l₁(w|m,L)^2 · L₁(L|m) · exp(-C(m))`.

The stacked L1 = L₂ (world posterior), stacked L1_latent = L₂_latent
(lexicon posterior). -/
noncomputable def expertiseCfg : RSAConfig Utterance World :=
  cfg.stack 2 two_pos
    (bonus := fun l u => cfg.L1_latent u l)
    (bonus_nonneg := fun l u => cfg.L1_latent_nonneg u l)
    (costFactor := disjCost)
    (costFactor_nonneg := disjCost_nonneg)

-- ---- L₂ World Predictions ----

/-- L₂ hearing "A or X": uncertainty state w₁₂ dominates w₁. -/
theorem L2_AorX_w12_vs_w1 :
    expertiseCfg.L1 .AorX .w₁₂ > expertiseCfg.L1 .AorX .w₁ := by
  rsa_predict

/-- L₂ hearing "A or X": uncertainty state w₁₂ dominates w₂. -/
theorem L2_AorX_w12_vs_w2 :
    expertiseCfg.L1 .AorX .w₁₂ > expertiseCfg.L1 .AorX .w₂ := by
  rsa_predict

/-- L₂ hearing "A or X": w₁ > w₂. -/
theorem L2_AorX_w1_vs_w2 :
    expertiseCfg.L1 .AorX .w₁ > expertiseCfg.L1 .AorX .w₂ := by
  rsa_predict

-- ---- L₂ Lexicon Predictions ----

/-- L₂ lexicon inference: excl dominates base for "A or X". -/
theorem L2_AorX_excl_vs_base :
    expertiseCfg.L1_latent .AorX .excl > expertiseCfg.L1_latent .AorX .base := by
  rsa_predict

/-- L₂ lexicon inference: excl dominates syn for "A or X". -/
theorem L2_AorX_excl_vs_syn :
    expertiseCfg.L1_latent .AorX .excl > expertiseCfg.L1_latent .AorX .syn := by
  rsa_predict

/-- L₂ lexicon inference: base > syn. Full ordering: excl > base > syn. -/
theorem L2_AorX_base_vs_syn :
    expertiseCfg.L1_latent .AorX .base > expertiseCfg.L1_latent .AorX .syn := by
  rsa_predict

-- ---- S₂ Expertise Speaker Predictions ----

/-- S₂ at w₁₂ prefers "A or X" over "A" (marginalized over lexica). -/
theorem S2_expertise_w12_AorX_vs_A :
    expertiseCfg.S2 .w₁₂ .AorX > expertiseCfg.S2 .w₁₂ .A := by
  rsa_predict

/-- S₂ at w₁ prefers "A" over "A or X" (marginalized over lexica). -/
theorem S2_expertise_w1_A_vs_AorX :
    expertiseCfg.S2 .w₁ .A > expertiseCfg.S2 .w₁ .AorX := by
  rsa_predict

-- ============================================================================
-- §12. Findings
-- ============================================================================

/-- The qualitative findings from the @cite{potts-levy-2015} LU + expertise model. -/
inductive Finding where
  /-- L1 -/
  | uncertainty_w12_vs_w1
  | uncertainty_w12_vs_w2
  | uncertainty_w1_vs_w2
  | lexicon_excl_vs_base
  | lexicon_excl_vs_syn
  | lexicon_base_vs_syn
  /-- S1 -/
  | s1_w12_prefers_AorX
  | s1_w1_prefers_A
  /-- S2 endorsement -/
  | s2_w12_AorX
  | s2_w1_A
  | AorX_signals_excl
  /-- L2 expertise (stacked) -/
  | L2_w12_vs_w1
  | L2_w12_vs_w2
  | L2_w1_vs_w2
  | L2_excl_vs_base
  | L2_excl_vs_syn
  | L2_base_vs_syn
  | S2_expertise_w12_AorX
  | S2_expertise_w1_A
  deriving Repr

/-- Verification: each finding is backed by a proved theorem. -/
def Finding.verified : Finding → Prop
  | .uncertainty_w12_vs_w1 => cfg.L1 .AorX .w₁₂ > cfg.L1 .AorX .w₁
  | .uncertainty_w12_vs_w2 => cfg.L1 .AorX .w₁₂ > cfg.L1 .AorX .w₂
  | .uncertainty_w1_vs_w2 => cfg.L1 .AorX .w₁ > cfg.L1 .AorX .w₂
  | .lexicon_excl_vs_base => cfg.L1_latent .AorX Lex.excl > cfg.L1_latent .AorX Lex.base
  | .lexicon_excl_vs_syn => cfg.L1_latent .AorX Lex.excl > cfg.L1_latent .AorX Lex.syn
  | .lexicon_base_vs_syn => cfg.L1_latent .AorX Lex.base > cfg.L1_latent .AorX Lex.syn
  | .s1_w12_prefers_AorX => cfg.S1 .excl .w₁₂ .AorX > cfg.S1 .excl .w₁₂ .A
  | .s1_w1_prefers_A => cfg.S1 .excl .w₁ .A > cfg.S1 .excl .w₁ .AorX
  | .s2_w12_AorX => cfg.S2 .w₁₂ .AorX > cfg.S2 .w₁₂ .A
  | .s2_w1_A => cfg.S2 .w₁ .A > cfg.S2 .w₁ .AorX
  | .AorX_signals_excl => cfg.L1_latent .AorX Lex.excl > cfg.L1_latent .A Lex.excl
  | .L2_w12_vs_w1 => expertiseCfg.L1 .AorX .w₁₂ > expertiseCfg.L1 .AorX .w₁
  | .L2_w12_vs_w2 => expertiseCfg.L1 .AorX .w₁₂ > expertiseCfg.L1 .AorX .w₂
  | .L2_w1_vs_w2 => expertiseCfg.L1 .AorX .w₁ > expertiseCfg.L1 .AorX .w₂
  | .L2_excl_vs_base => expertiseCfg.L1_latent .AorX .excl > expertiseCfg.L1_latent .AorX .base
  | .L2_excl_vs_syn => expertiseCfg.L1_latent .AorX .excl > expertiseCfg.L1_latent .AorX .syn
  | .L2_base_vs_syn => expertiseCfg.L1_latent .AorX .base > expertiseCfg.L1_latent .AorX .syn
  | .S2_expertise_w12_AorX => expertiseCfg.S2 .w₁₂ .AorX > expertiseCfg.S2 .w₁₂ .A
  | .S2_expertise_w1_A => expertiseCfg.S2 .w₁ .A > expertiseCfg.S2 .w₁ .AorX

theorem all_findings_verified (f : Finding) : f.verified := by
  cases f <;> simp only [Finding.verified]
  · exact uncertainty_w12_vs_w1
  · exact uncertainty_w12_vs_w2
  · exact uncertainty_w1_vs_w2
  · exact lexicon_excl_vs_base
  · exact lexicon_excl_vs_syn
  · exact lexicon_base_vs_syn
  · exact s1_w12_AorX_vs_A
  · exact s1_w1_A_vs_AorX
  · exact s2_w12_AorX_vs_A
  · exact s2_w1_A_vs_AorX
  · exact AorX_signals_excl_vs_A
  · exact L2_AorX_w12_vs_w1
  · exact L2_AorX_w12_vs_w2
  · exact L2_AorX_w1_vs_w2
  · exact L2_AorX_excl_vs_base
  · exact L2_AorX_excl_vs_syn
  · exact L2_AorX_base_vs_syn
  · exact S2_expertise_w12_AorX_vs_A
  · exact S2_expertise_w1_A_vs_AorX

end PottsLevy2015
