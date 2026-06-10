import Linglib.Pragmatics.RSA.Canonical

/-!
# [alsop-2024] — The pragmatics of free choice *any*

[alsop-2024] (Glossa 9(1)) argues that *You may read any book* does not
*entail* that each book may be read on its own ([menendez-benito-2010],
[dayal-2013]'s Viability Constraint) — it carries a particularly robust
**exclusiveness implicature**, derived pragmatically from [szabolcsi-2019]'s
weaker semantics. The derivation combines [champollion-alsop-grosu-2019]'s
ambiguity-driven free choice with [franke-bergen-2020]'s **Global
Intentions** architecture: each utterance comes with its own set of licit
exhaustified parses, the speaker chooses an utterance–parse pair jointly,
and the listener infers state and intended parse together.

The model (the paper's §5, eqs. (36)–(41)): seven permission states over a
two-class domain (their Table 1); four utterances with 12 utterance–parse
pairs in total (3 for *may S*, 3 for *may P*, 2 for *may any*, 4 for *may
every*; truth conditions in their Table 2); `L0(s|u,p) ∝ P(s)·⟦u⟧ᵖ(s)`;
`S1(u,p|s) ∝ exp(α·log L0)` over all 12 pairs; `L1(s,p|u) ∝ P(s)·S1(u,p|s)`
with parse-marginal `L1(s|u)`. Speaker optimality `α = 100`, equal costs.

Instantiated on the canonical pipeline: `L0` is `RSA.Canonical.L0OfBool`
over the Table-2 matrix, the joint speaker is `RSA.Canonical.S1` with
`powUtility`, the parse-marginal speaker is its `PMF.map` along
`Parse.utt`, and the pragmatic listener is `RSA.Canonical.L1`.

## Main statements

* `exclusiveness_derived` — at a uniform prior, hearing *may any* puts more
  posterior mass on the exclusiveness states {Only 1, Any #} than on the
  non-exclusive states {Only 2, S or 2, P or 2} (their Table 3).
* `mayAny_rules_out_onlyS` / `mayEvery_rules_out_onlyS` — *may any* and
  *may every* are false at single-class states under every parse.
* `s1_prefers_strong_parse` — the mechanism: at an exclusiveness state the
  speaker prefers the strong parse (their (34b)) of *may any* to the weak
  parse ((34a)), for **every** exponent `α ≥ 1` — the weak parse is true in
  five states, the strong in two.
* `literal_s_communicates_onlyS` — hearing *may S*, the listener prefers
  the Only-S state to the S-or-2 state (their Table 3: 0.67 vs 0.33).
* `exclusiveness_strict_asymmetry` — a refinement the paper's Table 3
  rounds away: `L1(Only 1 | may any)` strictly exceeds
  `L1(Any # | may any)` at every exponent, because *may every*'s parse
  (35b) is true at Any # but not Only 1, inflating the speaker's partition
  at Any #. The paper reports 0.50/0.50 at α = 100 (the difference is
  ≈ 2·10⁻³¹).

## Context manipulation (verified prose)

The paper's Tables 5–9 manipulate the state prior, which enters `L0`
(eq. (36)); independently recomputed, every reported cell reproduces
exactly. The *not every* implicature is absent at a uniform prior (the
50/50 split above), derived under a 70%-Only-1 prior (`L1(Only 1) ≈ 1`,
robust for all scanned `α ≥ 1`), and the Any-#-biased prior shifts `L1` to
0.93 while `S1` stays 50/50 — a prior-driven shift, not an implicature
(the paper's eq. (1)). Robustness of exclusiveness to a 70%-S-or-2 prior
(Table 5: 0.49/0.49/0.02) genuinely needs `α ≥ 45`, so the paper's
`α = 100` does real work there. These prior-in-`L0` results are recorded
as prose rather than theorems per the parameter-dependence policy.

## Implementation notes

Theorems are at the paper's `α = 100` (the parse preference at every
`α ≥ 1`) with a uniform prior, by `ℕ`-certificate dominance bounds — no
numeric reflection. The previous version of this file modelled two *global
interpretation functions* with an interpretation prior at `α = 2` — the
[champollion-alsop-grosu-2019] architecture that the paper explicitly
replaces with [franke-bergen-2020]'s — and included a negation finding
with no counterpart in the paper's model (its utterance set has no
negation; NPI *any* is set aside in the paper's §2.1).
-/

set_option autoImplicit false

namespace Alsop2024

open scoped ENNReal
open RSA.Canonical

/-! ### States, utterances, parses (the paper's Tables 1–2) -/

/-- The seven permission states (their Table 1), each a set of accessible
worlds over {take nothing, take S, take P, take both}; every state makes
taking nothing accessible. -/
inductive FCIState where
  | onlyS   -- {w₀, w_S}
  | onlyP   -- {w₀, w_P}
  | only1   -- {w₀, w_S, w_P}: each on its own, not both
  | anyNum  -- {w₀, w_S, w_P, w_SP}
  | only2   -- {w₀, w_SP}: only both together
  | sOr2    -- {w₀, w_S, w_SP}
  | pOr2    -- {w₀, w_P, w_SP}
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The four utterances (their (31)). -/
inductive Utterance where
  | mayS | mayP | mayAny | mayEvery
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The 12 utterance–parse pairs (their (32)–(35)): per-utterance licit
exhaustified parses, `a` the weakest. *May any* has exactly two — the weak
parse (34a, Szabolcsi: every class may be taken, possibly only together)
and the strong parse (34b, Dayal: every class may be taken on its own). -/
inductive Parse where
  | sA | sB | sC          -- (32a–c)
  | pA | pB | pC          -- (33a–c)
  | anyA | anyB           -- (34a–b)
  | evA | evB | evC | evD -- (35a–d)
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The utterance a parse belongs to. -/
def Parse.utt : Parse → Utterance
  | .sA | .sB | .sC => .mayS
  | .pA | .pB | .pC => .mayP
  | .anyA | .anyB => .mayAny
  | .evA | .evB | .evC | .evD => .mayEvery

/-- Truth conditions for each utterance–parse pair (their Table 2). -/
def meaning : Parse → FCIState → Bool
  | .sA, s => (s matches .onlyS | .only1 | .anyNum | .only2 | .sOr2 | .pOr2)
  | .sB, s => (s matches .onlyS | .only1 | .anyNum | .sOr2)
  | .sC, s => (s matches .onlyS)
  | .pA, s => (s matches .onlyP | .only1 | .anyNum | .only2 | .sOr2 | .pOr2)
  | .pB, s => (s matches .onlyP | .only1 | .anyNum | .pOr2)
  | .pC, s => (s matches .onlyP)
  | .anyA, s => (s matches .only1 | .anyNum | .only2 | .sOr2 | .pOr2)
  | .anyB, s => (s matches .only1 | .anyNum)
  | .evA, s => (s matches .only1 | .anyNum | .only2 | .sOr2 | .pOr2)
  | .evB, s => (s matches .anyNum | .only2 | .sOr2 | .pOr2)
  | .evC, s => (s matches .only1 | .anyNum)
  | .evD, s => (s matches .only2)

private theorem ext_nonempty : ∀ (_ : Unit) (p : Parse),
    (RSA.extensionOf (fun q => meaning q) p).Nonempty := by
  intro _ p
  cases p <;> decide

/-! ### The canonical GI pipeline -/

/-- Per-parse literal listener (eq. (36) at a uniform state prior):
uniform on the parse's extension. -/
noncomputable abbrev l0 : Unit → Parse → PMF FCIState :=
  L0OfBool (fun _ p => meaning p) ext_nonempty

instance (α : ℕ) : ViableSpeaker (powUtility α l0) :=
  viableSpeaker_powUtility_of_witness α l0 fun s => by
    obtain ⟨w, ⟨⟩⟩ := s
    cases w
    · exact ⟨.sA, L0OfBool_ne_zero _ _ (by decide)⟩
    · exact ⟨.pA, L0OfBool_ne_zero _ _ (by decide)⟩
    · exact ⟨.anyB, L0OfBool_ne_zero _ _ (by decide)⟩
    · exact ⟨.anyB, L0OfBool_ne_zero _ _ (by decide)⟩
    · exact ⟨.evD, L0OfBool_ne_zero _ _ (by decide)⟩
    · exact ⟨.evB, L0OfBool_ne_zero _ _ (by decide)⟩
    · exact ⟨.evB, L0OfBool_ne_zero _ _ (by decide)⟩

/-- The joint speaker over utterance–parse pairs (eqs. (37)–(38)):
`S1(u,p|s) ∝ L0(s|u,p)^α`, equal costs. -/
noncomputable def speaker (α : ℕ) : FCIState × Unit → PMF Parse :=
  S1 (powUtility α l0)

/-- The parse-marginal speaker (eq. (39)): `S1(u|s) = Σ_p S1(u,p|s)`. -/
noncomputable def speakerU (α : ℕ) (s : FCIState × Unit) : PMF Utterance :=
  (speaker α s).map Parse.utt

/-- Uniform joint state prior. -/
noncomputable abbrev prior : PMF (FCIState × Unit) := PMF.uniformOfFintype _

private theorem speakerU_apply (α : ℕ) (s : FCIState × Unit) (u : Utterance) :
    speakerU α s u
      = ∑ p ∈ Finset.univ.filter (fun p => Parse.utt p = u), speaker α s p := by
  rw [speakerU, PMF.map_apply, tsum_fintype, Finset.sum_filter]
  congr 1
  funext p
  by_cases h : Parse.utt p = u
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

private theorem speakerU_mayAny (α : ℕ) (s : FCIState × Unit) :
    speakerU α s .mayAny = speaker α s .anyA + speaker α s .anyB := by
  rw [speakerU_apply,
      show Finset.univ.filter (fun p => Parse.utt p = .mayAny)
        = {Parse.anyA, Parse.anyB} from by decide,
      Finset.sum_insert (by decide), Finset.sum_singleton]

private theorem speakerU_mayS (α : ℕ) (s : FCIState × Unit) :
    speakerU α s .mayS
      = speaker α s .sA + (speaker α s .sB + speaker α s .sC) := by
  rw [speakerU_apply,
      show Finset.univ.filter (fun p => Parse.utt p = .mayS)
        = {Parse.sA, Parse.sB, Parse.sC} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]

theorem marginal_ne_zero (α : ℕ) (u : Utterance) :
    PMF.marginal (speakerU α) prior u ≠ 0 := by
  have key : ∀ (w : FCIState) (p : Parse), Parse.utt p = u → meaning p w = true →
      PMF.marginal (speakerU α) prior u ≠ 0 := by
    intro w p hpu hpw
    refine PMF.marginal_ne_zero _ _ u (a := (w, ())) ?_ ?_
    · exact (prior.mem_support_iff _).mp (PMF.mem_support_uniformOfFintype _)
    · rw [speakerU_apply, ← hpu]
      intro hz
      exact S1_ne_zero (powUtility α l0)
        (PMF.coe_mul_log_ne_bot (by positivity) (L0OfBool_ne_zero _ _ hpw))
        (Finset.sum_eq_zero_iff.mp hz p
          (Finset.mem_filter.mpr ⟨Finset.mem_univ p, rfl⟩))
  cases u
  · exact key .onlyS .sA rfl (by decide)
  · exact key .onlyP .pA rfl (by decide)
  · exact key .only1 .anyB rfl (by decide)
  · exact key .only2 .evD rfl (by decide)

/-- The pragmatic listener over states (eqs. (40)–(41), parse-marginal):
the canonical posterior of the parse-marginal speaker. -/
noncomputable def listener (α : ℕ) (u : Utterance) : PMF (FCIState × Unit) :=
  L1 (speakerU α) prior u (marginal_ne_zero α u)

/-! ### Extension sizes (their Table 2 row sums) -/

private theorem card_sA :
    (RSA.extensionOf (fun p => meaning p) Parse.sA).card = 6 := by decide
private theorem card_sB :
    (RSA.extensionOf (fun p => meaning p) Parse.sB).card = 4 := by decide
private theorem card_anyA :
    (RSA.extensionOf (fun p => meaning p) Parse.anyA).card = 5 := by decide
private theorem card_anyB :
    (RSA.extensionOf (fun p => meaning p) Parse.anyB).card = 2 := by decide
private theorem card_evB :
    (RSA.extensionOf (fun p => meaning p) Parse.evB).card = 4 := by decide
private theorem card_evD :
    (RSA.extensionOf (fun p => meaning p) Parse.evD).card = 1 := by decide

/-! ### B1 zeros: *may any* and *may every* exclude single-class states -/

/-- Both parses of *may any* are false at Only-S, so the speaker never
produces it there. -/
theorem speakerU_onlyS_mayAny (α : ℕ) (hα : α ≠ 0) :
    speakerU α (.onlyS, ()) .mayAny = 0 := by
  rw [speakerU_mayAny,
      show speaker α (.onlyS, ()) .anyA = 0 from
        S1_powUtility_eq_zero α l0 hα (L0OfBool_eq_zero _ _ (by decide)),
      show speaker α (.onlyS, ()) .anyB = 0 from
        S1_powUtility_eq_zero α l0 hα (L0OfBool_eq_zero _ _ (by decide)),
      add_zero]

/-- Hearing *may any*, the listener assigns zero posterior to Only-S. -/
theorem mayAny_rules_out_onlyS (α : ℕ) (hα : α ≠ 0) :
    listener α .mayAny (.onlyS, ()) = 0 := by
  rw [listener, L1, PMF.posterior_apply, speakerU_onlyS_mayAny α hα, mul_zero,
      zero_mul]

/-- All four parses of *may every* are false at Only-S. -/
theorem speakerU_onlyS_mayEvery (α : ℕ) (hα : α ≠ 0) :
    speakerU α (.onlyS, ()) .mayEvery = 0 := by
  rw [speakerU_apply,
      show Finset.univ.filter (fun p => Parse.utt p = .mayEvery)
        = {Parse.evA, Parse.evB, Parse.evC, Parse.evD} from by decide]
  refine Finset.sum_eq_zero fun p hp => ?_
  fin_cases hp <;>
    exact S1_powUtility_eq_zero α l0 hα (L0OfBool_eq_zero _ _ (by decide))

/-- Hearing *may every*, the listener assigns zero posterior to Only-S. -/
theorem mayEvery_rules_out_onlyS (α : ℕ) (hα : α ≠ 0) :
    listener α .mayEvery (.onlyS, ()) = 0 := by
  rw [listener, L1, PMF.posterior_apply, speakerU_onlyS_mayEvery α hα, mul_zero,
      zero_mul]

/-! ### The mechanism: the strong parse wins -/

/-- At the Only-1 state the speaker prefers the strong parse (34b) of *may
any* to the weak parse (34a), for **every** exponent `α ≥ 1`: the weak
parse is true in five states (`L0 = 1/5`), the strong in two (`L0 = 1/2`),
and within one state the softmax partition cancels. At `α = 100` the ratio
is `(5/2)^100`, the paper's "almost 100% of the time". -/
theorem s1_prefers_strong_parse {α : ℕ} (hα : α ≠ 0) :
    speaker α (.only1, ()) .anyA < speaker α (.only1, ()) .anyB := by
  show S1 (powUtility α l0) _ _ < S1 (powUtility α l0) _ _
  rw [S1_powUtility_eq_normalize, PMF.normalize_apply,
      PMF.normalize_apply,
      ENNReal.mul_lt_mul_iff_left
        (ENNReal.inv_ne_zero.mpr (tsum_powWeight_ne_top α l0 _))
        (ENNReal.inv_ne_top.mpr (tsum_powWeight_ne_zero α l0 _)),
      powWeight_L0OfBool_of_mem _ _ 5 (by decide) card_anyA,
      powWeight_L0OfBool_of_mem _ _ 2 (by decide) card_anyB]
  exact ENNReal.pow_lt_pow_left hα
    (ENNReal.inv_lt_inv' (show (2 : ℝ≥0∞) < 5 by norm_num))

/-! ### Exclusiveness (their Table 3, uniform prior, α = 100)

Per-state speaker bounds: at the exclusiveness states the strong parse
alone gives *may any* more than a third of the speaker's mass; at the
non-exclusive states only the weak parse survives and is dominated. -/

private theorem inv_pow_le_inv_pow {a b : ℕ} (h : a ≤ b) (n : ℕ) :
    ((b : ℝ≥0∞)⁻¹) ^ n ≤ ((a : ℝ≥0∞)⁻¹) ^ n :=
  pow_le_pow_left' (ENNReal.inv_le_inv' (by exact_mod_cast h)) n

private theorem third_lt_speakerU_only1 :
    ((2 : ℝ≥0∞) + 1)⁻¹ < speakerU 100 (.only1, ()) .mayAny := by
  have h := inv_succ_lt_S1_powUtility (n := 2) 100 l0
    (s := (FCIState.only1, ())) (a := Parse.anyB) ?_
  · refine h.trans_le ?_
    rw [speakerU_mayAny]
    exact le_add_self
  rw [show Finset.univ.erase Parse.anyB
        = {Parse.sA, Parse.sB, Parse.sC, Parse.pA, Parse.pB, Parse.pC,
           Parse.anyA, Parse.evA, Parse.evB, Parse.evC, Parse.evD}
      from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton,
      powWeight_L0OfBool_of_mem _ _ 6 (by decide) card_sA,
      powWeight_L0OfBool_of_mem _ _ 4 (by decide) card_sB,
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_mem _ _ 6 (by decide) (by decide),
      powWeight_L0OfBool_of_mem _ _ 4 (by decide) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_mem _ _ 5 (by decide) card_anyA,
      powWeight_L0OfBool_of_mem _ _ 5 (by decide) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_mem _ _ 2 (by decide) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_mem _ _ 2 (by decide) card_anyB]
  -- 2·6⁻¹⁰⁰ + 2·4⁻¹⁰⁰ + 2·5⁻¹⁰⁰ + 2⁻¹⁰⁰ < 2·2⁻¹⁰⁰
  calc _ = (2 : ℝ≥0∞) * ((6 : ℝ≥0∞)⁻¹) ^ 100 + 2 * ((4 : ℝ≥0∞)⁻¹) ^ 100
        + 2 * ((5 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 := by ring
    _ ≤ 2 * ((4 : ℝ≥0∞)⁻¹) ^ 100 + 2 * ((4 : ℝ≥0∞)⁻¹) ^ 100
        + 2 * ((4 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 := by
        refine add_le_add (add_le_add (add_le_add ?_ le_rfl) ?_) le_rfl <;>
          exact mul_le_mul_left' (inv_pow_le_inv_pow (by norm_num) 100) 2
    _ = (6 : ℝ≥0∞) * ((4 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 := by ring
    _ < ((2 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 :=
        ENNReal.add_lt_add_right (ENNReal.pow_ne_top (by norm_num))
          (ENNReal.natCast_mul_inv_pow_lt (by norm_num) (by norm_num)
            (by norm_num))
    _ = 2 * ((2 : ℝ≥0∞)⁻¹) ^ 100 := (two_mul _).symm

private theorem third_lt_speakerU_anyNum :
    ((2 : ℝ≥0∞) + 1)⁻¹ < speakerU 100 (.anyNum, ()) .mayAny := by
  have h := inv_succ_lt_S1_powUtility (n := 2) 100 l0
    (s := (FCIState.anyNum, ())) (a := Parse.anyB) ?_
  · refine h.trans_le ?_
    rw [speakerU_mayAny]
    exact le_add_self
  rw [show Finset.univ.erase Parse.anyB
        = {Parse.sA, Parse.sB, Parse.sC, Parse.pA, Parse.pB, Parse.pC,
           Parse.anyA, Parse.evA, Parse.evB, Parse.evC, Parse.evD}
      from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton,
      powWeight_L0OfBool_of_mem _ _ 6 (by decide) card_sA,
      powWeight_L0OfBool_of_mem _ _ 4 (by decide) card_sB,
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_mem _ _ 6 (by decide) (by decide),
      powWeight_L0OfBool_of_mem _ _ 4 (by decide) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_mem _ _ 5 (by decide) card_anyA,
      powWeight_L0OfBool_of_mem _ _ 5 (by decide) (by decide),
      powWeight_L0OfBool_of_mem _ _ 4 (by decide) card_evB,
      powWeight_L0OfBool_of_mem _ _ 2 (by decide) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_mem _ _ 2 (by decide) card_anyB]
  -- 2·6⁻¹⁰⁰ + 3·4⁻¹⁰⁰ + 2·5⁻¹⁰⁰ + 2⁻¹⁰⁰ < 2·2⁻¹⁰⁰ (extra 4⁻¹⁰⁰: parse 35b)
  calc _ = (2 : ℝ≥0∞) * ((6 : ℝ≥0∞)⁻¹) ^ 100 + 3 * ((4 : ℝ≥0∞)⁻¹) ^ 100
        + 2 * ((5 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 := by ring
    _ ≤ 2 * ((4 : ℝ≥0∞)⁻¹) ^ 100 + 3 * ((4 : ℝ≥0∞)⁻¹) ^ 100
        + 2 * ((4 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 := by
        refine add_le_add (add_le_add (add_le_add ?_ le_rfl) ?_) le_rfl
        · exact mul_le_mul_left' (inv_pow_le_inv_pow (by norm_num) 100) 2
        · exact mul_le_mul_left' (inv_pow_le_inv_pow (by norm_num) 100) 2
    _ = (7 : ℝ≥0∞) * ((4 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 := by ring
    _ < ((2 : ℝ≥0∞)⁻¹) ^ 100 + ((2 : ℝ≥0∞)⁻¹) ^ 100 :=
        ENNReal.add_lt_add_right (ENNReal.pow_ne_top (by norm_num))
          (ENNReal.natCast_mul_inv_pow_lt (by norm_num) (by norm_num)
            (by norm_num))
    _ = 2 * ((2 : ℝ≥0∞)⁻¹) ^ 100 := (two_mul _).symm

private theorem speakerU_only2_lt_ninth :
    speakerU 100 (.only2, ()) .mayAny < ((8 : ℝ≥0∞) + 1)⁻¹ := by
  rw [speakerU_mayAny,
      show speaker 100 (.only2, ()) .anyB = 0 from
        S1_powUtility_eq_zero 100 l0 (by norm_num)
          (L0OfBool_eq_zero _ _ (by decide)),
      add_zero]
  exact S1_L0OfBool_lt_inv_succ_of_dominator _ _ (by decide) (by decide)
    (by decide) card_anyA card_evD (by norm_num) (by norm_num)

private theorem speakerU_sOr2_lt_ninth :
    speakerU 100 (.sOr2, ()) .mayAny < ((8 : ℝ≥0∞) + 1)⁻¹ := by
  rw [speakerU_mayAny,
      show speaker 100 (.sOr2, ()) .anyB = 0 from
        S1_powUtility_eq_zero 100 l0 (by norm_num)
          (L0OfBool_eq_zero _ _ (by decide)),
      add_zero]
  exact S1_L0OfBool_lt_inv_succ_of_dominator (u' := Parse.evB) _ _ (by decide)
    (by decide) (by decide) card_anyA card_evB (by norm_num) (by norm_num)

private theorem speakerU_pOr2_lt_ninth :
    speakerU 100 (.pOr2, ()) .mayAny < ((8 : ℝ≥0∞) + 1)⁻¹ := by
  rw [speakerU_mayAny,
      show speaker 100 (.pOr2, ()) .anyB = 0 from
        S1_powUtility_eq_zero 100 l0 (by norm_num)
          (L0OfBool_eq_zero _ _ (by decide)),
      add_zero]
  exact S1_L0OfBool_lt_inv_succ_of_dominator (u' := Parse.evB) _ _ (by decide)
    (by decide) (by decide) card_anyA card_evB (by norm_num) (by norm_num)

/-- **The exclusiveness implicature** (their Table 3): hearing *may any*
at a uniform prior, the listener puts more posterior mass on the
exclusiveness states {Only 1, Any #} (where each class may be taken on its
own; the paper's 0.50 + 0.50) than on the non-exclusive states
{Only 2, S or 2, P or 2} (each ≈ 0). -/
theorem exclusiveness_derived :
    (listener 100 .mayAny).toOuterMeasure
        ↑({(.only2, ()), (.sOr2, ()), (.pOr2, ())} : Finset (FCIState × Unit))
      < (listener 100 .mayAny).toOuterMeasure
        ↑({(.only1, ()), (.anyNum, ())} : Finset (FCIState × Unit)) := by
  rw [listener, L1_uniform_event_lt_iff,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton, Finset.sum_insert (by decide),
      Finset.sum_singleton]
  have hbad : speakerU 100 (.only2, ()) .mayAny
      + (speakerU 100 (.sOr2, ()) .mayAny + speakerU 100 (.pOr2, ()) .mayAny)
      < ((8 : ℝ≥0∞) + 1)⁻¹ + (((8 : ℝ≥0∞) + 1)⁻¹ + ((8 : ℝ≥0∞) + 1)⁻¹) :=
    ENNReal.add_lt_add speakerU_only2_lt_ninth
      (ENNReal.add_lt_add speakerU_sOr2_lt_ninth speakerU_pOr2_lt_ninth)
  have hgood : ((2 : ℝ≥0∞) + 1)⁻¹ + ((2 : ℝ≥0∞) + 1)⁻¹
      < speakerU 100 (.only1, ()) .mayAny + speakerU 100 (.anyNum, ()) .mayAny :=
    ENNReal.add_lt_add third_lt_speakerU_only1 third_lt_speakerU_anyNum
  have h93 : ((8 : ℝ≥0∞) + 1)⁻¹ + (((8 : ℝ≥0∞) + 1)⁻¹ + ((8 : ℝ≥0∞) + 1)⁻¹)
      < ((2 : ℝ≥0∞) + 1)⁻¹ + ((2 : ℝ≥0∞) + 1)⁻¹ := by
    rw [show ((8 : ℝ≥0∞) + 1) = 9 from by norm_num,
        show ((2 : ℝ≥0∞) + 1) = 3 from by norm_num,
        show (9 : ℝ≥0∞)⁻¹ + ((9 : ℝ≥0∞)⁻¹ + (9 : ℝ≥0∞)⁻¹)
          = 3 * 9⁻¹ from by ring,
        show (9 : ℝ≥0∞) = 3 * 3 from by norm_num,
        ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
        ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
        one_mul]
    exact ENNReal.lt_add_right (ENNReal.inv_ne_top.mpr (by norm_num))
      (ENNReal.inv_ne_zero.mpr (by norm_num))
  exact hbad.trans (h93.trans hgood)

/-! ### *May S* communicates Only-S (their Table 3: 0.67 vs 0.33) -/

private theorem half_lt_speakerU_onlyS_mayS :
    (((1 : ℕ) : ℝ≥0∞) + 1)⁻¹ < speakerU 100 (.onlyS, ()) .mayS := by
  have h := inv_succ_lt_S1_powUtility (n := 1) 100 l0
    (s := (FCIState.onlyS, ())) (a := Parse.sC) ?_
  · refine h.trans_le ?_
    rw [speakerU_mayS]
    calc speaker 100 (.onlyS, ()) .sC
        ≤ speaker 100 (.onlyS, ()) .sB + speaker 100 (.onlyS, ()) .sC :=
          le_add_self
      _ ≤ _ := le_add_self
  rw [show Finset.univ.erase Parse.sC
        = {Parse.sA, Parse.sB, Parse.pA, Parse.pB, Parse.pC,
           Parse.anyA, Parse.anyB, Parse.evA, Parse.evB, Parse.evC, Parse.evD}
      from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton,
      powWeight_L0OfBool_of_mem _ _ 6 (by decide) card_sA,
      powWeight_L0OfBool_of_mem _ _ 4 (by decide) card_sB,
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_mem _ _ 1 (by decide) (by decide)]
  -- 6⁻¹⁰⁰ + 4⁻¹⁰⁰ < 1 · 1⁻¹⁰⁰
  calc _ = ((6 : ℝ≥0∞)⁻¹) ^ 100 + ((4 : ℝ≥0∞)⁻¹) ^ 100 := by ring
    _ ≤ ((4 : ℝ≥0∞)⁻¹) ^ 100 + ((4 : ℝ≥0∞)⁻¹) ^ 100 :=
        add_le_add (inv_pow_le_inv_pow (by norm_num) 100) le_rfl
    _ = 2 * ((4 : ℝ≥0∞)⁻¹) ^ 100 := (two_mul _).symm
    _ < ↑(1 : ℕ) * (((1 : ℕ) : ℝ≥0∞))⁻¹ ^ 100 := by
        have h := ENNReal.natCast_mul_inv_pow_lt (n := 2) (a := 4) (b := 1)
          (e := 100) (by norm_num) (by norm_num) (by norm_num)
        simpa using h

private theorem sum_S1_eq_mul_inv (s : FCIState × Unit) (p q : Parse) :
    speaker 100 s p + speaker 100 s q
      = (powWeight 100 l0 s p + powWeight 100 l0 s q)
        * (∑' r, powWeight 100 l0 s r)⁻¹ := by
  show S1 (powUtility 100 l0) s p + S1 (powUtility 100 l0) s q = _
  rw [S1_powUtility_eq_normalize, PMF.normalize_apply, PMF.normalize_apply]
  exact (add_mul _ _ _).symm

private theorem Z_sOr2 :
    (∑' r, powWeight 100 l0 (.sOr2, ()) r)
      = 2 * (((6 : ℝ≥0∞)⁻¹) ^ 100 + ((5 : ℝ≥0∞)⁻¹) ^ 100
          + ((4 : ℝ≥0∞)⁻¹) ^ 100) := by
  rw [tsum_fintype,
      show (Finset.univ : Finset Parse)
        = {Parse.sA, Parse.sB, Parse.sC, Parse.pA, Parse.pB, Parse.pC,
           Parse.anyA, Parse.anyB, Parse.evA, Parse.evB, Parse.evC, Parse.evD}
      from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton,
      powWeight_L0OfBool_of_mem _ _ 6 (by decide) card_sA,
      powWeight_L0OfBool_of_mem _ _ 4 (by decide) card_sB,
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_mem _ _ 6 (by decide) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_mem _ _ 5 (by decide) card_anyA,
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_mem _ _ 5 (by decide) (by decide),
      powWeight_L0OfBool_of_mem _ _ 4 (by decide) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
      powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide)]
  push_cast
  ring

private theorem speakerU_sOr2_mayS_lt_half :
    speakerU 100 (.sOr2, ()) .mayS < (((1 : ℕ) : ℝ≥0∞) + 1)⁻¹ := by
  rw [speakerU_mayS,
      show speaker 100 (.sOr2, ()) .sC = 0 from
        S1_powUtility_eq_zero 100 l0 (by norm_num)
          (L0OfBool_eq_zero _ _ (by decide)),
      add_zero, sum_S1_eq_mul_inv,
      powWeight_L0OfBool_of_mem _ _ 6 (by decide) card_sA,
      powWeight_L0OfBool_of_mem _ _ 4 (by decide) card_sB,
      show (((1 : ℕ) : ℝ≥0∞) + 1)⁻¹ = 2⁻¹ from by norm_num,
      ← division_def,
      ENNReal.div_lt_iff (Or.inl (tsum_powWeight_ne_zero 100 l0 _))
        (Or.inl (tsum_powWeight_ne_top 100 l0 _)),
      Z_sOr2, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
      one_mul]
  calc ((6 : ℝ≥0∞)⁻¹) ^ 100 + ((4 : ℝ≥0∞)⁻¹) ^ 100
      < ((6 : ℝ≥0∞)⁻¹) ^ 100 + ((4 : ℝ≥0∞)⁻¹) ^ 100 + ((5 : ℝ≥0∞)⁻¹) ^ 100 :=
        ENNReal.lt_add_right
          (ENNReal.add_ne_top.mpr
            ⟨ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num)),
             ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num))⟩)
          (pow_ne_zero 100 (ENNReal.inv_ne_zero.mpr (by norm_num)))
    _ = ((6 : ℝ≥0∞)⁻¹) ^ 100 + ((5 : ℝ≥0∞)⁻¹) ^ 100 + ((4 : ℝ≥0∞)⁻¹) ^ 100 := by
        ring

/-- Hearing *may S*, the listener prefers Only-S to S-or-2 (their
Table 3: 0.67 vs 0.33): the dedicated exhaustified parse (32c) is only
available at Only-S. -/
theorem literal_s_communicates_onlyS :
    (listener 100 .mayS).toOuterMeasure
        ↑({(.sOr2, ())} : Finset (FCIState × Unit))
      < (listener 100 .mayS).toOuterMeasure
        ↑({(.onlyS, ())} : Finset (FCIState × Unit)) := by
  rw [listener, L1_uniform_event_lt_iff, Finset.sum_singleton,
      Finset.sum_singleton]
  exact speakerU_sOr2_mayS_lt_half.trans half_lt_speakerU_onlyS_mayS

/-! ### The strict Only-1 / Any-# asymmetry (refining their Table 3) -/

private theorem Z_only1_lt_Z_anyNum :
    (∑' r, powWeight 100 l0 (.only1, ()) r)
      < ∑' r, powWeight 100 l0 (.anyNum, ()) r := by
  apply ENNReal.tsum_lt_tsum (tsum_powWeight_ne_top 100 l0 _) (i := Parse.evB)
  · intro p
    by_cases h1 : meaning p FCIState.only1 = true
    · have h2 : meaning p FCIState.anyNum = true := by
        revert h1; cases p <;> decide
      rw [powWeight_L0OfBool_of_mem (fun _ q => meaning q) ext_nonempty _ h1 rfl,
          powWeight_L0OfBool_of_mem (fun _ q => meaning q) ext_nonempty _ h2 rfl]
    · rw [powWeight_L0OfBool_of_not_mem (fun _ q => meaning q) ext_nonempty
            (by norm_num) h1]
      exact zero_le
  · rw [powWeight_L0OfBool_of_not_mem _ _ (by norm_num) (by decide),
        powWeight_L0OfBool_of_mem _ _ 4 (by decide) (by decide)]
    exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) 100

/-- **The asymmetry the paper's Table 3 rounds away**: at a uniform prior,
`L1(Only 1 | may any)` strictly exceeds `L1(Any # | may any)` — the paper
reports 0.50/0.50 at α = 100 (the difference is ≈ 2·10⁻³¹). Both parses of
*may any* carry the same weight at the two states, but *may every*'s parse
(35b) is true at Any # and not at Only 1, strictly inflating the speaker's
partition there, so the speaker is less likely to choose *may any* at
Any #. A formaliser's refinement, not a claim of the paper's. -/
theorem exclusiveness_strict_asymmetry :
    (listener 100 .mayAny).toOuterMeasure
        ↑({(.anyNum, ())} : Finset (FCIState × Unit))
      < (listener 100 .mayAny).toOuterMeasure
        ↑({(.only1, ())} : Finset (FCIState × Unit)) := by
  rw [listener, L1_uniform_event_lt_iff, Finset.sum_singleton,
      Finset.sum_singleton, speakerU_mayAny, speakerU_mayAny,
      sum_S1_eq_mul_inv, sum_S1_eq_mul_inv,
      powWeight_L0OfBool_of_mem _ _ 5 (by decide) card_anyA,
      powWeight_L0OfBool_of_mem _ _ 2 (by decide) card_anyB,
      powWeight_L0OfBool_of_mem _ _ 5 (by decide) card_anyA,
      powWeight_L0OfBool_of_mem _ _ 2 (by decide) card_anyB]
  exact (ENNReal.mul_lt_mul_iff_right
      (ne_of_gt (lt_of_lt_of_le
        (ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) 100) le_self_add))
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num)),
         ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by norm_num))⟩)).mpr
    (ENNReal.inv_lt_inv.mpr Z_only1_lt_Z_anyNum)

end Alsop2024
