import Linglib.Pragmatics.RSA.Canonical

/-!
# [franke-bergen-2020] — GI-RSA for Nested Aristotelians
[franke-bergen-2020] [fox-2007] [franke-2011]

"Theory-driven statistical modeling for semantics and pragmatics:
A case study on grammatically generated implicature readings"

## The Model

Domain: Nested Aristotelian sentences "Q₁ of the aliens drank Q₂ of their
water" with Q₁, Q₂ ∈ {none, some, all}. 7 world states based on which
alien types exist (none-drinkers, some-drinkers, all-drinkers). 8 grammatical
parses (subsets of {M, O, I} EXH positions) as latent variables.

The Global Intentions (GI) model treats the parse as a latent variable:
the speaker chooses both an utterance and a parse, the listener marginalizes
over parses to recover the world state.

- **L0**: L0(w|u,g) ∝ ⟦u⟧ᵍ(w) (meaning under parse g)
- **S1**: S1(u,g|w) ∝ L0(w|u,g)^α · P(g)
- **L1**: L1(w|u) ∝ P(w) · Σ_g S1(u,g|w)

Exhaustification uses compositional enrichment at inner/outer quantifier
positions: Exh(Q) conjoins Q with the negation of all strictly stronger
lexical alternatives on the {some, all} scale ([fox-2007]). Only
Exh(some) = "some but not all" is non-vacuous; Exh(all) and Exh(none)
have no strictly stronger alternative.

At matrix position, EXH uses exh_MW (eq. A2): negate the LITERAL meanings
of sentential alternatives that are strictly stronger than the sub-matrix
enriched meaning, with a noncontradictory fallback. Sentential alternatives
are the cross-product of scale-mate substitutions ({some, all}) for each
on-scale quantifier. "none" is treated as off-scale; the paper notes
(fn. 7) that including "not all" as an alternative to "none" has negligible
effect on predictions.

Parameters: α = 2 (modeling choice; the paper estimates α jointly with cost
and error parameters, reporting MLE ≈ 1.3 for GI), uniform priors. The
paper's cost term c(u) for "none"-initial utterances and error term ε are
omitted; the qualitative predictions below are robust to these simplifications.

## Qualitative Findings

| # | Finding | Theorem |
|---|---------|---------|
| 1 | SS exhaustifies inner Q | `ss_inner_exh` |
| 2 | SS exhaustifies outer Q | `ss_outer_exh` |
| 3 | AA identifies unique world | `aa_identifies` |
| 4 | AS exhaustifies inner Q | `as_inner_exh` |
| 5 | Full EXH preferred for SS | `ss_parse_pref` |
| 6 | Vanilla gets SS wrong (prefers wNA) | `vanilla_ss_prefers_wNA` |
| 7 | GI gets SS right (prefers wNS) | `gi_ss_prefers_wNS` |
| 8 | LU gets SS→wNS right | `lu_ss_prefers_wNS` |
| 9 | LI derives outer exh for SS | `li_ss_outer_exh` |
| 10 | LI also gets SS→wNS right | `li_ss_prefers_wNS` |

## Model Comparison

All four models share **one per-parse speaker** `S(w, p)` (the softmax at
exponent `α = 2` of the parse-`p` literal listener), because the speaker at a
`(world, parse)` state depends only on that parse's Boolean meaning. They differ
only in the *latent space* the pragmatic listener marginalises over — a joint
`PMF (World × Latent)` posterior (`RSA.Canonical.L1`) with a uniform prior:
- **Vanilla** (§3.1): latent `Unit` — literal parse only (`S(·, .none)`)
- **LU** (§3.2): latent `LULex` (2 lexica) — simplified to L1
  (the paper adds an S2/L2 layer following [potts-etal-2016]; our L1-only
  approximation suffices for qualitative predictions)
- **LI** (§3.3): latent `LIParse` (4 parses) — speaker chooses parse
- **GI** (§3.4): latent `Parse` (8 parses) — full parse space

The listener predictions are decided by exact `PMF` evaluation: each speaker
mass `S(w, p) u` is a rational `ENNReal.ofReal` value (`s_*` lemmas below),
and each theorem reduces via `RSA.Canonical.L1_world_prefers_iff` (or
`_latent_prefers_iff`) to a comparison of pooled speaker sums over the latent.

Bayesian model comparison: GI achieves 0.956 posterior probability,
LI = 0.033, LU = 0.010, vanilla = 0.
-/

set_option autoImplicit false

namespace FrankeBergen2020

open scoped ENNReal

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Aristotelian quantifiers: none, some, all. -/
inductive AristQuant where
  | none : AristQuant
  | some_ : AristQuant
  | all : AristQuant
  deriving DecidableEq, Repr, Inhabited

instance : Fintype AristQuant where
  elems := {.none, .some_, .all}
  complete := fun x => by cases x <;> simp

/-- The 7 world states, distinguished by which alien types exist.
    Three types: N (drank none), S (drank some but not all), A (drank all).
    Worlds are the 7 non-empty subsets of {N, S, A}. -/
inductive World where
  | wN    -- only N-type aliens
  | wNS   -- N and S types
  | wNA   -- N and A types
  | wNSA  -- all three types
  | wS    -- only S-type aliens
  | wSA   -- S and A types
  | wA    -- only A-type aliens
  deriving DecidableEq, Repr, Inhabited

instance : Fintype World where
  elems := {.wN, .wNS, .wNA, .wNSA, .wS, .wSA, .wA}
  complete := fun x => by cases x <;> simp

/-- The 9 nested Aristotelian utterances: Q_outer × Q_inner. -/
inductive Utterance where
  | nn | ns | na
  | sn | ss | sa
  | an | as_ | aa
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Utterance where
  elems := {.nn, .ns, .na, .sn, .ss, .sa, .an, .as_, .aa}
  complete := fun x => by cases x <;> simp

/-- The 8 grammatical parses: subsets of {M, O, I} EXH positions. -/
inductive Parse where
  | none   -- literal (no EXH)
  | m | o | i
  | mo | mi | oi
  | moi
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Parse where
  elems := {.none, .m, .o, .i, .mo, .mi, .oi, .moi}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- §2. Accessors
-- ============================================================================

/-- Whether N-type aliens (drank none) exist. -/
def World.hasN : World → Bool
  | .wN | .wNS | .wNA | .wNSA => true
  | _ => false

/-- Whether S-type aliens (drank some but not all) exist. -/
def World.hasS : World → Bool
  | .wS | .wNS | .wSA | .wNSA => true
  | _ => false

/-- Whether A-type aliens (drank all) exist. -/
def World.hasA : World → Bool
  | .wA | .wNA | .wSA | .wNSA => true
  | _ => false

/-- Outer quantifier of an utterance. -/
def Utterance.outer : Utterance → AristQuant
  | .nn | .ns | .na => .none
  | .sn | .ss | .sa => .some_
  | .an | .as_ | .aa => .all

/-- Inner quantifier of an utterance. -/
def Utterance.inner : Utterance → AristQuant
  | .nn | .sn | .an => .none
  | .ns | .ss | .as_ => .some_
  | .na | .sa | .aa => .all

/-- Construct an utterance from outer × inner quantifiers. -/
def Utterance.mk : AristQuant → AristQuant → Utterance
  | .none, .none => .nn | .none, .some_ => .ns | .none, .all => .na
  | .some_, .none => .sn | .some_, .some_ => .ss | .some_, .all => .sa
  | .all, .none => .an | .all, .some_ => .as_ | .all, .all => .aa

/-- Whether a quantifier is on the lexical scale {some, all}. -/
def AristQuant.onScale : AristQuant → Bool
  | .some_ | .all => true
  | .none => false

/-- Whether parse includes EXH at inner position. -/
def Parse.hasI : Parse → Bool
  | .i | .mi | .oi | .moi => true
  | _ => false

/-- Whether parse includes EXH at outer position. -/
def Parse.hasO : Parse → Bool
  | .o | .mo | .oi | .moi => true
  | _ => false

/-- Whether parse includes EXH at matrix position. -/
def Parse.hasM : Parse → Bool
  | .m | .mo | .mi | .moi => true
  | _ => false

-- ============================================================================
-- §3. Compositional Semantics
-- ============================================================================

/-- Inner VP satisfaction: which alien types satisfy "drank Q"?
    - Q = none: N-types satisfy (drank none of their water)
    - Q = some: S-types and A-types satisfy (drank some)
    - Q = all: only A-types satisfy (drank all) -/
def innerTypeSat (qi : AristQuant) : Bool × Bool × Bool :=
  match qi with
  | .none => (true, false, false)
  | .some_ => (false, true, true)
  | .all => (false, false, true)

/-- Outer quantifier evaluation: does the world satisfy "Q_outer of the
    aliens [satisfy inner VP]"? `nSat`, `sSat`, `aSat` indicate which
    alien types satisfy the inner VP. -/
def outerEval (qo : AristQuant) (nSat sSat aSat : Bool) (w : World) : Bool :=
  match qo with
  | .none => !(w.hasN && nSat) && !(w.hasS && sSat) && !(w.hasA && aSat)
  | .some_ => (w.hasN && nSat) || (w.hasS && sSat) || (w.hasA && aSat)
  | .all => (!w.hasN || nSat) && (!w.hasS || sSat) && (!w.hasA || aSat)

/-- Literal meaning: compose inner VP satisfaction with outer quantifier. -/
def literalMeaning (u : Utterance) (w : World) : Bool :=
  let (nSat, sSat, aSat) := innerTypeSat u.inner
  outerEval u.outer nSat sSat aSat w

-- ============================================================================
-- §4. Compositional Exhaustification
-- ============================================================================

/-- All 7 worlds for enumeration. -/
def allWorlds : List World := [.wN, .wNS, .wNA, .wNSA, .wS, .wSA, .wA]

/-- Inner VP satisfaction after EXH enrichment. Only "some" is enrichable:
    Exh(some) = "some but not all" — satisfied by S-types only (not A-types).
    Exh(none) and Exh(all) are vacuous (no strictly stronger alternative). -/
def enrichedInnerTypeSat (qi : AristQuant) (hasI : Bool) : Bool × Bool × Bool :=
  if hasI && qi == .some_ then
    (false, true, false)  -- only S-types satisfy "some but not all"
  else
    innerTypeSat qi

/-- The lexical scale: {some, all}. -/
def scale : List AristQuant := [.some_, .all]

/-- Sentential alternatives at matrix position: cross-product of
    scale-mate substitutions for each scalar item in the utterance.
    Non-scalar positions are held fixed. -/
def matrixAlts (u : Utterance) : List Utterance :=
  let outers := if u.outer.onScale then scale else [u.outer]
  let inners := if u.inner.onScale then scale else [u.inner]
  (outers.map fun o => inners.map fun i => Utterance.mk o i).flatten

/-- Exhaustified meaning under a given parse, using compositional enrichment.

    Inner/outer EXH enrich quantifiers in situ (at the quantifier level, not
    the sentence level), following the paper's Appendix. Only "some" →
    "some but not all" is a meaningful enrichment; Exh(all) and Exh(none)
    are vacuous (no strictly stronger lexical alternative on the scale).

    Matrix EXH uses exh_MW with a strength filter: negate the LITERAL
    meanings of sentential alternatives that are strictly stronger than
    the enriched (sub-matrix) meaning. Fall back to no matrix EXH if
    the conjunction is contradictory (eq. A2). -/
def exhMeaning (p : Parse) (u : Utterance) : World → Bool :=
  -- Step 1: Compute inner predicate (enriched if I ∈ parse)
  let (nSat, sSat, aSat) := enrichedInnerTypeSat u.inner p.hasI
  -- Step 2: Apply outer quantifier
  let baseMeaning := outerEval u.outer nSat sSat aSat
  -- Step 3: Outer EXH (if O ∈ parse and outer Q = some)
  -- Exh_O(some) = some ∧ ¬all: "some but not all types satisfy inner pred"
  let afterO :=
    if p.hasO && u.outer == .some_ then
      let allMeaning := outerEval .all nSat sSat aSat
      fun w => baseMeaning w && !allMeaning w
    else baseMeaning
  -- Step 4: Matrix EXH (if M ∈ parse)
  -- Uses MW with strength filter on LITERAL alternative meanings (eq. A2)
  if p.hasM then
    let enriched := afterO  -- meaning under parse without M
    -- Filter: keep sentential alternatives strictly stronger than enriched
    -- (S'^lit ⊂ enriched, proper subset)
    let strongerAlts := (matrixAlts u).filter fun a =>
      a != u &&
      allWorlds.all (fun w => if literalMeaning a w then enriched w else true) &&
      allWorlds.any (fun w => enriched w && !literalMeaning a w)
    -- Negate all stronger alternatives' LITERAL meanings (MW style)
    let result : World → Bool := fun w =>
      enriched w && strongerAlts.all fun a => !literalMeaning a w
    -- Noncontradictory check (eq. A2): if empty, fall back to enriched
    if allWorlds.any result then result else enriched
  else afterO

-- ============================================================================
-- §5. Verification Theorems
-- ============================================================================

/-- Literal SS is true at 6 of 7 worlds (all except wN). -/
theorem ss_literal_count :
    (allWorlds.filter (literalMeaning .ss)).length = 6 := by native_decide

/-- EXH_I(SS) = worlds with S-types (compositional: "some aliens drank
    some but not all"). Inner EXH enriches "some" to "some but not all",
    so S-types satisfy the VP but A-types do not. The outer "some"
    requires at least one S-type, giving {wNS, wNSA, wS, wSA}. -/
theorem exh_i_ss : exhMeaning .i .ss .wNS = true
    ∧ exhMeaning .i .ss .wNSA = true
    ∧ exhMeaning .i .ss .wS = true
    ∧ exhMeaning .i .ss .wSA = true
    ∧ exhMeaning .i .ss .wN = false
    ∧ exhMeaning .i .ss .wNA = false
    ∧ exhMeaning .i .ss .wA = false := by
  exact ⟨by native_decide, by native_decide, by native_decide,
         by native_decide, by native_decide, by native_decide,
         by native_decide⟩

/-- EXH_OI(SS) = {wNS, wNSA, wSA} — outer "some but not all" alien types
    satisfy the enriched inner predicate. wS excluded because at wS all
    types (just S) satisfy the inner pred, so "all" would be true. -/
theorem exh_oi_ss : exhMeaning .oi .ss .wNS = true
    ∧ exhMeaning .oi .ss .wNSA = true
    ∧ exhMeaning .oi .ss .wSA = true
    ∧ exhMeaning .oi .ss .wS = false := by
  exact ⟨by native_decide, by native_decide, by native_decide,
         by native_decide⟩

/-- EXH_MOI(SS) = EXH_OI(SS) = {wNS, wNSA, wSA} — matrix EXH is vacuous
    here because no sentential alternative is strictly stronger than
    the OI-enriched meaning. -/
theorem exh_moi_ss : ∀ w : World,
    exhMeaning .moi .ss w = exhMeaning .oi .ss w := by native_decide

/-- AA is true only at wA under all parses. -/
theorem aa_singleton : ∀ p : Parse, ∀ w : World,
    exhMeaning p .aa w = (w == .wA) := by native_decide

/-- Full truth table for SS across key parses, matching Table 1 of the paper.
    Format: (parse, [wN, wNS, wNA, wNSA, wS, wSA, wA]). -/
theorem table1_ss :
    -- lit: SS true everywhere except wN
    (allWorlds.map (exhMeaning .none .ss) = [false, true, true, true, true, true, true])
    -- I: inner EXH keeps worlds with S-types
    ∧ (allWorlds.map (exhMeaning .i .ss) = [false, true, false, true, true, true, false])
    -- OI: outer "some but not all" excludes wS (only S-types → all satisfy)
    ∧ (allWorlds.map (exhMeaning .oi .ss) = [false, true, false, true, false, true, false])
    -- MOI: same as OI (matrix EXH vacuous here)
    ∧ (allWorlds.map (exhMeaning .moi .ss) = [false, true, false, true, false, true, false])
    := by exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- §6. Latent spaces of the four models
-- ============================================================================

/-- LU lexicon: literal or OI (inner + outer EXH). Each speaker has a
    fixed lexicon; the listener marginalizes over the two lexica to infer
    the world state. Mirrors the [potts-etal-2016] architecture. -/
inductive LULex where
  | lit | oi
  deriving DecidableEq, Repr, Inhabited

instance : Fintype LULex where
  elems := {.lit, .oi}
  complete := fun x => by cases x <;> simp

/-- Map LU lexicon to the corresponding Parse. -/
def LULex.toParse : LULex → Parse
  | .lit => .none | .oi => .oi

/-- LI parse: lit, I, O, or OI. The speaker actively chooses a parse per
    utterance (unlike LU, where each speaker has a fixed lexicon). -/
inductive LIParse where
  | lit | i | o | oi
  deriving DecidableEq, Repr, Inhabited

instance : Fintype LIParse where
  elems := {.lit, .i, .o, .oi}
  complete := fun x => by cases x <;> simp

/-- Map LI parse to the full Parse type. -/
def LIParse.toParse : LIParse → Parse
  | .lit => .none | .i => .i | .o => .o | .oi => .oi

-- ============================================================================
-- §7. The shared per-parse speaker
-- ============================================================================

/-! All four models share **one speaker family** `S : World × Parse → PMF
Utterance`: the [frank-goodman-2012] softmax at exponent `α = 2` of the
per-parse literal listener `L0(· | u, p)` (uniform on `exhMeaning p u`'s
extension). The speaker at state `(w, p)` depends only on parse `p`'s Boolean
meaning, so vanilla / LU / LI / GI differ *only* in the latent space their
pragmatic listener marginalises over. Built on the `RSA.Canonical` PMF
pipeline (`powUtility`/`L0OfBool`), so `S = PMF.normalize (L0^2)`
(`RSA.Canonical.S1_powUtility_eq_normalize`). -/

/-- Every utterance is true at some world under every parse, so each per-parse
literal listener is well-defined (`L0OfBool`'s nonempty-extension obligation). -/
theorem ext_nonempty (p : Parse) (u : Utterance) :
    (RSA.extensionOf (exhMeaning p) u).Nonempty := by
  cases p <;> cases u <;> decide

/-- The per-parse literal listener `L0(· | u, p) : PMF World`, uniform on the
extension of `exhMeaning p u`. -/
noncomputable def L0m : Parse → Utterance → PMF World :=
  RSA.Canonical.L0OfBool exhMeaning ext_nonempty

/-- Every `(world, parse)` state has an applicable (true) utterance — the
`ViableSpeaker` witness that makes the softmax speaker well-defined. -/
theorem exists_true (w : World) (p : Parse) : ∃ u, exhMeaning p u w = true := by
  cases w <;> cases p <;> decide

noncomputable instance : RSA.Canonical.ViableSpeaker (RSA.Canonical.powUtility 2 L0m) :=
  RSA.Canonical.viableSpeaker_powUtility_of_witness 2 L0m (fun s => by
    obtain ⟨w, p⟩ := s
    obtain ⟨u, hu⟩ := exists_true w p
    exact ⟨u, RSA.Canonical.L0OfBool_ne_zero exhMeaning ext_nonempty hu⟩)

/-- The shared pragmatic speaker `S(w, p) ∝ L0(w | ·, p)^2` (α = 2, no cost). -/
noncomputable def S : World × Parse → PMF Utterance :=
  RSA.Canonical.S1 (RSA.Canonical.powUtility 2 L0m)

/-- LU speaker: the shared speaker re-indexed by the 2-lexicon latent. -/
noncomputable def luS (s : World × LULex) : PMF Utterance := S (s.1, s.2.toParse)

/-- LI speaker: the shared speaker re-indexed by the 4-parse latent. -/
noncomputable def liS (s : World × LIParse) : PMF Utterance := S (s.1, s.2.toParse)

/-- Vanilla speaker: the shared speaker at the literal parse only. -/
noncomputable def vanillaS (w : World) : PMF Utterance := S (w, .none)

-- ============================================================================
-- §8. Speaker mass as exact rationals
-- ============================================================================

/-! Each speaker mass `S(w, p) u` is an exact rational: `0` when `exhMeaning
p u w` is false, else `|ext(p,u)|⁻² / Z(w,p)` where `Z(w,p) = Σ_u |ext(p,u)|⁻²`
sums over utterances true at `w`. The `pw_*` lemmas give the unnormalised
weight `L0^2`; the `Z_*` lemmas the partition; the `s_*` lemmas the normalised
mass as `ENNReal.ofReal q`. Cards are certified by `decide`, arithmetic by
`norm_num`. -/

/-- Unnormalised speaker weight at a true utterance: `|ext(p,u)|⁻²`. -/
theorem pw_true {p : Parse} {u : Utterance} {w : World} {k : ℕ}
    (h : exhMeaning p u w = true) (hk : (RSA.extensionOf (exhMeaning p) u).card = k) :
    RSA.Canonical.powWeight 2 L0m (w, p) u = ENNReal.ofReal ((k : ℝ)⁻¹ ^ 2) := by
  have hpos : 0 < k := hk ▸ Finset.card_pos.mpr ⟨w, RSA.mem_extensionOf.mpr h⟩
  simp only [L0m]
  rw [RSA.Canonical.powWeight_L0OfBool_of_mem exhMeaning ext_nonempty k h hk,
    ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hpos), ENNReal.ofReal_natCast]

/-- Unnormalised speaker weight at a false utterance: `0` (as `ofReal 0`, so
partition sums combine uniformly through `ENNReal.ofReal_add`). -/
theorem pw_false {p : Parse} {u : Utterance} {w : World}
    (h : exhMeaning p u w = false) :
    RSA.Canonical.powWeight 2 L0m (w, p) u = ENNReal.ofReal 0 := by
  rw [ENNReal.ofReal_zero]
  simp only [L0m]
  exact RSA.Canonical.powWeight_L0OfBool_of_not_mem exhMeaning ext_nonempty (by decide)
    (by rw [h]; decide)

/-- Enumeration of the nine utterances (for partition sums). -/
theorem sumU (f : Utterance → ℝ≥0∞) :
    ∑' u, f u = f .nn + f .ns + f .na + f .sn + f .ss + f .sa + f .an + f .as_ + f .aa := by
  rw [tsum_fintype,
    show (Finset.univ : Finset Utterance)
      = {.nn, .ns, .na, .sn, .ss, .sa, .an, .as_, .aa} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- Normalised speaker mass at a true utterance: `|ext(p,u)|⁻² / Z(w,p)`, as an
exact `ENNReal.ofReal` rational. `hZ` supplies the partition `Z(w,p)`. -/
theorem S_val {p : Parse} {u : Utterance} {w : World} {k : ℕ} {z q : ℝ}
    (h : exhMeaning p u w = true) (hk : (RSA.extensionOf (exhMeaning p) u).card = k)
    (hz : 0 < z)
    (hZ : (∑' u', RSA.Canonical.powWeight 2 L0m (w, p) u') = ENNReal.ofReal z)
    (hq : (k : ℝ)⁻¹ ^ 2 / z = q) :
    S (w, p) u = ENNReal.ofReal q := by
  unfold S
  rw [RSA.Canonical.S1_powUtility_eq_normalize, PMF.normalize_apply, pw_true h hk, hZ,
    ← ENNReal.ofReal_inv_of_pos hz, ← ENNReal.ofReal_mul (by positivity), ← div_eq_mul_inv, hq]

/-- Normalised speaker mass at a false utterance: `0`. -/
theorem S_zero {p : Parse} {u : Utterance} {w : World}
    (h : exhMeaning p u w = false) : S (w, p) u = 0 := by
  unfold S
  rw [RSA.Canonical.S1_powUtility_eq_normalize, PMF.normalize_apply, pw_false h,
    ENNReal.ofReal_zero, zero_mul]

/-- `S_zero` in `ofReal 0` form, so pooled parse sums combine uniformly. -/
theorem S_zero' {p : Parse} {u : Utterance} {w : World}
    (h : exhMeaning p u w = false) : S (w, p) u = ENNReal.ofReal 0 := by
  rw [ENNReal.ofReal_zero]; exact S_zero h

/-- The shared speaker never assigns zero mass to a true utterance — the
witness for the pragmatic listener's marginal-nonzero obligations. -/
theorem S_ne_zero {p : Parse} {u : Utterance} {w : World}
    (h : exhMeaning p u w = true) : S (w, p) u ≠ 0 := by
  have hpos : 0 < (RSA.extensionOf (exhMeaning p) u).card :=
    Finset.card_pos.mpr ⟨w, RSA.mem_extensionOf.mpr h⟩
  unfold S
  rw [RSA.Canonical.S1_powUtility_eq_normalize, ← PMF.mem_support_iff,
    PMF.mem_support_normalize_iff, pw_true h rfl, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact pow_pos (inv_pos.mpr (by exact_mod_cast hpos)) 2

/-- Partition `Z(wNS, none) = 1/9 + 1/16 + 1/36 = 29/144` (SS-worlds: na, sn, ss). -/
theorem Z_none_wNS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNS, .none) u') = ENNReal.ofReal (29 / 144) := by
  rw [sumU, pw_false (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 4) (by decide) (by decide),
    pw_true (k := 6) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  norm_num

/-- `S(wNS, none) ss = 4/29`. -/
theorem s_none_wNS_ss : S (.wNS, .none) .ss = ENNReal.ofReal (4 / 29) :=
  S_val (k := 6) (by decide) (by decide) (by norm_num) Z_none_wNS (by norm_num)

/-- Enumeration of the eight parses (for the GI latent marginal). -/
theorem sumParse (f : Parse → ℝ≥0∞) :
    ∑ p : Parse, f p = f .none + f .m + f .o + f .i + f .mo + f .mi + f .oi + f .moi := by
  rw [show (Finset.univ : Finset Parse) = {.none, .m, .o, .i, .mo, .mi, .oi, .moi} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-! ### `wNS` partition and speaker masses (SS) -/

theorem Z_m_wNS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNS, .m) u') = ENNReal.ofReal (49 / 36) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_true (k := 2) (by decide) (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 1) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_o_wNS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNS, .o) u') = ENNReal.ofReal (1 / 3) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_i_wNS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNS, .i) u') = ENNReal.ofReal (17 / 72) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_true (k := 4) (by decide) (by decide), pw_true (k := 4) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_mo_wNS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNS, .mo) u') = ENNReal.ofReal (17 / 36) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_true (k := 2) (by decide) (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_mi_wNS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNS, .mi) u') = ENNReal.ofReal (61 / 144) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_true (k := 2) (by decide) (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 4) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_oi_wNS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNS, .oi) u') = ENNReal.ofReal (1 / 3) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_moi_wNS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNS, .moi) u') = ENNReal.ofReal (17 / 36) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_true (k := 2) (by decide) (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem s_m_wNS_ss : S (.wNS, .m) .ss = ENNReal.ofReal (36 / 49) :=
  S_val (k := 1) (by decide) (by decide) (by norm_num) Z_m_wNS (by norm_num)
theorem s_o_wNS_ss : S (.wNS, .o) .ss = ENNReal.ofReal (1 / 3) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_o_wNS (by norm_num)
theorem s_i_wNS_ss : S (.wNS, .i) .ss = ENNReal.ofReal (9 / 34) :=
  S_val (k := 4) (by decide) (by decide) (by norm_num) Z_i_wNS (by norm_num)
theorem s_mo_wNS_ss : S (.wNS, .mo) .ss = ENNReal.ofReal (4 / 17) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_mo_wNS (by norm_num)
theorem s_mi_wNS_ss : S (.wNS, .mi) .ss = ENNReal.ofReal (9 / 61) :=
  S_val (k := 4) (by decide) (by decide) (by norm_num) Z_mi_wNS (by norm_num)
theorem s_oi_wNS_ss : S (.wNS, .oi) .ss = ENNReal.ofReal (1 / 3) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_oi_wNS (by norm_num)
theorem s_moi_wNS_ss : S (.wNS, .moi) .ss = ENNReal.ofReal (4 / 17) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_moi_wNS (by norm_num)

theorem sumP_wNS_ss :
    (∑ p : Parse, S (.wNS, p) .ss) = ENNReal.ofReal (21415141 / 8841462) := by
  rw [sumParse, s_none_wNS_ss, s_m_wNS_ss, s_o_wNS_ss, s_i_wNS_ss, s_mo_wNS_ss, s_mi_wNS_ss,
    s_oi_wNS_ss, s_moi_wNS_ss]
  repeat rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

/-! ### `wNSA` partition and speaker masses (SS) -/

theorem Z_none_wNSA :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNSA, .none) u') = ENNReal.ofReal (11 / 72) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_false (by decide),
    pw_true (k := 4) (by decide) (by decide), pw_true (k := 6) (by decide) (by decide),
    pw_true (k := 4) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_o_wNSA :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNSA, .o) u') = ENNReal.ofReal (1 / 3) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_true (k := 3) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_i_wNSA :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNSA, .i) u') = ENNReal.ofReal (3 / 16) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_false (by decide),
    pw_true (k := 4) (by decide) (by decide), pw_true (k := 4) (by decide) (by decide),
    pw_true (k := 4) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_mo_wNSA :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNSA, .mo) u') = ENNReal.ofReal (1 / 3) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_true (k := 3) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_mi_wNSA :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNSA, .mi) u') = ENNReal.ofReal (41 / 144) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 4) (by decide) (by decide),
    pw_true (k := 3) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_oi_wNSA :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNSA, .oi) u') = ENNReal.ofReal (1 / 3) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_true (k := 3) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_moi_wNSA :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNSA, .moi) u') = ENNReal.ofReal (1 / 3) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_true (k := 3) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem s_none_wNSA_ss : S (.wNSA, .none) .ss = ENNReal.ofReal (2 / 11) :=
  S_val (k := 6) (by decide) (by decide) (by norm_num) Z_none_wNSA (by norm_num)
theorem s_o_wNSA_ss : S (.wNSA, .o) .ss = ENNReal.ofReal (1 / 3) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_o_wNSA (by norm_num)
theorem s_i_wNSA_ss : S (.wNSA, .i) .ss = ENNReal.ofReal (1 / 3) :=
  S_val (k := 4) (by decide) (by decide) (by norm_num) Z_i_wNSA (by norm_num)
theorem s_mo_wNSA_ss : S (.wNSA, .mo) .ss = ENNReal.ofReal (1 / 3) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_mo_wNSA (by norm_num)
theorem s_mi_wNSA_ss : S (.wNSA, .mi) .ss = ENNReal.ofReal (9 / 41) :=
  S_val (k := 4) (by decide) (by decide) (by norm_num) Z_mi_wNSA (by norm_num)
theorem s_oi_wNSA_ss : S (.wNSA, .oi) .ss = ENNReal.ofReal (1 / 3) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_oi_wNSA (by norm_num)
theorem s_moi_wNSA_ss : S (.wNSA, .moi) .ss = ENNReal.ofReal (1 / 3) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_moi_wNSA (by norm_num)

theorem sumP_wNSA_ss :
    (∑ p : Parse, S (.wNSA, p) .ss) = ENNReal.ofReal (2798 / 1353) := by
  rw [sumParse, s_none_wNSA_ss, S_zero' (w := .wNSA) (p := .m) (u := .ss) (by decide),
    s_o_wNSA_ss, s_i_wNSA_ss, s_mo_wNSA_ss, s_mi_wNSA_ss, s_oi_wNSA_ss, s_moi_wNSA_ss]
  repeat rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

/-! ### `wS` partition and speaker masses (SS and AS) -/

theorem Z_none_wS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wS, .none) u') = ENNReal.ofReal (13 / 36) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_false (by decide),
    pw_true (k := 6) (by decide) (by decide), pw_false (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_m_wS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wS, .m) u') = ENNReal.ofReal (11 / 18) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_false (by decide),
    pw_true (k := 2) (by decide) (by decide), pw_false (by decide), pw_false (by decide),
    pw_false (by decide), pw_false (by decide), pw_true (k := 2) (by decide) (by decide),
    pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_o_wS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wS, .o) u') = ENNReal.ofReal (1 / 3) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_false (by decide), pw_false (by decide),
    pw_false (by decide), pw_false (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_i_wS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wS, .i) u') = ENNReal.ofReal (185 / 144) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_false (by decide),
    pw_true (k := 4) (by decide) (by decide), pw_false (by decide), pw_false (by decide),
    pw_true (k := 1) (by decide) (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_mo_wS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wS, .mo) u') = ENNReal.ofReal (11 / 18) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_false (by decide),
    pw_true (k := 2) (by decide) (by decide), pw_false (by decide), pw_false (by decide),
    pw_false (by decide), pw_false (by decide), pw_true (k := 2) (by decide) (by decide),
    pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_mi_wS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wS, .mi) u') = ENNReal.ofReal (205 / 144) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_false (by decide),
    pw_true (k := 2) (by decide) (by decide), pw_false (by decide),
    pw_true (k := 4) (by decide) (by decide), pw_false (by decide), pw_false (by decide),
    pw_true (k := 1) (by decide) (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_oi_wS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wS, .oi) u') = ENNReal.ofReal (11 / 9) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_false (by decide), pw_false (by decide),
    pw_false (by decide), pw_false (by decide), pw_true (k := 1) (by decide) (by decide),
    pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_moi_wS :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wS, .moi) u') = ENNReal.ofReal (49 / 36) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_false (by decide),
    pw_true (k := 2) (by decide) (by decide), pw_false (by decide), pw_false (by decide),
    pw_false (by decide), pw_false (by decide), pw_true (k := 1) (by decide) (by decide),
    pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem s_none_wS_ss : S (.wS, .none) .ss = ENNReal.ofReal (1 / 13) :=
  S_val (k := 6) (by decide) (by decide) (by norm_num) Z_none_wS (by norm_num)
theorem s_i_wS_ss : S (.wS, .i) .ss = ENNReal.ofReal (9 / 185) :=
  S_val (k := 4) (by decide) (by decide) (by norm_num) Z_i_wS (by norm_num)
theorem s_mi_wS_ss : S (.wS, .mi) .ss = ENNReal.ofReal (9 / 205) :=
  S_val (k := 4) (by decide) (by decide) (by norm_num) Z_mi_wS (by norm_num)

theorem s_none_wS_as : S (.wS, .none) .as_ = ENNReal.ofReal (4 / 13) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_none_wS (by norm_num)
theorem s_m_wS_as : S (.wS, .m) .as_ = ENNReal.ofReal (9 / 22) :=
  S_val (k := 2) (by decide) (by decide) (by norm_num) Z_m_wS (by norm_num)
theorem s_o_wS_as : S (.wS, .o) .as_ = ENNReal.ofReal (1 / 3) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_o_wS (by norm_num)
theorem s_i_wS_as : S (.wS, .i) .as_ = ENNReal.ofReal (144 / 185) :=
  S_val (k := 1) (by decide) (by decide) (by norm_num) Z_i_wS (by norm_num)
theorem s_mo_wS_as : S (.wS, .mo) .as_ = ENNReal.ofReal (9 / 22) :=
  S_val (k := 2) (by decide) (by decide) (by norm_num) Z_mo_wS (by norm_num)
theorem s_mi_wS_as : S (.wS, .mi) .as_ = ENNReal.ofReal (144 / 205) :=
  S_val (k := 1) (by decide) (by decide) (by norm_num) Z_mi_wS (by norm_num)
theorem s_oi_wS_as : S (.wS, .oi) .as_ = ENNReal.ofReal (9 / 11) :=
  S_val (k := 1) (by decide) (by decide) (by norm_num) Z_oi_wS (by norm_num)
theorem s_moi_wS_as : S (.wS, .moi) .as_ = ENNReal.ofReal (36 / 49) :=
  S_val (k := 1) (by decide) (by decide) (by norm_num) Z_moi_wS (by norm_num)

/-! ### `wNA`, `wSA`, `wA` partitions and speaker masses -/

theorem Z_none_wNA :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNA, .none) u') = ENNReal.ofReal (11 / 72) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_false (by decide),
    pw_true (k := 4) (by decide) (by decide), pw_true (k := 6) (by decide) (by decide),
    pw_true (k := 4) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_o_wNA :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNA, .o) u') = ENNReal.ofReal (1 / 3) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_true (k := 3) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_mo_wNA :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wNA, .mo) u') = ENNReal.ofReal (1 / 3) := by
  rw [sumU, pw_false (by decide), pw_false (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_true (k := 3) (by decide) (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem s_none_wNA_ss : S (.wNA, .none) .ss = ENNReal.ofReal (2 / 11) :=
  S_val (k := 6) (by decide) (by decide) (by norm_num) Z_none_wNA (by norm_num)
theorem s_o_wNA_ss : S (.wNA, .o) .ss = ENNReal.ofReal (1 / 3) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_o_wNA (by norm_num)
theorem s_mo_wNA_ss : S (.wNA, .mo) .ss = ENNReal.ofReal (1 / 3) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_mo_wNA (by norm_num)

theorem Z_none_wSA :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wSA, .none) u') = ENNReal.ofReal (5 / 16) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_false (by decide), pw_false (by decide),
    pw_false (by decide), pw_true (k := 6) (by decide) (by decide),
    pw_true (k := 4) (by decide) (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_moi_wSA :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wSA, .moi) u') = ENNReal.ofReal (1 / 3) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_false (by decide), pw_false (by decide),
    pw_false (by decide), pw_true (k := 3) (by decide) (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_false (by decide), pw_false (by decide),
    pw_false (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem s_none_wSA_ss : S (.wSA, .none) .ss = ENNReal.ofReal (4 / 45) :=
  S_val (k := 6) (by decide) (by decide) (by norm_num) Z_none_wSA (by norm_num)
theorem s_moi_wSA_ss : S (.wSA, .moi) .ss = ENNReal.ofReal (1 / 3) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_moi_wSA (by norm_num)

theorem Z_none_wA :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wA, .none) u') = ENNReal.ofReal (21 / 16) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_false (by decide), pw_false (by decide),
    pw_false (by decide), pw_true (k := 6) (by decide) (by decide),
    pw_true (k := 4) (by decide) (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 1) (by decide) (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem Z_o_wA :
    (∑' u', RSA.Canonical.powWeight 2 L0m (.wA, .o) u') = ENNReal.ofReal (11 / 9) := by
  rw [sumU, pw_true (k := 3) (by decide) (by decide), pw_false (by decide), pw_false (by decide),
    pw_false (by decide), pw_false (by decide), pw_false (by decide), pw_false (by decide),
    pw_true (k := 3) (by decide) (by decide), pw_true (k := 1) (by decide) (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

theorem s_none_wA_ss : S (.wA, .none) .ss = ENNReal.ofReal (4 / 189) :=
  S_val (k := 6) (by decide) (by decide) (by norm_num) Z_none_wA (by norm_num)
theorem s_none_wA_as : S (.wA, .none) .as_ = ENNReal.ofReal (16 / 189) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_none_wA (by norm_num)
theorem s_o_wA_as : S (.wA, .o) .as_ = ENNReal.ofReal (1 / 11) :=
  S_val (k := 3) (by decide) (by decide) (by norm_num) Z_o_wA (by norm_num)

/-! ### Pooled speaker sums for the remaining worlds -/

theorem sumP_wS_ss : (∑ p : Parse, S (.wS, p) .ss) = ENNReal.ofReal (16711 / 98605) := by
  rw [sumParse, s_none_wS_ss, S_zero' (w := .wS) (p := .m) (u := .ss) (by decide),
    S_zero' (w := .wS) (p := .o) (u := .ss) (by decide), s_i_wS_ss,
    S_zero' (w := .wS) (p := .mo) (u := .ss) (by decide), s_mi_wS_ss,
    S_zero' (w := .wS) (p := .oi) (u := .ss) (by decide),
    S_zero' (w := .wS) (p := .moi) (u := .ss) (by decide)]
  repeat rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

theorem sumP_wNA_ss : (∑ p : Parse, S (.wNA, p) .ss) = ENNReal.ofReal (28 / 33) := by
  rw [sumParse, s_none_wNA_ss, S_zero' (w := .wNA) (p := .m) (u := .ss) (by decide), s_o_wNA_ss,
    S_zero' (w := .wNA) (p := .i) (u := .ss) (by decide), s_mo_wNA_ss,
    S_zero' (w := .wNA) (p := .mi) (u := .ss) (by decide),
    S_zero' (w := .wNA) (p := .oi) (u := .ss) (by decide),
    S_zero' (w := .wNA) (p := .moi) (u := .ss) (by decide)]
  repeat rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

theorem sumP_wS_as :
    (∑ p : Parse, S (.wS, p) .as_) = ENNReal.ofReal (716367317 / 159444285) := by
  rw [sumParse, s_none_wS_as, s_m_wS_as, s_o_wS_as, s_i_wS_as, s_mo_wS_as, s_mi_wS_as,
    s_oi_wS_as, s_moi_wS_as]
  repeat rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

theorem sumP_wA_as : (∑ p : Parse, S (.wA, p) .as_) = ENNReal.ofReal (365 / 2079) := by
  rw [sumParse, s_none_wA_as, S_zero' (w := .wA) (p := .m) (u := .as_) (by decide), s_o_wA_as,
    S_zero' (w := .wA) (p := .i) (u := .as_) (by decide),
    S_zero' (w := .wA) (p := .mo) (u := .as_) (by decide),
    S_zero' (w := .wA) (p := .mi) (u := .as_) (by decide),
    S_zero' (w := .wA) (p := .oi) (u := .as_) (by decide),
    S_zero' (w := .wA) (p := .moi) (u := .as_) (by decide)]
  repeat rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

/-- `AA` is false at `wSA` under every parse, so its pooled speaker sum is `0`. -/
theorem sumP_wSA_aa : (∑ p : Parse, S (.wSA, p) .aa) = 0 :=
  Finset.sum_eq_zero fun p _ => S_zero (by rw [aa_singleton]; decide)

/-! ### Latent pooling over worlds (parse-preference) -/

/-- Enumeration of the seven worlds (for the GI parse marginal). -/
theorem sumWorld (f : World → ℝ≥0∞) :
    ∑ w : World, f w = f .wN + f .wNS + f .wNA + f .wNSA + f .wS + f .wSA + f .wA := by
  rw [show (Finset.univ : Finset World) = {.wN, .wNS, .wNA, .wNSA, .wS, .wSA, .wA} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem sumW_none_ss :
    (∑ w : World, S (w, .none) .ss) = ENNReal.ofReal (2698343 / 3918915) := by
  rw [sumWorld, S_zero' (w := .wN) (p := .none) (u := .ss) (by decide), s_none_wNS_ss,
    s_none_wNA_ss, s_none_wNSA_ss, s_none_wS_ss, s_none_wSA_ss, s_none_wA_ss]
  repeat rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

theorem sumW_moi_ss : (∑ w : World, S (w, .moi) .ss) = ENNReal.ofReal (46 / 51) := by
  rw [sumWorld, S_zero' (w := .wN) (p := .moi) (u := .ss) (by decide), s_moi_wNS_ss,
    S_zero' (w := .wNA) (p := .moi) (u := .ss) (by decide), s_moi_wNSA_ss,
    S_zero' (w := .wS) (p := .moi) (u := .ss) (by decide), s_moi_wSA_ss,
    S_zero' (w := .wA) (p := .moi) (u := .ss) (by decide)]
  repeat rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

/-! ### LU / LI pooling over the smaller latent spaces -/

theorem sumLULex (f : LULex → ℝ≥0∞) : ∑ l : LULex, f l = f .lit + f .oi := by
  rw [show (Finset.univ : Finset LULex) = {.lit, .oi} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

theorem sumLU_wNS_ss : (∑ l : LULex, luS (.wNS, l) .ss) = ENNReal.ofReal (41 / 87) := by
  rw [sumLULex]
  show S (.wNS, .none) .ss + S (.wNS, .oi) .ss = _
  rw [s_none_wNS_ss, s_oi_wNS_ss, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

theorem sumLU_wNA_ss : (∑ l : LULex, luS (.wNA, l) .ss) = ENNReal.ofReal (2 / 11) := by
  rw [sumLULex]
  show S (.wNA, .none) .ss + S (.wNA, .oi) .ss = _
  rw [s_none_wNA_ss, S_zero' (w := .wNA) (p := .oi) (u := .ss) (by decide),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

theorem sumLIParse (f : LIParse → ℝ≥0∞) :
    ∑ l : LIParse, f l = f .lit + f .i + f .o + f .oi := by
  rw [show (Finset.univ : Finset LIParse) = {.lit, .i, .o, .oi} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

theorem sumLI_wNS_ss : (∑ l : LIParse, liS (.wNS, l) .ss) = ENNReal.ofReal (3163 / 2958) := by
  rw [sumLIParse]
  show S (.wNS, .none) .ss + S (.wNS, .i) .ss + S (.wNS, .o) .ss + S (.wNS, .oi) .ss = _
  rw [s_none_wNS_ss, s_i_wNS_ss, s_o_wNS_ss, s_oi_wNS_ss]
  repeat rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

theorem sumLI_wS_ss : (∑ l : LIParse, liS (.wS, l) .ss) = ENNReal.ofReal (302 / 2405) := by
  rw [sumLIParse]
  show S (.wS, .none) .ss + S (.wS, .i) .ss + S (.wS, .o) .ss + S (.wS, .oi) .ss = _
  rw [s_none_wS_ss, s_i_wS_ss, S_zero' (w := .wS) (p := .o) (u := .ss) (by decide),
    S_zero' (w := .wS) (p := .oi) (u := .ss) (by decide)]
  repeat rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

theorem sumLI_wNA_ss : (∑ l : LIParse, liS (.wNA, l) .ss) = ENNReal.ofReal (17 / 33) := by
  rw [sumLIParse]
  show S (.wNA, .none) .ss + S (.wNA, .i) .ss + S (.wNA, .o) .ss + S (.wNA, .oi) .ss = _
  rw [s_none_wNA_ss, S_zero' (w := .wNA) (p := .i) (u := .ss) (by decide), s_o_wNA_ss,
    S_zero' (w := .wNA) (p := .oi) (u := .ss) (by decide)]
  repeat rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1; norm_num

-- ============================================================================
-- §9. The four pragmatic listeners
-- ============================================================================

/-- GI (§3.4): joint posterior over `World × Parse` (8 parses). -/
noncomputable def giListener (u : Utterance)
    (h : PMF.marginal S (PMF.uniformOfFintype (World × Parse)) u ≠ 0) :
    PMF (World × Parse) :=
  RSA.Canonical.L1 S (PMF.uniformOfFintype (World × Parse)) u h

/-- LU (§3.2): joint posterior over `World × LULex`. -/
noncomputable def luListener (u : Utterance)
    (h : PMF.marginal luS (PMF.uniformOfFintype (World × LULex)) u ≠ 0) :
    PMF (World × LULex) :=
  RSA.Canonical.L1 luS (PMF.uniformOfFintype (World × LULex)) u h

/-- LI (§3.3): joint posterior over `World × LIParse`. -/
noncomputable def liListener (u : Utterance)
    (h : PMF.marginal liS (PMF.uniformOfFintype (World × LIParse)) u ≠ 0) :
    PMF (World × LIParse) :=
  RSA.Canonical.L1 liS (PMF.uniformOfFintype (World × LIParse)) u h

/-- Vanilla (§3.1): posterior over `World` for the single literal parse. -/
noncomputable def vanillaListener (u : Utterance)
    (h : PMF.marginal vanillaS (PMF.uniformOfFintype World) u ≠ 0) : PMF World :=
  PMF.posterior vanillaS (PMF.uniformOfFintype World) u h

-- ============================================================================
-- §10. Predictions
-- ============================================================================

/-! ### Listener-preference reductions

Each pragmatic listener's preference cancels the uniform joint prior, leaving a
comparison of pooled speaker sums over the model's latent space (`L1_world_/
_latent_prefers_iff`). -/

/-- GI world preference reduces to the pooled speaker sum over the 8 parses. -/
theorem giListener_fst_lt (u : Utterance)
    (h : PMF.marginal S (PMF.uniformOfFintype (World × Parse)) u ≠ 0) (w₁ w₂ : World) :
    (giListener u h).fst w₁ < (giListener u h).fst w₂ ↔
      (∑ p : Parse, S (w₁, p) u) < ∑ p : Parse, S (w₂, p) u := by
  unfold giListener
  rw [RSA.Canonical.L1_world_prefers_iff]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact ENNReal.mul_lt_mul_iff_right
    (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top (Fintype.card (World × Parse))))
    (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := World × Parse))))

/-- GI parse preference reduces to the pooled speaker sum over the 7 worlds. -/
theorem giListener_snd_lt (u : Utterance)
    (h : PMF.marginal S (PMF.uniformOfFintype (World × Parse)) u ≠ 0) (l₁ l₂ : Parse) :
    (giListener u h).snd l₁ < (giListener u h).snd l₂ ↔
      (∑ w : World, S (w, l₁) u) < ∑ w : World, S (w, l₂) u := by
  unfold giListener
  rw [RSA.Canonical.L1_latent_prefers_iff]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact ENNReal.mul_lt_mul_iff_right
    (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top (Fintype.card (World × Parse))))
    (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := World × Parse))))

/-- LU world preference reduces to the pooled speaker sum over the 2 lexica. -/
theorem luListener_fst_lt (u : Utterance)
    (h : PMF.marginal luS (PMF.uniformOfFintype (World × LULex)) u ≠ 0) (w₁ w₂ : World) :
    (luListener u h).fst w₁ < (luListener u h).fst w₂ ↔
      (∑ l : LULex, luS (w₁, l) u) < ∑ l : LULex, luS (w₂, l) u := by
  unfold luListener
  rw [RSA.Canonical.L1_world_prefers_iff]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact ENNReal.mul_lt_mul_iff_right
    (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top (Fintype.card (World × LULex))))
    (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := World × LULex))))

/-- LI world preference reduces to the pooled speaker sum over the 4 parses. -/
theorem liListener_fst_lt (u : Utterance)
    (h : PMF.marginal liS (PMF.uniformOfFintype (World × LIParse)) u ≠ 0) (w₁ w₂ : World) :
    (liListener u h).fst w₁ < (liListener u h).fst w₂ ↔
      (∑ l : LIParse, liS (w₁, l) u) < ∑ l : LIParse, liS (w₂, l) u := by
  unfold liListener
  rw [RSA.Canonical.L1_world_prefers_iff]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact ENNReal.mul_lt_mul_iff_right
    (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top (Fintype.card (World × LIParse))))
    (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := World × LIParse))))

/-! ### Marginal-nonzero witnesses -/

theorem gi_marg_ss : PMF.marginal S (PMF.uniformOfFintype (World × Parse)) .ss ≠ 0 :=
  PMF.marginal_ne_zero S (PMF.uniformOfFintype (World × Parse)) .ss (a := (.wNS, .none))
    (((PMF.uniformOfFintype (World × Parse)).mem_support_iff (.wNS, .none)).mp
      (PMF.mem_support_uniformOfFintype _))
    (S_ne_zero (by decide))

theorem gi_marg_aa : PMF.marginal S (PMF.uniformOfFintype (World × Parse)) .aa ≠ 0 :=
  PMF.marginal_ne_zero S (PMF.uniformOfFintype (World × Parse)) .aa (a := (.wA, .none))
    (((PMF.uniformOfFintype (World × Parse)).mem_support_iff (.wA, .none)).mp
      (PMF.mem_support_uniformOfFintype _))
    (S_ne_zero (by decide))

theorem gi_marg_as : PMF.marginal S (PMF.uniformOfFintype (World × Parse)) .as_ ≠ 0 :=
  PMF.marginal_ne_zero S (PMF.uniformOfFintype (World × Parse)) .as_ (a := (.wS, .none))
    (((PMF.uniformOfFintype (World × Parse)).mem_support_iff (.wS, .none)).mp
      (PMF.mem_support_uniformOfFintype _))
    (S_ne_zero (by decide))

theorem lu_marg_ss : PMF.marginal luS (PMF.uniformOfFintype (World × LULex)) .ss ≠ 0 := by
  refine PMF.marginal_ne_zero luS (PMF.uniformOfFintype (World × LULex)) .ss (a := (.wNS, .lit))
    (((PMF.uniformOfFintype (World × LULex)).mem_support_iff (.wNS, .lit)).mp
      (PMF.mem_support_uniformOfFintype _)) ?_
  show S (.wNS, .none) .ss ≠ 0
  exact S_ne_zero (by decide)

theorem li_marg_ss : PMF.marginal liS (PMF.uniformOfFintype (World × LIParse)) .ss ≠ 0 := by
  refine PMF.marginal_ne_zero liS (PMF.uniformOfFintype (World × LIParse)) .ss (a := (.wNS, .lit))
    (((PMF.uniformOfFintype (World × LIParse)).mem_support_iff (.wNS, .lit)).mp
      (PMF.mem_support_uniformOfFintype _)) ?_
  show S (.wNS, .none) .ss ≠ 0
  exact S_ne_zero (by decide)

theorem vanilla_marg_ss : PMF.marginal vanillaS (PMF.uniformOfFintype World) .ss ≠ 0 := by
  refine PMF.marginal_ne_zero vanillaS (PMF.uniformOfFintype World) .ss (a := .wNS)
    (((PMF.uniformOfFintype World).mem_support_iff .wNS).mp
      (PMF.mem_support_uniformOfFintype _)) ?_
  show S (.wNS, .none) .ss ≠ 0
  exact S_ne_zero (by decide)

/-! ### The ten qualitative findings -/

/-- SS exhaustifies inner quantifier: L1 prefers wNS (N and S types, no A)
    over wNSA (all three types including A). Inner EXH negates "some drank all",
    disfavoring worlds with A-type aliens. -/
theorem ss_inner_exh :
    (giListener .ss gi_marg_ss).fst .wNS > (giListener .ss gi_marg_ss).fst .wNSA := by
  rw [gt_iff_lt, giListener_fst_lt, sumP_wNSA_ss, sumP_wNS_ss,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- SS exhaustifies outer quantifier: L1 prefers wNS (mixed N+S types)
    over wS (only S-type). At wS, "all aliens drank some but not all" would
    be true, but outer EXH negates the "all" reading. -/
theorem ss_outer_exh :
    (giListener .ss gi_marg_ss).fst .wNS > (giListener .ss gi_marg_ss).fst .wS := by
  rw [gt_iff_lt, giListener_fst_lt, sumP_wS_ss, sumP_wNS_ss,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- AA correctly identifies the unique world where all aliens drank all: L1
    prefers wA over wSA. AA is false at wSA under every parse (pooled sum `0`),
    while at wA the literal parse already makes it true. -/
theorem aa_identifies :
    (giListener .aa gi_marg_aa).fst .wA > (giListener .aa gi_marg_aa).fst .wSA := by
  rw [gt_iff_lt, giListener_fst_lt, sumP_wSA_aa]
  exact pos_iff_ne_zero.mpr fun hz =>
    S_ne_zero (p := .none) (w := .wA) (by decide)
      (Finset.sum_eq_zero_iff.mp hz .none (Finset.mem_univ _))

/-- AS exhaustifies inner: L1 prefers wS (all aliens are "some" drinkers)
    over wA (all aliens are "all" drinkers). -/
theorem as_inner_exh :
    (giListener .as_ gi_marg_as).fst .wS > (giListener .as_ gi_marg_as).fst .wA := by
  rw [gt_iff_lt, giListener_fst_lt, sumP_wA_as, sumP_wS_as,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- Full exhaustification is preferred: for SS, the GI parse marginal assigns
    more probability to the fully exhaustified parse (MOI) than to the literal
    parse (NONE). -/
theorem ss_parse_pref :
    (giListener .ss gi_marg_ss).snd .moi > (giListener .ss gi_marg_ss).snd .none := by
  rw [gt_iff_lt, giListener_snd_lt, sumW_none_ss, sumW_moi_ss,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- Vanilla RSA hearing SS prefers wNA over wNS — the wrong prediction.
    Without exhaustification SS is literally true at 6/7 worlds, and the
    competing utterances make wNA "win" more of the S1 score. Production data
    show SS is used for wNS, evidence for grammatical enrichment. -/
theorem vanilla_ss_prefers_wNA :
    (vanillaListener .ss vanilla_marg_ss) .wNA > (vanillaListener .ss vanilla_marg_ss) .wNS := by
  rw [gt_iff_lt]
  unfold vanillaListener
  rw [PMF.posterior_lt_iff_kernel_lt_of_uniform]
  show S (.wNS, .none) .ss < S (.wNA, .none) .ss
  rw [s_none_wNS_ss, s_none_wNA_ss, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- GI correctly predicts the opposite: SS → wNS, not wNA. The exhaustified
    parses concentrate probability on worlds with S-types but not A-types. -/
theorem gi_ss_prefers_wNS :
    (giListener .ss gi_marg_ss).fst .wNS > (giListener .ss gi_marg_ss).fst .wNA := by
  rw [gt_iff_lt, giListener_fst_lt, sumP_wNA_ss, sumP_wNS_ss,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- LU also gets the key SS prediction right: wNS > wNA. The OI lexicon gives
    ⟦SS⟧^OI = {wNS, wNSA, wSA}, which excludes wNA, tipping the balance. -/
theorem lu_ss_prefers_wNS :
    (luListener .ss lu_marg_ss).fst .wNS > (luListener .ss lu_marg_ss).fst .wNA := by
  rw [gt_iff_lt, luListener_fst_lt, sumLU_wNA_ss, sumLU_wNS_ss,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- LI derives outer exhaustification for SS via the OI parse:
    ⟦SS⟧^OI = {wNS, wNSA, wSA} pins down worlds with mixed types (wNS > wS). -/
theorem li_ss_outer_exh :
    (liListener .ss li_marg_ss).fst .wNS > (liListener .ss li_marg_ss).fst .wS := by
  rw [gt_iff_lt, liListener_fst_lt, sumLI_wS_ss, sumLI_wNS_ss,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- LI also gets the wNS > wNA ordering that vanilla misses. -/
theorem li_ss_prefers_wNS :
    (liListener .ss li_marg_ss).fst .wNS > (liListener .ss li_marg_ss).fst .wNA := by
  rw [gt_iff_lt, liListener_fst_lt, sumLI_wNA_ss, sumLI_wNS_ss,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

-- ============================================================================
-- §11. Extended Truth Table Verification
-- ============================================================================

/-- NN is vacuously exhaustified: "none" is off-scale, so EXH at any
    position has no alternatives to exclude. All parses agree. -/
theorem table1_nn :
    ∀ p : Parse, allWorlds.map (exhMeaning p .nn) =
      [false, false, false, false, true, true, true] := by native_decide

/-- AN is maximally informative: all types must satisfy "drank none."
    Only wN (all N-types) works. All parses agree. -/
theorem table1_an :
    ∀ p : Parse, allWorlds.map (exhMeaning p .an) =
      [true, false, false, false, false, false, false] := by native_decide

/-- AA is maximally informative: all types must satisfy "drank all."
    Only wA works. All parses agree (already proved in aa_singleton). -/
theorem table1_aa :
    ∀ p : Parse, allWorlds.map (exhMeaning p .aa) =
      [false, false, false, false, false, false, true] := by native_decide

/-- NS lit = {wN}: "none drank some" requires no type to satisfy
    "drank some." S-types and A-types satisfy, so they must be absent.
    Only wN (all N-types) works. -/
theorem table1_ns :
    allWorlds.map (exhMeaning .none .ns) =
      [true, false, false, false, false, false, false] := by native_decide

/-- SA: "some drank all" requires ≥1 A-type. EXH_I vacuous (inner=all).
    EXH_O enriches outer "some" to "some but not all," excluding wA
    (where all types are A → "all" would hold). -/
theorem table1_sa :
    (allWorlds.map (exhMeaning .none .sa) =
      [false, false, true, true, false, true, true])
    ∧ (allWorlds.map (exhMeaning .o .sa) =
      [false, false, true, true, false, true, false]) := by
  exact ⟨by native_decide, by native_decide⟩

/-- NA: "none drank all" requires no A-types. True at {wN, wNS, wS}.
    Matrix EXH negates the stronger alternative NS (= "none drank some" =
    {wN}), removing wN. -/
theorem table1_na :
    (allWorlds.map (exhMeaning .none .na) =
      [true, true, false, false, true, false, false])
    ∧ (allWorlds.map (exhMeaning .m .na) =
      [false, true, false, false, true, false, false]) := by
  exact ⟨by native_decide, by native_decide⟩

/-- SN: "some drank none" requires ≥1 N-type. True at {wN, wNS, wNA, wNSA}.
    EXH_O enriches outer "some" to "some but not all," negating AN = {wN}.
    Matrix EXH gives the same result (M ⊆ O for SN). -/
theorem table1_sn :
    (allWorlds.map (exhMeaning .none .sn) =
      [true, true, true, true, false, false, false])
    ∧ (allWorlds.map (exhMeaning .o .sn) =
      [false, true, true, true, false, false, false]) := by
  exact ⟨by native_decide, by native_decide⟩

/-- AS: "all drank some" requires every type to satisfy "drank some."
    EXH_I enriches to "all drank [some but not all]" — only S-types satisfy,
    so only wS (all S-types) works. Matrix EXH without I negates AA,
    excluding wA (where "all drank all" holds). -/
theorem table1_as_full :
    (allWorlds.map (exhMeaning .none .as_) =
      [false, false, false, false, true, true, true])
    ∧ (allWorlds.map (exhMeaning .i .as_) =
      [false, false, false, false, true, false, false])
    ∧ (allWorlds.map (exhMeaning .m .as_) =
      [false, false, false, false, true, true, false]) := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- §12. Structural Properties
-- ============================================================================

/-- Literal meaning equals exhaustified meaning under the empty parse. -/
theorem literal_eq_exh_none : ∀ u : Utterance, ∀ w : World,
    literalMeaning u w = exhMeaning .none u w := by native_decide

/-- ⟦SS⟧^M = {wNS}: matrix EXH narrows SS to a single world.
    This is the paper's key finding (§6): the M reading "uniquely singles
    out this world state" (p. e86, eq. 22), giving GI its decisive
    advantage over LI and LU. -/
theorem m_ss_singleton : ∀ w : World,
    exhMeaning .m .ss w = (w == .wNS) := by native_decide

/-- LI cannot access M-containing parses: none of {lit, I, O, OI}
    include matrix EXH. This excludes ⟦SS⟧^M from LI's parse space. -/
theorem li_excludes_matrix : ∀ l : LIParse,
    l.toParse.hasM = false := by decide

/-- LU cannot access M-containing parses: neither lit nor OI
    include matrix EXH. This excludes ⟦SS⟧^M from LU's parse space. -/
theorem lu_excludes_matrix : ∀ l : LULex,
    l.toParse.hasM = false := by decide

/-- The latent space grows across models: 1 → 2 → 4 → 8. -/
theorem latent_space_hierarchy :
    Fintype.card Unit = 1 ∧
    Fintype.card LULex = 2 ∧
    Fintype.card LIParse = 4 ∧
    Fintype.card Parse = 8 := by decide

-- ============================================================================
-- §13. Cross-Study Bridges
-- ============================================================================

/-! ## Connection to [potts-etal-2016]

The LU model here uses latent `LULex` (2 lexica: lit, OI), the same
latent-variable architecture as [potts-etal-2016]'s weak/strong "some"
lexica. Both implement Bergen et al.'s lexical uncertainty via the pragmatic
listener's marginalisation over a latent lexicon — no special `LUScenario`
infrastructure needed. Our LU uses L1 only; the paper adds an S2/L2
layer (eqs. 14a-14b) for production predictions.

## Connection to [cremers-wilcox-spector-2023]

Cremers et al. test 9 model variants, including EXH-LU and RSA-LI, which
correspond to our LU and LI listeners (`luListener`, `liListener`). Their key
finding —
grammatical models (EXH-LU, RSA-LI) block anti-exhaustivity regardless
of prior bias — is consistent with our LU and LI predictions: both
correctly derive exhaustification for SS (`lu_ss_prefers_wNS`,
`li_ss_outer_exh`), concentrating probability on the exhaustified worlds.

## Connection to [franke-2011]

The matrix EXH in `exhMeaning` uses exh_MW: conjoin the sub-matrix meaning
with the negation of all strictly stronger alternatives' literal meanings.
[franke-2011] proves that IBR fixed points equal exh_MW for scalar
games (`Franke2011.r1_eq_exhMW_under_totality`). This grounds the matrix
position of our GI model in game-theoretic equilibrium semantics.

## Connection to [fox-2007]

The exhaustification implementation uses compositional enrichment at
inner/outer quantifier positions (scale-mate substitution on {some, all})
and MW-style sentential alternative negation at matrix position. The models
differ only in which EXH positions are available to the speaker/listener,
demonstrating that the key theoretical question is not HOW to exhaustify
but WHERE EXH can be inserted and WHO controls the insertion (grammar vs.
speaker vs. listener).

## Why GI wins (§6)

The decisive advantage of GI over LI and LU is the M parse:
`m_ss_singleton` proves ⟦SS⟧^M = {wNS}, and `li_excludes_matrix` /
`lu_excludes_matrix` prove that M-containing parses are structurally
unavailable to the smaller models. Only GI can access the reading that
uniquely identifies wNS, explaining its superior production predictions
for SS (Figure 5, Figure 7c). -/

end FrankeBergen2020
