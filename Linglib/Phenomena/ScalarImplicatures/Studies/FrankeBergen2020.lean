import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Tactics.RSAPredict
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# @cite{franke-bergen-2020} — GI-RSA for Nested Aristotelians
@cite{franke-bergen-2020} @cite{fox-2007} @cite{franke-2011}

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
lexical alternatives on the {some, all} scale (@cite{fox-2007}). Only
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

All four models from the paper are formalized as `RSAConfig` instances
differing only in `Latent` type:
- **Vanilla** (§3.1): `Latent := Unit` — literal semantics only
- **LU** (§3.2): `Latent := LULex` (2 lexica) — simplified to L1
  (the paper adds an S2/L2 layer, eqs. 14a-14b, following
  @cite{potts-etal-2016}; our L1-only approximation suffices for
  qualitative predictions)
- **LI** (§3.3): `Latent := LIParse` (4 parses) — speaker chooses parse
- **GI** (§3.4): `Latent := Parse` (8 parses) — full parse space

Bayesian model comparison: GI achieves 0.956 posterior probability,
LI = 0.033, LU = 0.010, vanilla = 0.
-/

set_option autoImplicit false

namespace Phenomena.ScalarImplicatures.Studies.FrankeBergen2020

open Real (rpow rpow_nonneg)

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Aristotelian quantifiers: none, some, all. -/
inductive AristQuant where
  | none : AristQuant
  | some_ : AristQuant
  | all : AristQuant
  deriving DecidableEq, BEq, Repr, Inhabited

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
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype World where
  elems := {.wN, .wNS, .wNA, .wNSA, .wS, .wSA, .wA}
  complete := fun x => by cases x <;> simp

/-- The 9 nested Aristotelian utterances: Q_outer × Q_inner. -/
inductive Utterance where
  | nn | ns | na
  | sn | ss | sa
  | an | as_ | aa
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype Utterance where
  elems := {.nn, .ns, .na, .sn, .ss, .sa, .an, .as_, .aa}
  complete := fun x => by cases x <;> simp

/-- The 8 grammatical parses: subsets of {M, O, I} EXH positions. -/
inductive Parse where
  | none   -- literal (no EXH)
  | m | o | i
  | mo | mi | oi
  | moi
  deriving DecidableEq, BEq, Repr, Inhabited

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
-- §6. GI-RSA Config
-- ============================================================================

/-- GI-RSA model for nested Aristotelians.
    Parse is the latent variable; meaning under each parse is determined
    by compositional exhaustification. α = 2 is a modeling choice
    for qualitative predictions (the paper estimates α ≈ 1.3 jointly with
    cost and error parameters). -/
noncomputable def giConfig : RSA.RSAConfig Utterance World where
  Latent := Parse
  meaning _ p u w := if exhMeaning p u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _p w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos
  worldPrior_nonneg := fun _ => le_of_lt one_pos

-- ============================================================================
-- §7. Predictions
-- ============================================================================

/-- SS exhaustifies inner quantifier: L1 prefers wNS (N and S types, no A)
    over wNSA (all three types including A). Inner EXH negates "some drank all",
    disfavoring worlds with A-type aliens. -/
theorem ss_inner_exh :
    giConfig.L1 .ss .wNS > giConfig.L1 .ss .wNSA := by
  rsa_predict

/-- SS exhaustifies outer quantifier: L1 prefers wNS (mixed N+S types)
    over wS (only S-type). At wS, "all aliens drank some but not all" would
    be true, but outer EXH negates the "all" reading, preferring worlds where
    not all alien types are uniform. -/
theorem ss_outer_exh :
    giConfig.L1 .ss .wNS > giConfig.L1 .ss .wS := by
  rsa_predict

/-- AA correctly identifies the unique world where all aliens drank all. -/
theorem aa_identifies :
    giConfig.L1 .aa .wA > giConfig.L1 .aa .wSA := by
  rsa_predict

/-- AS exhaustifies inner: L1 prefers wS (all aliens are "some" drinkers)
    over wA (all aliens are "all" drinkers). -/
theorem as_inner_exh :
    giConfig.L1 .as_ .wS > giConfig.L1 .as_ .wA := by
  rsa_predict

set_option maxHeartbeats 1600000 in
/-- Full exhaustification is preferred: L1 assigns more probability to the
    fully exhaustified parse (MOI) than to the literal parse for SS. -/
theorem ss_parse_pref :
    giConfig.L1_latent .ss .moi > giConfig.L1_latent .ss .none := by
  rsa_predict

-- ============================================================================
-- §8. Alternative Models (§3.1–§3.3)
-- ============================================================================

/-- Vanilla RSA (§3.1): literal semantics only, no grammatical enrichment.
    Each utterance has a single reading; no latent parse variable. -/
noncomputable def vanillaConfig : RSA.RSAConfig Utterance World where
  meaning _ _ u w := if literalMeaning u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos
  worldPrior_nonneg := fun _ => le_of_lt one_pos

/-- LU lexicon: literal or OI (inner + outer EXH). Each speaker has a
    fixed lexicon; listeners marginalize over the two lexica to infer
    the world state. Mirrors the @cite{potts-etal-2016} architecture
    (Latent := Lexicon). -/
inductive LULex where
  | lit | oi
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype LULex where
  elems := {.lit, .oi}
  complete := fun x => by cases x <;> simp

/-- Map LU lexicon to the corresponding Parse. -/
def LULex.toParse : LULex → Parse
  | .lit => .none | .oi => .oi

/-- Lexical Uncertainty model (§3.2): speaker has a fixed lexicon (lit or
    OI), listener marginalizes over lexica. Simplified to L1 — the paper
    adds an S2/L2 layer (eqs. 14a-14b) for production predictions. -/
noncomputable def luConfig : RSA.RSAConfig Utterance World where
  Latent := LULex
  meaning _ l u w := if exhMeaning l.toParse u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos
  worldPrior_nonneg := fun _ => le_of_lt one_pos

/-- LI parse: lit, I, O, or OI. The speaker actively chooses a parse per
    utterance (unlike LU, where each speaker has a fixed lexicon). -/
inductive LIParse where
  | lit | i | o | oi
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Fintype LIParse where
  elems := {.lit, .i, .o, .oi}
  complete := fun x => by cases x <;> simp

/-- Map LI parse to the full Parse type. -/
def LIParse.toParse : LIParse → Parse
  | .lit => .none | .i => .i | .o => .o | .oi => .oi

/-- Lexical Intentions model (§3.3): speaker chooses (utterance, parse)
    jointly from {lit, I, O, OI}, listener marginalizes over parses. -/
noncomputable def liConfig : RSA.RSAConfig Utterance World where
  Latent := LIParse
  meaning _ l u w := if exhMeaning l.toParse u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos
  worldPrior_nonneg := fun _ => le_of_lt one_pos

-- ============================================================================
-- §9. Cross-Model Comparisons
-- ============================================================================

/-! The paper's key empirical finding: GI predicts SS→wNS (the state where
    N-types and S-types coexist), matching production data. Vanilla RSA
    cannot access the exhaustified reading ⟦SS⟧^MOI = {wNS, wNSA, wSA}
    and instead predicts wNA (N+A types) for hearing SS. -/

/-- Vanilla RSA hearing SS: prefers wNA over wNS. Without exhaustification,
    SS is literally true at 6/7 worlds. At wNA, the competing utterances
    (SN, SA) are less informative than at wNS (where NA is a strong
    competitor), so SS "wins" more of the S1 score at wNA.

    This is the wrong prediction — production data shows SS is used
    for state wNS, not wNA. Evidence for grammatical enrichment. -/
theorem vanilla_ss_prefers_wNA :
    vanillaConfig.L1 .ss .wNA > vanillaConfig.L1 .ss .wNS := by
  rsa_predict

/-- GI correctly predicts the opposite: SS→wNS, not wNA.
    The exhaustified parses concentrate probability on worlds with
    S-types but not A-types, overriding the literal-meaning signal. -/
theorem gi_ss_prefers_wNS :
    giConfig.L1 .ss .wNS > giConfig.L1 .ss .wNA := by
  rsa_predict

/-- LU also gets the key SS prediction right: wNS > wNA. The OI lexicon
    gives ⟦SS⟧^OI = {wNS, wNSA, wSA}, which excludes wNA. The lit lexicon
    includes both, but OI's exclusion of wNA is enough to tip the balance.
    Same architecture as @cite{potts-etal-2016} (Latent := Lexicon). -/
theorem lu_ss_prefers_wNS :
    luConfig.L1 .ss .wNS > luConfig.L1 .ss .wNA := by
  rsa_predict

/-- LI derives outer exhaustification for SS via the OI parse:
    ⟦SS⟧^OI = {wNS, wNSA, wSA} pins down worlds with mixed types. -/
theorem li_ss_outer_exh :
    liConfig.L1 .ss .wNS > liConfig.L1 .ss .wS := by
  rsa_predict

/-- LI also gets the wNS > wNA ordering that vanilla misses. -/
theorem li_ss_prefers_wNS :
    liConfig.L1 .ss .wNS > liConfig.L1 .ss .wNA := by
  rsa_predict

-- ============================================================================
-- §10. Extended Truth Table Verification
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
-- §11. Structural Properties
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
-- §12. Cross-Study Bridges
-- ============================================================================

/-! ## Connection to @cite{potts-etal-2016}

The LU model here uses Latent := LULex (2 lexica: lit, OI), the same
RSAConfig architecture as @cite{potts-etal-2016}'s Latent := Lexicon
(weak, strong "some"). Both implement Bergen et al.'s lexical uncertainty
via RSAConfig's latent variable mechanism — no special `LUScenario`
infrastructure needed. Our LU uses L1 only; the paper adds an S2/L2
layer (eqs. 14a-14b) for production predictions.

## Connection to @cite{cremers-wilcox-spector-2023}

Cremers et al. test 9 model variants, including EXH-LU and RSA-LI, which
correspond to our `luConfig` and `liConfig`. Their key finding —
grammatical models (EXH-LU, RSA-LI) block anti-exhaustivity regardless
of prior bias — is consistent with our LU and LI predictions: both
correctly derive exhaustification for SS (`lu_ss_prefers_wNS`,
`li_ss_outer_exh`), concentrating probability on the exhaustified worlds.

## Connection to @cite{franke-2011}

The matrix EXH in `exhMeaning` uses exh_MW: conjoin the sub-matrix meaning
with the negation of all strictly stronger alternatives' literal meanings.
@cite{franke-2011} proves that IBR fixed points equal exh_MW for scalar
games (`Franke2011.r1_eq_exhMW_under_totality`). This grounds the matrix
position of our GI model in game-theoretic equilibrium semantics.

## Connection to @cite{fox-2007}

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

end Phenomena.ScalarImplicatures.Studies.FrankeBergen2020
