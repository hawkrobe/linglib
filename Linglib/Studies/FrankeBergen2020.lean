import Linglib.Pragmatics.RSA.Canonical
import Linglib.Semantics.Exhaustification.InnocentExclusion
import Mathlib.Tactic.DeriveFintype

/-!
# Franke & Bergen 2020: grammatically generated implicature readings

[franke-bergen-2020] compares four RSA models ([frank-goodman-2012]) of the
nested Aristotelians "Q₁ of the aliens drank Q₂ of their water"
(Q ∈ {none, some, all}): 7 world states (which alien types — none-, some-,
all-drinkers — exist), 9 utterances, and 8 grammatical parses (subsets of
{M, O, I} EXH positions), whose readings are the paper's Table 1
(`table1_ss` … `table1_as`). The models differ in where the parse enters the
speaker: vanilla (§3.1) has only the literal parse; LU (§3.2) fixes a lexicon
`l ∈ {lit, OI}` per speaker — the parse an *argument* of the speaker (eq. 11)
and a latent the listener marginalizes ([bergen-levy-goodman-2016],
[potts-etal-2016]); the LI (§3.3) and GI (§3.4) speakers instead *choose* an
(utterance, parse) pair (eqs. 18a/21a), over the 4 matrix-free parses resp.
all 8 — one softmax over pairs per world, read by `RSA.Canonical.L1Intent`.

We show that GI corrects the SS interpretation vanilla gets wrong
(`vanilla_ss_prefers_wNA` vs `gi_ss_prefers_wNS`), and that its parse
posterior for SS peaks at the matrix-only parse (`ss_m_parse_pref`), whose
reading ⟦SS⟧^M = {wNS} "uniquely singles out this world state" (eq. 22,
`m_ss_singleton`) and is unavailable to LI and LU (`li_excludes_matrix`,
`lu_excludes_matrix`) — the paper's explanation of GI's win in its Bayesian
model comparison (posterior 0.956 vs LI 0.033, LU 0.01, vanilla 0; Table 2).
LI and LU still derive the embedded enrichments (`li_ss_outer_exh`,
`li_ss_prefers_wNS`, `lu_ss_prefers_wNS`).

## Main results

* `table1_ss` … `table1_as` — the paper's Table 1, including NN's distinct
  matrix row (fn. 7) from the `none ~ not all` lexical alternative
  ([levinson-2000]).
* `ss_m_parse_pref` — GI's parse posterior for SS peaks at M.
* `moi_ss_ne_innocent_exclusion` — the paper's matrix operator (eq. A2) is
  not Fox-style innocent exclusion ([fox-2007]).

## Implementation notes

Sentential alternatives (A3a) range over a fourth quantifier `notAll` that is
never an utterance — the paper's grammatical-vs-utterance alternatives
distinction (its comparison with [gotzner-romoli-2018]'s alternative set
favors this one by a Bayes factor of ~1,530). We fix α = 2 and omit the
paper's cost term for *none*-initial utterances and fixed error ε = 0.045
(eqs. 25–28); each finding except `vanilla_ss_prefers_wNA` is robust to this.
The paper's S2/L2 layer for LU ([lassiter-goodman-2017], eqs. 14a–14b) is
also omitted: our L1-only LU keeps wNS over wNA, though the paper's LU-L2
concentrates on wNSA (eq. 15). Predictions are decided by exact rational
evaluation (`RSA.Canonical.S1_eq_ofReal` + `norm_num`).
-/

namespace FrankeBergen2020

open scoped ENNReal
open RSA.Canonical

/-! ### Domain -/

/-- Aristotelian quantifiers: the utterance vocabulary. -/
inductive AristQuant where
  | none | some | all
  deriving DecidableEq, Repr, Inhabited, Fintype

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
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The 9 nested Aristotelian utterances: Q_outer × Q_inner. -/
inductive Utterance where
  | nn | ns | na
  | sn | ss | sa
  | an | as | aa
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The 8 grammatical parses: subsets of {M, O, I} EXH positions. -/
inductive Parse where
  | none   -- literal (no EXH)
  | m | o | i
  | mo | mi | oi
  | moi
  deriving DecidableEq, Repr, Inhabited, Fintype

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
  | .sn | .ss | .sa => .some
  | .an | .as | .aa => .all

/-- Inner quantifier of an utterance. -/
def Utterance.inner : Utterance → AristQuant
  | .nn | .sn | .an => .none
  | .ns | .ss | .as => .some
  | .na | .sa | .aa => .all

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

/-! ### Alternative quantifiers

Sentential alternatives (A3a) substitute lexical alternatives per quantifier
position: `some ↔ all`, and `not all` for `none`. -/

/-- The quantifiers of sentential alternatives: the utterance quantifiers
plus *not all*, the lexical alternative of *none*. -/
inductive AltQuant where
  | none | some | all | notAll
  deriving DecidableEq, Repr

/-- Utterance quantifiers are alternative quantifiers. -/
def AristQuant.toAlt : AristQuant → AltQuant
  | .none => .none
  | .some => .some
  | .all => .all

/-- Scale-mate candidates at a quantifier position of a sentential
alternative: the quantifier itself and its lexical alternatives. -/
def AristQuant.altCandidates : AristQuant → List AltQuant
  | .none => [.none, .notAll]
  | .some => [.some, .all]
  | .all => [.all, .some]

/-! ### Compositional semantics -/

/-- Inner VP satisfaction: which alien types satisfy "drank Q"? -/
def AltQuant.innerTypeSat : AltQuant → Bool × Bool × Bool
  | .none => (true, false, false)
  | .some => (false, true, true)
  | .all => (false, false, true)
  | .notAll => (true, true, false)

/-- Outer quantifier evaluation: does the world satisfy "Q of the aliens
[satisfy inner VP]"? `nSat`, `sSat`, `aSat` say which alien types satisfy
the inner VP. -/
def AltQuant.outerEval (q : AltQuant) (nSat sSat aSat : Bool) (w : World) : Bool :=
  match q with
  | .none => !(w.hasN && nSat) && !(w.hasS && sSat) && !(w.hasA && aSat)
  | .some => (w.hasN && nSat) || (w.hasS && sSat) || (w.hasA && aSat)
  | .all => (!w.hasN || nSat) && (!w.hasS || sSat) && (!w.hasA || aSat)
  | .notAll => !((!w.hasN || nSat) && (!w.hasS || sSat) && (!w.hasA || aSat))

/-- A sentential alternative: a pair of alternative quantifiers. -/
abbrev AltSentence := AltQuant × AltQuant

/-- Literal meaning of a sentential alternative. -/
def altLiteral (a : AltSentence) : World → Bool :=
  let (nSat, sSat, aSat) := a.2.innerTypeSat
  a.1.outerEval nSat sSat aSat

/-- Literal meaning of an utterance. -/
def literalMeaning (u : Utterance) : World → Bool :=
  altLiteral (u.outer.toAlt, u.inner.toAlt)

/-! ### Compositional exhaustification -/

/-- All 7 worlds for enumeration. -/
def allWorlds : List World := [.wN, .wNS, .wNA, .wNSA, .wS, .wSA, .wA]

/-- Inner VP satisfaction after EXH enrichment. Only "some" is enrichable:
Exh(some) = "some but not all" — satisfied by S-types only. Exh(none) and
Exh(all) are vacuous (no strictly stronger lexical alternative). -/
def enrichedInnerTypeSat (qi : AristQuant) (hasI : Bool) : Bool × Bool × Bool :=
  if hasI && qi == .some then
    (false, true, false)  -- only S-types satisfy "some but not all"
  else
    qi.toAlt.innerTypeSat

/-- Sentential alternatives at matrix position (A3a): the cross-product of
scale-mate candidates for the two quantifier positions. -/
def matrixAlts (u : Utterance) : List AltSentence :=
  (u.outer.altCandidates.map fun o => u.inner.altCandidates.map fun i => (o, i)).flatten

/-- Exhaustified meaning under a parse. Inner/outer EXH enrich *some* to
"some but not all" in situ; matrix EXH (eq. A2) negates the literal meanings
of the strictly stronger sentential alternatives (A3b: proper subsets of the
sub-matrix meaning), falling back to the sub-matrix meaning on contradiction. -/
def exhMeaning (p : Parse) (u : Utterance) : World → Bool :=
  -- Step 1: inner predicate (enriched if I ∈ parse)
  let (nSat, sSat, aSat) := enrichedInnerTypeSat u.inner p.hasI
  -- Step 2: outer quantifier
  let base := AltQuant.outerEval u.outer.toAlt nSat sSat aSat
  -- Step 3: outer EXH (if O ∈ parse and outer Q = some): some ∧ ¬all
  let afterO :=
    if p.hasO && u.outer == .some then
      fun w => base w && !(AltQuant.outerEval .all nSat sSat aSat w)
    else base
  -- Step 4: matrix EXH (if M ∈ parse), eq. A2
  if p.hasM then
    let strongerAlts := (matrixAlts u).filter fun a =>
      allWorlds.all (fun w => !altLiteral a w || afterO w) &&
      allWorlds.any (fun w => afterO w && !altLiteral a w)
    let result : World → Bool := fun w => afterO w && strongerAlts.all fun a => !altLiteral a w
    if allWorlds.any result then result else afterO
  else afterO

/-! ### Truth-table verification (the paper's Table 1) -/

/-- EXH_I(SS): inner EXH enriches "some" to "some but not all", so the outer
"some" requires an S-type — {wNS, wNSA, wS, wSA}. -/
theorem exh_i_ss :
    allWorlds.map (exhMeaning .i .ss) = [false, true, false, true, true, true, false] := by
  decide

/-- EXH_OI(SS) = {wNS, wNSA, wSA}: outer "some but not all" alien types satisfy
the enriched inner predicate; wS drops because there all types satisfy it. -/
theorem exh_oi_ss :
    allWorlds.map (exhMeaning .oi .ss) = [false, true, false, true, false, true, false] := by
  decide

/-- EXH_MOI(SS) = EXH_OI(SS): matrix EXH is vacuous at MOI — no sentential
alternative's literal meaning is a proper subset of the OI-enriched meaning. -/
theorem exh_moi_ss : ∀ w : World, exhMeaning .moi .ss w = exhMeaning .oi .ss w := by
  decide

/-- AA is true only at wA under all parses. -/
theorem aa_singleton : ∀ p : Parse, ∀ w : World, exhMeaning p .aa w = (w == .wA) := by
  decide

/-- Table 1, SS: the four reading families (lit / I / OI / M). -/
theorem table1_ss :
    (allWorlds.map (exhMeaning .none .ss) = [false, true, true, true, true, true, true])
    ∧ (allWorlds.map (exhMeaning .i .ss) = [false, true, false, true, true, true, false])
    ∧ (allWorlds.map (exhMeaning .oi .ss) = [false, true, false, true, false, true, false])
    ∧ (allWorlds.map (exhMeaning .m .ss) = [false, true, false, false, false, false, false]) := by
  decide

/-- Table 1, NN: matrix parses additionally negate "none drank not all"
(= {wA}) — the fn. 7 reading from the `none ~ not all` alternative. -/
theorem table1_nn :
    (∀ p : Parse, p.hasM = false →
      allWorlds.map (exhMeaning p .nn) = [false, false, false, false, true, true, true])
    ∧ (∀ p : Parse, p.hasM = true →
      allWorlds.map (exhMeaning p .nn) = [false, false, false, false, true, true, false]) := by
  decide

/-- Table 1, NS: inner EXH weakens NS, so under MI matrix EXH negates the
sentence's own now-stronger literal meaning {wN} (A3b filters by properness
alone), giving {wNA, wA}. -/
theorem table1_ns :
    (allWorlds.map (exhMeaning .none .ns) = [true, false, false, false, false, false, false])
    ∧ (allWorlds.map (exhMeaning .i .ns) = [true, false, true, false, false, false, true])
    ∧ (allWorlds.map (exhMeaning .mi .ns) = [false, false, true, false, false, false, true]) := by
  decide

/-- Table 1, AN: maximally informative — only wN. All parses agree. -/
theorem table1_an : ∀ p : Parse,
    allWorlds.map (exhMeaning p .an) = [true, false, false, false, false, false, false] := by
  decide

/-- Table 1, AA: only wA. All parses agree (cf. `aa_singleton`). -/
theorem table1_aa : ∀ p : Parse,
    allWorlds.map (exhMeaning p .aa) = [false, false, false, false, false, false, true] := by
  decide

/-- Table 1, SA: "some drank all" requires an A-type; EXH_O enriches outer
"some" to "some but not all", excluding wA. -/
theorem table1_sa :
    (allWorlds.map (exhMeaning .none .sa) = [false, false, true, true, false, true, true])
    ∧ (allWorlds.map (exhMeaning .o .sa) = [false, false, true, true, false, true, false]) := by
  decide

/-- Table 1, NA: "none drank all" = {wN, wNS, wS}; matrix EXH negates the
stronger NS (= {wN}), removing wN. -/
theorem table1_na :
    (allWorlds.map (exhMeaning .none .na) = [true, true, false, false, true, false, false])
    ∧ (allWorlds.map (exhMeaning .m .na) = [false, true, false, false, true, false, false]) := by
  decide

/-- Table 1, SN: "some drank none" = {wN, wNS, wNA, wNSA}; outer EXH (or
matrix EXH) negates AN = {wN}. -/
theorem table1_sn :
    (allWorlds.map (exhMeaning .none .sn) = [true, true, true, true, false, false, false])
    ∧ (allWorlds.map (exhMeaning .o .sn) = [false, true, true, true, false, false, false]) := by
  decide

/-- Table 1, AS: "all drank some" = {wS, wSA, wA}; EXH_I narrows to wS;
matrix EXH without I negates AA, excluding wA. -/
theorem table1_as :
    (allWorlds.map (exhMeaning .none .as) = [false, false, false, false, true, true, true])
    ∧ (allWorlds.map (exhMeaning .i .as) = [false, false, false, false, true, false, false])
    ∧ (allWorlds.map (exhMeaning .m .as) = [false, false, false, false, true, true, false]) := by
  decide

/-- Literal meaning is the empty parse's exhaustified meaning. -/
theorem literal_eq_exh_none : ∀ u : Utterance, ∀ w : World,
    literalMeaning u w = exhMeaning .none u w := by decide

/-- ⟦SS⟧^M = {wNS}: matrix EXH narrows SS to a single world — the reading
that "uniquely singles out this world state" (eq. 22) and drives GI's win. -/
theorem m_ss_singleton : ∀ w : World, exhMeaning .m .ss w = (w == .wNS) := by decide

/-- The matrix operator (eq. A2) is not Fox-style innocent exclusion
([fox-2007]): at MOI its strictly-stronger filter is empty and ⟦SS⟧^MOI keeps
wSA, which innocent exclusion over the same alternatives excludes. -/
theorem moi_ss_ne_innocent_exclusion :
    exhMeaning .moi .ss .wSA = true
      ∧ World.wSA ∉ Exhaustification.innocent.exh
          (Exhaustification.altsFromPreds ((matrixAlts .ss).map altLiteral))
          (Exhaustification.predToFinset (exhMeaning .oi .ss)) := by
  decide

/-! ### Latent spaces -/

/-- LU lexicon: literal or OI (inner + outer EXH). Each speaker has a fixed
lexicon; the listener marginalizes over the two lexica. -/
inductive LULex where
  | lit | oi
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Map LU lexicon to the corresponding parse. -/
def LULex.toParse : LULex → Parse
  | .lit => .none
  | .oi => .oi

/-- LI parse: lit, I, O, or OI — matrix-EXH parses are unavailable. -/
inductive LIParse where
  | lit | i | o | oi
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Map LI parse to the full parse space. -/
def LIParse.toParse : LIParse → Parse
  | .lit => .none
  | .i => .i
  | .o => .o
  | .oi => .oi

/-- LI cannot access matrix EXH: no LI parse includes M. -/
theorem li_excludes_matrix : ∀ l : LIParse, l.toParse.hasM = false := by decide

/-- LU cannot access matrix EXH: neither lexicon includes M. -/
theorem lu_excludes_matrix : ∀ l : LULex, l.toParse.hasM = false := by decide

/-! ### Speakers

The per-parse speaker (eq. 11) serves vanilla and LU; the LI/GI speakers
(eqs. 18a/21a) run the same power utility over (utterance, parse) pairs, one
softmax per world. -/

/-- Every utterance is true at some world under every parse, so each per-parse
literal listener is well-defined. -/
theorem ext_nonempty (p : Parse) (u : Utterance) :
    (RSA.extensionOf (exhMeaning p) u).Nonempty := by cases p <;> cases u <;> decide

/-- The per-parse literal listener `L0(· | u, p)`, uniform on the extension of
`exhMeaning p u`. -/
noncomputable abbrev L0 : Parse → Utterance → PMF World :=
  L0OfBool exhMeaning ext_nonempty

/-- Every `(world, parse)` state has a true utterance. -/
theorem exists_true (w : World) (p : Parse) : ∃ u, exhMeaning p u w = true := by
  cases w <;> cases p <;> decide

noncomputable instance : ViableSpeaker (powUtility 2 L0) :=
  viableSpeaker_powUtility_of_witness 2 L0 fun s => by
    obtain ⟨u, hu⟩ := exists_true s.1 s.2
    exact ⟨u, L0OfBool_ne_zero exhMeaning ext_nonempty hu⟩

/-- The per-parse (fixed-lexicon) speaker of the vanilla and LU models. -/
noncomputable def speaker : World × Parse → PMF Utterance := S1 (powUtility 2 L0)

/-- LU speaker: the per-parse speaker re-indexed by the 2-lexicon latent. -/
noncomputable def luSpeaker (s : World × LULex) : PMF Utterance := speaker (s.1, s.2.toParse)

/-- Vanilla speaker: the per-parse speaker at the literal parse. -/
noncomputable def vanillaSpeaker (w : World) : PMF Utterance := speaker (w, .none)

/-- The GI meaning family (`Unit`-indexed to fit `L0OfBool`): an
(utterance, parse) pair means its parse's reading. -/
def giMeaning : Unit → Utterance × Parse → World → Bool := fun _ x => exhMeaning x.2 x.1

theorem gi_ext_nonempty (i : Unit) (x : Utterance × Parse) :
    (RSA.extensionOf (giMeaning i) x).Nonempty := ext_nonempty x.2 x.1

noncomputable abbrev giL0 : Unit → Utterance × Parse → PMF World :=
  L0OfBool giMeaning gi_ext_nonempty

noncomputable instance : ViableSpeaker (powUtility 2 giL0) :=
  viableSpeaker_powUtility_of_witness 2 giL0 fun s => by
    obtain ⟨u, hu⟩ := exists_true s.1 .none
    exact ⟨(u, .none), L0OfBool_ne_zero giMeaning gi_ext_nonempty hu⟩

/-- The GI speaker (eq. 21a): one softmax over all 72 (utterance, parse)
pairs at each world. -/
noncomputable def giSpeaker (w : World) : PMF (Utterance × Parse) :=
  S1 (powUtility 2 giL0) (w, ())

/-- The LI meaning family: `giMeaning` restricted to matrix-free parses. -/
def liMeaning : Unit → Utterance × LIParse → World → Bool := fun _ x => exhMeaning x.2.toParse x.1

theorem li_ext_nonempty (i : Unit) (x : Utterance × LIParse) :
    (RSA.extensionOf (liMeaning i) x).Nonempty := ext_nonempty x.2.toParse x.1

noncomputable abbrev liL0 : Unit → Utterance × LIParse → PMF World :=
  L0OfBool liMeaning li_ext_nonempty

noncomputable instance : ViableSpeaker (powUtility 2 liL0) :=
  viableSpeaker_powUtility_of_witness 2 liL0 fun s => by
    obtain ⟨u, hu⟩ := exists_true s.1 .none
    exact ⟨(u, .lit), L0OfBool_ne_zero liMeaning li_ext_nonempty hu⟩

/-- The LI speaker (eq. 18a): one softmax over the 36 (utterance, parse)
pairs with matrix-free parses. -/
noncomputable def liSpeaker (w : World) : PMF (Utterance × LIParse) :=
  S1 (powUtility 2 liL0) (w, ())

/-! ### The four pragmatic listeners -/

/-- Vanilla listener (eq. 9): posterior over worlds. -/
noncomputable def vanillaListener (u : Utterance)
    (h : PMF.marginal vanillaSpeaker (PMF.uniformOfFintype World) u ≠ 0) : PMF World :=
  PMF.posterior vanillaSpeaker (PMF.uniformOfFintype World) u h

/-- LU listener (eqs. 12–13): joint posterior over `World × LULex` — the
lexicon is part of the state, drawn with the world. -/
noncomputable def luListener (u : Utterance)
    (h : PMF.marginal luSpeaker (PMF.uniformOfFintype (World × LULex)) u ≠ 0) :
    PMF (World × LULex) :=
  L1 luSpeaker (PMF.uniformOfFintype (World × LULex)) u h

/-- LI listener (eq. 18b): posterior over `World × LIParse` from the observed
utterance component of the speaker's pair choice. -/
noncomputable def liListener (u : Utterance)
    (h : PMF.marginal (fun w => (liSpeaker w).fst) (PMF.uniformOfFintype World) u ≠ 0) :
    PMF (World × LIParse) :=
  L1Intent liSpeaker (PMF.uniformOfFintype World) u h

/-- GI listener (eq. 21b): posterior over `World × Parse` from the observed
utterance component of the speaker's pair choice. -/
noncomputable def giListener (u : Utterance)
    (h : PMF.marginal (fun w => (giSpeaker w).fst) (PMF.uniformOfFintype World) u ≠ 0) :
    PMF (World × Parse) :=
  L1Intent giSpeaker (PMF.uniformOfFintype World) u h

/-! ### Exact rational reductions

Each listener preference reduces, the uniform prior cancelling, to a pooled
speaker-sum comparison evaluated as exact rationals via `S1_eq_ofReal` and
closed by `norm_num` against the partition values below. -/

private theorem univU : (Finset.univ : Finset Utterance)
    = {.nn, .ns, .na, .sn, .ss, .sa, .an, .as, .aa} := by decide

private theorem univP : (Finset.univ : Finset Parse)
    = {.none, .m, .o, .i, .mo, .mi, .oi, .moi} := by decide

private theorem univW : (Finset.univ : Finset World)
    = {.wN, .wNS, .wNA, .wNSA, .wS, .wSA, .wA} := by decide

private theorem univLU : (Finset.univ : Finset LULex) = {.lit, .oi} := by decide

private theorem univLI : (Finset.univ : Finset LIParse) = {.lit, .i, .o, .oi} := by decide

/-! GI partitions `Z(w) = Σ_{(u,p)} |ext(u,p)|⁻²` over the 72 pairs. -/

private theorem zGI_wN : boolPartition giMeaning 2 () World.wN = 307/24 := by
  norm_num +decide [boolPartition, boolWeight, giMeaning, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univP, univW]

private theorem zGI_wNS : boolPartition giMeaning 2 () World.wNS = 23/6 := by
  norm_num +decide [boolPartition, boolWeight, giMeaning, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univP, univW]

private theorem zGI_wNA : boolPartition giMeaning 2 () World.wNA = 23/9 := by
  norm_num +decide [boolPartition, boolWeight, giMeaning, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univP, univW]

private theorem zGI_wNSA : boolPartition giMeaning 2 () World.wNSA = 157/72 := by
  norm_num +decide [boolPartition, boolWeight, giMeaning, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univP, univW]

private theorem zGI_wS : boolPartition giMeaning 2 () World.wS = 559/72 := by
  norm_num +decide [boolPartition, boolWeight, giMeaning, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univP, univW]

private theorem zGI_wSA : boolPartition giMeaning 2 () World.wSA = 10/3 := by
  norm_num +decide [boolPartition, boolWeight, giMeaning, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univP, univW]

private theorem zGI_wA : boolPartition giMeaning 2 () World.wA = 229/24 := by
  norm_num +decide [boolPartition, boolWeight, giMeaning, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univP, univW]

/-! LI partitions over the 36 matrix-free pairs. -/

private theorem zLI_wNS : boolPartition liMeaning 2 () World.wNS = 53/48 := by
  norm_num +decide [boolPartition, boolWeight, liMeaning, LIParse.toParse, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univLI, univW]

private theorem zLI_wNA : boolPartition liMeaning 2 () World.wNA = 19/18 := by
  norm_num +decide [boolPartition, boolWeight, liMeaning, LIParse.toParse, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univLI, univW]

private theorem zLI_wS : boolPartition liMeaning 2 () World.wS = 461/144 := by
  norm_num +decide [boolPartition, boolWeight, liMeaning, LIParse.toParse, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univLI, univW]

/-! Per-parse partitions (vanilla and LU). -/

private theorem zNone_wNS : boolPartition exhMeaning 2 (.none : Parse) World.wNS = 29/144 := by
  norm_num +decide [boolPartition, boolWeight, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univU, univW]

private theorem zNone_wNA : boolPartition exhMeaning 2 (.none : Parse) World.wNA = 11/72 := by
  norm_num +decide [boolPartition, boolWeight, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univU, univW]

private theorem zOI_wNS : boolPartition exhMeaning 2 (.oi : Parse) World.wNS = 1/3 := by
  norm_num +decide [boolPartition, boolWeight, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univU, univW]

private theorem zOI_wNA : boolPartition exhMeaning 2 (.oi : Parse) World.wNA = 1/3 := by
  norm_num +decide [boolPartition, boolWeight, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univU, univW]

/-! Pooled speaker sums in `ofReal`-of-`ℚ` form. -/

private theorem gi_sum_eq (w : World) (u : Utterance) :
    (∑ p : Parse, giSpeaker w (u, p))
      = ENNReal.ofReal (∑ p : Parse, boolS1 giMeaning 2 () w (u, p)) :=
  sum_S1_eq_ofReal giMeaning gi_ext_nonempty (by norm_num) Finset.univ
    (fun _ => (w, ())) (fun p => (u, p))

private theorem gi_sumW_eq (p : Parse) (u : Utterance) :
    (∑ w : World, giSpeaker w (u, p))
      = ENNReal.ofReal (∑ w : World, boolS1 giMeaning 2 () w (u, p)) :=
  sum_S1_eq_ofReal giMeaning gi_ext_nonempty (by norm_num) Finset.univ
    (fun w => (w, ())) (fun _ => (u, p))

private theorem li_sum_eq (w : World) (u : Utterance) :
    (∑ l : LIParse, liSpeaker w (u, l))
      = ENNReal.ofReal (∑ l : LIParse, boolS1 liMeaning 2 () w (u, l)) :=
  sum_S1_eq_ofReal liMeaning li_ext_nonempty (by norm_num) Finset.univ
    (fun _ => (w, ())) (fun l => (u, l))

private theorem speaker_eq (p : Parse) (w : World) (u : Utterance) :
    speaker (w, p) u = ENNReal.ofReal (boolS1 exhMeaning 2 p w u) :=
  S1_eq_ofReal exhMeaning ext_nonempty (by norm_num) p w u

private theorem lu_sum_eq (w : World) (u : Utterance) :
    (∑ l : LULex, luSpeaker (w, l) u)
      = ENNReal.ofReal (boolS1 exhMeaning 2 (.none : Parse) w u
          + boolS1 exhMeaning 2 (.oi : Parse) w u) := by
  rw [show (Finset.univ : Finset LULex) = {.lit, .oi} from univLU,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  show speaker (w, .none) u + speaker (w, .oi) u = _
  rw [speaker_eq, speaker_eq,
    ← ENNReal.ofReal_add (by exact_mod_cast boolS1_nonneg exhMeaning 2 _ w u)
      (by exact_mod_cast boolS1_nonneg exhMeaning 2 _ w u)]

private theorem vanilla_eq (w : World) (u : Utterance) :
    vanillaSpeaker w u = ENNReal.ofReal (boolS1 exhMeaning 2 (.none : Parse) w u) :=
  S1_eq_ofReal exhMeaning ext_nonempty (by norm_num) .none w u

/-! Listener-preference reductions to `ℚ`. -/

private theorem gi_fst_lt {u : Utterance} (h) {w₁ w₂ : World}
    (hq : (∑ p : Parse, boolS1 giMeaning 2 () w₁ (u, p))
        < ∑ p : Parse, boolS1 giMeaning 2 () w₂ (u, p)) :
    (giListener u h).fst w₁ < (giListener u h).fst w₂ := by
  have h₀ : (0 : ℚ) ≤ ∑ p : Parse, boolS1 giMeaning 2 () w₁ (u, p) :=
    Finset.sum_nonneg fun p _ => boolS1_nonneg giMeaning 2 () w₁ (u, p)
  rw [giListener, L1Intent_uniform_world_prefers_iff, gi_sum_eq, gi_sum_eq,
    ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast lt_of_le_of_lt h₀ hq)]
  exact_mod_cast hq

private theorem gi_snd_lt {u : Utterance} (h) {p₁ p₂ : Parse}
    (hq : (∑ w : World, boolS1 giMeaning 2 () w (u, p₁))
        < ∑ w : World, boolS1 giMeaning 2 () w (u, p₂)) :
    (giListener u h).snd p₁ < (giListener u h).snd p₂ := by
  have h₀ : (0 : ℚ) ≤ ∑ w : World, boolS1 giMeaning 2 () w (u, p₁) :=
    Finset.sum_nonneg fun w _ => boolS1_nonneg giMeaning 2 () w (u, p₁)
  rw [giListener, L1Intent_uniform_latent_prefers_iff, gi_sumW_eq, gi_sumW_eq,
    ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast lt_of_le_of_lt h₀ hq)]
  exact_mod_cast hq

private theorem li_fst_lt {u : Utterance} (h) {w₁ w₂ : World}
    (hq : (∑ l : LIParse, boolS1 liMeaning 2 () w₁ (u, l))
        < ∑ l : LIParse, boolS1 liMeaning 2 () w₂ (u, l)) :
    (liListener u h).fst w₁ < (liListener u h).fst w₂ := by
  have h₀ : (0 : ℚ) ≤ ∑ l : LIParse, boolS1 liMeaning 2 () w₁ (u, l) :=
    Finset.sum_nonneg fun l _ => boolS1_nonneg liMeaning 2 () w₁ (u, l)
  rw [liListener, L1Intent_uniform_world_prefers_iff, li_sum_eq, li_sum_eq,
    ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast lt_of_le_of_lt h₀ hq)]
  exact_mod_cast hq

private theorem lu_fst_lt {u : Utterance} (h) {w₁ w₂ : World}
    (hq : boolS1 exhMeaning 2 (.none : Parse) w₁ u + boolS1 exhMeaning 2 (.oi : Parse) w₁ u
        < boolS1 exhMeaning 2 (.none : Parse) w₂ u + boolS1 exhMeaning 2 (.oi : Parse) w₂ u) :
    (luListener u h).fst w₁ < (luListener u h).fst w₂ := by
  have h₀ : (0 : ℚ) ≤ boolS1 exhMeaning 2 (.none : Parse) w₁ u
      + boolS1 exhMeaning 2 (.oi : Parse) w₁ u :=
    add_nonneg (boolS1_nonneg exhMeaning 2 _ w₁ u) (boolS1_nonneg exhMeaning 2 _ w₁ u)
  rw [luListener, L1_uniform_world_prefers_iff, lu_sum_eq, lu_sum_eq,
    ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast lt_of_le_of_lt h₀ hq)]
  exact_mod_cast hq

private theorem vanilla_lt {u : Utterance} (h) {w₁ w₂ : World}
    (hq : boolS1 exhMeaning 2 (.none : Parse) w₁ u < boolS1 exhMeaning 2 (.none : Parse) w₂ u) :
    (vanillaListener u h) w₁ < (vanillaListener u h) w₂ := by
  have h₀ : (0 : ℚ) ≤ boolS1 exhMeaning 2 (.none : Parse) w₁ u :=
    boolS1_nonneg exhMeaning 2 _ w₁ u
  rw [vanillaListener, PMF.posterior_lt_iff_kernel_lt_of_uniform, vanilla_eq, vanilla_eq,
    ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast lt_of_le_of_lt h₀ hq)]
  exact_mod_cast hq

/-! ### Marginal-nonzero witnesses -/

theorem gi_marg_ss :
    PMF.marginal (fun w => (giSpeaker w).fst) (PMF.uniformOfFintype World) .ss ≠ 0 :=
  L1Intent_uniform_marginal_ne_zero giSpeaker
    (show giSpeaker .wNS (.ss, .none) ≠ 0 from
      S1_L0OfBool_ne_zero giMeaning gi_ext_nonempty (by decide))

theorem gi_marg_aa :
    PMF.marginal (fun w => (giSpeaker w).fst) (PMF.uniformOfFintype World) .aa ≠ 0 :=
  L1Intent_uniform_marginal_ne_zero giSpeaker
    (show giSpeaker .wA (.aa, .none) ≠ 0 from
      S1_L0OfBool_ne_zero giMeaning gi_ext_nonempty (by decide))

theorem gi_marg_as :
    PMF.marginal (fun w => (giSpeaker w).fst) (PMF.uniformOfFintype World) .as ≠ 0 :=
  L1Intent_uniform_marginal_ne_zero giSpeaker
    (show giSpeaker .wS (.as, .none) ≠ 0 from
      S1_L0OfBool_ne_zero giMeaning gi_ext_nonempty (by decide))

theorem li_marg_ss :
    PMF.marginal (fun w => (liSpeaker w).fst) (PMF.uniformOfFintype World) .ss ≠ 0 :=
  L1Intent_uniform_marginal_ne_zero liSpeaker
    (show liSpeaker .wNS (.ss, .lit) ≠ 0 from
      S1_L0OfBool_ne_zero liMeaning li_ext_nonempty (by decide))

theorem lu_marg_ss :
    PMF.marginal luSpeaker (PMF.uniformOfFintype (World × LULex)) .ss ≠ 0 :=
  PMF.marginal_ne_zero luSpeaker (PMF.uniformOfFintype (World × LULex)) .ss
    (a := (.wNS, .lit))
    (((PMF.uniformOfFintype (World × LULex)).mem_support_iff (.wNS, .lit)).mp
      (PMF.mem_support_uniformOfFintype _))
    (show speaker (.wNS, .none) .ss ≠ 0 from
      S1_L0OfBool_ne_zero exhMeaning ext_nonempty (by decide))

theorem vanilla_marg_ss :
    PMF.marginal vanillaSpeaker (PMF.uniformOfFintype World) .ss ≠ 0 :=
  PMF.marginal_ne_zero vanillaSpeaker (PMF.uniformOfFintype World) .ss (a := .wNS)
    (((PMF.uniformOfFintype World).mem_support_iff .wNS).mp
      (PMF.mem_support_uniformOfFintype _))
    (show speaker (.wNS, .none) .ss ≠ 0 from
      S1_L0OfBool_ne_zero exhMeaning ext_nonempty (by decide))

/-! ### The ten qualitative findings -/

/-- SS exhaustifies the inner quantifier: GI's listener prefers wNS to wNSA. -/
theorem ss_inner_exh :
    (giListener .ss gi_marg_ss).fst .wNSA < (giListener .ss gi_marg_ss).fst .wNS :=
  gi_fst_lt _ (by norm_num +decide [boolS1, boolWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wNS, zGI_wNSA])

/-- SS exhaustifies the outer quantifier: GI's listener prefers wNS to wS. -/
theorem ss_outer_exh :
    (giListener .ss gi_marg_ss).fst .wS < (giListener .ss gi_marg_ss).fst .wNS :=
  gi_fst_lt _ (by norm_num +decide [boolS1, boolWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wNS, zGI_wS])

/-- AA identifies the unique world where all aliens drank all: wA over wSA. -/
theorem aa_identifies :
    (giListener .aa gi_marg_aa).fst .wSA < (giListener .aa gi_marg_aa).fst .wA :=
  gi_fst_lt _ (by norm_num +decide [boolS1, boolWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wSA, zGI_wA])

/-- AS exhaustifies the inner quantifier: GI's listener prefers wS to wA. -/
theorem as_inner_exh :
    (giListener .as gi_marg_as).fst .wA < (giListener .as gi_marg_as).fst .wS :=
  gi_fst_lt _ (by norm_num +decide [boolS1, boolWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wS, zGI_wA])

/-- GI's parse posterior for SS peaks at the matrix-only parse, whose reading
uniquely identifies wNS (eq. 22). Pair choice drives this: under per-parse
normalization M would not dominate. -/
theorem ss_m_parse_pref : ∀ p : Parse, p ≠ .m →
    (giListener .ss gi_marg_ss).snd p < (giListener .ss gi_marg_ss).snd .m := by
  intro p hp
  cases p
  case m => exact absurd rfl hp
  all_goals
    exact gi_snd_lt _ (by norm_num +decide [boolS1, boolWeight, giMeaning, RSA.extensionOf,
      Finset.filter_insert, Finset.filter_singleton, univW, zGI_wN, zGI_wNS, zGI_wNA,
      zGI_wNSA, zGI_wS, zGI_wSA, zGI_wA])

/-- Vanilla RSA hearing SS prefers wNA to wNS — the wrong prediction (the
cost-free illustration of eq. 10; the direction reverses at the fitted cost). -/
theorem vanilla_ss_prefers_wNA :
    (vanillaListener .ss vanilla_marg_ss) .wNS < (vanillaListener .ss vanilla_marg_ss) .wNA :=
  vanilla_lt _ (by norm_num +decide [boolS1, boolWeight, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univW, zNone_wNS, zNone_wNA])

/-- GI corrects vanilla's error: SS → wNS, not wNA. -/
theorem gi_ss_prefers_wNS :
    (giListener .ss gi_marg_ss).fst .wNA < (giListener .ss gi_marg_ss).fst .wNS :=
  gi_fst_lt _ (by norm_num +decide [boolS1, boolWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wNS, zGI_wNA])

/-- LU also keeps wNS above wNA: the OI lexicon's ⟦SS⟧ excludes wNA (the
paper's full LU-L2 nonetheless concentrates on wNSA, eq. 15). -/
theorem lu_ss_prefers_wNS :
    (luListener .ss lu_marg_ss).fst .wNA < (luListener .ss lu_marg_ss).fst .wNS :=
  lu_fst_lt _ (by norm_num +decide [boolS1, boolWeight, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univW,
    zNone_wNS, zNone_wNA, zOI_wNS, zOI_wNA])

/-- LI derives outer exhaustification for SS: wNS over wS via the OI parse. -/
theorem li_ss_outer_exh :
    (liListener .ss li_marg_ss).fst .wS < (liListener .ss li_marg_ss).fst .wNS :=
  li_fst_lt _ (by norm_num +decide [boolS1, boolWeight, liMeaning, LIParse.toParse,
    RSA.extensionOf, Finset.filter_insert, Finset.filter_singleton, univLI, univW,
    zLI_wNS, zLI_wS])

/-- LI also gets the wNS-over-wNA ordering that vanilla misses. -/
theorem li_ss_prefers_wNS :
    (liListener .ss li_marg_ss).fst .wNA < (liListener .ss li_marg_ss).fst .wNS :=
  li_fst_lt _ (by norm_num +decide [boolS1, boolWeight, liMeaning, LIParse.toParse,
    RSA.extensionOf, Finset.filter_insert, Finset.filter_singleton, univLI, univW,
    zLI_wNS, zLI_wNA])

end FrankeBergen2020
