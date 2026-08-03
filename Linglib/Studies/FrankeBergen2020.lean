import Linglib.Pragmatics.RSA.Canonical
import Linglib.Semantics.Exhaustification.InnocentExclusion
import Mathlib.Tactic.DeriveFintype

/-!
# [franke-bergen-2020] — Grammatically generated implicature readings

"Theory-driven statistical modeling for semantics and pragmatics: A case study
on grammatically generated implicature readings" compares four RSA models
([frank-goodman-2012]) of the **nested Aristotelians** "Q₁ of the aliens drank Q₂ of their water"
(Q ∈ {none, some, all}): 7 world states (which alien types — none-drinkers,
some-drinkers, all-drinkers — exist), 9 utterances, and 8 grammatical parses
(subsets of {M, O, I} EXH positions) generating the readings of the paper's
Table 1.

## The four models

The models differ in **where the parse enters the speaker function** — the
paper's central architectural contrast (its §3.3):

* **Vanilla** (§3.1): literal parse only; `PMF.posterior` over worlds.
* **LU** (§3.2): each speaker has a *fixed* lexicon `l ∈ {lit, OI}` — the parse
  is an **argument** of the speaker (eq. 11, per-lexicon normalization), and
  the listener marginalizes the latent lexicon (eqs. 12–13; `Canonical.L1`).
  Lexical uncertainty follows [bergen-levy-goodman-2016] and [potts-etal-2016];
  the paper adds an S2/L2 layer after [lassiter-goodman-2017] (eqs. 14a–14b),
  which we omit — our L1-only LU preserves the wNS-over-wNA ordering proved
  below, though the paper's LU-L2 concentrates on wNSA (eq. 15), which is why
  the paper counts SS-production data *against* LU.
* **LI** (§3.3): the speaker **chooses** an (utterance, parse) pair with
  `l ∈ {lit, I, O, OI}` — the parse is an **output** of the speaker function
  (eq. 18a): one softmax over pairs per world. The listener infers the joint
  (world, parse) from the utterance alone (`Canonical.L1Intent`).
* **GI** (§3.4): as LI but over all 8 parses (eq. 21a). The paper stresses
  (its §3.3) that enlarging LU's latent instead would be "conceptually highly
  implausible" — pair choice, not per-parse normalization, is what separates
  LI/GI from LU.

All four share the Boolean semantics `exhMeaning` and the α = 2 informativity
exponent (a modeling choice; the paper's MLEs are α ≈ 0.9–1.4). The paper's
cost term `c(u)` for *none*-initial utterances (estimated) and error term ε
(fixed at 0.045) are omitted; every prediction below is robust to this except
`vanilla_ss_prefers_wNA`, which is the paper's own cost-free illustration
(eq. 10) and reverses at the fitted cost.

## Exhaustification (appendix, defs. A1–A4)

In-situ EXH at the inner/outer quantifier conjoins with the negation of
strictly stronger lexical alternatives on the scale — only Exh(some) = "some
but not all" is non-vacuous ([fox-2007]). Matrix EXH (eq. A2) negates the
LITERAL meanings of the strictly stronger sentential alternatives (A3b: proper
subsets of the sub-matrix enriched meaning), with a noncontradictory fallback.
Sentential alternatives (A3a) substitute lexical alternatives per position:
`some ↔ all`, and `not all` for `none` (analyzed as *not some*;
[levinson-2000]) — so alternative sentences range over a fourth quantifier
`notAll` that is not itself an utterance, the paper's grammatical-vs-utterance
alternatives distinction. Including the `none ~ not all` alternative gives NN
its distinct matrix-parse row in Table 1 (the paper's fn. 7); the paper's own
comparison of this alternative construction with Gotzner & Romoli's
([gotzner-romoli-2018]) favors it by a Bayes factor of ~1,530.

## Findings

| # | Finding | Theorem |
|---|---------|---------|
| 1 | SS exhaustifies inner Q | `ss_inner_exh` |
| 2 | SS exhaustifies outer Q | `ss_outer_exh` |
| 3 | AA identifies unique world | `aa_identifies` |
| 4 | AS exhaustifies inner Q | `as_inner_exh` |
| 5 | GI's parse posterior for SS peaks at M | `ss_m_parse_pref` |
| 6 | Vanilla gets SS wrong (prefers wNA) | `vanilla_ss_prefers_wNA` |
| 7 | GI gets SS right (prefers wNS) | `gi_ss_prefers_wNS` |
| 8 | LU keeps wNS over wNA | `lu_ss_prefers_wNS` |
| 9 | LI derives outer exh for SS | `li_ss_outer_exh` |
| 10 | LI also gets SS→wNS right | `li_ss_prefers_wNS` |

Finding 5 is the model-side face of the paper's explanation of GI's win:
⟦SS⟧^M = {wNS} (`m_ss_singleton`) "uniquely singles out this world state"
(eq. 22), M-parses are unavailable to LI and LU (`li_excludes_matrix`,
`lu_excludes_matrix`), and Bayesian comparison on the paper's production +
comprehension data gives GI 0.956 posterior probability (LI 0.033, LU 0.01,
vanilla 0; the paper's Table 2). Predictions are decided by exact rational
evaluation: `RSA.Canonical.S1_eq_ofReal` reduces each speaker mass to a `ℚ`
value and each listener preference to a `ℚ` comparison closed by `norm_num`.
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

Sentential alternatives (A3a) substitute *lexical alternatives* per quantifier
position: `some ↔ all`, and `not all` for `none`. `not all` occurs only in
alternative sentences, never as an utterance — the paper's grammatical
alternatives outstrip its utterance alternatives. -/

/-- Quantifiers available in sentential alternatives: the utterance
quantifiers plus *not all*, the lexical alternative of *none*. -/
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

/-- Exhaustified meaning under a given parse.

Inner/outer EXH enrich quantifiers in situ; only "some" → "some but not all"
is non-vacuous. Matrix EXH (eq. A2) conjoins the sub-matrix meaning with the
negations of the LITERAL meanings of the strictly stronger sentential
alternatives (A3b: literal meaning a *proper* subset of the sub-matrix
enriched meaning — properness alone filters, so an utterance's own literal
meaning survives as an alternative when a parse weakens it, as for NS under
MI), falling back to the sub-matrix meaning on contradiction. -/
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

/-- Table 1, NN: matrix-free parses give {wS, wSA, wA}; matrix parses negate
the strictly stronger "none of the aliens drank not all of their water"
(= {wA}), dropping wA — the paper's fn. 7 reading, available only because
`not all` is a lexical alternative of `none`. -/
theorem table1_nn :
    (∀ p : Parse, p.hasM = false →
      allWorlds.map (exhMeaning p .nn) = [false, false, false, false, true, true, true])
    ∧ (∀ p : Parse, p.hasM = true →
      allWorlds.map (exhMeaning p .nn) = [false, false, false, false, true, true, false]) := by
  decide

/-- Table 1, NS: literal {wN}; inner EXH weakens to {wN, wNA, wA}; adding
matrix EXH then negates the sentence's own (strictly stronger) literal
meaning, giving {wNA, wA}. -/
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

/-- The paper's matrix operator (eq. A2) is **not** Fox-style innocent
exclusion ([fox-2007]): on SS's own sentential alternatives with the
OI-enriched prejacent, innocent exclusion excludes SA, AS, and AA and narrows
⟦SS⟧^OI to {wNS}, while A2's strictly-stronger filter comes up empty and MOI
keeps all of {wNS, wNSA, wSA} — witness wSA. -/
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

The per-parse speaker `speaker (w, p) ∝ L0(w | ·, p)²` (eq. 11, the parse an
*argument*) serves vanilla and LU. The LI/GI speakers (eqs. 18a/21a, the parse
an *output*) run the same power utility over (utterance, parse) *pairs*: one
softmax per world across the whole pair space, so a pair's overall
informativity — not its within-parse share — drives production. -/

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

/-- GI meaning family: an (utterance, parse) pair means its parse's reading.
The `Unit` index is the degenerate latent of the `L0OfBool` shape. -/
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

/-- LI meaning family: as `giMeaning`, over the 4 matrix-free parses. -/
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

Each listener preference reduces (uniform prior cancelling) to a comparison of
pooled speaker sums, which `S1_eq_ofReal`/`sum_S1_eq_ofReal` evaluate as exact
rationals; `norm_num` closes the resulting `ℚ` inequalities against the
partition values below. -/

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

/-- SS exhaustifies the inner quantifier: GI's listener prefers wNS (no A-type
aliens) to wNSA. -/
theorem ss_inner_exh :
    (giListener .ss gi_marg_ss).fst .wNSA < (giListener .ss gi_marg_ss).fst .wNS :=
  gi_fst_lt _ (by norm_num +decide [boolS1, boolWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wNS, zGI_wNSA])

/-- SS exhaustifies the outer quantifier: GI's listener prefers wNS (mixed
types) to wS, where "all aliens drank some but not all" would hold. -/
theorem ss_outer_exh :
    (giListener .ss gi_marg_ss).fst .wS < (giListener .ss gi_marg_ss).fst .wNS :=
  gi_fst_lt _ (by norm_num +decide [boolS1, boolWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wNS, zGI_wS])

/-- AA identifies the unique world where all aliens drank all: wA over wSA
(where AA is false under every parse). -/
theorem aa_identifies :
    (giListener .aa gi_marg_aa).fst .wSA < (giListener .aa gi_marg_aa).fst .wA :=
  gi_fst_lt _ (by norm_num +decide [boolS1, boolWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wSA, zGI_wA])

/-- AS exhaustifies the inner quantifier: GI's listener prefers wS (all aliens
are some-but-not-all drinkers) to wA. -/
theorem as_inner_exh :
    (giListener .as gi_marg_as).fst .wA < (giListener .as gi_marg_as).fst .wS :=
  gi_fst_lt _ (by norm_num +decide [boolS1, boolWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wS, zGI_wA])

/-- GI's parse posterior for SS peaks at the matrix-only parse M — the
model-side face of the paper's explanation for GI's win: ⟦SS⟧^M = {wNS}
uniquely identifies the state SS is in fact used for. Under per-parse
normalization (the LU architecture) M would rank only mid-field; pair choice
is what lets the maximally informative parse dominate. -/
theorem ss_m_parse_pref : ∀ p : Parse, p ≠ .m →
    (giListener .ss gi_marg_ss).snd p < (giListener .ss gi_marg_ss).snd .m := by
  intro p hp
  cases p
  case m => exact absurd rfl hp
  all_goals
    exact gi_snd_lt _ (by norm_num +decide [boolS1, boolWeight, giMeaning, RSA.extensionOf,
      Finset.filter_insert, Finset.filter_singleton, univW, zGI_wN, zGI_wNS, zGI_wNA,
      zGI_wNSA, zGI_wS, zGI_wSA, zGI_wA])

/-- Vanilla RSA hearing SS prefers wNA to wNS — the wrong prediction: without
exhaustification SS is literally true at 6 of 7 worlds and competing utterances
absorb wNS. The paper's cost-free illustration (eq. 10); its direction reverses
at the paper's fitted cost for *none*-initial utterances. -/
theorem vanilla_ss_prefers_wNA :
    (vanillaListener .ss vanilla_marg_ss) .wNS < (vanillaListener .ss vanilla_marg_ss) .wNA :=
  vanilla_lt _ (by norm_num +decide [boolS1, boolWeight, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univW, zNone_wNS, zNone_wNA])

/-- GI corrects vanilla's error: SS → wNS, not wNA. -/
theorem gi_ss_prefers_wNS :
    (giListener .ss gi_marg_ss).fst .wNA < (giListener .ss gi_marg_ss).fst .wNS :=
  gi_fst_lt _ (by norm_num +decide [boolS1, boolWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wNS, zGI_wNA])

/-- LU also keeps wNS above wNA: the OI lexicon's ⟦SS⟧ excludes wNA. (The
paper's full LU-L2 nonetheless concentrates on wNSA, eq. 15.) -/
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
