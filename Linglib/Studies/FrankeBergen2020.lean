import Linglib.Pragmatics.RSA.Canonical
import Linglib.Pragmatics.Implicature.SomeAll
import Linglib.Semantics.Exhaustification.InnocentExclusion
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic.DeriveFintype

/-!
# Franke & Bergen 2020: grammatically generated implicature readings

[franke-bergen-2020] compares four RSA models ([frank-goodman-2012]) of the
nested Aristotelians "Q₁ of the aliens drank Q₂ of their water"
(Q ∈ {none, some, all}). An alien's drinking amount is a `SomeAllWorld`; a
world state is the nonempty set of amounts realized by at least one alien
(7 states); a parse is the set of EXH insertion sites among matrix/outer/inner
(8 parses); the readings are the paper's Table 1 (`table1_ss` … `table1_as`,
each row characterized by a membership predicate). The models differ in where
the parse enters the speaker: vanilla (§3.1) has only the literal parse; LU
(§3.2) fixes a lexicon `l ∈ {lit, OI}` per speaker — the parse an *argument*
of the speaker (eq. 11) and a latent the listener marginalizes
([bergen-levy-goodman-2016], [potts-etal-2016]); the LI (§3.3) and GI (§3.4)
speakers instead *choose* an (utterance, parse) pair (eqs. 18a/21a), over the
4 matrix-free parses resp. all 8 — one softmax over pairs per world, read by
`RSA.Canonical.L1Intent`.

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

/-- An alien's drinking amount: none, some but not all, or all of its water. -/
abbrev AlienType := SomeAllWorld

/-- A world state is the set of drinking amounts realized by at least one
alien — a nonempty subset of the three amounts. -/
def World := {s : Finset AlienType // s.Nonempty}

instance : DecidableEq World := Subtype.instDecidableEq
instance : Fintype World := Subtype.fintype _

/-- The seven world states, named by the alien types present: N drank none,
S drank some but not all, A drank all. -/
def wN : World := ⟨{.none}, Finset.singleton_nonempty _⟩
def wNS : World := ⟨{.none, .someNotAll}, by decide⟩
def wNA : World := ⟨{.none, .all}, by decide⟩
def wNSA : World := ⟨{.none, .someNotAll, .all}, by decide⟩
def wS : World := ⟨{.someNotAll}, Finset.singleton_nonempty _⟩
def wSA : World := ⟨{.someNotAll, .all}, by decide⟩
def wA : World := ⟨{.all}, Finset.singleton_nonempty _⟩

instance : Nonempty World := ⟨wN⟩

/-- EXH insertion sites: applying to the whole sentence, the outer
quantifier, or the inner quantifier. -/
inductive ExhPosition where
  | matrix | outer | inner
  deriving DecidableEq, Fintype

/-- A parse is the set of EXH insertion sites. -/
abbrev Parse := Finset ExhPosition

/-- Aristotelian quantifiers: the utterance vocabulary. -/
inductive AristQuant where
  | none | some | all
  deriving DecidableEq, Repr, Fintype

/-- The 9 nested Aristotelian utterances, named outer-then-inner:
`.ns` is "None of the aliens drank some of their water". -/
inductive Utterance where
  | nn | ns | na
  | sn | ss | sa
  | an | as | aa
  deriving DecidableEq, Repr, Fintype

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

/-! ### Alternative quantifiers

Sentential alternatives (A3a) substitute lexical alternatives per quantifier
position: `some ↔ all`, and `not all` for `none`. -/

/-- The quantifiers of sentential alternatives: the utterance quantifiers
plus *not all*, the lexical alternative of *none*. -/
inductive AltQuant where
  | none | some | all | notAll
  deriving DecidableEq, Repr

instance : Coe AristQuant AltQuant where
  coe
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

/-- Satisfaction of "drank Q" by an alien of a given amount, via the
`SomeAllWorld` meanings. -/
def AltQuant.sat : AltQuant → AlienType → Prop
  | .none => fun t => ¬ t.atLeastOne
  | .some => SomeAllWorld.atLeastOne
  | .all => SomeAllWorld.universal
  | .notAll => SomeAllWorld.notUniversal

instance : ∀ q : AltQuant, DecidablePred q.sat
  | .none, _ => inferInstanceAs (Decidable ¬ _)
  | .some, t => inferInstanceAs (Decidable (SomeAllWorld.atLeastOne t))
  | .all, t => inferInstanceAs (Decidable (SomeAllWorld.universal t))
  | .notAll, t => inferInstanceAs (Decidable (SomeAllWorld.notUniversal t))

/-- Quantifier denotation over the alien types realized in a world. -/
def AltQuant.eval : AltQuant → World → (AlienType → Prop) → Prop
  | .none, w, sat => ∀ t ∈ w.val, ¬ sat t
  | .some, w, sat => ∃ t ∈ w.val, sat t
  | .all, w, sat => ∀ t ∈ w.val, sat t
  | .notAll, w, sat => ¬ ∀ t ∈ w.val, sat t

instance : ∀ (q : AltQuant) (w : World) (sat : AlienType → Prop) [DecidablePred sat],
    Decidable (q.eval w sat)
  | .none, _, _, _ => inferInstanceAs (Decidable (∀ _ ∈ _, ¬ _))
  | .some, _, _, _ => inferInstanceAs (Decidable (∃ _ ∈ _, _))
  | .all, _, _, _ => inferInstanceAs (Decidable (∀ _ ∈ _, _))
  | .notAll, _, _, _ => inferInstanceAs (Decidable (¬ ∀ _ ∈ _, _))

/-- *not all* is the negation of *all* — definitionally, where the Bool
version transcribed the negated clause by hand. -/
theorem eval_notAll_iff (w : World) (sat : AlienType → Prop) :
    AltQuant.eval .notAll w sat ↔ ¬ AltQuant.eval .all w sat := Iff.rfl

/-- *none* is the negation of *some*. -/
theorem eval_none_iff (w : World) (sat : AlienType → Prop) :
    AltQuant.eval .none w sat ↔ ¬ AltQuant.eval .some w sat := by
  simp [AltQuant.eval]

/-- A sentential alternative: a pair of alternative quantifiers. -/
abbrev AltSentence := AltQuant × AltQuant

/-- Literal meaning of a sentential alternative. -/
def altLiteral (a : AltSentence) (w : World) : Prop := a.1.eval w a.2.sat

instance (a : AltSentence) : DecidablePred (altLiteral a) := fun _ =>
  inferInstanceAs (Decidable (AltQuant.eval _ _ _))

/-- Literal meaning of an utterance. -/
def literalMeaning (u : Utterance) : World → Prop := altLiteral (↑u.outer, ↑u.inner)

instance (u : Utterance) : DecidablePred (literalMeaning u) :=
  inferInstanceAs (DecidablePred (altLiteral _))

/-! ### Compositional exhaustification -/

/-- Sentential alternatives at matrix position (A3a): scale-mate candidates
at the two quantifier positions. -/
def matrixAlts (u : Utterance) : List AltSentence :=
  u.outer.altCandidates ×ˢ u.inner.altCandidates

/-- Inner satisfaction after EXH enrichment: Exh(some) = "some but not all",
the `.someNotAll` amount exactly; Exh(none) and Exh(all) are vacuous. -/
def enrichedSat (qi : AristQuant) (p : Parse) : AlienType → Prop :=
  if ExhPosition.inner ∈ p ∧ qi = .some then
    fun t => t.atLeastOne ∧ t.notUniversal
  else (↑qi : AltQuant).sat

instance (qi : AristQuant) (p : Parse) : DecidablePred (enrichedSat qi p) := fun t => by
  unfold enrichedSat; split <;> infer_instance

/-- The sub-matrix reading: in-situ enrichments, with outer EXH (Exh(some) at
the outer position) as an implication guard. -/
def subMatrix (p : Parse) (u : Utterance) (w : World) : Prop :=
  AltQuant.eval (↑u.outer) w (enrichedSat u.inner p)
  ∧ (ExhPosition.outer ∈ p ∧ u.outer = .some →
      ¬ AltQuant.eval .all w (enrichedSat u.inner p))

instance (p : Parse) (u : Utterance) : DecidablePred (subMatrix p u) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- A sentential alternative is strictly stronger than the sub-matrix reading
(A3b: proper subset — an utterance's own literal meaning qualifies when a
parse weakens it, as for NS under MI). -/
def StrictlyStronger (p : Parse) (u : Utterance) (a : AltSentence) : Prop :=
  (∀ w, altLiteral a w → subMatrix p u w) ∧ ∃ w, subMatrix p u w ∧ ¬ altLiteral a w

instance (p : Parse) (u : Utterance) (a : AltSentence) :
    Decidable (StrictlyStronger p u a) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The matrix-exhaustified reading: the sub-matrix reading with every
strictly stronger sentential alternative's literal meaning negated. -/
def matrixExh (p : Parse) (u : Utterance) (w : World) : Prop :=
  subMatrix p u w ∧ ∀ a ∈ matrixAlts u, StrictlyStronger p u a → ¬ altLiteral a w

instance (p : Parse) (u : Utterance) : DecidablePred (matrixExh p u) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- Exhaustified meaning under a parse: the matrix-exhaustified reading when
M is in the parse and that reading is noncontradictory, else the sub-matrix
reading (eq. A2). -/
def exhMeaning (p : Parse) (u : Utterance) (w : World) : Prop :=
  if ExhPosition.matrix ∈ p ∧ ∃ w', matrixExh p u w' then matrixExh p u w
  else subMatrix p u w

instance (p : Parse) (u : Utterance) : DecidablePred (exhMeaning p u) := fun w => by
  unfold exhMeaning; split <;> infer_instance

/-! ### Truth-table verification (the paper's Table 1)

Each reading is characterized by a membership predicate on the world's
alien-type set, rather than transcribed as a truth vector. -/

/-- Table 1, SS: literal true except at wN; inner EXH requires an S-type;
outer EXH additionally excludes wS; matrix EXH pins wNS. -/
theorem table1_ss :
    (∀ w, exhMeaning ∅ .ss w ↔ w ≠ wN)
    ∧ (∀ w, exhMeaning {.inner} .ss w ↔ .someNotAll ∈ w.val)
    ∧ (∀ w, exhMeaning {.outer, .inner} .ss w ↔ (.someNotAll ∈ w.val ∧ w ≠ wS))
    ∧ (∀ w, exhMeaning {.matrix} .ss w ↔ w = wNS) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- EXH_MOI(SS) = EXH_OI(SS): matrix EXH is vacuous at MOI. -/
theorem exh_moi_ss : ∀ w,
    exhMeaning {.matrix, .outer, .inner} .ss w ↔ exhMeaning {.outer, .inner} .ss w := by
  decide

/-- Table 1, NN: no N-types; matrix parses additionally negate "none drank
not all" (= {wA}) — the fn. 7 reading from the `none ~ not all` alternative. -/
theorem table1_nn :
    (∀ p : Parse, .matrix ∉ p → ∀ w, exhMeaning p .nn w ↔ .none ∉ w.val)
    ∧ (∀ p : Parse, .matrix ∈ p → ∀ w, exhMeaning p .nn w ↔ (.none ∉ w.val ∧ w ≠ wA)) :=
  ⟨by decide, by decide⟩

/-- Table 1, NS: inner EXH weakens NS to the S-free worlds, so under MI
matrix EXH negates the sentence's own now-stronger literal meaning {wN}. -/
theorem table1_ns :
    (∀ w, exhMeaning ∅ .ns w ↔ w = wN)
    ∧ (∀ w, exhMeaning {.inner} .ns w ↔ .someNotAll ∉ w.val)
    ∧ (∀ w, exhMeaning {.matrix, .inner} .ns w ↔ (.someNotAll ∉ w.val ∧ w ≠ wN)) :=
  ⟨by decide, by decide, by decide⟩

/-- Table 1, AN: only wN, under every parse. -/
theorem table1_an : ∀ p : Parse, ∀ w, exhMeaning p .an w ↔ w = wN := by decide

/-- Table 1, AA: only wA, under every parse. -/
theorem table1_aa : ∀ p : Parse, ∀ w, exhMeaning p .aa w ↔ w = wA := by decide

/-- Table 1, SA: an A-type exists; outer EXH excludes wA. -/
theorem table1_sa :
    (∀ w, exhMeaning ∅ .sa w ↔ .all ∈ w.val)
    ∧ (∀ w, exhMeaning {.outer} .sa w ↔ (.all ∈ w.val ∧ w ≠ wA)) :=
  ⟨by decide, by decide⟩

/-- Table 1, NA: no A-types; matrix EXH negates the stronger NS = {wN}. -/
theorem table1_na :
    (∀ w, exhMeaning ∅ .na w ↔ .all ∉ w.val)
    ∧ (∀ w, exhMeaning {.matrix} .na w ↔ (.all ∉ w.val ∧ w ≠ wN)) :=
  ⟨by decide, by decide⟩

/-- Table 1, SN: an N-type exists; outer EXH negates AN = {wN}. -/
theorem table1_sn :
    (∀ w, exhMeaning ∅ .sn w ↔ .none ∈ w.val)
    ∧ (∀ w, exhMeaning {.outer} .sn w ↔ (.none ∈ w.val ∧ w ≠ wN)) :=
  ⟨by decide, by decide⟩

/-- Table 1, AS: no N-types; inner EXH pins wS; matrix EXH without I
negates AA, excluding wA. -/
theorem table1_as :
    (∀ w, exhMeaning ∅ .as w ↔ .none ∉ w.val)
    ∧ (∀ w, exhMeaning {.inner} .as w ↔ w = wS)
    ∧ (∀ w, exhMeaning {.matrix} .as w ↔ (.none ∉ w.val ∧ w ≠ wA)) :=
  ⟨by decide, by decide, by decide⟩

/-- Literal meaning is the empty parse's exhaustified meaning. -/
theorem literal_eq_exh_none : ∀ u : Utterance, ∀ w,
    literalMeaning u w ↔ exhMeaning ∅ u w := by decide

/-- ⟦SS⟧^M = {wNS}: matrix EXH narrows SS to a single world — the reading
that "uniquely singles out this world state" (eq. 22) and drives GI's win. -/
theorem m_ss_singleton : ∀ w, exhMeaning {.matrix} .ss w ↔ w = wNS :=
  table1_ss.2.2.2

/-- The matrix operator (eq. A2) is not Fox-style innocent exclusion
([fox-2007]): at MOI its strictly-stronger filter is empty and ⟦SS⟧^MOI keeps
wSA, which innocent exclusion over the same alternatives excludes. -/
theorem moi_ss_ne_innocent_exclusion :
    exhMeaning {.matrix, .outer, .inner} .ss wSA
      ∧ wSA ∉ Exhaustification.innocent.exh
          (Exhaustification.altsFromPreds
            ((matrixAlts .ss).map fun a w => decide (altLiteral a w)))
          (Exhaustification.predToFinset
            fun w => decide (exhMeaning {.outer, .inner} .ss w)) :=
  ⟨by decide, by decide⟩

/-! ### Latent spaces -/

/-- LU lexicon: literal or OI (inner + outer EXH). Each speaker has a fixed
lexicon; the listener marginalizes over the two lexica. -/
inductive LULex where
  | lit | oi
  deriving DecidableEq, Repr, Fintype

instance : Nonempty LULex := ⟨.lit⟩

/-- Map LU lexicon to the corresponding parse. -/
def LULex.toParse : LULex → Parse
  | .lit => ∅
  | .oi => {.outer, .inner}

/-- LI parse: lit, I, O, or OI — matrix-EXH parses are unavailable. -/
inductive LIParse where
  | lit | i | o | oi
  deriving DecidableEq, Repr, Fintype

/-- Map LI parse to the full parse space. -/
def LIParse.toParse : LIParse → Parse
  | .lit => ∅
  | .i => {.inner}
  | .o => {.outer}
  | .oi => {.outer, .inner}

/-- LI cannot access matrix EXH: no LI parse includes M. -/
theorem li_excludes_matrix : ∀ l : LIParse, .matrix ∉ l.toParse := by decide

/-- LU cannot access matrix EXH: neither lexicon includes M. -/
theorem lu_excludes_matrix : ∀ l : LULex, .matrix ∉ l.toParse := by decide

/-! ### Speakers

The per-parse speaker (eq. 11) serves vanilla and LU; the LI/GI speakers
(eqs. 18a/21a) run the same power utility over (utterance, parse) pairs, one
softmax per world. -/

/-- Every utterance is true at some world under every parse, so each per-parse
literal listener is well-defined. -/
theorem ext_nonempty : ∀ (p : Parse) (u : Utterance),
    (RSA.extensionOf (exhMeaning p) u).Nonempty := by decide

/-- The per-parse literal listener `L0(· | u, p)`, uniform on the extension of
`exhMeaning p u`. -/
noncomputable abbrev L0 : Parse → Utterance → PMF World :=
  L0OfPred exhMeaning ext_nonempty

/-- Every `(world, parse)` state has a true utterance. -/
theorem exists_true : ∀ (w : World) (p : Parse), ∃ u, exhMeaning p u w := by decide

noncomputable instance : ViableSpeaker (powUtility 2 L0) :=
  viableSpeaker_powUtility_of_witness 2 L0 fun s => by
    obtain ⟨u, hu⟩ := exists_true s.1 s.2
    exact ⟨u, L0OfPred_ne_zero exhMeaning ext_nonempty hu⟩

/-- The per-parse (fixed-lexicon) speaker of the vanilla and LU models. -/
noncomputable def speaker : World × Parse → PMF Utterance := S1 (powUtility 2 L0)

/-- LU speaker: the per-parse speaker re-indexed by the 2-lexicon latent. -/
noncomputable def luSpeaker (s : World × LULex) : PMF Utterance := speaker (s.1, s.2.toParse)

/-- Vanilla speaker: the per-parse speaker at the literal parse. -/
noncomputable def vanillaSpeaker (w : World) : PMF Utterance := speaker (w, ∅)

/-- The GI meaning family (`Unit`-indexed to fit `L0OfPred`): an
(utterance, parse) pair means its parse's reading. -/
def giMeaning : Unit → Utterance × Parse → World → Prop := fun _ x => exhMeaning x.2 x.1

instance (i : Unit) (x : Utterance × Parse) : DecidablePred (giMeaning i x) :=
  inferInstanceAs (DecidablePred (exhMeaning x.2 x.1))

theorem gi_ext_nonempty (i : Unit) (x : Utterance × Parse) :
    (RSA.extensionOf (giMeaning i) x).Nonempty := ext_nonempty x.2 x.1

noncomputable abbrev giL0 : Unit → Utterance × Parse → PMF World :=
  L0OfPred giMeaning gi_ext_nonempty

noncomputable instance : ViableSpeaker (powUtility 2 giL0) :=
  viableSpeaker_powUtility_of_witness 2 giL0 fun s => by
    obtain ⟨u, hu⟩ := exists_true s.1 ∅
    exact ⟨(u, ∅), L0OfPred_ne_zero giMeaning gi_ext_nonempty hu⟩

/-- The GI speaker (eq. 21a): one softmax over all 72 (utterance, parse)
pairs at each world. -/
noncomputable def giSpeaker (w : World) : PMF (Utterance × Parse) :=
  S1 (powUtility 2 giL0) (w, ())

/-- The LI meaning family: `giMeaning` restricted to matrix-free parses. -/
def liMeaning : Unit → Utterance × LIParse → World → Prop :=
  fun _ x => exhMeaning x.2.toParse x.1

instance (i : Unit) (x : Utterance × LIParse) : DecidablePred (liMeaning i x) :=
  inferInstanceAs (DecidablePred (exhMeaning x.2.toParse x.1))

theorem li_ext_nonempty (i : Unit) (x : Utterance × LIParse) :
    (RSA.extensionOf (liMeaning i) x).Nonempty := ext_nonempty x.2.toParse x.1

noncomputable abbrev liL0 : Unit → Utterance × LIParse → PMF World :=
  L0OfPred liMeaning li_ext_nonempty

noncomputable instance : ViableSpeaker (powUtility 2 liL0) :=
  viableSpeaker_powUtility_of_witness 2 liL0 fun s => by
    obtain ⟨u, hu⟩ := exists_true s.1 ∅
    exact ⟨(u, .lit), L0OfPred_ne_zero liMeaning li_ext_nonempty hu⟩

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
    = {∅, {.matrix}, {.outer}, {.inner}, {.matrix, .outer}, {.matrix, .inner},
       {.outer, .inner}, {.matrix, .outer, .inner}} := by decide

private theorem univW : (Finset.univ : Finset World)
    = {wN, wNS, wNA, wNSA, wS, wSA, wA} := by decide

private theorem univLU : (Finset.univ : Finset LULex) = {.lit, .oi} := by decide

private theorem univLI : (Finset.univ : Finset LIParse) = {.lit, .i, .o, .oi} := by decide

/-! GI partitions `Z(w) = Σ_{(u,p)} |ext(u,p)|⁻²` over the 72 pairs. -/

private theorem zGI_wN : ratPartition giMeaning 2 () wN = 307/24 := by
  norm_num +decide [ratPartition, ratWeight, giMeaning, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univP, univW]

private theorem zGI_wNS : ratPartition giMeaning 2 () wNS = 23/6 := by
  norm_num +decide [ratPartition, ratWeight, giMeaning, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univP, univW]

private theorem zGI_wNA : ratPartition giMeaning 2 () wNA = 23/9 := by
  norm_num +decide [ratPartition, ratWeight, giMeaning, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univP, univW]

private theorem zGI_wNSA : ratPartition giMeaning 2 () wNSA = 157/72 := by
  norm_num +decide [ratPartition, ratWeight, giMeaning, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univP, univW]

private theorem zGI_wS : ratPartition giMeaning 2 () wS = 559/72 := by
  norm_num +decide [ratPartition, ratWeight, giMeaning, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univP, univW]

private theorem zGI_wSA : ratPartition giMeaning 2 () wSA = 10/3 := by
  norm_num +decide [ratPartition, ratWeight, giMeaning, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univP, univW]

private theorem zGI_wA : ratPartition giMeaning 2 () wA = 229/24 := by
  norm_num +decide [ratPartition, ratWeight, giMeaning, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univP, univW]

/-! LI partitions over the 36 matrix-free pairs. -/

private theorem zLI_wNS : ratPartition liMeaning 2 () wNS = 53/48 := by
  norm_num +decide [ratPartition, ratWeight, liMeaning, LIParse.toParse, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univLI, univW]

private theorem zLI_wNA : ratPartition liMeaning 2 () wNA = 19/18 := by
  norm_num +decide [ratPartition, ratWeight, liMeaning, LIParse.toParse, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univLI, univW]

private theorem zLI_wS : ratPartition liMeaning 2 () wS = 461/144 := by
  norm_num +decide [ratPartition, ratWeight, liMeaning, LIParse.toParse, RSA.extensionOf,
    Fintype.sum_prod_type, Finset.filter_insert, Finset.filter_singleton, univU, univLI, univW]

/-! Per-parse partitions (vanilla and LU). -/

private theorem zNone_wNS : ratPartition exhMeaning 2 (∅ : Parse) wNS = 29/144 := by
  norm_num +decide [ratPartition, ratWeight, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univU, univW]

private theorem zNone_wNA : ratPartition exhMeaning 2 (∅ : Parse) wNA = 11/72 := by
  norm_num +decide [ratPartition, ratWeight, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univU, univW]

private theorem zOI_wNS : ratPartition exhMeaning 2 ({.outer, .inner} : Parse) wNS = 1/3 := by
  norm_num +decide [ratPartition, ratWeight, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univU, univW]

private theorem zOI_wNA : ratPartition exhMeaning 2 ({.outer, .inner} : Parse) wNA = 1/3 := by
  norm_num +decide [ratPartition, ratWeight, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univU, univW]

/-! Pooled speaker sums in `ofReal`-of-`ℚ` form. -/

private theorem gi_sum_eq (w : World) (u : Utterance) :
    (∑ p : Parse, giSpeaker w (u, p))
      = ENNReal.ofReal (∑ p : Parse, ratS1 giMeaning 2 () w (u, p)) :=
  sum_S1_eq_ofReal giMeaning gi_ext_nonempty (by norm_num) Finset.univ
    (fun _ => (w, ())) (fun p => (u, p))

private theorem gi_sumW_eq (p : Parse) (u : Utterance) :
    (∑ w : World, giSpeaker w (u, p))
      = ENNReal.ofReal (∑ w : World, ratS1 giMeaning 2 () w (u, p)) :=
  sum_S1_eq_ofReal giMeaning gi_ext_nonempty (by norm_num) Finset.univ
    (fun w => (w, ())) (fun _ => (u, p))

private theorem li_sum_eq (w : World) (u : Utterance) :
    (∑ l : LIParse, liSpeaker w (u, l))
      = ENNReal.ofReal (∑ l : LIParse, ratS1 liMeaning 2 () w (u, l)) :=
  sum_S1_eq_ofReal liMeaning li_ext_nonempty (by norm_num) Finset.univ
    (fun _ => (w, ())) (fun l => (u, l))

private theorem speaker_eq (p : Parse) (w : World) (u : Utterance) :
    speaker (w, p) u = ENNReal.ofReal (ratS1 exhMeaning 2 p w u) :=
  S1_eq_ofReal exhMeaning ext_nonempty (by norm_num) p w u

private theorem lu_sum_eq (w : World) (u : Utterance) :
    (∑ l : LULex, luSpeaker (w, l) u)
      = ENNReal.ofReal (ratS1 exhMeaning 2 (∅ : Parse) w u
          + ratS1 exhMeaning 2 ({.outer, .inner} : Parse) w u) := by
  rw [show (Finset.univ : Finset LULex) = {.lit, .oi} from univLU,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  show speaker (w, ∅) u + speaker (w, {.outer, .inner}) u = _
  rw [speaker_eq, speaker_eq,
    ← ENNReal.ofReal_add (by exact_mod_cast ratS1_nonneg exhMeaning 2 _ w u)
      (by exact_mod_cast ratS1_nonneg exhMeaning 2 _ w u)]

/-! Listener-preference reductions to `ℚ`. -/

private theorem gi_fst_lt {u : Utterance} (h) {w₁ w₂ : World}
    (hq : (∑ p : Parse, ratS1 giMeaning 2 () w₁ (u, p))
        < ∑ p : Parse, ratS1 giMeaning 2 () w₂ (u, p)) :
    (giListener u h).fst w₁ < (giListener u h).fst w₂ := by
  have h₀ : (0 : ℚ) ≤ ∑ p : Parse, ratS1 giMeaning 2 () w₁ (u, p) :=
    Finset.sum_nonneg fun p _ => ratS1_nonneg giMeaning 2 () w₁ (u, p)
  rw [giListener, L1Intent_uniform_world_prefers_iff, gi_sum_eq, gi_sum_eq,
    ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast lt_of_le_of_lt h₀ hq)]
  exact_mod_cast hq

private theorem gi_snd_lt {u : Utterance} (h) {p₁ p₂ : Parse}
    (hq : (∑ w : World, ratS1 giMeaning 2 () w (u, p₁))
        < ∑ w : World, ratS1 giMeaning 2 () w (u, p₂)) :
    (giListener u h).snd p₁ < (giListener u h).snd p₂ := by
  have h₀ : (0 : ℚ) ≤ ∑ w : World, ratS1 giMeaning 2 () w (u, p₁) :=
    Finset.sum_nonneg fun w _ => ratS1_nonneg giMeaning 2 () w (u, p₁)
  rw [giListener, L1Intent_uniform_latent_prefers_iff, gi_sumW_eq, gi_sumW_eq,
    ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast lt_of_le_of_lt h₀ hq)]
  exact_mod_cast hq

private theorem li_fst_lt {u : Utterance} (h) {w₁ w₂ : World}
    (hq : (∑ l : LIParse, ratS1 liMeaning 2 () w₁ (u, l))
        < ∑ l : LIParse, ratS1 liMeaning 2 () w₂ (u, l)) :
    (liListener u h).fst w₁ < (liListener u h).fst w₂ := by
  have h₀ : (0 : ℚ) ≤ ∑ l : LIParse, ratS1 liMeaning 2 () w₁ (u, l) :=
    Finset.sum_nonneg fun l _ => ratS1_nonneg liMeaning 2 () w₁ (u, l)
  rw [liListener, L1Intent_uniform_world_prefers_iff, li_sum_eq, li_sum_eq,
    ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast lt_of_le_of_lt h₀ hq)]
  exact_mod_cast hq

private theorem lu_fst_lt {u : Utterance} (h) {w₁ w₂ : World}
    (hq : ratS1 exhMeaning 2 (∅ : Parse) w₁ u
          + ratS1 exhMeaning 2 ({.outer, .inner} : Parse) w₁ u
        < ratS1 exhMeaning 2 (∅ : Parse) w₂ u
          + ratS1 exhMeaning 2 ({.outer, .inner} : Parse) w₂ u) :
    (luListener u h).fst w₁ < (luListener u h).fst w₂ := by
  have h₀ : (0 : ℚ) ≤ ratS1 exhMeaning 2 (∅ : Parse) w₁ u
      + ratS1 exhMeaning 2 ({.outer, .inner} : Parse) w₁ u :=
    add_nonneg (ratS1_nonneg exhMeaning 2 _ w₁ u) (ratS1_nonneg exhMeaning 2 _ w₁ u)
  rw [luListener, L1_uniform_world_prefers_iff, lu_sum_eq, lu_sum_eq,
    ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast lt_of_le_of_lt h₀ hq)]
  exact_mod_cast hq

private theorem vanilla_lt {u : Utterance} (h) {w₁ w₂ : World}
    (hq : ratS1 exhMeaning 2 (∅ : Parse) w₁ u < ratS1 exhMeaning 2 (∅ : Parse) w₂ u) :
    (vanillaListener u h) w₁ < (vanillaListener u h) w₂ := by
  have h₀ : (0 : ℚ) ≤ ratS1 exhMeaning 2 (∅ : Parse) w₁ u :=
    ratS1_nonneg exhMeaning 2 _ w₁ u
  rw [vanillaListener, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  show speaker (w₁, ∅) u < speaker (w₂, ∅) u
  rw [speaker_eq, speaker_eq,
    ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast lt_of_le_of_lt h₀ hq)]
  exact_mod_cast hq

/-! ### Marginal-nonzero witnesses -/

theorem gi_marg_ss :
    PMF.marginal (fun w => (giSpeaker w).fst) (PMF.uniformOfFintype World) .ss ≠ 0 :=
  L1Intent_uniform_marginal_ne_zero giSpeaker
    (show giSpeaker wNS (.ss, ∅) ≠ 0 from
      S1_L0OfPred_ne_zero giMeaning gi_ext_nonempty (by decide))

theorem gi_marg_aa :
    PMF.marginal (fun w => (giSpeaker w).fst) (PMF.uniformOfFintype World) .aa ≠ 0 :=
  L1Intent_uniform_marginal_ne_zero giSpeaker
    (show giSpeaker wA (.aa, ∅) ≠ 0 from
      S1_L0OfPred_ne_zero giMeaning gi_ext_nonempty (by decide))

theorem gi_marg_as :
    PMF.marginal (fun w => (giSpeaker w).fst) (PMF.uniformOfFintype World) .as ≠ 0 :=
  L1Intent_uniform_marginal_ne_zero giSpeaker
    (show giSpeaker wS (.as, ∅) ≠ 0 from
      S1_L0OfPred_ne_zero giMeaning gi_ext_nonempty (by decide))

theorem li_marg_ss :
    PMF.marginal (fun w => (liSpeaker w).fst) (PMF.uniformOfFintype World) .ss ≠ 0 :=
  L1Intent_uniform_marginal_ne_zero liSpeaker
    (show liSpeaker wNS (.ss, .lit) ≠ 0 from
      S1_L0OfPred_ne_zero liMeaning li_ext_nonempty (by decide))

theorem lu_marg_ss :
    PMF.marginal luSpeaker (PMF.uniformOfFintype (World × LULex)) .ss ≠ 0 :=
  PMF.marginal_ne_zero luSpeaker (PMF.uniformOfFintype (World × LULex)) .ss
    (a := (wNS, .lit))
    (((PMF.uniformOfFintype (World × LULex)).mem_support_iff (wNS, .lit)).mp
      (PMF.mem_support_uniformOfFintype _))
    (show speaker (wNS, ∅) .ss ≠ 0 from
      S1_L0OfPred_ne_zero exhMeaning ext_nonempty (by decide))

theorem vanilla_marg_ss :
    PMF.marginal vanillaSpeaker (PMF.uniformOfFintype World) .ss ≠ 0 :=
  PMF.marginal_ne_zero vanillaSpeaker (PMF.uniformOfFintype World) .ss (a := wNS)
    (((PMF.uniformOfFintype World).mem_support_iff wNS).mp
      (PMF.mem_support_uniformOfFintype _))
    (show speaker (wNS, ∅) .ss ≠ 0 from
      S1_L0OfPred_ne_zero exhMeaning ext_nonempty (by decide))

/-! ### The ten qualitative findings -/

/-- SS exhaustifies the inner quantifier: GI's listener prefers wNS to wNSA. -/
theorem ss_inner_exh :
    (giListener .ss gi_marg_ss).fst wNSA < (giListener .ss gi_marg_ss).fst wNS :=
  gi_fst_lt _ (by norm_num +decide [ratS1, ratWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wNS, zGI_wNSA])

/-- SS exhaustifies the outer quantifier: GI's listener prefers wNS to wS. -/
theorem ss_outer_exh :
    (giListener .ss gi_marg_ss).fst wS < (giListener .ss gi_marg_ss).fst wNS :=
  gi_fst_lt _ (by norm_num +decide [ratS1, ratWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wNS, zGI_wS])

/-- AA identifies the unique world where all aliens drank all: wA over wSA. -/
theorem aa_identifies :
    (giListener .aa gi_marg_aa).fst wSA < (giListener .aa gi_marg_aa).fst wA :=
  gi_fst_lt _ (by norm_num +decide [ratS1, ratWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wSA, zGI_wA])

/-- AS exhaustifies the inner quantifier: GI's listener prefers wS to wA. -/
theorem as_inner_exh :
    (giListener .as gi_marg_as).fst wA < (giListener .as gi_marg_as).fst wS :=
  gi_fst_lt _ (by norm_num +decide [ratS1, ratWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wS, zGI_wA])

/-- GI's parse posterior for SS peaks at the matrix-only parse, whose reading
uniquely identifies wNS (eq. 22). Pair choice drives this: under per-parse
normalization M would not dominate. -/
theorem ss_m_parse_pref : ∀ p : Parse, p ≠ {.matrix} →
    (giListener .ss gi_marg_ss).snd p < (giListener .ss gi_marg_ss).snd {.matrix} := by
  have key : ∀ p ∈ ({∅, {.outer}, {.inner}, {.matrix, .outer}, {.matrix, .inner},
      {.outer, .inner}, {.matrix, .outer, .inner}} : Finset Parse),
      (giListener .ss gi_marg_ss).snd p < (giListener .ss gi_marg_ss).snd {.matrix} := by
    intro p hp
    fin_cases hp <;>
      exact gi_snd_lt _ (by norm_num +decide [ratS1, ratWeight, giMeaning, RSA.extensionOf,
        Finset.filter_insert, Finset.filter_singleton, univW, zGI_wN, zGI_wNS, zGI_wNA,
        zGI_wNSA, zGI_wS, zGI_wSA, zGI_wA])
  intro p hp
  refine key p ?_
  have hu : p ∈ (Finset.univ : Finset Parse) := Finset.mem_univ p
  rw [univP] at hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
  tauto

/-- Vanilla RSA hearing SS prefers wNA to wNS — the wrong prediction (the
cost-free illustration of eq. 10; the direction reverses at the fitted cost). -/
theorem vanilla_ss_prefers_wNA :
    (vanillaListener .ss vanilla_marg_ss) wNS < (vanillaListener .ss vanilla_marg_ss) wNA :=
  vanilla_lt _ (by norm_num +decide [ratS1, ratWeight, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univW, zNone_wNS, zNone_wNA])

/-- GI corrects vanilla's error: SS → wNS, not wNA. -/
theorem gi_ss_prefers_wNS :
    (giListener .ss gi_marg_ss).fst wNA < (giListener .ss gi_marg_ss).fst wNS :=
  gi_fst_lt _ (by norm_num +decide [ratS1, ratWeight, giMeaning, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univP, univW, zGI_wNS, zGI_wNA])

/-- LU also keeps wNS above wNA: the OI lexicon's ⟦SS⟧ excludes wNA (the
paper's full LU-L2 nonetheless concentrates on wNSA, eq. 15). -/
theorem lu_ss_prefers_wNS :
    (luListener .ss lu_marg_ss).fst wNA < (luListener .ss lu_marg_ss).fst wNS :=
  lu_fst_lt _ (by norm_num +decide [ratS1, ratWeight, RSA.extensionOf,
    Finset.filter_insert, Finset.filter_singleton, univW,
    zNone_wNS, zNone_wNA, zOI_wNS, zOI_wNA])

/-- LI derives outer exhaustification for SS: wNS over wS via the OI parse. -/
theorem li_ss_outer_exh :
    (liListener .ss li_marg_ss).fst wS < (liListener .ss li_marg_ss).fst wNS :=
  li_fst_lt _ (by norm_num +decide [ratS1, ratWeight, liMeaning, LIParse.toParse,
    RSA.extensionOf, Finset.filter_insert, Finset.filter_singleton, univLI, univW,
    zLI_wNS, zLI_wS])

/-- LI also gets the wNS-over-wNA ordering that vanilla misses. -/
theorem li_ss_prefers_wNS :
    (liListener .ss li_marg_ss).fst wNA < (liListener .ss li_marg_ss).fst wNS :=
  li_fst_lt _ (by norm_num +decide [ratS1, ratWeight, liMeaning, LIParse.toParse,
    RSA.extensionOf, Finset.filter_insert, Finset.filter_singleton, univLI, univW,
    zLI_wNS, zLI_wNA])

end FrankeBergen2020
