import Linglib.Pragmatics.RSA.Basic
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
(8 parses); the readings are the paper's Table 1 (the `table1_*` lemmas, one
per row, each characterized by a membership predicate). The models differ in where
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

* `table1_*` — the paper's Table 1, one lemma per row, including NN's
  distinct matrix row (fn. 7) from the `none ~ not all` lexical alternative
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
open MeasureTheory ProbabilityTheory

/-! ### Domain -/

/-- An alien's drinking amount: none, some but not all, or all of its water. -/
abbrev AlienType := SomeAllWorld

/-- A world state is the set of drinking amounts realized by at least one
alien — a nonempty subset of the three amounts. -/
def World := {s : Finset AlienType // s.Nonempty}

instance : DecidableEq World := Subtype.instDecidableEq
instance : Fintype World := Subtype.fintype _

instance : Membership AlienType World := ⟨fun w t => t ∈ w.val⟩

instance (t : AlienType) (w : World) : Decidable (t ∈ w) :=
  inferInstanceAs (Decidable (t ∈ w.val))

/-- The world with only N-type aliens (each drank none). -/
def wN : World := ⟨{.none}, Finset.singleton_nonempty _⟩
/-- The world with N-type and S-type aliens. -/
def wNS : World := ⟨{.none, .someNotAll}, by decide⟩
/-- The world with N-type and A-type aliens. -/
def wNA : World := ⟨{.none, .all}, by decide⟩
/-- The world with all three alien types. -/
def wNSA : World := ⟨{.none, .someNotAll, .all}, by decide⟩
/-- The world with only S-type aliens (each drank some but not all). -/
def wS : World := ⟨{.someNotAll}, Finset.singleton_nonempty _⟩
/-- The world with S-type and A-type aliens. -/
def wSA : World := ⟨{.someNotAll, .all}, by decide⟩
/-- The world with only A-type aliens (each drank all). -/
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
  | .none, w, sat => ∀ t ∈ w, ¬ sat t
  | .some, w, sat => ∃ t ∈ w, sat t
  | .all, w, sat => ∀ t ∈ w, sat t
  | .notAll, w, sat => ¬ ∀ t ∈ w, sat t

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

/-- Inner satisfaction after EXH enrichment: when licensed, EXH conjoins
*some* with its not-all implicature — the `.someNotAll` amount exactly;
Exh(none) and Exh(all) are vacuous. -/
def enrichedSat (qi : AristQuant) (p : Parse) (t : AlienType) : Prop :=
  (↑qi : AltQuant).sat t ∧ (ExhPosition.inner ∈ p ∧ qi = .some → t.notUniversal)

instance (qi : AristQuant) (p : Parse) : DecidablePred (enrichedSat qi p) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

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

/-- Exhaustified meaning under a parse: the sub-matrix reading, negating the
strictly stronger alternatives when M is in the parse and doing so is
noncontradictory (eq. A2). -/
def exhMeaning (p : Parse) (u : Utterance) (w : World) : Prop :=
  subMatrix p u w ∧ (ExhPosition.matrix ∈ p ∧ (∃ w', matrixExh p u w') →
    ∀ a ∈ matrixAlts u, StrictlyStronger p u a → ¬ altLiteral a w)

instance (p : Parse) (u : Utterance) : DecidablePred (exhMeaning p u) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Truth-table verification (the paper's Table 1)

Each reading is characterized by a membership predicate on the world's
alien-type set, rather than transcribed as a truth vector. -/

/-- Table 1, SS literal row: true everywhere but wN. -/
theorem table1_ss_lit : ∀ w, exhMeaning ∅ .ss w ↔ w ≠ wN := by decide

/-- Table 1, SS inner-EXH row: an S-type exists. -/
theorem table1_ss_i : ∀ w, exhMeaning {.inner} .ss w ↔ .someNotAll ∈ w := by decide

/-- Table 1, SS outer+inner row: an S-type exists but not exclusively. -/
theorem table1_ss_oi :
    ∀ w, exhMeaning {.outer, .inner} .ss w ↔ (.someNotAll ∈ w ∧ w ≠ wS) := by decide

/-- EXH_MOI(SS) = EXH_OI(SS): matrix EXH is vacuous at MOI. -/
theorem exh_moi_ss : ∀ w,
    exhMeaning {.matrix, .outer, .inner} .ss w ↔ exhMeaning {.outer, .inner} .ss w := by
  decide

/-- Table 1, NN matrix-free rows: no N-types. -/
theorem table1_nn_lit : ∀ p : Parse, .matrix ∉ p →
    ∀ w, exhMeaning p .nn w ↔ .none ∉ w := by decide

/-- Table 1, NN matrix rows: matrix EXH additionally negates "none drank not
all" (= {wA}) — the fn. 7 reading from the `none ~ not all` alternative. -/
theorem table1_nn_m : ∀ p : Parse, .matrix ∈ p →
    ∀ w, exhMeaning p .nn w ↔ (.none ∉ w ∧ w ≠ wA) := by decide

/-- Table 1, NS literal row: only wN. -/
theorem table1_ns_lit : ∀ w, exhMeaning ∅ .ns w ↔ w = wN := by decide

/-- Table 1, NS inner-EXH row: no S-types — inner EXH weakens NS. -/
theorem table1_ns_i : ∀ w, exhMeaning {.inner} .ns w ↔ .someNotAll ∉ w := by decide

/-- Table 1, NS matrix+inner row: matrix EXH negates the sentence's own
now-stronger literal meaning {wN}. -/
theorem table1_ns_mi :
    ∀ w, exhMeaning {.matrix, .inner} .ns w ↔ (.someNotAll ∉ w ∧ w ≠ wN) := by decide

/-- Table 1, AN: only wN, under every parse. -/
theorem table1_an : ∀ p : Parse, ∀ w, exhMeaning p .an w ↔ w = wN := by decide

/-- Table 1, AA: only wA, under every parse. -/
theorem table1_aa : ∀ p : Parse, ∀ w, exhMeaning p .aa w ↔ w = wA := by decide

/-- Table 1, SA literal row: an A-type exists. -/
theorem table1_sa_lit : ∀ w, exhMeaning ∅ .sa w ↔ .all ∈ w := by decide

/-- Table 1, SA outer-EXH row: outer EXH excludes wA. -/
theorem table1_sa_o : ∀ w, exhMeaning {.outer} .sa w ↔ (.all ∈ w ∧ w ≠ wA) := by decide

/-- Table 1, NA literal row: no A-types. -/
theorem table1_na_lit : ∀ w, exhMeaning ∅ .na w ↔ .all ∉ w := by decide

/-- Table 1, NA matrix row: matrix EXH negates the stronger NS = {wN}. -/
theorem table1_na_m : ∀ w, exhMeaning {.matrix} .na w ↔ (.all ∉ w ∧ w ≠ wN) := by decide

/-- Table 1, SN literal row: an N-type exists. -/
theorem table1_sn_lit : ∀ w, exhMeaning ∅ .sn w ↔ .none ∈ w := by decide

/-- Table 1, SN outer-EXH row: outer EXH negates AN = {wN}. -/
theorem table1_sn_o : ∀ w, exhMeaning {.outer} .sn w ↔ (.none ∈ w ∧ w ≠ wN) := by decide

/-- Table 1, AS literal row: no N-types. -/
theorem table1_as_lit : ∀ w, exhMeaning ∅ .as w ↔ .none ∉ w := by decide

/-- Table 1, AS inner-EXH row: inner EXH pins wS. -/
theorem table1_as_i : ∀ w, exhMeaning {.inner} .as w ↔ w = wS := by decide

/-- Table 1, AS matrix row: matrix EXH without I negates AA, excluding wA. -/
theorem table1_as_m :
    ∀ w, exhMeaning {.matrix} .as w ↔ (.none ∉ w ∧ w ≠ wA) := by decide

/-- Literal meaning is the empty parse's exhaustified meaning. -/
theorem literal_eq_exh_none : ∀ u : Utterance, ∀ w,
    literalMeaning u w ↔ exhMeaning ∅ u w := by decide

/-- Table 1, SS matrix row — ⟦SS⟧^M = {wNS}: the reading that "uniquely
singles out this world state" (eq. 22) and drives GI's win. -/
theorem m_ss_singleton : ∀ w, exhMeaning {.matrix} .ss w ↔ w = wNS := by decide

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

/-! ### Measurable structure -/

instance : MeasurableSpace World := ⊤
instance : DiscreteMeasurableSpace World := ⟨fun _ => trivial⟩
instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ => trivial⟩
instance : Nonempty Utterance := ⟨.nn⟩
instance : MeasurableSpace Parse := ⊤
instance : DiscreteMeasurableSpace Parse := ⟨fun _ => trivial⟩
instance : Nonempty Parse := ⟨∅⟩
instance : MeasurableSpace LULex := ⊤
instance : DiscreteMeasurableSpace LULex := ⟨fun _ => trivial⟩
instance : MeasurableSpace LIParse := ⊤
instance : DiscreteMeasurableSpace LIParse := ⟨fun _ => trivial⟩
instance : Nonempty LIParse := ⟨.lit⟩

/-! ### The model on kernels

Priors are `uniformOn`; per-parse literal listeners condition the prior on
the reading's extension; the speakers are the softmax-utility kernel at
α = 2; the listeners are `κ†μ` (vanilla; LU with the lexicon in the state)
and `jointPosterior` (LI/GI pair choice). -/

/-- The extension of an utterance under a parse. -/
def sem (p : Parse) (u : Utterance) : Set World := {w | exhMeaning p u w}

noncomputable def prior : Measure World := uniformOn Set.univ

instance : IsProbabilityMeasure prior :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn _))

private theorem card_world : Fintype.card World = 7 := by decide

theorem prior_real_singleton (w : World) : prior.real {w} = 7⁻¹ := by
  rw [prior, uniformOn_univ_real_singleton, card_world]
  norm_num

theorem prior_singleton_ne_zero (w : World) : prior {w} ≠ 0 := by
  rw [prior, uniformOn_univ, Measure.count_singleton]
  simp

/-- Every `(world, parse)` state has a true utterance. -/
theorem exists_true : ∀ (w : World) (p : Parse), ∃ u, exhMeaning p u w := by decide

/-- Per-parse literal listener. -/
noncomputable def L0 (p : Parse) : Kernel Utterance World :=
  RSA.literalListener prior (sem p)

theorem L0_ne_zero {p : Parse} {u : Utterance} {w : World} (h : exhMeaning p u w) :
    L0 p u {w} ≠ 0 :=
  RSA.literalListener_apply_singleton_ne_zero prior h (prior_singleton_ne_zero w)

/-- Within its extension, L0 mass is the inverse extension cardinality. -/
theorem L0_real_of_mem {p : Parse} {u : Utterance} {w : World} (h : exhMeaning p u w) :
    (L0 p u).real {w} = ((Finset.univ.filter (exhMeaning p u)).card : ℝ)⁻¹ := by
  have hk : 0 < (Finset.univ.filter (exhMeaning p u)).card :=
    Finset.card_pos.mpr ⟨w, by simp [h]⟩
  rw [L0, RSA.literalListener_real_singleton_of_mem prior h, prior_real_singleton,
    show sem p u = ↑(Finset.univ.filter (exhMeaning p u)) from by ext w'; simp [sem],
    prior, uniformOn_univ_real_coe_finset, card_world]
  rw [div_div_eq_mul_div]
  push_cast
  rw [inv_mul_cancel₀ (by norm_num : (7 : ℝ) ≠ 0), one_div]

theorem L0_toReal (p : Parse) (u : Utterance) (w : World) :
    (L0 p u {w}).toReal
      = if exhMeaning p u w then ((Finset.univ.filter (exhMeaning p u)).card : ℝ)⁻¹
        else 0 := by
  split
  · exact L0_real_of_mem ‹_›
  · exact RSA.literalListener_real_singleton_of_not_mem prior ‹_›

/-! ### Speakers -/

/-- Vanilla speaker: informativity softmax over the literal parse. -/
noncomputable def vanillaSpeaker : Kernel World Utterance :=
  RSA.speaker 2 (RSA.utility (L0 ∅) fun _ => 0)

/-- The GI literal listener, keyed by (utterance, parse) pairs: a pair means
its parse's reading. -/
noncomputable def giL0 : Kernel (Utterance × Parse) World :=
  RSA.literalListener prior fun x => sem x.2 x.1

/-- The GI speaker (eq. 21a): one softmax over all 72 pairs per world. -/
noncomputable def giSpeaker : Kernel World (Utterance × Parse) :=
  RSA.speaker 2 (RSA.utility giL0 fun _ => 0)

/-- The LI literal listener over the 36 matrix-free pairs. -/
noncomputable def liL0 : Kernel (Utterance × LIParse) World :=
  RSA.literalListener prior fun x => sem x.2.toParse x.1

/-- The LI speaker (eq. 18a). -/
noncomputable def liSpeaker : Kernel World (Utterance × LIParse) :=
  RSA.speaker 2 (RSA.utility liL0 fun _ => 0)

/-- LU's joint prior: the lexicon is drawn with the world. -/
noncomputable def luPrior : Measure (World × LULex) := uniformOn Set.univ

instance : IsProbabilityMeasure luPrior :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn _))

/-- The LU speaker (eq. 11): per-lexicon informativity — the lexicon is an
argument of the speaker, not a choice. -/
noncomputable def luSpeaker : Kernel (World × LULex) Utterance :=
  RSA.speaker 2 fun s u => RSA.utility (L0 s.2.toParse) (fun _ => 0) s.1 u

/-! ### Markov structure -/

theorem giL0_toReal (x : Utterance × Parse) (w : World) :
    (giL0 x {w}).toReal
      = if exhMeaning x.2 x.1 w then ((Finset.univ.filter (exhMeaning x.2 x.1)).card : ℝ)⁻¹
        else 0 :=
  L0_toReal x.2 x.1 w

theorem liL0_toReal (x : Utterance × LIParse) (w : World) :
    (liL0 x {w}).toReal
      = if exhMeaning x.2.toParse x.1 w
          then ((Finset.univ.filter (exhMeaning x.2.toParse x.1)).card : ℝ)⁻¹
        else 0 :=
  L0_toReal x.2.toParse x.1 w

instance : IsMarkovKernel vanillaSpeaker :=
  RSA.isMarkovKernel_speaker_utility_zero (by norm_num)
    (fun u w => RSA.literalListener_apply_ne_top prior (sem ∅) u {w})
    fun w => (exists_true w ∅).imp fun u hu => L0_ne_zero hu

instance : IsMarkovKernel giSpeaker :=
  RSA.isMarkovKernel_speaker_utility_zero (by norm_num)
    (fun x w => RSA.literalListener_apply_ne_top prior _ x {w})
    fun w => (exists_true w ∅).elim fun u hu => ⟨(u, ∅), L0_ne_zero hu⟩

instance : IsMarkovKernel liSpeaker :=
  RSA.isMarkovKernel_speaker_utility_zero (by norm_num)
    (fun x w => RSA.literalListener_apply_ne_top prior _ x {w})
    fun w => (exists_true w ∅).elim fun u hu => ⟨(u, .lit), L0_ne_zero hu⟩

instance : IsMarkovKernel luSpeaker := by
  refine RSA.isMarkovKernel_speaker (fun s u => ?_) fun s => ?_
  · rw [RSA.utility, EReal.coe_zero, sub_zero]
    exact RSA.coe_mul_log_ne_top (by norm_num)
      (RSA.literalListener_apply_ne_top prior _ u {s.1})
  · refine (exists_true s.1 s.2.toParse).imp fun u hu => ?_
    rw [RSA.utility, EReal.coe_zero, sub_zero]
    exact RSA.coe_mul_log_ne_bot (by norm_num) (L0_ne_zero hu)

/-! ### Listeners -/

/-- Vanilla listener (eq. 9): the Bayesian inverse of the vanilla speaker. -/
noncomputable def vanillaListener : Kernel Utterance World := vanillaSpeaker†prior

/-- LU listener (eqs. 12–13): Bayesian inverse over the joint state. -/
noncomputable def luListener : Kernel Utterance (World × LULex) := luSpeaker†luPrior

/-- LI listener (eq. 18b): joint posterior over (world, parse). -/
noncomputable def liListener : Kernel Utterance (World × LIParse) :=
  jointPosterior liSpeaker prior

/-- GI listener (eq. 21b). -/
noncomputable def giListener : Kernel Utterance (World × Parse) :=
  jointPosterior giSpeaker prior

/-! ### Utility bounds for positivity witnesses -/

private theorem util_ne_bot {p : Parse} {u : Utterance} {w : World}
    (h : exhMeaning p u w) :
    ((2 : ℝ) : EReal) * RSA.utility (L0 p) (fun _ => 0) w u ≠ ⊥ := by
  rw [RSA.utility, EReal.coe_zero, sub_zero]
  exact RSA.coe_mul_log_ne_bot (by norm_num) (L0_ne_zero h)

private theorem util_ne_top (p : Parse) (u : Utterance) (w : World) :
    ((2 : ℝ) : EReal) * RSA.utility (L0 p) (fun _ => 0) w u ≠ ⊤ := by
  rw [RSA.utility, EReal.coe_zero, sub_zero]
  exact RSA.coe_mul_log_ne_top (by norm_num)
    (RSA.literalListener_apply_ne_top prior _ u {w})

/-! ### Marginal-positivity witnesses -/

theorem vanilla_marg_ss : (vanillaSpeaker ∘ₘ prior) {Utterance.ss} ≠ 0 :=
  comp_apply_singleton_ne_zero _ _ (prior_singleton_ne_zero wNS)
    (RSA.speaker_apply_singleton_ne_zero (util_ne_bot (by decide)) (util_ne_top ∅ · wNS))

theorem gi_marg (u : Utterance) {w : World} (h : exhMeaning ∅ u w) :
    ((giSpeaker ∘ₘ prior).map Prod.fst) {u} ≠ 0 :=
  map_fst_comp_apply_singleton_ne_zero _ _ (θ := (∅ : Parse))
    (prior_singleton_ne_zero w)
    (RSA.speaker_apply_singleton_ne_zero
      (show _ ≠ ⊥ by
        rw [RSA.utility, EReal.coe_zero, sub_zero]
        exact RSA.coe_mul_log_ne_bot (by norm_num) (L0_ne_zero h))
      fun x => by
        rw [RSA.utility, EReal.coe_zero, sub_zero]
        exact RSA.coe_mul_log_ne_top (by norm_num)
          (RSA.literalListener_apply_ne_top prior _ x {w}))

theorem gi_marg_ss : ((giSpeaker ∘ₘ prior).map Prod.fst) {Utterance.ss} ≠ 0 :=
  gi_marg .ss (w := wNS) (by decide)

theorem gi_marg_aa : ((giSpeaker ∘ₘ prior).map Prod.fst) {Utterance.aa} ≠ 0 :=
  gi_marg .aa (w := wA) (by decide)

theorem gi_marg_as : ((giSpeaker ∘ₘ prior).map Prod.fst) {Utterance.as} ≠ 0 :=
  gi_marg .as (w := wS) (by decide)

theorem li_marg_ss : ((liSpeaker ∘ₘ prior).map Prod.fst) {Utterance.ss} ≠ 0 :=
  map_fst_comp_apply_singleton_ne_zero _ _ (θ := LIParse.lit)
    (prior_singleton_ne_zero wNS)
    (RSA.speaker_apply_singleton_ne_zero
      (show _ ≠ ⊥ by
        rw [RSA.utility, EReal.coe_zero, sub_zero]
        exact RSA.coe_mul_log_ne_bot (by norm_num) (L0_ne_zero (p := ∅) (by decide)))
      fun x => by
        rw [RSA.utility, EReal.coe_zero, sub_zero]
        exact RSA.coe_mul_log_ne_top (by norm_num)
          (RSA.literalListener_apply_ne_top prior _ x {wNS}))

theorem luPrior_singleton_ne_zero (s : World × LULex) : luPrior {s} ≠ 0 := by
  rw [luPrior, uniformOn_univ, Measure.count_singleton, ne_eq, ENNReal.div_eq_zero_iff]
  simp
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)

theorem lu_marg_ss : (luSpeaker ∘ₘ luPrior) {Utterance.ss} ≠ 0 :=
  comp_apply_singleton_ne_zero _ _ (luPrior_singleton_ne_zero (wNS, .lit))
    (RSA.speaker_apply_singleton_ne_zero (util_ne_bot (p := ∅) (by decide))
      (util_ne_top ∅ · wNS))

end FrankeBergen2020
