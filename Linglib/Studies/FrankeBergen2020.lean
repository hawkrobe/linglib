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
`ProbabilityTheory.jointPosterior`.

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
concentrates on wNSA (eq. 15). The model lives on mathlib's probability API:
`uniformOn` priors, `ProbabilityTheory.cond` literal listeners, softmax
kernels, and posterior kernels; predictions are stated on `Measure.real` and
close by partition-value rewrites plus `norm_num`.
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

One characterization per utterance, total over all eight parses — the paper's
row-groups appear as the guards. Each reading is a membership predicate on
the world's alien-type set, not a truth vector. -/

/-- Table 1, NN: no N-types; matrix parses additionally negate "none drank
not all" (= {wA}) — the fn. 7 reading from the `none ~ not all` alternative. -/
theorem table1_nn : ∀ (p : Parse) (w : World),
    exhMeaning p .nn w ↔ (.none ∉ w ∧ (.matrix ∈ p → w ≠ wA)) := by decide

/-- Table 1, NS: only wN literally; inner EXH weakens to the S-free worlds,
whereupon matrix EXH negates the sentence's own now-stronger literal {wN}. -/
theorem table1_ns : ∀ (p : Parse) (w : World),
    exhMeaning p .ns w ↔
      if .inner ∈ p then .someNotAll ∉ w ∧ (.matrix ∈ p → w ≠ wN)
      else w = wN := by decide

/-- Table 1, NA: no A-types; matrix EXH negates the stronger NS = {wN}. -/
theorem table1_na : ∀ (p : Parse) (w : World),
    exhMeaning p .na w ↔ (.all ∉ w ∧ (.matrix ∈ p → w ≠ wN)) := by decide

/-- Table 1, SN: an N-type exists; outer or matrix EXH negates AN = {wN}. -/
theorem table1_sn : ∀ (p : Parse) (w : World),
    exhMeaning p .sn w ↔
      (.none ∈ w ∧ (.outer ∈ p ∨ .matrix ∈ p → w ≠ wN)) := by decide

/-- Table 1, SS: the five row-groups — literal; inner EXH requires an S-type
(matrix then vacuous); adding outer EXH excludes wS; outer alone keeps mixed
worlds; matrix alone pins wNS. -/
theorem table1_ss : ∀ (p : Parse) (w : World),
    exhMeaning p .ss w ↔
      if .inner ∈ p then .someNotAll ∈ w ∧ (.outer ∈ p → w ≠ wS)
      else if .outer ∈ p then .none ∈ w ∧ w ≠ wN
      else if .matrix ∈ p then w = wNS
      else w ≠ wN := by decide

/-- Table 1, SA: an A-type exists; outer or matrix EXH excludes wA. -/
theorem table1_sa : ∀ (p : Parse) (w : World),
    exhMeaning p .sa w ↔
      (.all ∈ w ∧ (.outer ∈ p ∨ .matrix ∈ p → w ≠ wA)) := by decide

/-- Table 1, AN: only wN, under every parse. -/
theorem table1_an : ∀ (p : Parse) (w : World), exhMeaning p .an w ↔ w = wN := by decide

/-- Table 1, AS: no N-types; inner EXH pins wS; matrix EXH without inner
negates AA, excluding wA. -/
theorem table1_as : ∀ (p : Parse) (w : World),
    exhMeaning p .as w ↔
      if .inner ∈ p then w = wS
      else .none ∉ w ∧ (.matrix ∈ p → w ≠ wA) := by decide

/-- Table 1, AA: only wA, under every parse. -/
theorem table1_aa : ∀ (p : Parse) (w : World), exhMeaning p .aa w ↔ w = wA := by decide

/-- Literal meaning is the empty parse's exhaustified meaning. -/
theorem literal_eq_exh_none : ∀ (u : Utterance) (w : World),
    literalMeaning u w ↔ exhMeaning ∅ u w := by decide

/-- ⟦SS⟧^M = {wNS} — the reading that "uniquely singles out this world
state" (eq. 22) and drives GI's win; the matrix-alone case of `table1_ss`. -/
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

@[simp] theorem mem_sem {p : Parse} {u : Utterance} {w : World} :
    w ∈ sem p u ↔ exhMeaning p u w := Iff.rfl

instance (p : Parse) (u : Utterance) (w : World) : Decidable (w ∈ sem p u) :=
  inferInstanceAs (Decidable (exhMeaning p u w))

/-- The extension of an utterance under a parse, as a `Finset` — the
`RSA.Scenario` semantic field. -/
def ext (p : Parse) (u : Utterance) : Finset World :=
  Finset.univ.filter (exhMeaning p u)

@[simp] theorem mem_ext {p : Parse} {u : Utterance} {w : World} :
    w ∈ ext p u ↔ exhMeaning p u w := by
  simp [ext]

/-- Extension form of Table 1's AA row: ⟦AA⟧ = {wA} under every parse. -/
theorem ext_aa : ∀ p : Parse, ext p .aa = {wA} := by decide

noncomputable def prior : Measure World := uniformOn Set.univ

instance : IsProbabilityMeasure prior :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn _))

private theorem card_world : Fintype.card World = 7 := by decide

theorem prior_real_singleton (w : World) : prior.real {w} = 7⁻¹ := by
  rw [prior, uniformOn_univ_real_singleton, card_world]
  norm_num

theorem prior_singleton_eq (w w' : World) : prior {w} = prior {w'} := by
  simp [prior, uniformOn_univ]

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

/-! ### The models as bundled speakers

Each model is an `RSA.Speaker` at α = 2 over its own choice space: vanilla
chooses bare utterances read literally, GI chooses over all 72 (utterance,
parse) pairs (eq. 21a), LI over the 36 matrix-free pairs (eq. 18a). LU is
*not* a `Speaker` over the joint (world, lexicon) state: its utility
normalizes per lexicon rather than against the pooled extension — the
type-level content of the paper's LU-vs-intentions contrast. -/

/-- The vanilla model: utterances read literally. -/
@[simps] noncomputable def vanillaM : RSA.Speaker World Utterance where
  α := 2
  α_pos := two_pos
  prior := prior
  sem := sem ∅

/-- The GI model: pair choice with all parses available. -/
@[simps] noncomputable def giM : RSA.Speaker World (Utterance × Parse) where
  α := 2
  α_pos := two_pos
  prior := prior
  sem x := sem x.2 x.1

/-- The LI model: pair choice over matrix-free parses. -/
@[simps] noncomputable def liM : RSA.Speaker World (Utterance × LIParse) where
  α := 2
  α_pos := two_pos
  prior := prior
  sem x := sem x.2.toParse x.1

instance : IsProbabilityMeasure vanillaM.prior := inferInstanceAs (IsProbabilityMeasure prior)
instance : IsProbabilityMeasure giM.prior := inferInstanceAs (IsProbabilityMeasure prior)
instance : IsProbabilityMeasure liM.prior := inferInstanceAs (IsProbabilityMeasure prior)

instance : vanillaM.Positive := ⟨prior_singleton_ne_zero⟩
instance : giM.Positive := ⟨prior_singleton_ne_zero⟩
instance : liM.Positive := ⟨prior_singleton_ne_zero⟩

instance : vanillaM.Viable := ⟨fun w => exists_true w ∅⟩
instance : giM.Viable := ⟨fun w => (exists_true w ∅).elim fun u h => ⟨(u, ∅), h⟩⟩
instance : liM.Viable := ⟨fun w => (exists_true w ∅).elim fun u h => ⟨(u, .lit), h⟩⟩

/-! ### The models as choice scenarios

Each model is an `RSA.Scenario`: an extension and an observable form per
choice, with rationality a parameter of the derived kernels — findings
quantify over `α` where the paper's argument does. Vanilla chooses bare
utterances read literally (obs = id); GI chooses over all 72 (utterance,
parse) pairs (eq. 21a), LI over the 36 matrix-free pairs (eq. 18a), both
heard through `Prod.fst`. LU's per-lexicon speakers form the `luFam` family
(eq. 11) — the lexicon sits in the state, not the choice, so LU is *not* one
`Scenario`: the type-level content of the paper's LU-vs-intentions contrast. -/

/-- The vanilla scenario (§3.1): utterances read literally. -/
@[simps] def vanilla : RSA.Scenario World Utterance Utterance where
  sem := ext ∅
  obs := id

/-- The GI scenario (eq. 21): pair choice with all parses available. -/
@[simps] def gi : RSA.Scenario World (Utterance × Parse) Utterance where
  sem x := ext x.2 x.1
  obs := Prod.fst

/-- The LI scenario (eq. 18): pair choice over matrix-free parses. -/
@[simps] def li : RSA.Scenario World (Utterance × LIParse) Utterance where
  sem x := ext x.2.toParse x.1
  obs := Prod.fst

/-- The LU speaker family (eq. 11): one scenario per lexicon. -/
@[simps] def luFam (l : LULex) : RSA.Scenario World Utterance Utterance where
  sem := ext l.toParse
  obs := id

instance : vanilla.Expressible := ⟨fun w => (exists_true w ∅).imp fun _ h => mem_ext.mpr h⟩
instance : gi.Expressible :=
  ⟨fun w => (exists_true w ∅).elim fun u h => ⟨(u, ∅), mem_ext.mpr h⟩⟩
instance : li.Expressible :=
  ⟨fun w => (exists_true w ∅).elim fun u h => ⟨(u, .lit), mem_ext.mpr h⟩⟩

/-- LU's joint prior: the lexicon is drawn with the world. -/
noncomputable def luPrior : Measure (World × LULex) := uniformOn Set.univ

instance : IsProbabilityMeasure luPrior :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn _))

/-- The LU speaker (eq. 11): per-lexicon informativity — the lexicon is an
argument of the speaker, not a choice. -/
noncomputable def luSpeaker : Kernel (World × LULex) Utterance :=
  RSA.speaker 2 fun s u => RSA.utility (L0 s.2.toParse) (fun _ => 0) s.1 u

/-! ### Markov structure -/

instance : IsMarkovKernel luSpeaker := by
  refine RSA.isMarkovKernel_speaker (fun s u => ?_) fun s => ?_
  · rw [RSA.utility, EReal.coe_zero, sub_zero]
    exact RSA.coe_mul_log_ne_top (by norm_num)
      (RSA.literalListener_apply_ne_top prior _ u {s.1})
  · refine (exists_true s.1 s.2.toParse).imp fun u hu => ?_
    rw [RSA.utility, EReal.coe_zero, sub_zero]
    exact RSA.coe_mul_log_ne_bot (by norm_num) (L0_ne_zero hu)

/-! ### Listeners

Vanilla's pragmatic listener is `vanillaM.listener` (eq. 9); the intention
models' are `giM.jointListener` (eq. 21b) and `liM.jointListener` (eq. 18b).
LU keeps a bespoke inverse over the joint state (eqs. 12–13). -/

/-- LU listener: Bayesian inverse over the joint (world, lexicon) state. -/
noncomputable def luListener : Kernel Utterance (World × LULex) := luSpeaker†luPrior

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

theorem luPrior_singleton_ne_zero (s : World × LULex) : luPrior {s} ≠ 0 := by
  rw [luPrior, uniformOn_univ, Measure.count_singleton]
  simp [ENNReal.mul_eq_top]

theorem lu_marg_ss : (luSpeaker ∘ₘ luPrior) {Utterance.ss} ≠ 0 :=
  comp_apply_singleton_ne_zero _ _ (luPrior_singleton_ne_zero (wNS, .lit))
    (RSA.speaker_apply_singleton_ne_zero (util_ne_bot (p := ∅) (by decide))
      (util_ne_top ∅ · wNS))

/-! ### Speaker values on reals -/

private theorem rpow_two (r : ℝ) : r ^ (2 : ℝ) = r ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

private theorem rpow_five (r : ℝ) : r ^ (5 : ℝ) = r ^ 5 := by
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

private theorem luS_real (s : World × LULex) (u : Utterance) :
    (luSpeaker s).real {u}
      = (L0 s.2.toParse u {s.1}).toReal ^ (2 : ℝ)
        / ∑ u', (L0 s.2.toParse u' {s.1}).toReal ^ (2 : ℝ) := by
  rw [measureReal_def, luSpeaker, RSA.speaker_apply_singleton]
  simp_rw [RSA.exp_mul_utility_zero]
  rw [ENNReal.toReal_div, ENNReal.toReal_sum fun u' _ =>
    ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (show L0 s.2.toParse u' {s.1} ≠ ⊤ from
        RSA.literalListener_apply_ne_top prior _ u' {s.1})]
  simp_rw [ENNReal.toReal_rpow]

/-! ### Enumeration scaffolding -/

private theorem univU : (Finset.univ : Finset Utterance)
    = {.nn, .ns, .na, .sn, .ss, .sa, .an, .as, .aa} := by decide

private theorem univP : (Finset.univ : Finset Parse)
    = {∅, {.matrix}, {.outer}, {.inner}, {.matrix, .outer}, {.matrix, .inner},
       {.outer, .inner}, {.matrix, .outer, .inner}} := by decide

private theorem univW : (Finset.univ : Finset World)
    = {wN, wNS, wNA, wNSA, wS, wSA, wA} := by decide

private theorem univLU : (Finset.univ : Finset LULex) = {.lit, .oi} := by decide

private theorem univLI : (Finset.univ : Finset LIParse) = {.lit, .i, .o, .oi} := by decide

/-! ### Partitions

The per-world softmax partitions, as real rationals: `Z(w) = Σ |ext|⁻²` over
the model's choice space. -/

/-! ### Per-parse and LI partitions -/

private theorem zP (p : Parse) (w : World) (z : ℝ)
    (h : (∑ u : Utterance,
        (if exhMeaning p u w then ((Finset.univ.filter (exhMeaning p u)).card : ℝ)⁻¹
         else 0) ^ 2) = z) :
    (∑ u' : Utterance, (L0 p u' {w}).toReal ^ 2) = z := by
  simp_rw [L0_toReal]
  exact h

set_option maxRecDepth 8192 in
private theorem zVan_wNS : (∑ u' : Utterance, (L0 ∅ u' {wNS}).toReal ^ 2) = 29 / 144 :=
  zP _ _ _ (by norm_num +decide [rpow_two, univU, univP, univW, Finset.sum_insert,
    Finset.sum_singleton, Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, Finset.card_singleton])

set_option maxRecDepth 8192 in
private theorem zVan_wNA : (∑ u' : Utterance, (L0 ∅ u' {wNA}).toReal ^ 2) = 11 / 72 :=
  zP _ _ _ (by norm_num +decide [rpow_two, univU, univP, univW, Finset.sum_insert,
    Finset.sum_singleton, Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, Finset.card_singleton])

set_option maxRecDepth 8192 in
private theorem zOI_wNS :
    (∑ u' : Utterance, (L0 {.outer, .inner} u' {wNS}).toReal ^ 2) = 1 / 3 :=
  zP _ _ _ (by norm_num +decide [rpow_two, univU, univP, univW, Finset.sum_insert,
    Finset.sum_singleton, Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, Finset.card_singleton])

set_option maxRecDepth 8192 in
private theorem zOI_wNA :
    (∑ u' : Utterance, (L0 {.outer, .inner} u' {wNA}).toReal ^ 2) = 1 / 3 :=
  zP _ _ _ (by norm_num +decide [rpow_two, univU, univP, univW, Finset.sum_insert,
    Finset.sum_singleton, Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, Finset.card_singleton])

/-! ### Listener-preference reductions -/

private theorem lu_fst_lt {u : Utterance}
    (hx : (luSpeaker ∘ₘ luPrior) {u} ≠ 0) {w₁ w₂ : World}
    (h : (∑ l : LULex, luPrior.real {(w₁, l)} * (luSpeaker (w₁, l)).real {u})
        < ∑ l : LULex, luPrior.real {(w₂, l)} * (luSpeaker (w₂, l)).real {u}) :
    (luListener u).fst.real {w₁} < (luListener u).fst.real {w₂} := by
  rw [luListener, posterior_fst_real_lt_iff luSpeaker luPrior hx]
  exact h

private theorem luPrior_real_singleton (s : World × LULex) : luPrior.real {s} = 14⁻¹ := by
  rw [luPrior, uniformOn_univ_real_singleton,
    show Fintype.card (World × LULex) = 14 from by decide]
  norm_num

/-! ### Pooled speaker masses

Each finding compares two pooled speaker masses; naming their values keeps
the findings two-line. -/

private theorem luPool_ss_wNS :
    (∑ l : LULex, (luSpeaker (wNS, l)).real {Utterance.ss}) = 41 / 87 := by
  simp_rw [luS_real, rpow_two]
  norm_num +decide [univLU, Finset.sum_insert, Finset.sum_singleton, LULex.toParse]
  simp_rw [zVan_wNS, zOI_wNS, L0_toReal]
  norm_num +decide [rpow_two, univU, univP, univW, Finset.sum_insert,
    Finset.sum_singleton, Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, Finset.card_singleton]

private theorem luPool_ss_wNA :
    (∑ l : LULex, (luSpeaker (wNA, l)).real {Utterance.ss}) = 2 / 11 := by
  simp_rw [luS_real, rpow_two]
  norm_num +decide [univLU, Finset.sum_insert, Finset.sum_singleton, LULex.toParse]
  simp_rw [zVan_wNA, zOI_wNA, L0_toReal]
  norm_num +decide [rpow_two, univU, univP, univW, Finset.sum_insert,
    Finset.sum_singleton, Finset.filter_insert, Finset.filter_singleton,
    Finset.card_insert_of_notMem, Finset.card_singleton]

/-! ### The ten qualitative findings -/

set_option maxRecDepth 8192 in
/-- SS exhaustifies the inner quantifier at the paper's illustrative α = 5:
hearing SS, the listener prefers wNS to wNSA (eq. 22's regime). Evaluation
register — the domination certificate provably fails here (wNSA's SS-fiber is
not termwise matched by wNS's), so profile literals by `decide` plus
fifth-power arithmetic by `norm_num` decide it. -/
theorem ss_inner_exh :
    (gi.listener 5 prior .ss).real {wNSA} < (gi.listener 5 prior .ss).real {wNS} := by
  rw [gi.listener_real_lt_iff_invPowSum (o := .ss) (by norm_num) (prior_singleton_eq wNSA wNS)
      (prior_singleton_ne_zero wNS) ⟨(.ss, ∅), rfl, by decide⟩,
    show gi.fiberProfile .ss wNSA = {3, 3, 3, 3, 4, 4, 6} from by decide,
    show gi.profile wNS
      = {1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 6} from by
      decide,
    show gi.fiberProfile .ss wNS = {1, 3, 3, 3, 3, 4, 4, 6} from by decide,
    show gi.profile wNSA
      = {3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 6} from by decide,
    Multiset.invPowSum_toReal (by norm_num) (by decide),
    Multiset.invPowSum_toReal (by norm_num) (by decide),
    Multiset.invPowSum_toReal (by norm_num) (by decide),
    Multiset.invPowSum_toReal (by norm_num) (by decide)]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]
  norm_num [rpow_five]

set_option maxRecDepth 8192 in
/-- SS exhaustifies the outer quantifier for every rationality: hearing SS,
the listener prefers wNS to wS. Certificate register: the fiber-by-rest
cross-product domination closes by `decide`. -/
theorem ss_outer_exh {α : ℝ} (hα : 0 < α) :
    (gi.listener α prior .ss).real {wS} < (gi.listener α prior .ss).real {wNS} :=
  gi.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wS wNS)
    (prior_singleton_ne_zero wNS) ⟨(.ss, ∅), rfl, by decide⟩ (by decide)

/-- AA identifies the unique world where all aliens drank all, for every
rationality: AA is false at wSA under every parse (`sem_aa`, Table 1's AA row)
and true at wA under the bare parse. Purely structural — no masses computed. -/
theorem aa_identifies {α : ℝ} (hα : 0 < α) :
    (gi.listener α prior .aa).real {wSA} < (gi.listener α prior .aa).real {wA} :=
  gi.listener_real_lt_of_support hα (prior_singleton_ne_zero wA)
    (fun c hc => by
      obtain ⟨u, p⟩ := c
      obtain rfl : u = .aa := hc
      simp only [gi_sem, ext_aa]
      decide)
    ⟨(.aa, ∅), rfl, by simp only [gi_sem, ext_aa]; decide⟩

set_option maxRecDepth 8192 in
/-- AS exhaustifies the inner quantifier for every rationality: hearing AS,
the listener prefers wS to wA. Certificate register. -/
theorem as_inner_exh {α : ℝ} (hα : 0 < α) :
    (gi.listener α prior .as).real {wA} < (gi.listener α prior .as).real {wS} :=
  gi.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wA wS)
    (prior_singleton_ne_zero wS) ⟨(.as, ∅), rfl, by decide⟩ (by decide)

set_option maxRecDepth 8192 in
private theorem giProfile_wN : gi.profile wN
    = {1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 4, 4} := by decide

set_option maxRecDepth 8192 in
private theorem giProfile_wNS : gi.profile wNS
    = {1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 6} := by decide

set_option maxRecDepth 8192 in
private theorem giProfile_wNA : gi.profile wNA
    = {2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 6} := by decide

set_option maxRecDepth 8192 in
private theorem giProfile_wNSA : gi.profile wNSA
    = {3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 6} := by decide

set_option maxRecDepth 8192 in
private theorem giProfile_wS : gi.profile wS
    = {1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 6} := by
  decide

set_option maxRecDepth 8192 in
private theorem giProfile_wSA : gi.profile wSA
    = {2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 6} := by decide

set_option maxRecDepth 8192 in
private theorem giProfile_wA : gi.profile wA
    = {1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 6} := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- GI's parse posterior for SS peaks at the matrix-only parse, whose reading
uniquely identifies wNS, at the paper's illustrative α = 5 (eq. 22's regime).
Pair choice drives this: under per-parse normalization M would not dominate.
Evaluation register — genuinely α-dependent: as α → 0 the singleton reading's
informativity advantage vanishes, so no α-free certificate exists. -/
theorem ss_m_parse_pref : ∀ p : Parse, p ≠ {.matrix} →
    (gi.choicePosterior 5 prior .ss).real {(.ss, p)}
      < (gi.choicePosterior 5 prior .ss).real {(.ss, {.matrix})} := by
  intro p hp
  have hmem : p ∈ ({∅, {.matrix}, {.outer}, {.inner}, {.matrix, .outer}, {.matrix, .inner},
      {.outer, .inner}, {.matrix, .outer, .inner}} : Finset Parse) :=
    univP ▸ Finset.mem_univ p
  have ho : ((gi.speaker 5 ∘ₘ prior).map gi.obs) {Utterance.ss} ≠ 0 :=
    gi.map_obs_comp_ne_zero (c := (.ss, ∅)) (prior_singleton_ne_zero wNS) rfl
      (gi.speaker_apply_singleton_ne_zero (by norm_num) (by decide))
  fin_cases hmem <;>
    first
      | exact absurd rfl hp
      | (rw [gi.choicePosterior_real_lt_iff ho rfl rfl]
         simp_rw [gi.speaker_real_singleton (α := 5) (by norm_num), prior_real_singleton]
         norm_num +decide [-Multiset.invPowSum_cons, -Multiset.invPowSum_singleton,
           -Multiset.invPowSum_add, -Multiset.invPowSum_zero,
           univW, Finset.sum_insert, Finset.sum_singleton,
           giProfile_wN, giProfile_wNS, giProfile_wNA, giProfile_wNSA, giProfile_wS,
           giProfile_wSA, giProfile_wA, Multiset.invPowSum_toReal,
           Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
           Multiset.sum_cons, Multiset.sum_singleton, rpow_five, ext,
           Finset.filter_insert, Finset.filter_singleton,
           Finset.card_insert_of_notMem, Finset.card_singleton])

/-- Vanilla RSA hearing SS prefers wNA to wNS — the wrong prediction — at the
paper's illustrative α = 5 (eq. 10, cost-free; the direction reverses at the
fitted cost). Evaluation register. -/
theorem vanilla_ss_prefers_wNA :
    (vanilla.listener 5 prior .ss).real {wNS} < (vanilla.listener 5 prior .ss).real {wNA} := by
  rw [vanilla.listener_real_lt_iff_invPowSum (o := .ss) (by norm_num) (prior_singleton_eq wNS wNA)
      (prior_singleton_ne_zero wNA) ⟨.ss, rfl, by decide⟩,
    show vanilla.fiberProfile .ss wNS = {6} from by decide,
    show vanilla.profile wNA = {4, 4, 6} from by decide,
    show vanilla.fiberProfile .ss wNA = {6} from by decide,
    show vanilla.profile wNS = {3, 4, 6} from by decide,
    Multiset.invPowSum_toReal (by norm_num) (by decide),
    Multiset.invPowSum_toReal (by norm_num) (by decide),
    Multiset.invPowSum_toReal (by norm_num) (by decide)]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]
  norm_num [rpow_five]

set_option maxRecDepth 8192 in
/-- GI corrects vanilla's error for every rationality: hearing SS, the
listener prefers wNS to wNA. Certificate register: wNS's SS-fiber
{1,3,3,3,3,4,4,6} strictly dominates wNA's {3,3,6} — the M-pair's singleton
extension is the spare element — and the cross-product certificate closes the
partition side by `decide`. -/
theorem gi_ss_prefers_wNS {α : ℝ} (hα : 0 < α) :
    (gi.listener α prior .ss).real {wNA} < (gi.listener α prior .ss).real {wNS} :=
  gi.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wNA wNS)
    (prior_singleton_ne_zero wNS) ⟨(.ss, ∅), rfl, by decide⟩ (by decide)

/-- LU also keeps wNS above wNA: the OI lexicon's ⟦SS⟧ excludes wNA (the
paper's full LU-L2 nonetheless concentrates on wNSA, eq. 15). -/
theorem lu_ss_prefers_wNS :
    (luListener .ss).fst.real {wNA} < (luListener .ss).fst.real {wNS} :=
  lu_fst_lt lu_marg_ss (by
    simp_rw [luPrior_real_singleton, ← Finset.mul_sum, luPool_ss_wNA, luPool_ss_wNS]
    norm_num)

set_option maxRecDepth 8192 in
/-- LI derives outer exhaustification for SS at every rationality: wNS over
wS via the OI parse. Certificate register. -/
theorem li_ss_outer_exh {α : ℝ} (hα : 0 < α) :
    (li.listener α prior .ss).real {wS} < (li.listener α prior .ss).real {wNS} :=
  li.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wS wNS)
    (prior_singleton_ne_zero wNS) ⟨(.ss, .lit), rfl, by decide⟩ (by decide)

set_option maxRecDepth 8192 in
/-- LI also gets the wNS-over-wNA ordering that vanilla misses, at every
rationality. Certificate register. -/
theorem li_ss_prefers_wNS {α : ℝ} (hα : 0 < α) :
    (li.listener α prior .ss).real {wNA} < (li.listener α prior .ss).real {wNS} :=
  li.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wNA wNS)
    (prior_singleton_ne_zero wNS) ⟨(.ss, .lit), rfl, by decide⟩ (by decide)

end FrankeBergen2020
