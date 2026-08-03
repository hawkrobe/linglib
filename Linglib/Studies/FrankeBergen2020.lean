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
4 matrix-free parses resp. all 8 — one softmax over pairs per world, heard
through the `RSA.Scenario` observation map.

We show that GI corrects the SS interpretation vanilla gets wrong
(`vanilla_ss_prefers_wNA` vs `gi_ss_prefers_wNS`), and that its parse
posterior for SS peaks at the matrix-only parse (`ss_m_parse_pref`), whose
reading ⟦SS⟧^M = {wNS} "uniquely singles out this world state" (eq. 22,
`m_ss_singleton`) and is unavailable to LI and LU (`li_excludes_matrix`,
`lu_excludes_matrix`) — the paper's explanation of GI's win in its Bayesian
model comparison (posterior 0.956 vs LI 0.033, LU 0.01, vanilla 0; Table 2).
The M-advantage exists *because* the pooled speaker normalizes over pairs:
under the per-parse normalization the paper rejects (p. e85), O beats M at
every rationality (`perParse_ss_o_beats_m`). LI and LU still derive the
embedded enrichments (`li_ss_outer_exh`, `li_ss_prefers_wNS`,
`lu_ss_prefers_wNS`).

## Main results

* `table1_*` — the paper's Table 1, one lemma per row, including NN's
  distinct matrix row (fn. 7) from the `none ~ not all` lexical alternative
  ([levinson-2000]).
* `ss_m_parse_pref` vs `perParse_ss_o_beats_m` — the architectural headline:
  pooled (utterance, parse) choice peaks at M (α = 5), per-parse
  normalization prefers O for every rationality. With
  `RSA.Scenario.pool_L0` (identical weights), the pair locates GI's win
  purely in the position of the latent parameter (p. e86).
* `moi_ss_ne_innocent_exclusion` — the paper's matrix operator (eq. A2) is
  not Fox-style innocent exclusion ([fox-2007]).

## Implementation notes

One reading family (`readings`) generates every model: vanilla is its
literal member, GI and LI pool (utterance, parse) pairs into the choice
space (`RSA.Scenario.pool`, eqs. 18a/21a), and LU — like the rejected
per-parse architecture — fixes the latent as a speaker argument
(`RSA.Scenario.familySpeaker`, eq. 11). Sentential alternatives (A3a) range
over a fourth quantifier `notAll` that is never an utterance — the paper's
grammatical-vs-utterance alternatives distinction (its comparison with
[gotzner-romoli-2018]'s alternative set favors this one by a Bayes factor of
~1,530). Findings come in two registers, both closed by `decide`:
`Multiset.StrictDominates` certificates — strict stochastic dominance of
informativity profiles — hold for every rationality `α > 0`, while genuinely
α-dependent findings are pinned at the paper's illustrative α = 5, where
comparisons clear to ℕ inequalities via `Multiset.divPowSum`. We omit the
paper's cost term for *none*-initial utterances and fixed error ε = 0.045
(eqs. 25–28); `vanilla_ss_prefers_wNA` reverses at the fitted cost. The
paper's S2/L2 layer for LU ([lassiter-goodman-2017], eqs. 14a–14b) is also
omitted: our L1-only LU keeps wNS over wNA at every rationality, though the
paper's LU-L2 concentrates on wNSA (eq. 15).
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

/-- The extension of an utterance under a parse, as a `Finset` — the
`RSA.Scenario` semantic field. -/
def ext (p : Parse) (u : Utterance) : Finset World :=
  Finset.univ.filter (exhMeaning p u)

@[simp] theorem mem_ext {p : Parse} {u : Utterance} {w : World} :
    w ∈ ext p u ↔ exhMeaning p u w := by
  simp [ext]

noncomputable def prior : Measure World := uniformOn Set.univ

instance : IsProbabilityMeasure prior :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn _))

theorem prior_singleton_eq (w w' : World) : prior {w} = prior {w'} := by
  simp [prior, uniformOn_univ]

theorem prior_singleton_ne_zero (w : World) : prior {w} ≠ 0 := by
  rw [prior, uniformOn_univ, Measure.count_singleton]
  simp

/-- Every `(world, parse)` state has a true utterance. -/
theorem exists_true : ∀ (w : World) (p : Parse), ∃ u, exhMeaning p u w := by decide

/-! ### The models as combinators over one reading family

Each parse yields a scenario (`readings`); the paper's models are combinators
applied to this single family. Vanilla (§3.1) is the literal member. GI
(eq. 21a) and LI (eq. 18a) pool (utterance, parse) pairs into one choice
space — the speaker *chooses* the parse — while LU (eq. 11) fixes the lexicon
as a speaker argument (`RSA.Scenario.familySpeaker`). By
`RSA.Scenario.pool_L0` the weights agree, so the models differ *only* in the
position of the latent parameter (p. e86); `ss_m_parse_pref` against
`perParse_ss_o_beats_m` below turns that difference into diverging
predictions. Rationality is a parameter of the derived kernels, and findings
quantify over it wherever the paper's argument does. -/

/-- One scenario per parse: utterances read under it. -/
@[simps] def readings (p : Parse) : RSA.Scenario World Utterance Utterance where
  sem := ext p
  obs := id

/-- The vanilla scenario (§3.1): the literal member of the family. -/
abbrev vanilla : RSA.Scenario World Utterance Utterance := readings ∅

/-- The GI scenario (eq. 21a): pair choice over the full reading family. -/
def gi : RSA.Scenario World (Utterance × Parse) Utterance := .pool readings

/-- The LI scenario (eq. 18a): pair choice over the matrix-free parses. -/
def li : RSA.Scenario World (Utterance × LIParse) Utterance :=
  .pool fun l => readings l.toParse

instance : vanilla.Expressible := ⟨fun w => (exists_true w ∅).imp fun _ h => mem_ext.mpr h⟩
instance : gi.Expressible :=
  ⟨fun w => (exists_true w ∅).elim fun u h => ⟨(u, ∅), mem_ext.mpr h⟩⟩
instance : li.Expressible :=
  ⟨fun w => (exists_true w ∅).elim fun u h => ⟨(u, .lit), mem_ext.mpr h⟩⟩

/-! ### Lexical uncertainty: the latent as a speaker argument -/

/-- The LU speaker family (eq. 11): one member of `readings` per lexicon. -/
def luFam (l : LULex) : RSA.Scenario World Utterance Utterance := readings l.toParse

/-- LU's joint prior: the lexicon is drawn with the world. -/
noncomputable def luPrior : Measure (World × LULex) := uniformOn Set.univ

instance : IsProbabilityMeasure luPrior :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn _))

/-- The LU speaker (eq. 11): the lexicon is an argument, not a choice. -/
noncomputable def luSpeaker (α : ℝ) : Kernel (World × LULex) Utterance :=
  RSA.Scenario.familySpeaker luFam α

instance (α : ℝ) : IsFiniteKernel (luSpeaker α) :=
  inferInstanceAs (IsFiniteKernel (RSA.Scenario.familySpeaker luFam α))

/-- LU listener (eqs. 12–13): Bayesian inverse over the joint state. -/
noncomputable def luListener (α : ℝ) : Kernel Utterance (World × LULex) :=
  (luSpeaker α)†luPrior

theorem luPrior_singleton_ne_zero (s : World × LULex) : luPrior {s} ≠ 0 := by
  rw [luPrior, uniformOn_univ, Measure.count_singleton]
  simp [ENNReal.mul_eq_top]

private theorem univLU : (Finset.univ : Finset LULex) = {.lit, .oi} := by decide

private theorem luPrior_real_singleton (s : World × LULex) : luPrior.real {s} = 14⁻¹ := by
  rw [luPrior, uniformOn_univ_real_singleton,
    show Fintype.card (World × LULex) = 14 from by decide]
  norm_num

/-! ### The rejected architecture: per-parse normalization -/

/-- The architecture the paper rejects as "conceptually highly implausible"
(p. e85): the full parse family with the parse as a speaker *argument* —
eq. 11 with an enlarged latent set, rather than eq. 21a's pooled choice. -/
noncomputable def perParseSpeaker (α : ℝ) : Kernel (World × Parse) Utterance :=
  RSA.Scenario.familySpeaker readings α

noncomputable def perParsePrior : Measure (World × Parse) := uniformOn Set.univ

instance : IsProbabilityMeasure perParsePrior :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn _))

instance (α : ℝ) : IsFiniteKernel (perParseSpeaker α) :=
  inferInstanceAs (IsFiniteKernel (RSA.Scenario.familySpeaker readings α))

private theorem perParsePrior_singleton_ne_zero (s : World × Parse) :
    perParsePrior {s} ≠ 0 := by
  rw [perParsePrior, uniformOn_univ, Measure.count_singleton]
  simp [ENNReal.mul_eq_top]

private theorem perParsePrior_real_singleton (s : World × Parse) :
    perParsePrior.real {s} = 56⁻¹ := by
  rw [perParsePrior, uniformOn_univ_real_singleton,
    show Fintype.card (World × Parse) = 56 from by decide]
  norm_num

/-! ### The ten findings

Two registers, both closed by `decide`. Certificate findings hold for every
rationality `α > 0`: a decided `Multiset.StrictDominates` fact — strict
stochastic dominance of informativity profiles — settles the fiber-by-rest
odds comparison uniformly. Evaluation findings are genuinely α-dependent
(their direction degenerates as α → 0) and are pinned at the paper's
illustrative α = 5, where the comparison clears to a ℕ inequality via
`Multiset.divPowSum`. -/

private theorem univW : (Finset.univ : Finset World)
    = {wN, wNS, wNA, wNSA, wS, wSA, wA} := by decide

/-- SS exhaustifies the inner quantifier at the paper's illustrative α = 5:
hearing SS, the listener prefers wNS to wNSA (eq. 22's regime). Evaluation
register — the domination certificate provably fails here (wNSA's SS-fiber is
not stochastically dominated), and the preference degenerates as α → 0. -/
theorem ss_inner_exh :
    (gi.listener 5 prior .ss).real {wNSA} < (gi.listener 5 prior .ss).real {wNS} :=
  gi.listener_real_lt_of_divPowSum (k := 5) (D := 12) (by decide) (by decide)
    (prior_singleton_eq wNSA wNS) (prior_singleton_ne_zero wNS)
    (by decide) (by decide) (by decide)

set_option maxRecDepth 1024 in
/-- SS exhaustifies the outer quantifier for every rationality: hearing SS,
the listener prefers wNS to wS. Certificate register. -/
theorem ss_outer_exh {α : ℝ} (hα : 0 < α) :
    (gi.listener α prior .ss).real {wS} < (gi.listener α prior .ss).real {wNS} :=
  gi.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wS wNS)
    (prior_singleton_ne_zero wNS) (by decide)

set_option maxRecDepth 1024 in
/-- AA identifies the unique world where all aliens drank all, for every
rationality: AA's readings are all {wA} (Table 1), so wSA's AA-fiber is empty
and any nonempty product strictly dominates it — the support case of the
certificate register. -/
theorem aa_identifies {α : ℝ} (hα : 0 < α) :
    (gi.listener α prior .aa).real {wSA} < (gi.listener α prior .aa).real {wA} :=
  gi.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wSA wA)
    (prior_singleton_ne_zero wA) (by decide)

set_option maxRecDepth 1024 in
/-- AS exhaustifies the inner quantifier for every rationality: hearing AS,
the listener prefers wS to wA. Certificate register. -/
theorem as_inner_exh {α : ℝ} (hα : 0 < α) :
    (gi.listener α prior .as).real {wA} < (gi.listener α prior .as).real {wS} :=
  gi.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wA wS)
    (prior_singleton_ne_zero wS) (by decide)

/-- GI's parse posterior for SS peaks at the matrix-only parse, whose reading
uniquely identifies wNS, at the paper's illustrative α = 5 (eq. 22's regime).
Pair choice drives this — see `perParse_ss_o_beats_m` for the contrast.
Evaluation register: as α → 0 the singleton reading's informativity advantage
vanishes, so no α-free certificate exists. -/
theorem ss_m_parse_pref : ∀ p : Parse, p ≠ {.matrix} →
    (gi.choicePosterior 5 prior .ss).real {(.ss, p)}
      < (gi.choicePosterior 5 prior .ss).real {(.ss, {.matrix})} := by
  have hnat : ∀ p : Parse, p ≠ {ExhPosition.matrix} →
      (∑ t : World, if t ∈ gi.sem (.ss, p) then
          (12 / (gi.sem (.ss, p)).card) ^ 5
            * ∏ t' ∈ Finset.univ.erase t, (gi.profile t').divPowSum 12 5
        else 0)
        < ∑ t : World, if t ∈ gi.sem (.ss, ({.matrix} : Parse)) then
          (12 / (gi.sem (.ss, ({.matrix} : Parse))).card) ^ 5
            * ∏ t' ∈ Finset.univ.erase t, (gi.profile t').divPowSum 12 5
        else 0 := by decide
  exact fun p hp =>
    gi.choicePosterior_real_lt_of_divPowSum (by decide) (by decide) (by decide)
      prior_singleton_eq prior_singleton_ne_zero rfl rfl (hnat p hp)

/-- Vanilla RSA hearing SS prefers wNA to wNS — the wrong prediction — for
every rationality (cost-free; the direction reverses at the paper's fitted
cost). Certificate register: {6}·{3,4} = {18,24} strictly dominates
{6}·{4,4} = {24,24} with a strictly smaller matched entry and no spare. -/
theorem vanilla_ss_prefers_wNA {α : ℝ} (hα : 0 < α) :
    (vanilla.listener α prior .ss).real {wNS} < (vanilla.listener α prior .ss).real {wNA} :=
  vanilla.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wNS wNA)
    (prior_singleton_ne_zero wNA) (by decide)

set_option maxRecDepth 1024 in
/-- GI corrects vanilla's error for every rationality: hearing SS, the
listener prefers wNS to wNA. Certificate register: wNS's SS-fiber
{1,3,3,3,3,4,4,6} strictly dominates wNA's {3,3,6} — the M-pair's singleton
extension is the spare element. -/
theorem gi_ss_prefers_wNS {α : ℝ} (hα : 0 < α) :
    (gi.listener α prior .ss).real {wNA} < (gi.listener α prior .ss).real {wNS} :=
  gi.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wNA wNS)
    (prior_singleton_ne_zero wNS) (by decide)

set_option maxRecDepth 1024 in
/-- LI derives outer exhaustification for SS at every rationality: wNS over
wS via the OI parse. Certificate register. -/
theorem li_ss_outer_exh {α : ℝ} (hα : 0 < α) :
    (li.listener α prior .ss).real {wS} < (li.listener α prior .ss).real {wNS} :=
  li.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wS wNS)
    (prior_singleton_ne_zero wNS) (by decide)

set_option maxRecDepth 1024 in
/-- LI also gets the wNS-over-wNA ordering that vanilla misses, at every
rationality. Certificate register. -/
theorem li_ss_prefers_wNS {α : ℝ} (hα : 0 < α) :
    (li.listener α prior .ss).real {wNA} < (li.listener α prior .ss).real {wNS} :=
  li.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wNA wNS)
    (prior_singleton_ne_zero wNS) (by decide)

/-- LU keeps wNS above wNA for every rationality: the OI lexicon's ⟦SS⟧
excludes wNA outright, contributing a constant third of the posterior odds at
wNS, while wNA's literal-lexicon share stays below a third (the paper's full
LU-L2 nonetheless concentrates on wNSA, eq. 15). -/
theorem lu_ss_prefers_wNS {α : ℝ} (hα : 0 < α) :
    (luListener α .ss).fst.real {wNA} < (luListener α .ss).fst.real {wNS} := by
  have hκ : luSpeaker α (wNS, LULex.lit) {Utterance.ss} ≠ 0 := by
    rw [luSpeaker, RSA.Scenario.familySpeaker_apply]
    exact (luFam .lit).speaker_apply_singleton_ne_zero hα.le (by decide)
  rw [luListener, posterior_fst_real_lt_iff (luSpeaker α) luPrior
      (comp_apply_singleton_ne_zero _ _ (luPrior_singleton_ne_zero (wNS, .lit)) hκ)]
  simp_rw [luSpeaker, RSA.Scenario.familySpeaker_apply]
  norm_num +decide [univLU, Finset.sum_insert, Finset.sum_singleton, luPrior_real_singleton]
  rw [(luFam .lit).speaker_real_singleton hα, (luFam .oi).speaker_real_singleton hα,
    (luFam .lit).speaker_real_singleton hα, (luFam .oi).speaker_real_singleton hα,
    show (luFam .lit).profile wNS = {3, 4, 6} from by decide,
    show (luFam .lit).profile wNA = {4, 4, 6} from by decide,
    show (luFam .oi).profile wNS = {3, 3, 3} from by decide,
    show (luFam .oi).profile wNA = {3, 3, 3} from by decide,
    Multiset.invPowSum_toReal hα.le (by decide),
    Multiset.invPowSum_toReal hα.le (by decide),
    Multiset.invPowSum_toReal hα.le (by decide),
    show ((luFam LULex.lit).sem Utterance.ss).card = 6 from by decide,
    show ((luFam LULex.oi).sem Utterance.ss).card = 3 from by decide]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]
  norm_num +decide
  have p6 : (0 : ℝ) < (1 / 6 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  have h46 : (1 / 6 : ℝ) ^ α < (1 / 4 : ℝ) ^ α :=
    Real.rpow_lt_rpow (by norm_num) (by norm_num) hα
  have keyA : (1 / 6 : ℝ) ^ α / ((1 / 4 : ℝ) ^ α + ((1 / 4 : ℝ) ^ α + (1 / 6 : ℝ) ^ α))
      < 1 / 3 := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have keyB : (1 / 3 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + ((1 / 3 : ℝ) ^ α + (1 / 3 : ℝ) ^ α))
      = 1 / 3 := by
    rw [div_eq_iff (by positivity)]
    ring
  have keyC : (0 : ℝ) < (1 / 6 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + ((1 / 4 : ℝ) ^ α + (1 / 6 : ℝ) ^ α)) :=
    div_pos p6 (by positivity)
  linarith

set_option maxRecDepth 1024 in
/-- The headline divergence, for every rationality: hearing SS, the
*per-parse-normalized* listener's parse posterior puts more mass on O than on
M. Renormalizing within each parse erases exactly the informativity advantage
of the singleton reading ⟦SS⟧^M that the pooled speaker exploits in
`ss_m_parse_pref`; with `RSA.Scenario.pool_L0` (identical weights), the pair
locates GI's win purely in the position of the latent parameter
(pp. e85–e86). -/
theorem perParse_ss_o_beats_m {α : ℝ} (hα : 0 < α) :
    (((perParseSpeaker α)†perParsePrior) .ss).snd.real {({.matrix} : Parse)}
      < (((perParseSpeaker α)†perParsePrior) .ss).snd.real {({.outer} : Parse)} := by
  have hκ : perParseSpeaker α (wNS, ({.matrix} : Parse)) {Utterance.ss} ≠ 0 := by
    rw [perParseSpeaker, RSA.Scenario.familySpeaker_apply]
    exact (readings _).speaker_apply_singleton_ne_zero hα.le (by decide)
  rw [posterior_snd_real_lt_iff _ _
      (comp_apply_singleton_ne_zero _ _
        (perParsePrior_singleton_ne_zero (wNS, {.matrix})) hκ)]
  simp_rw [perParseSpeaker, RSA.Scenario.familySpeaker_apply]
  norm_num +decide [univW, Finset.sum_insert, Finset.sum_singleton, perParsePrior_real_singleton]
  simp only [(readings ({ExhPosition.matrix} : Parse)).speaker_real_singleton hα,
    (readings ({ExhPosition.outer} : Parse)).speaker_real_singleton hα]
  norm_num +decide
  rw [show (readings ({ExhPosition.matrix} : Parse)).profile wNS = {1, 2, 3} from by decide,
    show (readings ({ExhPosition.outer} : Parse)).profile wNS = {3, 3, 3} from by decide,
    show (readings ({ExhPosition.outer} : Parse)).profile wNA = {3, 3, 3} from by decide,
    show (readings ({ExhPosition.outer} : Parse)).profile wNSA = {3, 3, 3} from by decide,
    show (ext ({ExhPosition.matrix} : Parse) Utterance.ss).card = 1 from by decide,
    show (ext ({ExhPosition.outer} : Parse) Utterance.ss).card = 3 from by decide,
    Multiset.invPowSum_toReal hα.le (by decide),
    Multiset.invPowSum_toReal hα.le (by decide)]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]
  norm_num
  have p2 : (0 : ℝ) < (1 / 2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  have p3 : (0 : ℝ) < (1 / 3 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  have keyM : (1 + ((1 / 2 : ℝ) ^ α + (1 / 3 : ℝ) ^ α))⁻¹ < 1 := by
    rw [inv_lt_one₀ (by positivity)]
    linarith
  have keyO : (1 / 3 : ℝ) ^ α / ((1 / 3 : ℝ) ^ α + ((1 / 3 : ℝ) ^ α + (1 / 3 : ℝ) ^ α))
      = 1 / 3 := by
    rw [div_eq_iff (by positivity)]
    ring
  linarith

end FrankeBergen2020
