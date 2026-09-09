import Linglib.Pragmatics.RSA.Uniform
import Linglib.Pragmatics.Implicature.SomeAll
import Linglib.Semantics.Exhaustification.Finite
import Mathlib.Data.List.ProdSigma
import Mathlib.Tactic.DeriveFintype

/-!
# Franke and Bergen (2020): Theory-Driven Statistical Modeling for Semantics and Pragmatics

This file formalizes [franke-bergen-2020]'s comparison of four rational speech act models
([frank-goodman-2012]) of the nested Aristotelians *Q₁ of the aliens drank Q₂ of their water*,
with *none*, *some* and *all* in each position. An alien's drinking amount is a `SomeAllWorld`, a
world state is the nonempty set of amounts some alien realizes, and a parse is the set of sites,
among the whole sentence and the two quantifiers, at which an exhaustivity operator applies; the
readings of every utterance under every parse are the paper's Table 1, one characterization per
utterance (`table1_ss` and its siblings). The models differ in where the parse enters the
speaker. The vanilla model has only the literal parse; lexical uncertainty fixes a lexicon per
speaker, the parse an argument of the speaker and a latent the listener marginalizes
([bergen-levy-goodman-2016], [potts-etal-2016]); the local- and global-implicature speakers
instead choose an utterance together with a parse, over the four matrix-free parses or over all
eight, one softmax over pairs per world heard through the utterance alone. The global model
corrects the interpretation of *some of the aliens drank some of their water* that the vanilla
model gets wrong, and its parse posterior peaks at the matrix-only parse, whose reading singles
out the world with none- and some-drinkers only and is unavailable to the other two models: the
paper's explanation of the global model's win in its Bayesian model comparison. The advantage
exists because the pooled speaker normalizes over pairs; under the per-parse normalization the
paper rejects, exhaustifying the outer quantifier beats exhaustifying the whole sentence at every
rationality (`perParse_ss_prefers_o`).

## Implementation notes

* One reading family, `ext`, generates every model: the vanilla model is its literal member, the
  pooled models run `RSA.uniformJointListener` over utterance–parse pairs, and lexical
  uncertainty, like the rejected per-parse architecture, fixes the latent as a speaker argument
  through `RSA.familySpeaker`. Sentential alternatives range over a fourth quantifier, *not all*,
  that is never uttered: the paper's distinction between grammatical and utterance alternatives,
  which its model comparison favors over the alternative set of [gotzner-romoli-2018].
* Findings that hold at every rationality are closed by strict stochastic dominance of
  informativity profiles (`Multiset.StrictDominates`); the rationality-dependent ones are pinned
  at the paper's illustrative value of 5, where the comparisons clear to inequalities of naturals.
* The paper's cost term for *none*-initial utterances and its fixed error rate are omitted, and
  the vanilla preference reverses at the fitted cost. The second-level layer of the
  lexical-uncertainty model ([lassiter-goodman-2017]) is omitted; the first-level listener
  formalized here keeps the preference the paper's second-level listener loses.
* The paper's matrix exhaustivity operator is not innocent exclusion ([fox-2007]):
  `moi_ss_ne_innocent_exclusion`. The distinct matrix reading of *none of the aliens drank none
  of their water* comes from the lexical alternative *not all* of *none* ([levinson-2000]).

## References

* [franke-bergen-2020]
* [frank-goodman-2012]
* [bergen-levy-goodman-2016]
* [potts-etal-2016]
* [lassiter-goodman-2017]
* [gotzner-romoli-2018]
* [levinson-2000]
* [fox-2007]
-/

namespace FrankeBergen2020

open scoped ENNReal
open MeasureTheory ProbabilityTheory

/-! ## The grammar of readings -/

/-! ### Domain -/

/-- An alien's drinking amount: none, some but not all, or all of its water. -/
abbrev AlienType := SomeAllWorld

/-- A world state is the set of drinking amounts realized by at least one
alien — a nonempty subset of the three amounts. -/
def World := {s : Finset AlienType // s.Nonempty}

instance : DecidableEq World := Subtype.instDecidableEq
instance : Fintype World := Subtype.fintype _

instance : Membership AlienType World := ⟨λ w t => t ∈ w.val⟩

instance (t : AlienType) (w : World) : Decidable (t ∈ w) :=
  inferInstanceAs (Decidable (t ∈ w.val))

instance : MeasurableSpace World := ⊤
instance : DiscreteMeasurableSpace World := ⟨λ _ => trivial⟩

/-- The world with only N-type aliens (each drank none). -/
def wN : World := ⟨{.none}, Finset.singleton_nonempty _⟩
/-- The world with N-type and S-type aliens. -/
def wNS : World := ⟨{.none, .someNotAll}, by decide +kernel⟩
/-- The world with N-type and A-type aliens. -/
def wNA : World := ⟨{.none, .all}, by decide +kernel⟩
/-- The world with all three alien types. -/
def wNSA : World := ⟨{.none, .someNotAll, .all}, by decide +kernel⟩
/-- The world with only S-type aliens (each drank some but not all). -/
def wS : World := ⟨{.someNotAll}, Finset.singleton_nonempty _⟩
/-- The world with S-type and A-type aliens. -/
def wSA : World := ⟨{.someNotAll, .all}, by decide +kernel⟩
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

instance : MeasurableSpace Parse := ⊤
instance : DiscreteMeasurableSpace Parse := ⟨λ _ => trivial⟩
instance : Nonempty Parse := ⟨∅⟩

/-- The matrix-only parse M. -/
def pM : Parse := {.matrix}

/-- The outer-only parse O. -/
def pO : Parse := {.outer}

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

instance : Nonempty Utterance := ⟨.nn⟩
instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨λ _ => trivial⟩

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
  | .none => λ t => ¬ t.atLeastOne
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

/-- *not all* is the negation of *all*, definitionally. -/
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

instance (a : AltSentence) : DecidablePred (altLiteral a) := λ _ =>
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

instance (qi : AristQuant) (p : Parse) : DecidablePred (enrichedSat qi p) := λ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- The sub-matrix reading: in-situ enrichments, with outer EXH (Exh(some) at
the outer position) as an implication guard. -/
def subMatrix (p : Parse) (u : Utterance) (w : World) : Prop :=
  AltQuant.eval (↑u.outer) w (enrichedSat u.inner p)
  ∧ (ExhPosition.outer ∈ p ∧ u.outer = .some →
      ¬ AltQuant.eval .all w (enrichedSat u.inner p))

instance (p : Parse) (u : Utterance) : DecidablePred (subMatrix p u) := λ _ =>
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

instance (p : Parse) (u : Utterance) : DecidablePred (matrixExh p u) := λ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- Exhaustified meaning under a parse: the sub-matrix reading, negating the
strictly stronger alternatives when M is in the parse and doing so is
noncontradictory (eq. A2). -/
def exhMeaning (p : Parse) (u : Utterance) (w : World) : Prop :=
  subMatrix p u w ∧ (ExhPosition.matrix ∈ p ∧ (∃ w', matrixExh p u w') →
    ∀ a ∈ matrixAlts u, StrictlyStronger p u a → ¬ altLiteral a w)

instance (p : Parse) (u : Utterance) : DecidablePred (exhMeaning p u) := λ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Truth-table verification (the paper's Table 1)

One characterization per utterance, total over all eight parses — the paper's
row-groups appear as the guards. Each reading is a membership predicate on
the world's alien-type set, not a truth vector. -/

/-- Table 1, NN: no N-types; matrix parses additionally negate "none drank
not all" (= {wA}) — the fn. 7 reading from the `none ~ not all` alternative. -/
theorem table1_nn : ∀ (p : Parse) (w : World),
    exhMeaning p .nn w ↔ (.none ∉ w ∧ (.matrix ∈ p → w ≠ wA)) := by decide +kernel

/-- Table 1, NS: only wN literally; inner EXH weakens to the S-free worlds,
whereupon matrix EXH negates the sentence's own now-stronger literal {wN}. -/
theorem table1_ns : ∀ (p : Parse) (w : World),
    exhMeaning p .ns w ↔
      if .inner ∈ p then .someNotAll ∉ w ∧ (.matrix ∈ p → w ≠ wN)
      else w = wN := by decide +kernel

/-- Table 1, NA: no A-types; matrix EXH negates the stronger NS = {wN}. -/
theorem table1_na : ∀ (p : Parse) (w : World),
    exhMeaning p .na w ↔ (.all ∉ w ∧ (.matrix ∈ p → w ≠ wN)) := by decide +kernel

/-- Table 1, SN: an N-type exists; outer or matrix EXH negates AN = {wN}. -/
theorem table1_sn : ∀ (p : Parse) (w : World),
    exhMeaning p .sn w ↔
      (.none ∈ w ∧ (.outer ∈ p ∨ .matrix ∈ p → w ≠ wN)) := by decide +kernel

/-- Table 1, SS: the five row-groups — literal; inner EXH requires an S-type
(matrix then vacuous); adding outer EXH excludes wS; outer alone keeps mixed
worlds; matrix alone pins wNS. -/
theorem table1_ss : ∀ (p : Parse) (w : World),
    exhMeaning p .ss w ↔
      if .inner ∈ p then .someNotAll ∈ w ∧ (.outer ∈ p → w ≠ wS)
      else if .outer ∈ p then .none ∈ w ∧ w ≠ wN
      else if .matrix ∈ p then w = wNS
      else w ≠ wN := by decide +kernel

/-- Table 1, SA: an A-type exists; outer or matrix EXH excludes wA. -/
theorem table1_sa : ∀ (p : Parse) (w : World),
    exhMeaning p .sa w ↔
      (.all ∈ w ∧ (.outer ∈ p ∨ .matrix ∈ p → w ≠ wA)) := by decide +kernel

/-- Table 1, AN: only wN, under every parse. -/
theorem table1_an : ∀ (p : Parse) (w : World), exhMeaning p .an w ↔ w = wN := by decide +kernel

/-- Table 1, AS: no N-types; inner EXH pins wS; matrix EXH without inner
negates AA, excluding wA. -/
theorem table1_as : ∀ (p : Parse) (w : World),
    exhMeaning p .as w ↔
      if .inner ∈ p then w = wS
      else .none ∉ w ∧ (.matrix ∈ p → w ≠ wA) := by decide +kernel

/-- Table 1, AA: only wA, under every parse. -/
theorem table1_aa : ∀ (p : Parse) (w : World), exhMeaning p .aa w ↔ w = wA := by decide +kernel

/-- Literal meaning is the empty parse's exhaustified meaning. -/
theorem literal_eq_exh_none : ∀ (u : Utterance) (w : World),
    literalMeaning u w ↔ exhMeaning ∅ u w := by decide +kernel

/-- ⟦SS⟧^M = {wNS}, the reading that "uniquely singles out this world state" in the
discussion of eq. 22 and drives GI's win; the matrix-alone case of `table1_ss`. -/
theorem m_ss_singleton : ∀ w, exhMeaning pM .ss w ↔ w = wNS := by decide +kernel

/-- The matrix operator (eq. A2) is not Fox-style innocent exclusion
([fox-2007]): at MOI its strictly-stronger filter is empty and ⟦SS⟧^MOI keeps
wSA, which innocent exclusion over the same alternatives excludes. -/
theorem moi_ss_ne_innocent_exclusion :
    exhMeaning {.matrix, .outer, .inner} .ss wSA
      ∧ wSA ∉ Exhaustification.innocent.exh
          (Exhaustification.altsFromPreds
            ((matrixAlts .ss).map λ a w => decide (altLiteral a w)))
          (Exhaustification.predToFinset
            λ w => decide (exhMeaning {.outer, .inner} .ss w)) :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- Every `(world, parse)` state has a true utterance. -/
theorem exists_true : ∀ (w : World) (p : Parse), ∃ u, exhMeaning p u w := by decide +kernel

/-! ## The models -/

/-! ### The reading family and the pooled models

Each parse yields an extension per utterance (`ext`); the paper's models are
the uniform-prior pipeline applied to this single family. Vanilla (§3.1) is the
literal member. GI (eq. 21a) and LI (eq. 18a) pool (utterance, parse) pairs
into one choice space heard as the utterance — the speaker *chooses* the
parse — while LU (eq. 11) fixes the lexicon as a speaker argument
(`RSA.familySpeaker`). The weights agree (`RSA.familySpeaker_apply`), so the
models differ *only* in the position of the latent parameter (p. e86);
`ss_m_parse_pref` against `perParse_ss_prefers_o` below turns that
difference into diverging predictions. Rationality is a parameter of the
derived kernels, and findings quantify over it wherever the paper's argument
does. -/

/-- The extension of an utterance under a parse. -/
def ext (p : Parse) (u : Utterance) : Finset World :=
  Finset.univ.filter (exhMeaning p u)

@[simp] theorem mem_ext {p : Parse} {u : Utterance} {w : World} :
    w ∈ ext p u ↔ exhMeaning p u w := by
  simp [ext]

/-- The GI choice space (eq. 21a): (utterance, parse) pairs over the full reading
family, heard as the utterance. -/
def giSem (cl : Utterance × Parse) : Finset World := ext cl.2 cl.1

/-- LI parse: lit, I, O, or OI — matrix-EXH parses are unavailable. -/
inductive LIParse where
  | lit | i | o | oi
  deriving DecidableEq, Repr, Fintype

instance : Nonempty LIParse := ⟨.lit⟩
instance : MeasurableSpace LIParse := ⊤
instance : DiscreteMeasurableSpace LIParse := ⟨λ _ => trivial⟩

/-- Map LI parse to the full parse space. -/
def LIParse.toParse : LIParse → Parse
  | .lit => ∅
  | .i => {.inner}
  | .o => {.outer}
  | .oi => {.outer, .inner}

/-- LI cannot access matrix EXH: no LI parse includes M. -/
theorem li_excludes_matrix : ∀ l : LIParse, .matrix ∉ l.toParse := by decide +kernel

/-- The LI choice space (eq. 18a): pairs over the matrix-free parses. -/
def liSem (cl : Utterance × LIParse) : Finset World := ext cl.2.toParse cl.1

theorem vanilla_expressible : ∀ w, ∃ u, w ∈ ext ∅ u := λ w =>
  (exists_true w ∅).imp λ _ h => mem_ext.mpr h

theorem gi_expressible : ∀ w, ∃ c, w ∈ giSem c := λ w =>
  (exists_true w ∅).elim λ u h => ⟨(u, ∅), mem_ext.mpr h⟩

theorem li_expressible : ∀ w, ∃ c, w ∈ liSem c := λ w =>
  (exists_true w ∅).elim λ u h => ⟨(u, .lit), mem_ext.mpr h⟩

/-- The vanilla listener (§3.1): the literal reading only. -/
noncomputable abbrev vanillaListener (α : ℝ) : Kernel Utterance World :=
  (RSA.uniformJointListener (ext ∅) id α).fst

/-- The GI listener (eq. 21b), marginalized to worlds. -/
noncomputable abbrev giListener (α : ℝ) : Kernel Utterance World :=
  (RSA.uniformJointListener giSem Prod.fst α).fst

/-- The GI parse posterior: the joint listener of eq. 21b marginalized to parses. -/
noncomputable abbrev giParsePosterior (α : ℝ) : Kernel Utterance (Utterance × Parse) :=
  (RSA.uniformJointListener giSem Prod.fst α).snd

/-- The LI listener (eq. 18b), marginalized to worlds. -/
noncomputable abbrev liListener (α : ℝ) : Kernel Utterance World :=
  (RSA.uniformJointListener liSem Prod.fst α).fst

/-! ### Lexical uncertainty: the latent as a speaker argument -/

/-- LU lexicon: literal or OI (inner + outer EXH). Each speaker has a fixed
lexicon; the listener marginalizes over the two lexica. -/
inductive LULex where
  | lit | oi
  deriving DecidableEq, Repr, Fintype

instance : Nonempty LULex := ⟨.lit⟩
instance : MeasurableSpace LULex := ⊤
instance : DiscreteMeasurableSpace LULex := ⟨λ _ => trivial⟩

/-- Map LU lexicon to the corresponding parse. -/
def LULex.toParse : LULex → Parse
  | .lit => ∅
  | .oi => {.outer, .inner}

/-- LU cannot access matrix EXH: neither lexicon includes M. -/
theorem lu_excludes_matrix : ∀ l : LULex, .matrix ∉ l.toParse := by decide +kernel

/-- The LU speaker family (eq. 11): one uniform literal listener per lexicon. -/
noncomputable abbrev luFam (l : LULex) : Kernel Utterance World :=
  RSA.uniformListener (ext l.toParse)

/-- LU's joint prior: the lexicon is drawn with the world. -/
noncomputable def luPrior : Measure (World × LULex) := uniformOn Set.univ

instance : IsProbabilityMeasure luPrior :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn _))

/-- LU listener (eqs. 12–13): Bayesian inverse over the joint state. -/
noncomputable def luListener (α : ℝ) : Kernel Utterance (World × LULex) :=
  RSA.familyListener luFam α 1 luPrior

theorem luPrior_singleton_eq (p q : World × LULex) : luPrior {p} = luPrior {q} := by
  simp [luPrior, uniformOn_univ]

theorem luPrior_singleton_ne_zero (s : World × LULex) : luPrior {s} ≠ 0 := by
  rw [luPrior, uniformOn_univ, Measure.count_singleton]
  simp [ENNReal.mul_eq_top]

/-! ### The rejected architecture: per-parse normalization -/

/-- The architecture the paper rejects as "conceptually highly implausible"
(p. e85): the full parse family with the parse as a speaker *argument* —
eq. 11 with an enlarged latent set, rather than eq. 21a's pooled choice. -/
noncomputable def perParsePrior : Measure (World × Parse) := uniformOn Set.univ

instance : IsProbabilityMeasure perParsePrior :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn _))

theorem perParsePrior_singleton_eq (p q : World × Parse) :
    perParsePrior {p} = perParsePrior {q} := by
  simp [perParsePrior, uniformOn_univ]

theorem perParsePrior_singleton_ne_zero (s : World × Parse) :
    perParsePrior {s} ≠ 0 := by
  rw [perParsePrior, uniformOn_univ, Measure.count_singleton]
  simp [ENNReal.mul_eq_top]

/-- Listener of the rejected architecture: the Bayesian inverse of the
per-parse speaker over the joint (world, parse) state. -/
noncomputable abbrev perParseFam (p : Parse) : Kernel Utterance World :=
  RSA.uniformListener (ext p)

noncomputable def perParseListener (α : ℝ) : Kernel Utterance (World × Parse) :=
  RSA.familyListener perParseFam α 1 perParsePrior

/-! ## The findings -/

/-! ### Exhaustified interpretation -/

/-- Hearing "some of the aliens drank some of their water", the pooled
listener favors the world where no alien drank all of its water over the one
where some did (inner exhaustification). -/
theorem ss_inner_exh :
    (giListener 5 .ss).real {wNSA} < (giListener 5 .ss).real {wNS} :=
  RSA.uniformJointListener_fst_real_lt_of_divPowSum giSem Prod.fst gi_expressible (k := 5)
    (D := 12) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Hearing "some of the aliens drank some of their water", the pooled
listener favors a world where some alien drank nothing (outer
exhaustification). -/
theorem ss_outer_exh {α : ℝ} (hα : 0 < α) :
    (giListener α .ss).real {wS} < (giListener α .ss).real {wNS} :=
  RSA.uniformJointListener_fst_real_lt_of_prodMul_strictDominates giSem Prod.fst gi_expressible hα
    (by decide +kernel)

/-- Hearing "all of the aliens drank all of their water", the pooled
listener favors the unique world where every alien did just that. -/
theorem aa_identifies {α : ℝ} (hα : 0 < α) :
    (giListener α .aa).real {wSA} < (giListener α .aa).real {wA} :=
  RSA.uniformJointListener_fst_real_lt_of_prodMul_strictDominates giSem Prod.fst gi_expressible hα
    (by decide +kernel)

/-- Hearing "all of the aliens drank some of their water", the pooled
listener favors the world where every alien drank some but not all (inner
exhaustification). -/
theorem as_inner_exh {α : ℝ} (hα : 0 < α) :
    (giListener α .as).real {wA} < (giListener α .as).real {wS} :=
  RSA.uniformJointListener_fst_real_lt_of_prodMul_strictDominates giSem Prod.fst gi_expressible hα
    (by decide +kernel)

/-! ### The model comparison -/

/-- Hearing "some of the aliens drank some of their water", the
literal-semantics listener favors all-drinkers over some-but-not-all
drinkers — opposite to the attested preference. -/
theorem vanilla_ss_prefers_wNA {α : ℝ} (hα : 0 < α) :
    (vanillaListener α .ss).real {wNS} < (vanillaListener α .ss).real {wNA} :=
  RSA.uniformJointListener_fst_real_lt_of_prodMul_strictDominates (ext ∅) id vanilla_expressible
    hα (by decide +kernel)

/-- Hearing "some of the aliens drank some of their water", the pooled
listener favors some-but-not-all drinkers over all-drinkers, as attested. -/
theorem gi_ss_prefers_wNS {α : ℝ} (hα : 0 < α) :
    (giListener α .ss).real {wNA} < (giListener α .ss).real {wNS} :=
  RSA.uniformJointListener_fst_real_lt_of_prodMul_strictDominates giSem Prod.fst gi_expressible hα
    (by decide +kernel)

/-- Hearing "some of the aliens drank some of their water", the matrix-free
pooled listener still favors a world where some alien drank nothing (outer
exhaustification). -/
theorem li_ss_outer_exh {α : ℝ} (hα : 0 < α) :
    (liListener α .ss).real {wS} < (liListener α .ss).real {wNS} :=
  RSA.uniformJointListener_fst_real_lt_of_prodMul_strictDominates liSem Prod.fst li_expressible hα
    (by decide +kernel)

/-- Hearing "some of the aliens drank some of their water", the matrix-free
pooled listener favors some-but-not-all drinkers over all-drinkers. -/
theorem li_ss_prefers_wNS {α : ℝ} (hα : 0 < α) :
    (liListener α .ss).real {wNA} < (liListener α .ss).real {wNS} :=
  RSA.uniformJointListener_fst_real_lt_of_prodMul_strictDominates liSem Prod.fst li_expressible hα
    (by decide +kernel)

/-- Hearing "some of the aliens drank some of their water", the
lexical-uncertainty listener favors some-but-not-all drinkers over
all-drinkers. -/
theorem lu_ss_prefers_wNS {α : ℝ} (hα : 0 < α) :
    (luListener α .ss).fst.real {wNA} < (luListener α .ss).fst.real {wNS} := by
  rw [luListener, RSA.familyListener_fst_real_lt_iff luFam luPrior_singleton_eq
      luPrior_singleton_ne_zero (RSA.uniformSpeaker_apply_singleton_ne_zero
        (ext LULex.lit.toParse) hα.le (by decide +kernel : wNS ∈ ext LULex.lit.toParse .ss))]
  calc (∑ l : LULex, (RSA.speaker α 1 (luFam l) wNA).real {.ss})
      = (RSA.uniformSpeaker (ext LULex.lit.toParse) α wNA).real {.ss} :=
        Fintype.sum_eq_single LULex.lit λ
          | .lit, hl => absurd rfl hl
          | .oi, _ => RSA.uniformSpeaker_real_singleton_eq_zero (ext LULex.oi.toParse) hα
              (by decide +kernel : wNA ∉ ext LULex.oi.toParse .ss)
    _ < (RSA.uniformSpeaker (ext LULex.oi.toParse) α wNS).real {.ss} := by
        rw [RSA.uniformSpeaker_real_singleton_of_profile_replicate (ext LULex.oi.toParse) hα
          (by decide +kernel : RSA.profile (ext LULex.oi.toParse) wNS = Multiset.replicate 3 3)
          (by decide +kernel : wNS ∈ ext LULex.oi.toParse .ss)]
        have hsum := RSA.sum_uniformSpeaker_real_singleton_le_one (ext LULex.lit.toParse) α wNA
          {.ss, .sn, .sa}
        rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at hsum
        have hsn := RSA.uniformSpeaker_real_singleton_lt_of_card_lt (ext LULex.lit.toParse) hα
          (by decide +kernel : wNA ∈ ext LULex.lit.toParse .ss)
          (by decide +kernel : wNA ∈ ext LULex.lit.toParse .sn) (by decide +kernel)
        have hsa := RSA.uniformSpeaker_real_singleton_lt_of_card_lt (ext LULex.lit.toParse) hα
          (by decide +kernel : wNA ∈ ext LULex.lit.toParse .ss)
          (by decide +kernel : wNA ∈ ext LULex.lit.toParse .sa) (by decide +kernel)
        linarith
    _ ≤ ∑ l : LULex, (RSA.speaker α 1 (luFam l) wNS).real {.ss} :=
        Finset.single_le_sum
          (λ l _ => measureReal_nonneg (μ := RSA.speaker α 1 (luFam l) wNS))
          (Finset.mem_univ LULex.oi)

/-! ### The position of the latent parameter -/

/-- Hearing "some of the aliens drank some of their water", the pooled
listener's parse posterior peaks at exhaustification of the whole
sentence. -/
theorem ss_m_parse_pref : ∀ p : Parse, p ≠ pM →
    (giParsePosterior 5 .ss).real {(.ss, p)} < (giParsePosterior 5 .ss).real {(.ss, pM)} :=
  λ p _ =>
  RSA.uniformJointListener_snd_real_lt_of_divPowSum giSem Prod.fst gi_expressible (k := 5)
    (D := 12) (by decide +kernel) rfl rfl (by revert p; decide +kernel)

/-- Hearing "some of the aliens drank some of their water", the per-parse
listener favors exhaustifying the outer quantifier over exhaustifying the
whole sentence. -/
theorem perParse_ss_prefers_o {α : ℝ} (hα : 0 < α) :
    (perParseListener α .ss).snd.real {pM} < (perParseListener α .ss).snd.real {pO} := by
  have hOprof : ∀ w ∈ ({wNS, wNA, wNSA} : Finset World),
      RSA.profile (ext pO) w = Multiset.replicate 3 3 := by decide +kernel
  have hOmem : ∀ w ∈ ({wNS, wNA, wNSA} : Finset World), w ∈ ext pO .ss := by decide +kernel
  rw [perParseListener, RSA.familyListener_snd_real_lt_iff perParseFam
      perParsePrior_singleton_eq perParsePrior_singleton_ne_zero
      (RSA.uniformSpeaker_apply_singleton_ne_zero (ext pM) hα.le
        (mem_ext.mpr ((m_ss_singleton wNS).mpr rfl)))]
  calc (∑ w : World, (RSA.uniformSpeaker (ext pM) α w).real {.ss})
      = (RSA.uniformSpeaker (ext pM) α wNS).real {.ss} :=
        Fintype.sum_eq_single wNS λ w hw =>
          RSA.uniformSpeaker_real_singleton_eq_zero (ext pM) hα λ hmem =>
            hw ((m_ss_singleton w).mp (mem_ext.mp hmem))
    _ < 1 :=
        RSA.uniformSpeaker_real_singleton_lt_one (ext pM) hα.le
          (nofun : Utterance.sn ≠ Utterance.ss) (by decide +kernel : wNS ∈ ext pM .sn)
    _ = ∑ w ∈ ({wNS, wNA, wNSA} : Finset World),
          (RSA.uniformSpeaker (ext pO) α w).real {.ss} := by
        rw [Finset.sum_eq_card_nsmul λ w hw =>
            RSA.uniformSpeaker_real_singleton_of_profile_replicate (ext pO) hα
              (hOprof w hw) (hOmem w hw),
          show ({wNS, wNA, wNSA} : Finset World).card = 3 from by decide +kernel]
        norm_num
    _ ≤ ∑ w : World, (RSA.uniformSpeaker (ext pO) α w).real {.ss} :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          λ w _ _ => measureReal_nonneg

end FrankeBergen2020
