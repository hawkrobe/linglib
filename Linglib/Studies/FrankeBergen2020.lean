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
every rationality (`perParse_ss_prefers_o`). LI and LU still derive the
embedded enrichments (`li_ss_outer_exh`, `li_ss_prefers_wNS`,
`lu_ss_prefers_wNS`).

## Main results

* `table1_*` — the paper's Table 1, one lemma per row, including NN's
  distinct matrix row (fn. 7) from the `none ~ not all` lexical alternative
  ([levinson-2000]).
* `ss_m_parse_pref` vs `perParse_ss_prefers_o` — the architectural headline:
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

/-- ⟦SS⟧^M = {wNS} — the reading that "uniquely singles out this world
state" (eq. 22) and drives GI's win; the matrix-alone case of `table1_ss`. -/
theorem m_ss_singleton : ∀ w, exhMeaning pM .ss w ↔ w = wNS := by decide +kernel

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
  ⟨by decide +kernel, by decide +kernel⟩

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
theorem li_excludes_matrix : ∀ l : LIParse, .matrix ∉ l.toParse := by decide +kernel

/-- LU cannot access matrix EXH: neither lexicon includes M. -/
theorem lu_excludes_matrix : ∀ l : LULex, .matrix ∉ l.toParse := by decide +kernel

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
theorem exists_true : ∀ (w : World) (p : Parse), ∃ u, exhMeaning p u w := by decide +kernel

/-! ### The models as combinators over one reading family

Each parse yields a scenario (`readings`); the paper's models are combinators
applied to this single family. Vanilla (§3.1) is the literal member. GI
(eq. 21a) and LI (eq. 18a) pool (utterance, parse) pairs into one choice
space — the speaker *chooses* the parse — while LU (eq. 11) fixes the lexicon
as a speaker argument (`RSA.Scenario.familySpeaker`). By
`RSA.Scenario.pool_L0` the weights agree, so the models differ *only* in the
position of the latent parameter (p. e86); `ss_m_parse_pref` against
`perParse_ss_prefers_o` below turns that difference into diverging
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

/-- LU listener (eqs. 12–13): Bayesian inverse over the joint state. -/
noncomputable def luListener (α : ℝ) : Kernel Utterance (World × LULex) :=
  RSA.Scenario.familyListener luFam α luPrior

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
noncomputable def perParseListener (α : ℝ) : Kernel Utterance (World × Parse) :=
  RSA.Scenario.familyListener readings α perParsePrior

/-! ### The ten findings

Two registers, both closed by `decide`. Certificate findings hold for every
rationality `α > 0`: a decided `Multiset.StrictDominates` fact — strict
stochastic dominance of informativity profiles — settles the fiber-by-rest
odds comparison uniformly. Evaluation findings are genuinely α-dependent
(their direction degenerates as α → 0) and are pinned at the paper's
illustrative α = 5, where the comparison clears to a ℕ inequality via
`Multiset.divPowSum`. -/

/-- Hearing "some of the aliens drank some of their water", the pooled
listener favors the world where no alien drank all of its water over the one
where some did (inner exhaustification). -/
theorem ss_inner_exh :
    (gi.listener 5 prior .ss).real {wNSA} < (gi.listener 5 prior .ss).real {wNS} :=
  gi.listener_real_lt_of_divPowSum (k := 5) (D := 12) (by decide +kernel) (by decide +kernel)
    (prior_singleton_eq wNSA wNS) (prior_singleton_ne_zero wNS)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Hearing "some of the aliens drank some of their water", the pooled
listener favors a world where some alien drank nothing (outer
exhaustification). -/
theorem ss_outer_exh {α : ℝ} (hα : 0 < α) :
    (gi.listener α prior .ss).real {wS} < (gi.listener α prior .ss).real {wNS} :=
  gi.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wS wNS)
    (prior_singleton_ne_zero wNS) (by decide +kernel)

/-- Hearing "all of the aliens drank all of their water", the pooled
listener favors the unique world where every alien did just that. -/
theorem aa_identifies {α : ℝ} (hα : 0 < α) :
    (gi.listener α prior .aa).real {wSA} < (gi.listener α prior .aa).real {wA} :=
  gi.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wSA wA)
    (prior_singleton_ne_zero wA) (by decide +kernel)

/-- Hearing "all of the aliens drank some of their water", the pooled
listener favors the world where every alien drank some but not all (inner
exhaustification). -/
theorem as_inner_exh {α : ℝ} (hα : 0 < α) :
    (gi.listener α prior .as).real {wA} < (gi.listener α prior .as).real {wS} :=
  gi.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wA wS)
    (prior_singleton_ne_zero wS) (by decide +kernel)

/-- Hearing "some of the aliens drank some of their water", the pooled
listener's parse posterior peaks at exhaustification of the whole
sentence. -/
theorem ss_m_parse_pref : ∀ p : Parse, p ≠ pM →
    (gi.choicePosterior 5 prior .ss).real {(.ss, p)}
      < (gi.choicePosterior 5 prior .ss).real {(.ss, pM)} := by
  have hnat : ∀ p : Parse, p ≠ pM →
      (∑ t : World, if t ∈ gi.sem (.ss, p) then
          (12 / (gi.sem (.ss, p)).card) ^ 5
            * ∏ t' ∈ Finset.univ.erase t, (gi.profile t').divPowSum 12 5
        else 0)
        < ∑ t : World, if t ∈ gi.sem (.ss, pM) then
          (12 / (gi.sem (.ss, pM)).card) ^ 5
            * ∏ t' ∈ Finset.univ.erase t, (gi.profile t').divPowSum 12 5
        else 0 := by decide +kernel
  exact fun p hp =>
    gi.choicePosterior_real_lt_of_divPowSum (by decide +kernel) (by decide +kernel)
      (by decide +kernel) prior_singleton_eq prior_singleton_ne_zero rfl rfl (hnat p hp)

/-- Hearing "some of the aliens drank some of their water", the
literal-semantics listener favors all-drinkers over some-but-not-all
drinkers — opposite to the attested preference. -/
theorem vanilla_ss_prefers_wNA {α : ℝ} (hα : 0 < α) :
    (vanilla.listener α prior .ss).real {wNS} < (vanilla.listener α prior .ss).real {wNA} :=
  vanilla.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wNS wNA)
    (prior_singleton_ne_zero wNA) (by decide +kernel)

/-- Hearing "some of the aliens drank some of their water", the pooled
listener favors some-but-not-all drinkers over all-drinkers, as attested. -/
theorem gi_ss_prefers_wNS {α : ℝ} (hα : 0 < α) :
    (gi.listener α prior .ss).real {wNA} < (gi.listener α prior .ss).real {wNS} :=
  gi.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wNA wNS)
    (prior_singleton_ne_zero wNS) (by decide +kernel)

/-- Hearing "some of the aliens drank some of their water", the matrix-free
pooled listener still favors a world where some alien drank nothing (outer
exhaustification). -/
theorem li_ss_outer_exh {α : ℝ} (hα : 0 < α) :
    (li.listener α prior .ss).real {wS} < (li.listener α prior .ss).real {wNS} :=
  li.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wS wNS)
    (prior_singleton_ne_zero wNS) (by decide +kernel)

/-- Hearing "some of the aliens drank some of their water", the matrix-free
pooled listener favors some-but-not-all drinkers over all-drinkers. -/
theorem li_ss_prefers_wNS {α : ℝ} (hα : 0 < α) :
    (li.listener α prior .ss).real {wNA} < (li.listener α prior .ss).real {wNS} :=
  li.listener_real_lt_of_prodMul_strictDominates hα (prior_singleton_eq wNA wNS)
    (prior_singleton_ne_zero wNS) (by decide +kernel)

/-- Hearing "some of the aliens drank some of their water", the
lexical-uncertainty listener favors some-but-not-all drinkers over
all-drinkers. -/
theorem lu_ss_prefers_wNS {α : ℝ} (hα : 0 < α) :
    (luListener α .ss).fst.real {wNA} < (luListener α .ss).fst.real {wNS} := by
  rw [luListener, RSA.Scenario.familyListener_fst_real_lt_iff luFam hα.le
      luPrior_singleton_eq luPrior_singleton_ne_zero
      (by decide +kernel : wNS ∈ (luFam .lit).sem .ss)]
  calc (∑ l : LULex, ((luFam l).speaker α wNA).real {.ss})
      = ((luFam .lit).speaker α wNA).real {.ss} :=
        Fintype.sum_eq_single LULex.lit fun
          | .lit, hl => absurd rfl hl
          | .oi, _ => (luFam .oi).speaker_real_singleton_eq_zero hα
              (by decide +kernel : wNA ∉ (luFam .oi).sem .ss)
    _ < ((luFam .oi).speaker α wNS).real {.ss} := by
        rw [(luFam .oi).speaker_real_singleton_of_profile_replicate hα
          (by decide +kernel : (luFam .oi).profile wNS = Multiset.replicate 3 3)
          (by decide +kernel : wNS ∈ (luFam .oi).sem .ss)]
        have hsum := (luFam .lit).sum_speaker_real_singleton_le_one α wNA {.ss, .sn, .sa}
        rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at hsum
        have hsn := (luFam .lit).speaker_real_singleton_lt_of_card_lt hα
          (by decide +kernel : wNA ∈ (luFam .lit).sem .ss)
          (by decide +kernel : wNA ∈ (luFam .lit).sem .sn) (by decide +kernel)
        have hsa := (luFam .lit).speaker_real_singleton_lt_of_card_lt hα
          (by decide +kernel : wNA ∈ (luFam .lit).sem .ss)
          (by decide +kernel : wNA ∈ (luFam .lit).sem .sa) (by decide +kernel)
        linarith
    _ ≤ ∑ l : LULex, ((luFam l).speaker α wNS).real {.ss} :=
        Finset.single_le_sum
          (fun l _ => measureReal_nonneg (μ := (luFam l).speaker α wNS))
          (Finset.mem_univ LULex.oi)

/-- Hearing "some of the aliens drank some of their water", the per-parse
listener favors exhaustifying the outer quantifier over exhaustifying the
whole sentence. -/
theorem perParse_ss_prefers_o {α : ℝ} (hα : 0 < α) :
    (perParseListener α .ss).snd.real {pM} < (perParseListener α .ss).snd.real {pO} := by
  have hOprof : ∀ w ∈ ({wNS, wNA, wNSA} : Finset World),
      (readings pO).profile w = Multiset.replicate 3 3 := by decide +kernel
  have hOmem : ∀ w ∈ ({wNS, wNA, wNSA} : Finset World),
      w ∈ (readings pO).sem .ss := by decide +kernel
  rw [perParseListener, RSA.Scenario.familyListener_snd_real_lt_iff readings hα.le
      perParsePrior_singleton_eq perParsePrior_singleton_ne_zero
      (mem_ext.mpr ((m_ss_singleton wNS).mpr rfl))]
  calc (∑ w : World, ((readings pM).speaker α w).real {.ss})
      = ((readings pM).speaker α wNS).real {.ss} :=
        Fintype.sum_eq_single wNS fun w hw =>
          (readings pM).speaker_real_singleton_eq_zero hα fun hmem =>
            hw ((m_ss_singleton w).mp (mem_ext.mp hmem))
    _ < 1 :=
        (readings pM).speaker_real_singleton_lt_one hα.le
          (nofun : Utterance.sn ≠ Utterance.ss)
          (by decide +kernel : wNS ∈ (readings pM).sem .sn)
    _ = ∑ w ∈ ({wNS, wNA, wNSA} : Finset World),
          ((readings pO).speaker α w).real {.ss} := by
        rw [Finset.sum_eq_card_nsmul fun w hw =>
            (readings pO).speaker_real_singleton_of_profile_replicate hα
              (hOprof w hw) (hOmem w hw),
          show ({wNS, wNA, wNSA} : Finset World).card = 3 from by decide +kernel]
        norm_num
    _ ≤ ∑ w : World, ((readings pO).speaker α w).real {.ss} :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun w _ _ => measureReal_nonneg

end FrankeBergen2020
