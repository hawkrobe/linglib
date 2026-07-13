import Mathlib.Tactic.DeriveFintype
import Linglib.Pragmatics.Implicature.Defs
import Linglib.Semantics.Exhaustification.InnocentExclusion
import Linglib.Semantics.Alternatives.Lexical
import Linglib.Semantics.Genericity.SortedOntology
import Linglib.Data.Examples.CohenErteschikShir2002
import Linglib.Fragments.German.BarePluralWordOrder

/-!
# Blind Mandatory Scalar Implicatures
[magri-2009]

[magri-2009]. Natural Language Semantics 17(3): 245–297.
DOI: 10.1007/s11050-009-9042-x.

Three pieces form the substantive core of the paper:

1. **Blindness Hypothesis (BH)** (§3.2.2, eq. (32)): The exhaustivity
   operator EXH computes the strengthened meaning using *logical*
   entailment (→_W), not entailment given common knowledge (→_{W_ck}).

2. **Mismatch Hypothesis (MH)** (§3.2.2, eq. (33)): If the blind
   strengthened meaning EXH(φ) is a contradiction given common knowledge
   (EXH(φ) ∩ W_ck = ∅), then φ sounds odd.

3. **Mandatoriness machinery** (§3.2.5, eq. (41)–(43)): EXH is mandatory
   in matrix clauses (eq. 41); a contextual relevance variable R subject
   to (43a) "uttered ⇒ relevant" and (43b) "relevance closed under
   contextual equivalence" makes mismatching SIs mandatory while leaving
   standard SIs non-mandatory. The mandatoriness is the load-bearing
   premise — without it, the SI could be cancelled and the deviance
   rescued (Magri's §1 "robustness" claim).

## Substrate split

`BlindScenario` + `strengthened` + `blindOdd` capture (1) and (2): the
*outcome* of mismatching SIs. The deviance prediction is correct under
mandatoriness as an external assumption.

`RelevantBlindScenario` adds R as a structure field with (43a)/(43b) as
laws, and `strengthenedR` implements the R-relativized EXH (eq. (42)).
The substantive theorem `mismatching_alt_relevant` proves Magri's
mandatoriness consequence: when target and alternative are
CK-equivalent, R cannot block the alternative — the SI is mandatory.

## Introductory Example

"# Some Italians come from a warm country" (ex. (2))
- Literal: some Italians come from a warm country
- Strengthened (blind, via BH): some BUT NOT ALL Italians come from a warm country
- CK: Italy is warm → all Italians come from a warm country
- Strengthened ∩ CK = ∅ → odd (via MH)
- "Some" and "all" are CK-equivalent (both denote {allWarm} in CK) →
  R(all) = R(some) = 1 → SI is mandatory (eq. 43a + 43b consequence).

## Application to Individual-Level Predicates

The paper's main contribution (§4) derives properties of individual-level
predicates (ILPs) from BH + MH via assumption (70): ILPs are
**homogeneous** — if an i-predicate holds at any time in W_ck, it holds at
all times. This homogeneity makes blind strengthening systematically
contradict CK for i-predicate constructions.

Key applications: "#Sometimes, John is tall" (§4.1), bare plural subject
restrictions (§4.2), embedding under universal quantifiers (§4.3), and
German word order (§4.5). See §5 below for the Q-adverb formalization.

The ILP/SLP distinction is [carlson-1977]'s `PredicateLevel`:
individual-level predicates trigger homogeneity (assumption (70)), while
stage-level predicates do not.

## Naming note: `BPSWorld`

Section §6 below uses `BPSWorld` for **Bare Plural Subjects**, the
empirical phenomenon [magri-2009] extends his account to. This is
unrelated to the Bassi–Del Pinal–Sauerland 2021 *Presuppositional EXH*
abbreviation also used in this project (`bpsToImplicature`,
`.bpsPresuppositional`). Different `BPS`, different file.
-/

namespace Magri2009

open Exhaustification (innocent predToFinset altsFromPreds)
open Semantics.Kinds.SortedOntology (PredicateLevel)

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Blind Strengthening Framework
-- ═══════════════════════════════════════════════════════════════════════

/-- A scenario for blind scalar implicature computation.

[magri-2009]'s mechanism needs only literal meanings, scalar
alternatives, and common knowledge — no QUD or complexity ordering. -/
structure BlindScenario (W U : Type) [Fintype W] [DecidableEq W] where
  /-- Literal meaning of each utterance at each world. -/
  meaning : U → W → Bool
  /-- All scalar alternatives for each utterance.
      [fox-2007]'s innocent exclusion algorithm determines which
      alternatives are excludable — weaker alternatives (e.g., "some"
      when the prejacent is "all") are automatically filtered out. -/
  alternatives : U → List U
  /-- Common knowledge: which worlds are CK-compatible. -/
  context : W → Bool

namespace BlindScenario

variable {W U : Type} [Fintype W] [DecidableEq W] (s : BlindScenario W U)

/-- CK-compatible worlds. -/
def cWorlds : Finset W := Finset.univ.filter (fun w => s.context w)

/-- Strengthened meaning via [fox-2007]'s exhaustivity operator.

Implements the **Blindness Hypothesis** (BH): EXH computes the
strengthened meaning using logical entailment over W, not entailment
given common knowledge W_ck. The grammar strengthens automatically,
even when the result contradicts what speaker and hearer both know. -/
def strengthened (u : U) (w : W) : Bool :=
  decide (w ∈ innocent.exh (altsFromPreds ((s.alternatives u).map s.meaning))
                    (predToFinset (s.meaning u)))

/-- Blind oddness: the exhaustivity operator produced a non-vacuous
implicature, yet the strengthened meaning is false at every CK world.

Implements the **Mismatch Hypothesis** (MH): if EXH(φ) ∩ W_ck = ∅
(the blind strengthened meaning contradicts common knowledge), then
φ sounds odd. -/
def blindOdd (u : U) : Bool :=
  let alts := altsFromPreds ((s.alternatives u).map s.meaning)
  let φ := predToFinset (s.meaning u)
  decide (innocent.excluded alts φ).Nonempty &&
  decide (∀ w ∈ s.cWorlds, w ∉ innocent.exh alts φ)

/-- Structural extraction of the second `blindOdd` conjunct: when the
strengthened meaning is `blindOdd`, every CK-compatible world is
*excluded* by the EXH operator. This is the load-bearing fact for the
"strengthened meaning has no CK-realizer" claim — `strengthened u w =
true` means `w ∈ innocent.exh ...`, but blindOdd says no CK world is in
that set. Lifting this lemma to the `BlindScenario` level (rather than
inlining it at every consumer site) decouples the proof from the
specific shape of `blindOdd`. -/
theorem blindOdd_excludes_cWorlds (u : U) (h : s.blindOdd u = true) :
    ∀ w ∈ s.cWorlds,
      w ∉ innocent.exh (altsFromPreds ((s.alternatives u).map s.meaning))
                      (predToFinset (s.meaning u)) := by
  simp only [blindOdd, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- Membership in `cWorlds` reflects context truth. Convenience for callers
that have a `s.context w = true` hypothesis and need `w ∈ s.cWorlds`. -/
theorem mem_cWorlds_of_context (w : W) (h : s.context w = true) :
    w ∈ s.cWorlds := by
  simp only [cWorlds, Finset.mem_filter, Finset.mem_univ, true_and, h]

/-- Ignorance-based oddness: alternatives exist that are NOT innocently
excludable (so ignorance inferences are derived), yet CK settles every
alternative (all true at every CK world, or all false at every CK
world). The speaker cannot be genuinely ignorant → contradiction →
deviant.

This complements `blindOdd`: `blindOdd` detects when *scalar*
implicatures contradict CK (EXH(φ) ∩ W_ck = ∅), while
`ignoranceContradictsCK` detects when *ignorance* inferences
contradict CK (alternatives are relevant but CK-settled).

[denic-2023] §6: deviance of "#Each of those three girls is Mary,
Susan, or Jane" arises because ignorance inferences about singleton-
denoting predicates contradict CK. -/
def ignoranceContradictsCK (u : U) : Bool :=
  let altSet := altsFromPreds ((s.alternatives u).map s.meaning)
  let φ := predToFinset (s.meaning u)
  -- There are alternatives that are NOT IE (so ignorance inferences arise)
  decide (altSet.card > (innocent.excluded altSet φ).card) &&
  -- All CK worlds agree on all alternatives (speaker can't be ignorant)
  (s.alternatives u).all (λ alt =>
    let altMeaning := s.meaning alt
    -- Either alt is true at ALL CK worlds or false at ALL CK worlds
    decide (∀ w ∈ s.cWorlds, altMeaning w = true) ||
    decide (∀ w ∈ s.cWorlds, altMeaning w = false))

end BlindScenario

-- ═══════════════════════════════════════════════════════════════════════
-- §1b  R-Relativized EXH and Mandatoriness ([magri-2009] §3.2.5)
-- ═══════════════════════════════════════════════════════════════════════

/-! ## R-relativized exhaustification: the mandatoriness mechanism

§3.2.2 (BH+MH above) states the *outcome* of [magri-2009]'s account:
blind EXH mismatches CK, sentence sounds odd. §3.2.5 is the *mechanism*
explaining why mismatching SIs are mandatory while standard SIs (e.g.
the answer to (40c) "John is usually available after dinner") are not.
The key is a contextually-supplied relevance predicate `R`, an
R-relativized EXH operator (eq. (42)), and two postulates on R
(eq. (43)).

The mandatoriness consequence (p. 263): for *mismatching* SIs, the
target φ and its scalar alternative ψ are contextually equivalent
(φ ↔_{W_ck} ψ — common knowledge forces them to denote the same set
within W_ck). By postulate (43b), R is closed under contextual
equivalence, so R(ψ) = R(φ). By postulate (43a), R(φ) = 1 (the
uttered proposition is always relevant). Hence R(ψ) = 1, and
EXHᴿ(φ) negates ψ no matter how the context assigns R to other
propositions. The SI is *mandatory*.

For *standard* SIs (φ and alternatives NOT contextually equivalent),
R can be set independently — the context can make ψ irrelevant
(R(ψ) = 0), in which case EXHᴿ(φ) does not negate ψ and the SI is
not derived. Hence the SI is non-mandatory.

Without this machinery, `BlindScenario`'s `blindOdd` over-predicts
deviance: it fires whenever any logically stronger CK-incompatible
alternative exists, regardless of whether R would block it. The
substrate below adds R as a field with the postulates as structure
laws, and proves that for CK-equivalent (target, alternative) pairs
the SI is mandatory. -/

/-- Magri's relevance predicate, contextually supplied
([magri-2009] §3.2.5). A property `R : Finset W → Bool` of
propositions (extensions, as Finsets of CK-compatible-or-not worlds)
satisfying:

- **(43a)** *Maximize Relevance*: an uttered proposition's denotation
  is relevant. Hardwires the Gricean Maxim of Relevance.
- **(43b)** *Contextual closure*: if two propositions are equivalent
  given common knowledge (`p ∩ W_ck = q ∩ W_ck`), they share their
  relevance status. Captures that R is a contextual variable.

Together with mandatory EXH (eq. (41), an external assumption — Magri
states it as a stipulation about matrix clauses), R determines whether
SIs are mandatory: see `mismatching_alt_relevant` below. -/
structure RelevantBlindScenario (W U : Type) [Fintype W] [DecidableEq W]
    extends BlindScenario W U where
  /-- R: which propositions (as Finsets of worlds) are contextually relevant. -/
  relevant : Finset W → Bool
  /-- [magri-2009] eq. (43a): every uttered proposition's denotation
      is relevant. -/
  uttered_relevant : ∀ u, relevant (predToFinset (toBlindScenario.meaning u)) = true
  /-- [magri-2009] eq. (43b): R is closed under common-knowledge
      equivalence. Two propositions agreeing on every CK-compatible world
      have the same R-value. -/
  relevant_ck_closed : ∀ p q : Finset W,
    p ∩ toBlindScenario.cWorlds = q ∩ toBlindScenario.cWorlds →
    relevant p = relevant q

namespace RelevantBlindScenario

variable {W U : Type} [Fintype W] [DecidableEq W] (s : RelevantBlindScenario W U)

/-- [magri-2009] eq. (42): R-relativized exhaustification.
`EXHᴿ(φ) := φ ∧ ⋀_{ψ ∈ Excl(φ)} (¬ψ ∨ ¬R(ψ))`. A world `w` survives
iff `w ∈ φ` AND, for every excludable alternative ψ, either `w ∉ ψ`
or ψ is irrelevant. Equivalently: `w ∈ φ` and every *relevant*
excludable alternative is false at `w`.

Reduces to plain `strengthened` (Fox 2007 IE) when all excludable
alternatives are relevant. -/
def strengthenedR (u : U) (w : W) : Bool :=
  let alts := altsFromPreds ((s.alternatives u).map s.meaning)
  let φ := predToFinset (s.meaning u)
  decide (w ∈ φ ∧ ∀ ψ ∈ innocent.excluded alts φ,
                    s.relevant ψ = true → w ∉ ψ)

/-- **Mandatoriness consequence of (43a) + (43b)** for mismatching SIs.
When the uttered prejacent's denotation and an alternative's denotation
are contextually equivalent (= agree on every CK-compatible world),
postulate (43b) lifts the alternative's relevance to match the prejacent's,
and (43a) forces the prejacent's relevance to 1. So the alternative
is *mandatorily relevant* — no contextual choice of R can block it.

This is the formal core of [magri-2009]'s argument on p. 263:
mismatching SIs are mandatory because the alternative cannot be
R-blocked. The contrast with non-mismatching SIs (where φ and ψ are
*not* CK-equivalent, so R(ψ) is free) explains why standard SIs are
non-mandatory. -/
theorem mismatching_alt_relevant (u alt : U)
    (h_ck_equiv : predToFinset (s.meaning u) ∩ s.cWorlds =
                   predToFinset (s.meaning alt) ∩ s.cWorlds) :
    s.relevant (predToFinset (s.meaning alt)) = true := by
  rw [← s.relevant_ck_closed _ _ h_ck_equiv]
  exact s.uttered_relevant u

end RelevantBlindScenario

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Italian Warmth Example
-- ═══════════════════════════════════════════════════════════════════════

/-! "# Some Italians come from a warm country" ([magri-2009])

Three worlds are needed because the strengthened meaning "some but not
all" requires a world where some but not all Italians come from a warm
country.

CK: Italy is a warm country → all Italians come from a warm country.
Only `allWarm` is CK-compatible. -/

inductive ItalyWorld₃ where
  | allWarm     -- all Italians come from a warm country (CK-compatible)
  | someNotAll  -- some but not all (not CK-compatible)
  | noneWarm    -- none do (not CK-compatible)
  deriving DecidableEq, Repr, Fintype

inductive ItalyUtt where
  | some_ | all_
  deriving DecidableEq, Repr, Fintype

open ItalyWorld₃ ItalyUtt in
def italianScenario : BlindScenario ItalyWorld₃ ItalyUtt where
  meaning
    | some_, allWarm => true  | some_, someNotAll => true  | some_, noneWarm => false
    | all_,  allWarm => true  | all_,  someNotAll => false | all_,  noneWarm => false
  alternatives
    | some_ => [all_]  -- ⟨some, all⟩ scale partner
    | all_  => [some_]
  context
    | allWarm => true | someNotAll => false | noneWarm => false

/-- Lift `italianScenario` to a `RelevantBlindScenario` by adding a
canonical relevance predicate: `R(p) := 1` iff `p`'s CK-projection
matches that of some uttered alternative. This is the *minimal* R
satisfying both (43a) and (43b) — and crucially, it forces R(meaning all_)
= R(meaning some_) = 1 because both denote `{allWarm}` in CK. -/
def italianRelevantScenario : RelevantBlindScenario ItalyWorld₃ ItalyUtt where
  toBlindScenario := italianScenario
  -- p is relevant iff its CK-projection equals that of some utterance.
  relevant p := decide (∃ u : ItalyUtt,
    p ∩ italianScenario.cWorlds =
      predToFinset (italianScenario.meaning u) ∩ italianScenario.cWorlds)
  uttered_relevant u := by
    -- exhibit u as the witness
    refine decide_eq_true ?_
    exact ⟨u, rfl⟩
  relevant_ck_closed p q hpq := by
    -- relevant unfolds to `decide (∃ u, p ∩ cWorlds = …)`; rewriting
    -- the `p ∩ cWorlds` occurrences via hpq makes both sides identical.
    rw [show p ∩ italianScenario.cWorlds = q ∩ italianScenario.cWorlds from hpq]

/-- **Mandatoriness consequence on the Italian example** (Magri eq. 43
applied). The scalar alternative `all_` is mandatorily relevant when
`some_` is uttered, because both denote `{allWarm}` in CK
(the only CK-compatible world). The `R(meaning all_) = 1` conclusion
follows from `mismatching_alt_relevant`, parametric in the choice of
relevance variable — no contextual escape hatch exists. -/
example : italianRelevantScenario.relevant
    (predToFinset (italianRelevantScenario.meaning .all_)) = true := by
  apply italianRelevantScenario.mismatching_alt_relevant .some_ .all_
  -- show: predToFinset (meaning some_) ∩ cWorlds = predToFinset (meaning all_) ∩ cWorlds
  decide

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Core Predictions
-- ═══════════════════════════════════════════════════════════════════════

/-- Strengthened "some" at allWarm is false:
some(allWarm) ∧ ¬all(allWarm) = true ∧ false = false.
The blind implicature "not all" kills the literal meaning at the CK world. -/
theorem some_strengthened_false_at_ck :
    italianScenario.strengthened .some_ .allWarm = false := by decide

/-- Strengthened "some" at someNotAll is true:
some(someNotAll) ∧ ¬all(someNotAll) = true ∧ true = true.
But someNotAll is ruled out by CK — no help. -/
theorem some_strengthened_true_at_nonck :
    italianScenario.strengthened .some_ .someNotAll = true := by decide

/-- [magri-2009] prediction: "some Italians" is odd.
The blind implicature "not all" contradicts CK (Italy is warm). -/
theorem italian_some_blind_odd :
    italianScenario.blindOdd .some_ = true := by decide

/-- "all Italians" is not odd: no stronger alternative to negate,
so no blind implicature is generated. -/
theorem italian_all_not_odd :
    italianScenario.blindOdd .all_ = false := by decide

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Individual-Level Predicates: Q-Adverbs (§4.1)
-- ═══════════════════════════════════════════════════════════════════════

/-! [magri-2009] ex. (3)/(72b): "# Sometimes, John is tall"

The paper's main contribution derives oddness of Q-adverbs with
individual-level predicates (ILPs) from BH + MH. The key assumption
**homogeneity** (assumption (70)): if an i-predicate holds of
an individual at any time in W_ck, it holds at all times. This rules
out mixed worlds (tall at some times but not all) from the common
ground.

- Literal: at some times, John is tall
- Strengthened (blind, via BH): at some but NOT ALL times, John is tall
- CK: "tall" is an ILP → homogeneity → John is either always tall
  or never tall. The "sometimes but not always" world is CK-incompatible.
- Strengthened ∩ CK = ∅ → odd (via MH)

Contrast with the stage-level predicate "Sometimes, John is available":
since availability can genuinely vary over time, the "sometimes but not
always" world is CK-compatible → strengthened meaning is satisfiable → OK.

The ILP/SLP distinction is [carlson-1977]'s `PredicateLevel`:
individual-level → homogeneity → oddness; stage-level → no homogeneity → fine.
-/

section QAdverb

inductive TallWorld where
  | alwaysTall   -- tall at all times (CK-compatible: homogeneity (70))
  | sometimesOnly -- tall at some but not all times (NOT CK-compatible)
  | neverTall    -- tall at no time (CK-compatible: homogeneity (70))
  deriving DecidableEq, Repr, Fintype

inductive QAdvUtt where
  | sometimes_ | always_
  deriving DecidableEq, Repr

open TallWorld QAdvUtt in
/-- [magri-2009] §4.1: Q-adverbs with individual-level predicates.

"Sometimes" and "always" form a ⟨sometimes, always⟩ scale analogous to
⟨some, all⟩. Homogeneity (assumption (70)) rules out `sometimesOnly`
from the common ground. -/
def tallScenario : BlindScenario TallWorld QAdvUtt where
  meaning
    | sometimes_, alwaysTall => true   -- at some times = yes (all ⊆ some)
    | sometimes_, sometimesOnly => true
    | sometimes_, neverTall => false
    | always_,    alwaysTall => true
    | always_,    sometimesOnly => false
    | always_,    neverTall => false
  alternatives
    | sometimes_ => [always_]  -- ⟨sometimes, always⟩ scale partner
    | always_    => [sometimes_]
  -- Homogeneity (70): only homogeneous worlds are CK-compatible
  context
    | alwaysTall => true | sometimesOnly => false | neverTall => true

/-- Strengthened "sometimes" at alwaysTall is false:
sometimes(alwaysTall) ∧ ¬always(alwaysTall) = true ∧ false = false. -/
theorem tall_sometimes_strengthened_false :
    tallScenario.strengthened .sometimes_ .alwaysTall = false := by decide

/-- Strengthened "sometimes" at neverTall is also false:
sometimes(neverTall) = false. -/
theorem tall_sometimes_strengthened_false_never :
    tallScenario.strengthened .sometimes_ .neverTall = false := by decide

/-- [magri-2009] prediction: "# Sometimes, John is tall" is odd.
The blind implicature "not always" contradicts homogeneity (70). -/
theorem tall_sometimes_blind_odd :
    tallScenario.blindOdd .sometimes_ = true := by decide

/-- "Always, John is tall" is fine: no stronger alternative exists. -/
theorem tall_always_not_odd :
    tallScenario.blindOdd .always_ = false := by decide


-- ═══════════════════════════════════════════════════════════════════════
-- §5.1  Homogeneity from PredicateLevel
-- ═══════════════════════════════════════════════════════════════════════

/-- Homogeneity determines which worlds are CK-compatible.

[magri-2009] assumption (70): if an i-predicate holds of an individual
at any time in a CK-compatible world, it holds at all times within that
individual's lifespan. This makes the predicate "homogeneous."

This maps [carlson-1977]'s `PredicateLevel` to a CK context:
- Individual-level → only homogeneous worlds are CK-compatible
- Stage-level → all worlds are CK-compatible (the predicate can
  genuinely vary over time) -/
def homogeneity : PredicateLevel → (TallWorld → Bool)
  | .individualLevel => fun w => match w with
    | .alwaysTall => true | .sometimesOnly => false | .neverTall => true
  | .stageLevel => fun _ => true

/-- The context function of `tallScenario` is exactly what ILP
homogeneity predicts for individual-level predicates. -/
theorem tall_context_from_ilp :
    tallScenario.context = homogeneity .individualLevel := by
  ext w; cases w <;> rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §5.2  Stage-Level Contrast: "Sometimes, John is available"
-- ═══════════════════════════════════════════════════════════════════════

open TallWorld QAdvUtt in
/-- Stage-level contrast scenario: "Sometimes, John is available."

Same literal semantics and scale as the tall scenario, but CK admits
all worlds because availability is stage-level — it CAN genuinely
vary over time. The homogeneity assumption (70) does not apply. -/
def availableScenario : BlindScenario TallWorld QAdvUtt where
  meaning := tallScenario.meaning
  alternatives := tallScenario.alternatives
  context := homogeneity .stageLevel

/-- The context of `availableScenario` matches stage-level homogeneity:
all worlds are CK-compatible. -/
theorem available_context_from_slp :
    availableScenario.context = homogeneity .stageLevel := rfl

/-- "Sometimes, John is available" is NOT odd.
Stage-level predicates don't trigger homogeneity (70), so `sometimesOnly`
is CK-compatible and the strengthened meaning is satisfiable. -/
theorem available_sometimes_not_odd :
    availableScenario.blindOdd .sometimes_ = false := by decide

/-- The ILP/SLP distinction determines oddness:
individual-level + "sometimes" → odd; stage-level + "sometimes" → fine.

This is the structural prediction: [carlson-1977]'s `PredicateLevel`
feeds into [magri-2009]'s blindness mechanism via homogeneity (70). -/
theorem predicate_level_determines_oddness :
    tallScenario.blindOdd .sometimes_ = true ∧
    availableScenario.blindOdd .sometimes_ = false := ⟨by decide, by decide⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §5.3  Homogeneity Is Necessary and Sufficient
-- ═══════════════════════════════════════════════════════════════════════

/-- The tall and available scenarios share literal semantics and alternatives
— they differ ONLY in the CK context. -/
theorem scenarios_share_semantics :
    tallScenario.meaning = availableScenario.meaning ∧
    tallScenario.alternatives = availableScenario.alternatives := ⟨rfl, rfl⟩

/-- The contexts genuinely differ: `sometimesOnly` is CK-incompatible
for individual-level (tall) but CK-compatible for stage-level (available). -/
theorem contexts_differ_at_sometimesOnly :
    tallScenario.context .sometimesOnly ≠
    availableScenario.context .sometimesOnly := by
  simp [tallScenario, availableScenario, homogeneity]

/-- Homogeneity (70) is necessary and sufficient for Q-adverb oddness.

The two scenarios have identical literal semantics, identical scale
structure, and identical worlds. The ONLY difference is the CK context,
which is determined by [carlson-1977]'s `PredicateLevel` via
`homogeneity`. Yet this single difference flips the oddness prediction:

- Individual-level ("tall"): context rules out `sometimesOnly` →
  strengthened meaning contradicts CK → odd
- Stage-level ("available"): context admits `sometimesOnly` →
  strengthened meaning satisfiable at CK world → fine

This proves that [carlson-1977]'s predicate-level classification
is doing genuine explanatory work in [magri-2009]'s system:
it is the SOLE factor determining oddness for Q-adverb sentences. -/
theorem homogeneity_necessary_and_sufficient :
    -- Same semantics
    tallScenario.meaning = availableScenario.meaning ∧
    tallScenario.alternatives = availableScenario.alternatives ∧
    -- Different context (from different PredicateLevel)
    tallScenario.context ≠ availableScenario.context ∧
    -- Different oddness prediction
    tallScenario.blindOdd .sometimes_ ≠ availableScenario.blindOdd .sometimes_ := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro h
    have := congrFun h .sometimesOnly
    simp [tallScenario, availableScenario, homogeneity] at this
  · decide

end QAdverb

-- ═══════════════════════════════════════════════════════════════════════
-- §6  Context Characterization: What Makes Q-Adverbs Odd?
-- ═══════════════════════════════════════════════════════════════════════

/-! ### Context characterization theorem

The existing proofs show that *specific* context functions (homogeneity,
stage-level) produce or prevent oddness. But what characterizes the oddness-
producing contexts in general?

For the ⟨sometimes, always⟩ scale, oddness of "sometimes" depends on a single
Boolean condition: whether the "mixed" world (`sometimesOnly`) is CK-compatible.
This is because the strengthened meaning "sometimes but not always" is true
*only* at the mixed world — so EXH(φ) ∩ W_ck = ∅ iff the mixed world is
excluded from CK.

This theorem is universally quantified over all possible context functions,
not just the two tested above. It explains *why* [carlson-1977]'s
predicate-level classification does the right work: individual-level predicates
produce oddness precisely because homogeneity rules out the mixed world. -/

section ContextCharacterization

open TallWorld QAdvUtt

/-- For any context function on the ⟨sometimes, always⟩ scale, oddness
of "sometimes" is equivalent to ruling out the mixed world from CK.

This characterizes EXACTLY which contexts produce oddness, independently
of any specific predicate-level classification. The proof factors the
abstract context into its 3 constructor values (8 cases) and verifies
each computationally. -/
theorem oddness_iff_mixed_excluded (ctx : TallWorld → Bool) :
    ({ tallScenario with context := ctx } :
      BlindScenario TallWorld QAdvUtt).blindOdd .sometimes_ =
    (!ctx .sometimesOnly) := by
  -- Case-split on ctx at all 3 constructors (8 cases).
  -- In each case, reconstruct ctx as a concrete function and compute.
  cases ha : ctx .alwaysTall <;> cases hs : ctx .sometimesOnly <;>
    cases hn : ctx .neverTall <;> {
    have hfun : ctx = fun w => match w with
        | .alwaysTall => ctx .alwaysTall
        | .sometimesOnly => ctx .sometimesOnly
        | .neverTall => ctx .neverTall := funext fun w => by cases w <;> rfl
    simp only [ha, hs, hn] at hfun
    rw [hfun]; decide
  }

/-- Homogeneity (70) produces oddness because it rules out the mixed world. -/
theorem ilp_rules_out_mixed :
    (homogeneity .individualLevel) .sometimesOnly = false := rfl

/-- SLP permits "sometimes" because it admits the mixed world. -/
theorem slp_admits_mixed :
    (homogeneity .stageLevel) .sometimesOnly = true := rfl

end ContextCharacterization

-- ═══════════════════════════════════════════════════════════════════════
-- §7  Bare Plural Subject Restriction (§4.2)
-- ═══════════════════════════════════════════════════════════════════════

/-! ### Bare plural subject restrictions

[magri-2009] §4.2: the BPS *firemen* of the s-predicate *available*
admits both the existential and generic readings (ex. (84a)):
- ∃-BPS: "There are firemen who are available"
- GEN-BPS: "Firemen are generally available"

But the BPS of the i-predicate *tall* lacks the existential reading (84b):
- #∃-BPS: "There are firemen who are tall"
- GEN-BPS: "Firemen are (generally) tall"

[magri-2009]'s key insight: the ∃-BPS reading of an ILP has
the SAME abstract structure as "#Sometimes, John is tall" (§4.1). This is
because existential BPs always take narrowest scope ([carlson-1977]),
making narrow-scope ∃ over times equivalent to "sometimes." The definite
description alternative plays the role of "always." Homogeneity (70) rules
out the partial world, so the strengthened meaning contradicts CK.

We model this with independent types and prove the meaning table is
isomorphic to the Q-adverb scenario from §5. -/

section BarePluralSubjects

/-- Worlds for the bare plural ∃-reading of "Firemen are tall."

[magri-2009] §4.2: the truth conditions (91b)/(92b) involve ∃ over
firemen and time. The three worlds correspond to whether any fireman is
tall throughout his lifespan within the contextually supplied restrictor. -/
inductive BPSWorld where
  | allThroughout  -- every fireman is tall throughout his lifespan
  | partialOnly    -- some fireman tall at some times but not throughout
  | noneTall       -- no fireman is ever tall
  deriving DecidableEq, Repr, Fintype

/-- The bare plural reading and its definite-description alternative.

Following the Heim-Diesing framework: the BP introduces a free
variable bound by a default existential operator (DEO) with VP scope.

The Horn scale is ⟨bare plural, definite description⟩ (eq. (94)):
the BP *firemen* alternates with *the fireman P* for each specific
fireman P. In the 3-world model, the definite-description alternative
ψ (eq. (95)) is extensionally equivalent to the GEN-BPS reading φ
(eq. (91b)), so we model both as `generic_`. -/
inductive BPSReading where
  | existential_  -- ∃-BPS: there exist firemen who are tall (narrow scope)
  | generic_      -- definite/GEN alternative: there is a fireman tall throughout
  deriving DecidableEq, Repr

open BPSWorld BPSReading in
/-- [magri-2009] §4.2: bare plural existential reading of an ILP.

- `existential_` (φ', (92b)): ∃_t[C̄(t)][∃x(fireman(x) ∧ tall(x,t))]
  "for some time t in C̄, there exists a fireman who is tall at t"
- `generic_` (φ, (91b)): GEN_t[C̄(t)][∃x(fireman(x) ∧ tall(x,t))]
  "for generically all times t in C̄, there exists a fireman who is tall at t"

Homogeneity (70) rules out `partialOnly`: if fireman d is tall at
any time, d is tall at ALL times within his lifespan. -/
def bpsScenario : BlindScenario BPSWorld BPSReading where
  meaning
    | existential_, allThroughout => true   -- ∃ fireman tall: yes (all are)
    | existential_, partialOnly   => true   -- ∃ fireman tall: yes (at some times)
    | existential_, noneTall      => false  -- none tall
    | generic_,     allThroughout => true   -- all tall throughout: yes
    | generic_,     partialOnly   => false  -- not all throughout: no
    | generic_,     noneTall      => false  -- none: no
  alternatives
    | existential_ => [generic_]    -- ⟨BP, definite description⟩ Horn scale (eq. 94)
    | generic_     => [existential_]
  -- Homogeneity (70): partialOnly is CK-incompatible
  context
    | allThroughout => true | partialOnly => false | noneTall => true

/-- The ∃-BPS reading of ILP "Firemen are tall" is odd.
Blind strengthening derives "∃ fireman tall at some times BUT no fireman
tall throughout" — contradicting homogeneity (70). -/
theorem bps_existential_ilp_odd :
    bpsScenario.blindOdd .existential_ = true := by decide

/-- The GEN-BPS reading of ILP "Firemen are tall" is fine. -/
theorem bps_generic_not_odd :
    bpsScenario.blindOdd .generic_ = false := by decide

open BPSWorld BPSReading in
/-- Stage-level counterpart: ∃-BPS reading of "Firemen are available."

Same meaning structure, but all worlds CK-compatible because
availability can genuinely vary over time (no homogeneity). -/
def bpsSLPScenario : BlindScenario BPSWorld BPSReading where
  meaning := bpsScenario.meaning
  alternatives := bpsScenario.alternatives
  context := fun _ => true

/-- The ∃-BPS reading of SLP "Firemen are available" is fine. -/
theorem bps_existential_slp_not_odd :
    bpsSLPScenario.blindOdd .existential_ = false := by decide

/-- The BPS scenario's meaning table is isomorphic to the Q-adverb scenario:
"∃-BPS at world w" has the same truth value as "sometimes at the
corresponding Q-adverb world."

This is [magri-2009]'s reduction (p. 275): "the existential reading
of the BPS of sentence (84b) can be ruled out in exactly the same way
as sentence (46a)." -/
theorem bps_meaning_matches_qadverb :
    ∀ (u : BPSReading) (w : BPSWorld),
      bpsScenario.meaning u w =
      tallScenario.meaning
        (match u with | .existential_ => .sometimes_ | .generic_ => .always_)
        (match w with | .allThroughout => .alwaysTall
                      | .partialOnly => .sometimesOnly
                      | .noneTall => .neverTall) := by
  intro u w; cases u <;> cases w <;> rfl

/-- The context functions match: homogeneity rules out the same
"mixed" world in both scenarios. -/
theorem bps_context_matches_qadverb :
    ∀ (w : BPSWorld),
      bpsScenario.context w =
      tallScenario.context
        (match w with | .allThroughout => .alwaysTall
                      | .partialOnly => .sometimesOnly
                      | .noneTall => .neverTall) := by
  intro w; cases w <;> rfl

end BarePluralSubjects

-- ═══════════════════════════════════════════════════════════════════════
-- §8  Universal Quantifier Rescue (§4.3)
-- ═══════════════════════════════════════════════════════════════════════

/-! ### Universal quantifier rescue

[magri-2009] §4.3, building on [fox-1995]: the ∃-BPS reading of
an i-predicate becomes available when the BP is embedded under a universal
quantifier.

- (102a) "Jewish women are related to Chomsky" — no ∃ reading
- (102b) "Jewish women are related to every Jewish man" — ∃ reading available

In (102b) the existential over Jewish women takes wide scope over both the
generic operator AND the universal quantifier *every Jewish man*. This creates
a "distributed witnesses" world — woman a₁ related to man b₁, a₂ to b₂ —
where EXH(φ) = φ ∧ ¬ψ is satisfiable.

Under homogeneity, "related" is permanent: once a₁ is related to b₁, she
always is. But this doesn't prevent different women from being related to
different men. The distributed-witnesses world is CK-compatible, so the
strengthened meaning is not vacuous at CK worlds → not odd.

The structural insight: the rescue scenario has the SAME context as the
stage-level scenario (all worlds CK-compatible), despite a different reason.
For SLPs, variability over time admits the mixed world. For universal
embedding, distributed witnesses admit the mixed world. [magri-2009]'s
mechanism produces the correct prediction in both cases: the mixed world
survives in CK. -/

section UniversalRescue

open TallWorld QAdvUtt

/-- [magri-2009] §4.3: universal quantifier rescue of ∃-BPS reading.

The meaning table matches the ⟨some, all⟩ pattern:
- `sometimes_` (φ): "for every Jewish man, ∃ a related Jewish woman"
- `always_` (ψ): "∃ a Jewish woman related to EVERY Jewish man"

The three worlds under the correspondence:
- `alwaysTall` → "concentrated": one woman related to all men (φ ∧ ψ)
- `sometimesOnly` → "distributed": different women for different men (φ ∧ ¬ψ)
- `neverTall` → "none": some man has no related woman (¬φ ∧ ¬ψ)

All worlds are CK-compatible because homogeneity for "related" (each
woman-man relationship is permanent) is compatible with distributed
witnesses. -/
def universalRescueScenario : BlindScenario TallWorld QAdvUtt where
  meaning := tallScenario.meaning
  alternatives := tallScenario.alternatives
  context := fun _ => true

/-- The ∃-BPS reading under a universal quantifier is NOT odd.
The distributed-witnesses world is CK-compatible, so the strengthened
meaning is satisfiable at a CK world. -/
theorem universal_rescue_not_odd :
    universalRescueScenario.blindOdd .sometimes_ = false := by decide

/-- The rescue scenario shares literal semantics and scale with the
ILP Q-adverb scenario — the ONLY difference is the CK context. -/
theorem rescue_shares_semantics :
    tallScenario.meaning = universalRescueScenario.meaning ∧
    tallScenario.alternatives = universalRescueScenario.alternatives := ⟨rfl, rfl⟩

/-- The rescue context matches the SLP context: both admit all worlds.

For SLPs: the predicate can genuinely vary over time → no worlds ruled out.
For universal rescue: distributed witnesses are CK-compatible → no worlds
ruled out. Different reasons, same abstract effect. -/
theorem rescue_context_equals_slp :
    universalRescueScenario.context = availableScenario.context := by
  funext w; cases w <;> rfl

/-- Three-way structural comparison:

| Scenario      | Context type    | Mixed world CK? | Odd?  |
|---------------|-----------------|------------------|-------|
| ILP Q-adverb  | Homogeneity (70) | No               | Yes   |
| SLP Q-adverb  | All worlds      | Yes              | No    |
| ILP + ∀       | All worlds      | Yes              | No    |

All three share the same meaning table and alternatives. Oddness is
entirely determined by whether the context rules out the mixed world —
as proved by `oddness_iff_mixed_excluded`. -/
theorem three_way_contrast :
    -- Same semantics across all three
    tallScenario.meaning = availableScenario.meaning ∧
    tallScenario.meaning = universalRescueScenario.meaning ∧
    tallScenario.alternatives = availableScenario.alternatives ∧
    tallScenario.alternatives = universalRescueScenario.alternatives ∧
    -- ILP is odd, SLP and rescue are not
    tallScenario.blindOdd .sometimes_ = true ∧
    availableScenario.blindOdd .sometimes_ = false ∧
    universalRescueScenario.blindOdd .sometimes_ = false ∧
    -- The reason: ILP context rules out mixed world, others don't
    tallScenario.context .sometimesOnly = false ∧
    availableScenario.context .sometimesOnly = true ∧
    universalRescueScenario.context .sometimesOnly = true := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · decide
  · decide
  · decide

end UniversalRescue

-- ═══════════════════════════════════════════════════════════════════════
-- §9  Presuppositional Extension (§3.4)
-- ═══════════════════════════════════════════════════════════════════════

/-! ### BH_prs and MH_prs

[magri-2009] extends BH and MH to presuppositions (§3.4, eqs. 64–66):

1. **BH_prs** (65): The strengthened presupposition EXH_prs(φ) is computed
   using *logical* entailment, not entailment given common knowledge.

2. **MH_prs** (66): If the blind strengthened presupposition contradicts
   common knowledge (EXH_prs(φ) ∩ W_ck = ∅), then φ sounds odd.

The strengthened presupposition mirrors standard EXH but operates on the
presupposition dimension:

    EXH_prs(φ) = φ_prs ∧ ∧_{ψ ∈ Excl_prs(φ)} ¬ψ_prs

where Excl_prs uses [fox-2007]'s innocent exclusion applied to
presuppositions. This reuses `exhB`/`ieIndices` directly — the same
algorithm, applied to a different dimension of meaning. -/

section PresuppositionalExtension

/-- A scenario with both meanings and presuppositions for blind SI computation.

[magri-2009] §3.4: presupposition strengthening runs in parallel
to meaning strengthening, using the same [fox-2007] algorithm. -/
structure BlindPresupScenario (W U : Type) [Fintype W] [DecidableEq W]
    extends BlindScenario W U where
  /-- Presupposition carried by each utterance. -/
  presup : U → W → Bool

namespace BlindPresupScenario

variable {W U : Type} [Fintype W] [DecidableEq W] (s : BlindPresupScenario W U)

/-- Strengthened presupposition via [fox-2007]'s EXH applied to
presuppositions.

Implements **BH_prs**: the strengthening uses logical entailment over W,
not entailment given common knowledge. -/
def strengthenedPresup (u : U) (w : W) : Bool :=
  decide (w ∈ innocent.exh (altsFromPreds ((s.alternatives u).map s.presup))
                    (predToFinset (s.presup u)))

/-- Blind presuppositional oddness: EXH_prs(φ) ∩ W_ck = ∅.

Implements **MH_prs** (66): if the blind strengthened presupposition
contradicts common knowledge, the sentence sounds odd. -/
def blindOddPrs (u : U) : Bool :=
  let alts := altsFromPreds ((s.alternatives u).map s.presup)
  let ψ := predToFinset (s.presup u)
  decide (innocent.excluded alts ψ).Nonempty &&
  decide (∀ w ∈ s.toBlindScenario.cWorlds, w ∉ innocent.exh alts ψ)

end BlindPresupScenario

end PresuppositionalExtension

-- ═══════════════════════════════════════════════════════════════════════
-- §10  Overt "always" Oddness (§4.6)
-- ═══════════════════════════════════════════════════════════════════════

/-! ### "#John is always tall" via presuppositional mismatch

[magri-2009] §4.6: *always* and covert GEN are Horn-mates with the
same denotation but different presuppositions. Overt *always* carries
no homogeneity presupposition; covert GEN carries the **homogeneity
presupposition** (eq. (137)): either ALL atomic parts of the restrictor
satisfy the scope or NONE do (YES ∪ NO).

The oddness of "#John is always tall" is derived via MH_prs (66):

1. φ_prs (*always*) = W (trivial presupposition)
2. ψ_prs (GEN) = YES ∪ NO (homogeneity presupposition)
3. ψ_prs asymmetrically entails φ_prs (YES ∪ NO ⊂ W)
4. EXH_prs(φ) = φ_prs ∧ ¬ψ_prs = ¬(YES ∪ NO) = mixed worlds only
5. CK (from assumption (70)): W_ck = YES ∪ NO (homogeneity for ILPs)
6. EXH_prs(φ) ∩ W_ck = ∅ → odd via MH_prs

The contrast with "John is tall" (= covert GEN): GEN has no stronger
presuppositional alternative, so EXH_prs is vacuous and no mismatch
arises.

The reuse of `TallWorld` is structural: the three worlds — `alwaysTall`,
`sometimesOnly`, `neverTall` — serve double duty across meaning (§5)
and presupposition (§10). -/

section OvertAlways

open TallWorld

/-- Utterance type for the ⟨always, GEN⟩ Horn scale. -/
inductive AlwaysGENUtt where
  | always_ | gen_
  deriving DecidableEq, Repr

open AlwaysGENUtt in
/-- [magri-2009] §4.6: *always* vs covert GEN.

The two utterances have IDENTICAL denotation (both mean "at all times,
John is tall") but DIFFERENT presuppositions:
- *always*: φ_prs = W (no homogeneity presupposition)
- GEN: ψ_prs = {alwaysTall, neverTall} (homogeneity: YES ∪ NO) -/
def alwaysGENScenario : BlindPresupScenario TallWorld AlwaysGENUtt where
  -- Identical meanings: both mean "tall at all times"
  meaning
    | _, alwaysTall => true
    | _, sometimesOnly => false
    | _, neverTall => false
  alternatives
    | .always_ => [.gen_]    -- ⟨always, GEN⟩ Horn scale (assumption (81))
    | .gen_    => [.always_]
  context := homogeneity .individualLevel
  -- Presuppositions differ:
  presup
    -- *always* has no homogeneity presupposition (φ_prs = W)
    | .always_, _ => true
    -- GEN has homogeneity presupposition (ψ_prs = YES ∪ NO)
    | .gen_, alwaysTall => true      -- YES: tall at all times
    | .gen_, sometimesOnly => false   -- mixed: neither YES nor NO
    | .gen_, neverTall => true        -- NO: tall at no time

/-- GEN's presupposition matches homogeneity: the same predicate as the
CK context. This is not coincidence — assumption (70) says W_ck is
exactly the set of homogeneous worlds, and GEN presupposes homogeneity. -/
theorem gen_presup_matches_context :
    ∀ w : TallWorld,
      alwaysGENScenario.presup .gen_ w =
      alwaysGENScenario.context w := by
  intro w; cases w <;> rfl

/-- *always* has trivial (universal) presupposition. -/
theorem always_presup_trivial :
    ∀ w : TallWorld, alwaysGENScenario.presup .always_ w = true := by
  intro w; cases w <;> rfl

/-- The strengthened presupposition of *always* asserts ¬(YES ∪ NO),
i.e., that there ARE mixed worlds — which is exactly what homogeneity
rules out. -/
theorem always_strengthened_presup_false_at_ck :
    alwaysGENScenario.strengthenedPresup .always_ .alwaysTall = false ∧
    alwaysGENScenario.strengthenedPresup .always_ .neverTall = false := by
  constructor <;> decide

/-- [magri-2009] §4.6: "#John is always tall" is odd via MH_prs.

The blind strengthened presupposition (= ¬homogeneity = mixed worlds
only) contradicts CK (= homogeneity = no mixed worlds). -/
theorem always_tall_blind_odd_prs :
    alwaysGENScenario.blindOddPrs .always_ = true := by decide

/-- "John is tall" (= covert GEN) is NOT odd via MH_prs.

GEN has no stronger presuppositional alternative — *always* is
presuppositionally weaker (trivial presupposition ⊂ homogeneity
presupposition is backwards). Since GEN's presupposition entails
*always*'s, *always* is not excludable w.r.t. GEN. -/
theorem gen_tall_not_odd_prs :
    alwaysGENScenario.blindOddPrs .gen_ = false := by decide

/-- Meanings are identical but oddness differs — the presupposition
is doing ALL the work. This is a pure presuppositional effect: the
same mechanism (BH + MH) applied to a different dimension of meaning. -/
theorem always_gen_same_meaning_different_presup :
    alwaysGENScenario.meaning .always_ = alwaysGENScenario.meaning .gen_ ∧
    alwaysGENScenario.presup .always_ ≠ alwaysGENScenario.presup .gen_ ∧
    alwaysGENScenario.blindOddPrs .always_ ≠ alwaysGENScenario.blindOddPrs .gen_ := by
  refine ⟨?_, ?_, ?_⟩
  · funext w; cases w <;> rfl
  · intro h
    have := congrFun h .sometimesOnly
    simp [alwaysGENScenario] at this
  · decide

end OvertAlways

-- ═══════════════════════════════════════════════════════════════════════
-- §11  Bridge to Bare Plural Data
-- ═══════════════════════════════════════════════════════════════════════

/-! ### Predictions match empirical BPS data

[magri-2009]'s theory predicts that individual-level predicates block
the existential reading of bare plural subjects. The rows in
`Data/Examples/CohenErteschikShir2002.json` independently record these
judgments as empirical observations ([cohen-erteschik-shir-2002]).

The bridge theorems verify that every ILP row lacks an acceptable
existential reading — exactly what the BH+MH mechanism predicts —
and every SLP-with-locative-argument row has one. -/

section BarePluralBridge

open Data.Examples

/-- The row's predicate level ([carlson-1977]), read from the
    `predicate_level` feature. -/
def predicateLevelOf (row : LinguisticExample) : Option PredicateLevel :=
  match row.feature? "predicate_level" with
  | some "individual" => some .individualLevel
  | some "stage"      => some .stageLevel
  | _                 => none

/-- Is the existential reading of the bare plural subject acceptable? -/
def existentialOK (row : LinguisticExample) : Bool :=
  (row.readings.find? (·.1 == "existential")).map (·.2) == some .acceptable

/-- Every individual-level row lacks the existential reading — matching
[magri-2009]'s prediction that the ∃-BPS of an ILP is odd
(BH + MH + homogeneity). -/
theorem ilp_data_matches_magri_prediction :
    ∀ row ∈ CohenErteschikShir2002.Examples.all,
      predicateLevelOf row = some .individualLevel → existentialOK row = false := by
  decide

/-- Every stage-level row with a locative argument HAS the existential
reading — matching [magri-2009]'s prediction that the ∃-BPS of an SLP
is fine (no homogeneity → no mismatch). -/
theorem slp_argument_data_matches_magri_prediction :
    ∀ row ∈ CohenErteschikShir2002.Examples.all,
      row.feature? "locative_status" = some "argument" →
        predicateLevelOf row = some .stageLevel ∧ existentialOK row = true := by
  decide

/-- The BPS scenario for ILPs is odd, AND the ILP rows independently
confirm no existential reading. Cross-validation between theory (BH+MH)
and empirical observation. -/
theorem magri_predicts_ilp_no_existential :
    bpsScenario.blindOdd .existential_ = true ∧
    ∀ row ∈ CohenErteschikShir2002.Examples.all,
      predicateLevelOf row = some .individualLevel → existentialOK row = false :=
  ⟨by decide, ilp_data_matches_magri_prediction⟩

/-- The BPS scenario for SLPs is fine, AND the SLP-argument rows
independently confirm the existential reading is available. -/
theorem magri_predicts_slp_existential :
    bpsSLPScenario.blindOdd .existential_ = false ∧
    ∀ row ∈ CohenErteschikShir2002.Examples.all,
      row.feature? "locative_status" = some "argument" → existentialOK row = true :=
  ⟨by decide, fun row h hf => (slp_argument_data_matches_magri_prediction row h hf).2⟩

end BarePluralBridge

-- ═══════════════════════════════════════════════════════════════════════
-- §12  Bridge to German *ja doch* Data (§4.5)
-- ═══════════════════════════════════════════════════════════════════════

/-! ### German BPS word order matches BH+MH predictions

[magri-2009] §4.5 argues that [diesing-1992]'s German BPS word
order contrast (BPS left vs right of *ja doch*) follows from BH+MH:

- S-predicate BPS both positions OK → BH+MH: no mismatch (SLP)
- I-predicate BPS left only → BH+MH: right-of-*ja doch* = VP-internal =
  existential reading only → mismatch with homogeneity → odd

The data in `German.BarePluralWordOrder` independently records
this pattern. The bridge theorem confirms that the oddness pattern in
the German data aligns with the model scenarios. -/

section GermanBridge

open German.BarePluralWordOrder

/-- The German *ja doch* data confirms the same ILP/SLP split:
the ONLY unacceptable configuration is ILP + right of *ja doch*
(= VP-internal = existential-only reading).

- ILP right of *ja doch* → odd: matches `bpsScenario.blindOdd .existential_`
- SLP both positions → fine: matches `bpsSLPScenario.blindOdd .existential_`
- ILP left of *ja doch* → fine: the GEN reading is available (not blocked) -/
theorem german_data_matches_magri :
    -- German data: only ILP + right is unacceptable
    allJaDochData.all (λ d =>
      d.acceptable == !(d.predicateLevel == .individualLevel &&
                        d.bpsPosition == .rightOfJaDoch)) = true ∧
    -- Magri model: ILP existential is odd
    bpsScenario.blindOdd .existential_ = true ∧
    -- Magri model: SLP existential is fine
    bpsSLPScenario.blindOdd .existential_ = false :=
  ⟨by decide, by decide, by decide⟩

end GermanBridge

-- ═══════════════════════════════════════════════════════════════════════
-- §13  Bare Plurals with "always" (§4.6.2 Remark)
-- ═══════════════════════════════════════════════════════════════════════

/-! ### "Firemen are always tall" is fine (§4.6.2 Remark)

[magri-2009] §4.6.2: "#John is always tall" is odd (§10 above),
but "Firemen are always tall" is FINE when the definite *John* is replaced
by a bare plural.

The key difference: with a bare plural subject, the strengthened
presupposition ¬ψ_prs asserts that homogeneity fails for the restrictor
(some firemen are tall, others aren't). This is NOT a contradiction given
common knowledge — there are CK-compatible worlds where some firemen are
tall and others aren't.

This shows the presuppositional mechanism is sensitive to the logical
form of the subject: definite subjects (John) produce oddness because
homogeneity must hold for a single individual; bare plural subjects
(firemen) don't because different individuals can differ. -/

section BarePluralAlways

open TallWorld

/-- Worlds for "Firemen are always tall" with bare plural subject.

With a bare plural, the homogeneity presupposition of GEN quantifies
over firemen: either ALL firemen are tall or NONE are. But CK for
a bare plural does NOT rule out mixed worlds (some tall, some not). -/
inductive BPAlwaysWorld where
  | allTall       -- all firemen always tall
  | mixedFiremen  -- some firemen tall, others not
  | noneTall      -- no fireman tall
  deriving DecidableEq, Repr, Fintype

open BPAlwaysWorld AlwaysGENUtt in
/-- [magri-2009] §4.6.2: *always* vs GEN with bare plural subject.

Meanings are identical (both: "all firemen are always tall"), but
presuppositions differ. GEN's homogeneity presupposition says either
all firemen are tall or none are (YES ∪ NO). But with a bare plural,
the mixed world (some tall, some not) IS CK-compatible. -/
def bpAlwaysScenario : BlindPresupScenario BPAlwaysWorld AlwaysGENUtt where
  meaning
    | _, allTall => true
    | _, mixedFiremen => false
    | _, noneTall => false
  alternatives
    | .always_ => [.gen_]
    | .gen_    => [.always_]
  -- CK: ALL worlds are compatible (some firemen could be tall, others not)
  context := fun _ => true
  presup
    | .always_, _ => true                -- *always* has no homogeneity presup
    | .gen_, allTall => true             -- YES: all firemen tall
    | .gen_, mixedFiremen => false       -- mixed: neither YES nor NO
    | .gen_, noneTall => true            -- NO: no fireman tall

/-- "Firemen are always tall" is NOT odd via MH_prs.

The strengthened presupposition ¬ψ_prs = {mixedFiremen} is satisfiable
at a CK world (mixedFiremen is CK-compatible for bare plurals), so
MH_prs does not fire. -/
theorem bp_always_not_odd_prs :
    bpAlwaysScenario.blindOddPrs .always_ = false := by decide

/-- Contrast: same logical structure, different subjects, different oddness.

- "#John is always tall" (definite): odd via MH_prs (§10)
- "Firemen are always tall" (bare plural): fine (§4.6.2)

The difference: CK for a definite (John) rules out the mixed world
(homogeneity for one individual), while CK for a bare plural does not
(different firemen can differ). -/
theorem definite_vs_bp_always_contrast :
    alwaysGENScenario.blindOddPrs .always_ = true ∧
    bpAlwaysScenario.blindOddPrs .always_ = false :=
  ⟨by decide, by decide⟩

end BarePluralAlways

-- ═══════════════════════════════════════════════════════════════════════
-- §8  Bridge to an alternative list
-- ═══════════════════════════════════════════════════════════════════════

section AlternativeSourceBridge

/-- The Italian ⟨some, all⟩ scale as a plain alternative list. -/
def italyAlternatives : List ItalyUtt := [.some_, .all_]

/-- Exhaustifying via the alternative list agrees with BlindScenario.strengthened.

    BlindScenario carries its own `alternatives` field; here we show that
    deriving alternatives from `italyAlternatives` produces the same
    exhaustified meaning. The key: including the assertion in the
    alternative list doesn't change the result — `exhIE` filters it out
    via the non-weaker check. -/
theorem strengthened_eq_alternativeSource :
    ∀ w : ItalyWorld₃,
      italianScenario.strengthened .some_ w =
      decide (w ∈ innocent.exh
        (altsFromPreds
          (italyAlternatives.map italianScenario.meaning))
        (predToFinset (italianScenario.meaning ItalyUtt.some_))) := by
  intro w; cases w <;> decide

end AlternativeSourceBridge

-- ═══════════════════════════════════════════════════════════════════════
-- §  Implicature spine bridge — magriToImplicature + honest diagnostic
-- ═══════════════════════════════════════════════════════════════════════

/-! ## Bridge: blind SI as `Implicature W Prop`

Wraps a `BlindScenario`-derived strengthened meaning as an `Implicature`
value over the same world type, exercising the cross-mechanism spine in
`Pragmatics/Implicature/Defs.lean`. The `Bool`-valued
strengthening becomes a `Prop`-valued implicature `content` via
`s.strengthened u w = true`.

### Why NOT a non-cancellability theorem

The [magri-2009] obligatoriness claim does *not* translate cleanly
into `Implicature.IsCancellable` failure, even CK-relativized. For
"#Some Italians come from a warm country" with CK = {allWarm},
*"in fact all"* is a consistent continuation at the CK world that
contradicts the EXH'd implicature — so `IsCancellable` (and
`IsCancellableInContext`) both *hold*. The contentful Magri claim
is a *different* diagnostic: **the strengthened meaning has no
CK-realizer.** That is the theorem delivered here. See
`Pragmatics/Implicature/Diagnostics.lean` docstring for the
extended discussion of why Magri obligatoriness ≠ IsCancellable failure.
-/

section ImplicatureSpineBridge

variable {W U : Type} [Fintype W] [DecidableEq W]

/-- Wrap a `BlindScenario`-derived strengthened meaning as an
`Implicature W Prop`. The `content` is `s.strengthened u · = true`
(the EXH'd meaning at each world); the `mechanism` is `.exhIE` —
[magri-2009] uses Fox's innocent-exclusion operator only
(`innocent.exh` in `Semantics/Exhaustification/Excluder.lean`,
implementing [fox-2007]'s IE algorithm), not the Bar-Lev–Fox
2020 IE+II extension that postdates the paper by 11 years. -/
def magriToImplicature (s : BlindScenario W U) (u : U) : Implicature W Prop where
  kind      := .scalar
  content   := fun w => s.strengthened u w = true
  altsUsed  := { p | ∃ alt ∈ s.alternatives u, p = fun w => s.meaning alt w = true }
  mechanism := .exhIE

/-- **Magri's mismatch consequence, restated against the implicature
spine.** When EXH is applied to φ blind to CK ([magri-2009] §3.2.2
eq. (32), the Blindness Hypothesis), and the resulting strengthened
meaning has no CK-realizer (eq. (33), the Mismatch Hypothesis), then
the wrapped implicature's content has no CK-compatible realizer.

The deviance [magri-2009] predicts is **not** Sadock truth-conditional
non-cancellability — for the "Some Italians" example, the continuation
"in fact all" IS truth-conditionally consistent with the literal "some"
and DOES contradict the EXH'd "not all" implicature, so `IsCancellable`
holds. The load-bearing premise is [magri-2009] §3.2.5 eq. (41)
"EXH is mandatory in matrix clauses" combined with the R-postulates
(43a)/(43b): the speaker is grammatically committed to the SI even
when uttering a cancellation continuation, and this commitment is what
creates the deviance. The mandatoriness machinery is formalized below
in `RelevantBlindScenario`; this theorem only states the *outcome*
(eq. (33) antecedent) translated to the implicature spine. -/
theorem magri_blindOdd_no_ck_realizer
    (s : BlindScenario W U) (u : U) (h : s.blindOdd u = true) :
    ¬ ∃ w, s.context w = true ∧ (magriToImplicature s u).content w := by
  rintro ⟨w, hctx, hcontent⟩
  have hExhMem :
      w ∈ innocent.exh (altsFromPreds ((s.alternatives u).map s.meaning))
                       (predToFinset (s.meaning u)) := by
    simpa [magriToImplicature, BlindScenario.strengthened] using hcontent
  exact s.blindOdd_excludes_cWorlds u h w (s.mem_cWorlds_of_context w hctx) hExhMem

end ImplicatureSpineBridge

end Magri2009
