import Linglib.Core.FelicityTypes
import Linglib.Theories.Semantics.Exhaustification.Fox2007
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Carlson1977

/-!
# Blind Mandatory Scalar Implicatures
@cite{magri-2009}

@cite{magri-2009}. Natural Language Semantics 17(3): 245–297.

Two hypotheses form the core of the paper:

1. **Blindness Hypothesis (BH)** (§3.2.2): The exhaustivity operator EXH
   computes the strengthened meaning using *logical* entailment (→_W),
   not entailment given common knowledge (→_{W_ck}). That is, whether
   an alternative is excludable is determined without consulting CK.

2. **Mismatch Hypothesis (MH)** (§3.2.2, item (33)): If the blind strengthened meaning
   EXH(φ) is a contradiction given common knowledge (EXH(φ) ∩ W_ck = ∅),
   then φ sounds odd.

## Introductory Example

"# Some Italians come from a warm country" (ex. (2))
- Literal: some Italians come from a warm country
- Strengthened (blind, via BH): some BUT NOT ALL Italians come from a warm country
- CK: Italy is warm → all Italians come from a warm country
- Strengthened ∩ CK = ∅ → odd (via MH)

## Application to Individual-Level Predicates

The paper's main contribution (§4) derives properties of individual-level
predicates (ILPs) from BH + MH via assumption (70): ILPs are
**homogeneous** — if an i-predicate holds at any time in W_ck, it holds at
all times. This homogeneity makes blind strengthening systematically
contradict CK for i-predicate constructions.

Key applications: "#Sometimes, John is tall" (§4.1), bare plural subject
restrictions (§4.2), embedding under universal quantifiers (§4.3), and
German word order (§4.5). See §5 below for the Q-adverb formalization.

The ILP/SLP distinction is @cite{carlson-1977}'s `PredicateLevel`:
individual-level predicates trigger homogeneity (assumption (70)), while
stage-level predicates do not.
-/

namespace Phenomena.ScalarImplicatures.Studies.Magri2009

open Exhaustification.Fox2007 (exhB ieIndices)
open Semantics.Lexical.Noun.Kind.Carlson1977 (PredicateLevel)

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Blind Strengthening Framework
-- ═══════════════════════════════════════════════════════════════════════

/-- A scenario for blind scalar implicature computation.

@cite{magri-2009}'s mechanism needs only literal meanings, scalar
alternatives, and common knowledge — no QUD or complexity ordering. -/
structure BlindScenario (W U : Type) where
  /-- Literal meaning of each utterance at each world. -/
  meaning : U → W → Bool
  /-- All scalar alternatives for each utterance.
      @cite{fox-2007}'s innocent exclusion algorithm (`ieIndices`) determines
      which alternatives are excludable — weaker alternatives (e.g., "some"
      when the prejacent is "all") are automatically filtered out by the
      non-weaker check (NW). -/
  alternatives : U → List U
  /-- Common knowledge: which worlds are CK-compatible. -/
  context : W → Bool
  /-- Exhaustive world enumeration. -/
  worlds : List W

namespace BlindScenario

variable {W U : Type} (s : BlindScenario W U)

/-- CK-compatible worlds. -/
def cWorlds : List W := s.worlds.filter s.context

/-- Strengthened meaning via @cite{fox-2007}'s exhaustivity operator.

Implements the **Blindness Hypothesis** (BH): EXH computes the
strengthened meaning using logical entailment over W, not entailment
given common knowledge W_ck. The grammar strengthens automatically,
even when the result contradicts what speaker and hearer both know. -/
def strengthened (u : U) (w : W) : Bool :=
  exhB s.worlds ((s.alternatives u).map s.meaning) (s.meaning u) w

/-- Blind oddness: the exhaustivity operator produced a non-vacuous
implicature, yet the strengthened meaning is false at every CK world.

Implements the **Mismatch Hypothesis** (MH): if EXH(φ) ∩ W_ck = ∅
(the blind strengthened meaning contradicts common knowledge), then
φ sounds odd. -/
def blindOdd (u : U) : Bool :=
  let ie := ieIndices s.worlds (s.meaning u) ((s.alternatives u).map s.meaning)
  !ie.isEmpty &&
  s.cWorlds.all (λ w => !s.strengthened u w)

end BlindScenario

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Italian Warmth Example
-- ═══════════════════════════════════════════════════════════════════════

/-! "# Some Italians come from a warm country" (@cite{magri-2009})

Three worlds are needed because the strengthened meaning "some but not
all" requires a world where some but not all Italians come from a warm
country.

CK: Italy is a warm country → all Italians come from a warm country.
Only `allWarm` is CK-compatible. -/

inductive ItalyWorld₃ where
  | allWarm     -- all Italians come from a warm country (CK-compatible)
  | someNotAll  -- some but not all (not CK-compatible)
  | noneWarm    -- none do (not CK-compatible)
  deriving DecidableEq, BEq, Repr

inductive ItalyUtt where
  | some_ | all_
  deriving DecidableEq, BEq, Repr

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
  worlds := [allWarm, someNotAll, noneWarm]

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Core Predictions
-- ═══════════════════════════════════════════════════════════════════════

/-- Strengthened "some" at allWarm is false:
some(allWarm) ∧ ¬all(allWarm) = true ∧ false = false.
The blind implicature "not all" kills the literal meaning at the CK world. -/
theorem some_strengthened_false_at_ck :
    italianScenario.strengthened .some_ .allWarm = false := by native_decide

/-- Strengthened "some" at someNotAll is true:
some(someNotAll) ∧ ¬all(someNotAll) = true ∧ true = true.
But someNotAll is ruled out by CK — no help. -/
theorem some_strengthened_true_at_nonck :
    italianScenario.strengthened .some_ .someNotAll = true := by native_decide

/-- @cite{magri-2009} prediction: "some Italians" is odd.
The blind implicature "not all" contradicts CK (Italy is warm). -/
theorem italian_some_blind_odd :
    italianScenario.blindOdd .some_ = true := by native_decide

/-- "all Italians" is not odd: no stronger alternative to negate,
so no blind implicature is generated. -/
theorem italian_all_not_odd :
    italianScenario.blindOdd .all_ = false := by native_decide

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Individual-Level Predicates: Q-Adverbs (§4.1)
-- ═══════════════════════════════════════════════════════════════════════

/-! @cite{magri-2009} ex. (3)/(72b): "# Sometimes, John is tall"

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

The ILP/SLP distinction is @cite{carlson-1977}'s `PredicateLevel`:
individual-level → homogeneity → oddness; stage-level → no homogeneity → fine.
-/

section QAdverb

inductive TallWorld where
  | alwaysTall   -- tall at all times (CK-compatible: homogeneity (70))
  | sometimesOnly -- tall at some but not all times (NOT CK-compatible)
  | neverTall    -- tall at no time (CK-compatible: homogeneity (70))
  deriving DecidableEq, BEq, Repr

inductive QAdvUtt where
  | sometimes_ | always_
  deriving DecidableEq, BEq, Repr

open TallWorld QAdvUtt in
/-- @cite{magri-2009} §4.1: Q-adverbs with individual-level predicates.

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
  worlds := [alwaysTall, sometimesOnly, neverTall]

/-- Strengthened "sometimes" at alwaysTall is false:
sometimes(alwaysTall) ∧ ¬always(alwaysTall) = true ∧ false = false. -/
theorem tall_sometimes_strengthened_false :
    tallScenario.strengthened .sometimes_ .alwaysTall = false := by native_decide

/-- Strengthened "sometimes" at neverTall is also false:
sometimes(neverTall) = false. -/
theorem tall_sometimes_strengthened_false_never :
    tallScenario.strengthened .sometimes_ .neverTall = false := by native_decide

/-- @cite{magri-2009} prediction: "# Sometimes, John is tall" is odd.
The blind implicature "not always" contradicts homogeneity (70). -/
theorem tall_sometimes_blind_odd :
    tallScenario.blindOdd .sometimes_ = true := by native_decide

/-- "Always, John is tall" is fine: no stronger alternative exists. -/
theorem tall_always_not_odd :
    tallScenario.blindOdd .always_ = false := by native_decide


-- ═══════════════════════════════════════════════════════════════════════
-- §5.1  Homogeneity from PredicateLevel
-- ═══════════════════════════════════════════════════════════════════════

/-- Homogeneity determines which worlds are CK-compatible.

@cite{magri-2009} assumption (70): if an i-predicate holds of an individual
at any time in a CK-compatible world, it holds at all times within that
individual's lifespan. This makes the predicate "homogeneous."

This maps @cite{carlson-1977}'s `PredicateLevel` to a CK context:
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
  worlds := tallScenario.worlds

/-- The context of `availableScenario` matches stage-level homogeneity:
all worlds are CK-compatible. -/
theorem available_context_from_slp :
    availableScenario.context = homogeneity .stageLevel := rfl

/-- "Sometimes, John is available" is NOT odd.
Stage-level predicates don't trigger homogeneity (70), so `sometimesOnly`
is CK-compatible and the strengthened meaning is satisfiable. -/
theorem available_sometimes_not_odd :
    availableScenario.blindOdd .sometimes_ = false := by native_decide

/-- The ILP/SLP distinction determines oddness:
individual-level + "sometimes" → odd; stage-level + "sometimes" → fine.

This is the structural prediction: @cite{carlson-1977}'s `PredicateLevel`
feeds into @cite{magri-2009}'s blindness mechanism via homogeneity (70). -/
theorem predicate_level_determines_oddness :
    tallScenario.blindOdd .sometimes_ = true ∧
    availableScenario.blindOdd .sometimes_ = false := ⟨by native_decide, by native_decide⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §5.3  Homogeneity Is Necessary and Sufficient
-- ═══════════════════════════════════════════════════════════════════════

/-- The tall and available scenarios share literal semantics, alternatives,
and worlds — they differ ONLY in the CK context. -/
theorem scenarios_share_semantics :
    tallScenario.meaning = availableScenario.meaning ∧
    tallScenario.alternatives = availableScenario.alternatives ∧
    tallScenario.worlds = availableScenario.worlds := ⟨rfl, rfl, rfl⟩

/-- The contexts genuinely differ: `sometimesOnly` is CK-incompatible
for individual-level (tall) but CK-compatible for stage-level (available). -/
theorem contexts_differ_at_sometimesOnly :
    tallScenario.context .sometimesOnly ≠
    availableScenario.context .sometimesOnly := by
  simp [tallScenario, availableScenario, homogeneity]

/-- Homogeneity (70) is necessary and sufficient for Q-adverb oddness.

The two scenarios have identical literal semantics, identical scale
structure, and identical worlds. The ONLY difference is the CK context,
which is determined by @cite{carlson-1977}'s `PredicateLevel` via
`homogeneity`. Yet this single difference flips the oddness prediction:

- Individual-level ("tall"): context rules out `sometimesOnly` →
  strengthened meaning contradicts CK → odd
- Stage-level ("available"): context admits `sometimesOnly` →
  strengthened meaning satisfiable at CK world → fine

This proves that @cite{carlson-1977}'s predicate-level classification
is doing genuine explanatory work in @cite{magri-2009}'s system:
it is the SOLE factor determining oddness for Q-adverb sentences. -/
theorem homogeneity_necessary_and_sufficient :
    -- Same semantics
    tallScenario.meaning = availableScenario.meaning ∧
    tallScenario.alternatives = availableScenario.alternatives ∧
    tallScenario.worlds = availableScenario.worlds ∧
    -- Different context (from different PredicateLevel)
    tallScenario.context ≠ availableScenario.context ∧
    -- Different oddness prediction
    tallScenario.blindOdd .sometimes_ ≠ availableScenario.blindOdd .sometimes_ := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro h
    have := congrFun h .sometimesOnly
    simp [tallScenario, availableScenario, homogeneity] at this
  · simp [tallScenario, availableScenario, homogeneity,
          BlindScenario.blindOdd, BlindScenario.strengthened,
          BlindScenario.cWorlds]
    native_decide

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
not just the two tested above. It explains *why* @cite{carlson-1977}'s
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
    rw [hfun]; native_decide
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

@cite{magri-2009} §4.2: the BPS *firemen* of the s-predicate *available*
admits both the existential and generic readings (ex. (84a)):
- ∃-BPS: "There are firemen who are available"
- GEN-BPS: "Firemen are generally available"

But the BPS of the i-predicate *tall* lacks the existential reading (84b):
- #∃-BPS: "There are firemen who are tall"
- GEN-BPS: "Firemen are (generally) tall"

@cite{magri-2009}'s key insight (p. 275): the ∃-BPS reading of an ILP has
the SAME abstract structure as "#Sometimes, John is tall" (§4.1). This is
because existential BPs always take narrowest scope (@cite{carlson-1977},
p. 16), making narrow-scope ∃ over times equivalent to "sometimes." The GEN
alternative plays the role of "always." Homogeneity (70) rules out the partial
world, so the strengthened meaning contradicts CK.

We model this with independent types and prove the meaning table is
isomorphic to the Q-adverb scenario from §5. -/

section BarePluralSubjects

/-- Worlds for the bare plural ∃-reading of "Firemen are tall."

@cite{magri-2009} §4.2: the truth conditions (91b)/(92b) involve ∃ over
firemen and time. The three worlds correspond to whether any fireman is
tall throughout his lifespan within the contextually supplied restrictor. -/
inductive BPSWorld where
  | allThroughout  -- every fireman is tall throughout his lifespan
  | partialOnly    -- some fireman tall at some times but not throughout
  | noneTall       -- no fireman is ever tall
  deriving DecidableEq, BEq, Repr

/-- The two readings of bare plural subjects.

Following the Heim-Diesing framework (@cite{magri-2009} (88)):
the BP introduces a free variable bound by a default existential
operator (DEO) with VP scope. The GEN reading arises when the
time argument is bound by a covert generic operator. -/
inductive BPSReading where
  | existential_  -- ∃-BPS: there exist firemen who are tall (narrow scope)
  | generic_      -- GEN-BPS: firemen are (generally/always) tall
  deriving DecidableEq, BEq, Repr

open BPSWorld BPSReading in
/-- @cite{magri-2009} §4.2: bare plural existential reading of an ILP.

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
    | existential_ => [generic_]    -- ⟨∃-BPS, GEN-BPS⟩ Horn scale
    | generic_     => [existential_]
  -- Homogeneity (70): partialOnly is CK-incompatible
  context
    | allThroughout => true | partialOnly => false | noneTall => true
  worlds := [allThroughout, partialOnly, noneTall]

/-- The ∃-BPS reading of ILP "Firemen are tall" is odd.
Blind strengthening derives "∃ fireman tall at some times BUT no fireman
tall throughout" — contradicting homogeneity (70). -/
theorem bps_existential_ilp_odd :
    bpsScenario.blindOdd .existential_ = true := by native_decide

/-- The GEN-BPS reading of ILP "Firemen are tall" is fine. -/
theorem bps_generic_not_odd :
    bpsScenario.blindOdd .generic_ = false := by native_decide

open BPSWorld BPSReading in
/-- Stage-level counterpart: ∃-BPS reading of "Firemen are available."

Same meaning structure, but all worlds CK-compatible because
availability can genuinely vary over time (no homogeneity). -/
def bpsSLPScenario : BlindScenario BPSWorld BPSReading where
  meaning := bpsScenario.meaning
  alternatives := bpsScenario.alternatives
  context := fun _ => true
  worlds := bpsScenario.worlds

/-- The ∃-BPS reading of SLP "Firemen are available" is fine. -/
theorem bps_existential_slp_not_odd :
    bpsSLPScenario.blindOdd .existential_ = false := by native_decide

/-- The BPS scenario's meaning table is isomorphic to the Q-adverb scenario:
"∃-BPS at world w" has the same truth value as "sometimes at the
corresponding Q-adverb world."

This is @cite{magri-2009}'s reduction (p. 275): "the existential reading
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

@cite{magri-2009} §4.3, building on @cite{fox-1995}: the ∃-BPS reading of
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
embedding, distributed witnesses admit the mixed world. @cite{magri-2009}'s
mechanism produces the correct prediction in both cases: the mixed world
survives in CK. -/

section UniversalRescue

open TallWorld QAdvUtt

/-- @cite{magri-2009} §4.3: universal quantifier rescue of ∃-BPS reading.

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
  worlds := tallScenario.worlds

/-- The ∃-BPS reading under a universal quantifier is NOT odd.
The distributed-witnesses world is CK-compatible, so the strengthened
meaning is satisfiable at a CK world. -/
theorem universal_rescue_not_odd :
    universalRescueScenario.blindOdd .sometimes_ = false := by native_decide

/-- The rescue scenario shares literal semantics and scale with the
ILP Q-adverb scenario — the ONLY difference is the CK context. -/
theorem rescue_shares_semantics :
    tallScenario.meaning = universalRescueScenario.meaning ∧
    tallScenario.alternatives = universalRescueScenario.alternatives ∧
    tallScenario.worlds = universalRescueScenario.worlds := ⟨rfl, rfl, rfl⟩

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
    tallScenario.worlds = availableScenario.worlds ∧
    tallScenario.worlds = universalRescueScenario.worlds ∧
    -- ILP is odd, SLP and rescue are not
    tallScenario.blindOdd .sometimes_ = true ∧
    availableScenario.blindOdd .sometimes_ = false ∧
    universalRescueScenario.blindOdd .sometimes_ = false ∧
    -- The reason: ILP context rules out mixed world, others don't
    tallScenario.context .sometimesOnly = false ∧
    availableScenario.context .sometimesOnly = true ∧
    universalRescueScenario.context .sometimesOnly = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · native_decide
  · native_decide
  · native_decide

end UniversalRescue

end Phenomena.ScalarImplicatures.Studies.Magri2009
