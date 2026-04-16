import Linglib.Core.Modality.DeonticNecessity
import Linglib.Theories.Semantics.Modality.Kratzer.Flavor
import Linglib.Theories.Semantics.Modality.Directive
import Linglib.Theories.Semantics.Attitudes.Intensional
import Linglib.Fragments.English.FunctionWords

/-!
# On Necessity and Comparison
@cite{rubinstein-2014}

Pacific Philosophical Quarterly 95(4): 512–554.

## Core Proposal

Weak necessity modals (*ought*, *should*) and evaluative comparative predicates
(*better*, *good*, *preferable*, *worthwhile*) form a **natural class**: both have
comparative semantics grounded in Kratzer's ordering sources, and both are
associated with **negotiable** ideals — priorities not universally endorsed
by all discourse participants.

This is the third of three competing analyses of weak necessity surveyed
in @cite{agha-jeretic-2026} §2.2:

1. **Domain restriction** (@cite{von-fintel-iatridou-2008}): `Directive.lean`
2. **Non-quantificational** (@cite{agha-jeretic-2022}): `AghaJeretic2022.lean`
3. **Comparative semantics** (@cite{rubinstein-2014}): this file

## Key Claims Formalized

1. **Two kinds of priorities** (§3.2): Non-negotiable priorities are promoted
   to modal-base status (restricting accessible worlds); negotiable priorities
   remain as ordering source material (ranking worlds).

2. **Favored worlds** (§3.2, def 40): worlds compatible with facts and
   non-negotiable priorities, via Frank (1996) compatibility-restricted union.

3. **Strong necessity** (§3.2, def 41): `∀w' ∈ Fav(f,h,e). p(w')` — universal
   quantification over favored worlds, NO ordering source.

4. **Weak necessity** (§3.2, def 42): `∀w' ∈ BEST(Fav(f,h,e), g(e)). p(w')` —
   universal quantification over the best favored worlds, ordered by
   negotiable ideals. This IS the comparative component.

5. **Negotiability** (§3.3, def 49): A premise set is negotiable iff not all
   discourse participants are committed to it. BEST is only defined when the
   ordering source is negotiable.

6. **Hebrew evidence** (§2.1): Hebrew lacks a lexical weak necessity modal;
   comparative evaluatives (*yoter tov*, *adif*, *kday*) serve as translations.

7. **Neg-raising** (§2.2): Weak necessity modals and evaluative comparatives
   are neg-raisers; strong necessity modals are not.

## Theoretical Disagreement with @cite{agha-jeretic-2022}

Both accounts agree on the data: "I don't think you should go" has a
lower-negation reading, while "I don't think you have to go" does not
(for most speakers). They disagree on the **mechanism**:

- **Rubinstein**: *should* genuinely neg-raises (pragmatic O→E strengthening,
  following @cite{horn-2001}). Strong necessity modals do NOT neg-raise.
- **Agha & Jeretič**: *should*'s apparent neg-raising is **scopelessness**
  (homogeneity), not true neg-raising. *must* genuinely neg-raises.

## Connection to Existing Infrastructure

- `Directive.lean` provides the @cite{von-fintel-iatridou-2008} analysis where
  weak necessity = ∀ over a refined best-world set (ordering refinement g ∪ g').
  Rubinstein differs by *promoting* some priorities to modal-base status.
- Under the simplifying assumption that no priorities are promoted (h = ∅),
  Rubinstein's analysis reduces to standard Kratzer necessity (bridge below).
- `FunctionWords.lean` classifies English *should*/*ought* as `weakNecessity`
  and *must* as `necessity`, matching Rubinstein's force assignments.
-/

namespace Phenomena.Modality.Studies.Rubinstein2014

open Semantics.Modality.Kratzer
open Semantics.Modality.Directive
open Semantics.Attitudes.Intensional (World)
open Core.Proposition (BProp)
open Core.Modality (ModalForce)

-- ============================================================================
-- §1. Priority Reconceptualization (§3.2)
-- ============================================================================

/-! ## Two kinds of priorities

Rubinstein argues that norms, ideals, and preferences — traditionally all
ordering-source material in @cite{kratzer-1981}'s framework — come in two kinds:

- **Non-negotiable**: promoted to modal-base status. These restrict which
  worlds are "live possibilities" (the favored worlds).
- **Negotiable**: remain as ordering-source material. These rank the favored
  worlds but do not eliminate any from consideration.

Strong necessity modals quantify over all favored worlds (no ordering).
Weak necessity modals quantify over the BEST favored worlds (with ordering). -/

/-- Whether a priority is negotiable among discourse participants.
    A priority is negotiable iff at least one discourse participant is not
    committed to it (§3.3, definition 49). -/
inductive Negotiability where
  | negotiable      -- not all participants committed; ordering source material
  | nonNegotiable   -- all participants committed; promoted to modal base
  deriving DecidableEq, Repr

/-- Rubinstein's reconceptualized modal backgrounds (§3.2).

    In standard @cite{kratzer-1981}, there is one modal base f and one ordering
    source g. Rubinstein splits priorities into two components based on
    negotiability, promoting the non-negotiable part to modal-base status. -/
structure PriorityTypology where
  /-- Factual circumstances: standard Kratzer modal base f(e). -/
  circumstances : ModalBase World
  /-- Non-negotiable priorities h(e): promoted to modal-base status.
      These are norms/ideals that all discourse participants endorse. -/
  nonNegotiable : ModalBase World
  /-- Negotiable priorities g(e): remain as ordering source.
      These are ideals promoted by an opinionated assessor but not
      universally endorsed. -/
  negotiable : OrderingSource World

-- ============================================================================
-- §2. Favored Worlds (§3.2, definitions 39–40)
-- ============================================================================

/-! ## Compatibility-restricted union and favored worlds

The favored worlds are determined by combining factual circumstances
with non-negotiable priorities. When priorities are consistent with
circumstances, this is simply the intersection of both.

Full definition: `Fav(f, h, e) = ∪{∩M : M ∈ f(e) + h(e)}` where
`f(e) + h(e)` is Frank (1996)'s compatibility-restricted union (def 39).
When h(w) is consistent with f(w), this reduces to `∩(f(w) ∪ h(w))`.
We implement the consistent case, which covers the paper's examples. -/

/-- **Favored worlds** (definition 40, consistent case):
    worlds satisfying both the factual circumstances f(w) and the
    non-negotiable priorities h(w). -/
def favoredWorlds (pt : PriorityTypology) (w : World) : Finset World :=
  propIntersection (pt.circumstances w ++ pt.nonNegotiable w)

/-- Favored worlds with no non-negotiable priorities reduce to
    standard Kratzer accessible worlds. -/
theorem favored_no_promoted (f : ModalBase World) (g : OrderingSource World) (w : World) :
    favoredWorlds ⟨f, emptyBackground, g⟩ w = accessibleWorlds f w := by
  unfold favoredWorlds accessibleWorlds emptyBackground propIntersection
  simp

-- `bestAmong`, `bestAmong_empty`, and `bestAmong_sub` are imported from
-- `Kratzer.lean`, where they were promoted as general-purpose operations.

-- ============================================================================
-- §4. Strong and Weak Necessity (§3.2, definitions 41–42)
-- ============================================================================

/-! ## The must/ought split

Strong necessity quantifies over ALL favored worlds (no ordering).
Weak necessity quantifies over the BEST favored worlds (ordered by
negotiable priorities). This is where the comparative semantics enters:
weak necessity uses world ranking, strong necessity does not. -/

/-- **Strong necessity** (definition 41):
    `⟦must⟧ = λpλe∀w'(w' ∈ Fav(f, h, e) → w' ∈ p)`

    Universal quantification over favored worlds. No ordering source
    is consulted — strong necessity is non-comparative. -/
def strongNecessityR (pt : PriorityTypology) (p : BProp World) (w : World) : Bool :=
  decide (∀ w' ∈ favoredWorlds pt w, p w' = true)

/-- **Weak necessity** (definition 42):
    `⟦ought⟧ = λpλe∀w'(w' ∈ BEST(Fav(f, h, e), g(e)) → w' ∈ p)`

    Universal quantification over the best favored worlds, where "best"
    is determined by the negotiable ordering source g(e). -/
def weakNecessityR (pt : PriorityTypology) (p : BProp World) (w : World) : Bool :=
  decide (∀ w' ∈ bestAmong (favoredWorlds pt w) (pt.negotiable w), p w' = true)

-- ============================================================================
-- §5. Entailment (§1, paper's key asymmetry)
-- ============================================================================

/-! ## Strong necessity entails weak necessity

Since `BEST(Fav, g) ⊆ Fav` (the best worlds are a subset of all
favored worlds), if p holds at all favored worlds, it a fortiori
holds at all best favored worlds. -/

/-- **Strong necessity entails weak necessity** in Rubinstein's framework.
    Parallel to `Directive.strong_entails_weak`, but derived from the
    subset relation `BEST(Fav, g) ⊆ Fav`. -/
theorem strong_entails_weak_R (pt : PriorityTypology) (p : BProp World) (w : World)
    (h : strongNecessityR pt p w = true) :
    weakNecessityR pt p w = true := by
  unfold strongNecessityR at h
  unfold weakNecessityR
  simp only [decide_eq_true_eq] at h ⊢
  intro w' hw'
  exact h w' (bestAmong_sub _ _ w' hw')

/-- Counterexample components for the converse. -/
private def ce_pt : PriorityTypology where
  circumstances := emptyBackground
  nonNegotiable := emptyBackground
  negotiable := λ _ => [λ w => w == .w1]

private def ce_p : BProp World := λ w => w == .w1

/-- The converse fails: weak necessity does NOT entail strong necessity.
    If p holds at all BEST favored worlds but not at all favored worlds,
    weak necessity holds but strong necessity does not. -/
theorem weak_not_entails_strong_R :
    ¬(∀ (pt : PriorityTypology) (p : BProp World) (w : World),
      weakNecessityR pt p w = true → strongNecessityR pt p w = true) := by
  intro h
  exact absurd
    (h ce_pt ce_p .w0 (by native_decide))
    (by native_decide)

-- ============================================================================
-- §6. Bridge to Directive.lean
-- ============================================================================

/-! ## Reduction to standard Kratzer semantics

When no priorities are promoted to modal-base status (h = ∅), Rubinstein's
strong necessity reduces to simple Kratzer necessity (no ordering), and
her weak necessity reduces to standard Kratzer necessity with the negotiable
ordering source. -/

/-- With no promoted priorities, Rubinstein's strong necessity equals
    simple Kratzer necessity (no ordering). -/
theorem strongR_eq_simpleNecessity (f : ModalBase World) (p : BProp World) (w : World) :
    (strongNecessityR ⟨f, emptyBackground, emptyBackground⟩ p w = true) ↔
    simpleNecessity f p w := by
  unfold strongNecessityR
  rw [decide_eq_true_eq, simpleNecessity_iff_all,
    show favoredWorlds ⟨f, emptyBackground, emptyBackground⟩ w =
      accessibleWorlds f w from favored_no_promoted f emptyBackground w]

/-- With no promoted priorities, Rubinstein's weak necessity equals
    standard Kratzer necessity under the negotiable ordering.

    This is **not** the same as `Directive.weakNecessity` — Rubinstein's
    "weak" with h=∅ equals Directive's "strong" (with g). The analyses
    differ structurally: Directive treats all priorities as ordering-source
    material; Rubinstein promotes some to modal-base status. -/
theorem weakR_eq_necessity (f : ModalBase World) (g : OrderingSource World)
    (p : BProp World) (w : World) :
    (weakNecessityR ⟨f, emptyBackground, g⟩ p w = true) ↔
    necessity f g p w := by
  rw [necessity_iff_all]
  unfold weakNecessityR
  rw [decide_eq_true_eq, show favoredWorlds ⟨f, emptyBackground, g⟩ w =
    accessibleWorlds f w from favored_no_promoted f g w]
  rfl

/-- When no priorities are promoted AND no negotiable ordering exists,
    strong and weak necessity coincide (both = simple necessity). -/
theorem strongR_eq_weakR_trivial (f : ModalBase World) (p : BProp World) (w : World) :
    strongNecessityR ⟨f, emptyBackground, emptyBackground⟩ p w =
    weakNecessityR ⟨f, emptyBackground, emptyBackground⟩ p w := by
  unfold strongNecessityR weakNecessityR
  congr 1
  rw [show favoredWorlds ⟨f, emptyBackground, emptyBackground⟩ w =
      accessibleWorlds f w from favored_no_promoted f emptyBackground w]
  simp only [emptyBackground, bestAmong_empty]

-- ============================================================================
-- §7. The Evaluative Comparative Natural Class (§1, §2.1.3)
-- ============================================================================

/-! ## Weak necessity modals and evaluative comparatives

The central empirical thesis: *ought*, *should*, *good*, *better*,
*preferable*, and *worthwhile* share a semantic core — they all involve
quantification over BEST worlds ranked by negotiable ordering sources.

In Hebrew, which lacks a lexical weak necessity modal, this natural class
is expressed exclusively through comparative evaluative language.

The paper establishes class membership via two diagnostic tests:

- **Test 1**: "x E q, but doesn't have to q" is felicitous (non-contradictory).
  This shows E is weaker than strong necessity.
- **Test 2**: "y has to q, x only E q" sets up a felicitous scalar contrast.
  This shows E sits below strong necessity on the modal scale. -/

/-- A priority-type modal expression: either a modal verb or an
    evaluative comparative predicate. -/
inductive PriorityExpression where
  | modal (name : String)           -- ought, should
  | evaluativeComp (name : String)  -- good, better, preferable, worthwhile
  deriving DecidableEq, Repr

/-- Properties shared by the evaluative comparative natural class. -/
structure ComparativeClassMember where
  expression : PriorityExpression
  /-- Passes Test 1: "x E q, but doesn't have to q" is felicitous. -/
  passesTest1 : Bool
  /-- Passes Test 2: "y has to q, x only E q" is felicitous. -/
  passesTest2 : Bool
  /-- Supports neg-raising under higher negation (Horn 1978, 1989). -/
  negRaises : Bool
  /-- Restricted to priority-type (non-epistemic) interpretation. -/
  priorityOnly : Bool
  deriving Repr

-- Weak necessity modals

def shouldMember : ComparativeClassMember where
  expression := .modal "should"
  passesTest1 := true   -- "You should go, but you don't have to"
  passesTest2 := true   -- "Waiters have to wash hands, guests only should"
  negRaises := true     -- "I don't think you should go" ≅ think not-should
  priorityOnly := false

def oughtMember : ComparativeClassMember where
  expression := .modal "ought"
  passesTest1 := true
  passesTest2 := true
  negRaises := true
  priorityOnly := false

-- Evaluative comparative predicates

/-- Modal *good* (positive form): "it would be good that p" (p. 517).
    Distinct from *better* (comparative) — *good* picks the overall best
    like *ought*, while *better* supports pairwise comparison. -/
def goodMember : ComparativeClassMember where
  expression := .evaluativeComp "good"
  passesTest1 := true   -- "It's good to resign, but he doesn't have to"
  passesTest2 := true   -- ex. 22: Hebrew "haxi tov" = "most good"
  negRaises := true     -- ex. 30: "It wouldn't be good to cheat" ≅ good not to
  priorityOnly := true

def betterMember : ComparativeClassMember where
  expression := .evaluativeComp "better"
  passesTest1 := true   -- "It's better to resign, but he doesn't have to"
  passesTest2 := true   -- ex. 22: "who is accused {better} resign, convicted must"
  negRaises := true     -- ex. 30 (comparative form of good)
  priorityOnly := true

def preferableMember : ComparativeClassMember where
  expression := .evaluativeComp "preferable"
  passesTest1 := true
  passesTest2 := true
  negRaises := true     -- ex. 33: Hebrew 'adif under think-negation cycles
  priorityOnly := true

def worthwhileMember : ComparativeClassMember where
  expression := .evaluativeComp "worthwhile"
  passesTest1 := true   -- ex. 1c
  passesTest2 := true
  negRaises := true
  priorityOnly := true  -- only teleological/bouletic

-- Strong necessity modals (for contrast)

def mustMember : ComparativeClassMember where
  expression := .modal "must"
  passesTest1 := false  -- *"You must go, but you don't have to" (contradictory)
  passesTest2 := false  -- *"Waiters have to, guests only must" (≈ same force)
  negRaises := false    -- ex. 31b: "I don't think you must go" ≠ think must-not
  priorityOnly := false

def haveToMember : ComparativeClassMember where
  expression := .modal "have to"
  passesTest1 := false
  passesTest2 := false
  negRaises := false
  priorityOnly := false

/-- *need* fails Tests 1 and 2 (§2.1.2, examples 16, 18–19), aligning
    with strong necessity. Hebrew *carix* 'need' similarly aligns with
    *xayav*/*muxrax* 'must'/'obliged' in direct comparison. Note 14
    confirms: "we can conclude that need is not a weak modal." -/
def needMember : ComparativeClassMember where
  expression := .modal "need"
  passesTest1 := false  -- ex. 16a: *"He needs to, but doesn't have to" (contradictory)
  passesTest2 := false  -- ex. 19: *"waiters must, guests only need" (infelicitous)
  negRaises := false    -- note 16: Hebrew carix shows some NR, but borderline
  priorityOnly := false

def comparativeClass : List ComparativeClassMember :=
  [shouldMember, oughtMember, goodMember, betterMember, preferableMember,
   worthwhileMember]

def strongNecessityModals : List ComparativeClassMember :=
  [mustMember, haveToMember, needMember]

/-- All members of the evaluative comparative class pass both scalar tests. -/
theorem class_passes_both_tests :
    comparativeClass.all (fun m => m.passesTest1 && m.passesTest2) = true := by
  native_decide

/-- All members of the evaluative comparative class support neg-raising
    (following Horn's (1978, 1989) classification of weak obligation predicates). -/
theorem class_neg_raises :
    comparativeClass.all (·.negRaises) = true := by native_decide

/-- No strong necessity modal passes the scalar tests. -/
theorem strong_fails_tests :
    strongNecessityModals.all (fun m => !m.passesTest1 && !m.passesTest2) = true := by
  native_decide

/-- No strong necessity modal supports neg-raising. -/
theorem strong_no_neg_raising :
    strongNecessityModals.all (fun m => !m.negRaises) = true := by native_decide

/-- Evaluative comparatives are restricted to priority-type interpretation;
    modal verbs are more flexible (can also be epistemic). -/
theorem evaluatives_priority_only :
    (comparativeClass.filter (fun m => match m.expression with
      | .evaluativeComp _ => true | _ => false)).all
    (·.priorityOnly) = true := by native_decide

-- ============================================================================
-- §8. Neg-Raising and Negotiability (§2.2, §3.4)
-- ============================================================================

/-! ## Negotiability explains neg-raising

Rubinstein connects the evaluative comparative class to neg-raising (§3.4):
modals and predicates that use negotiable ordering sources have an
"opinionated" alternative (□.¬p) available, enabling the excluded-middle
inference that underlies neg-raising. Strong necessity modals, which
quantify over favored worlds WITHOUT ordering, lack this alternative.

### Theoretical disagreement

This classification **disagrees** with @cite{agha-jeretic-2022} /
@cite{agha-jeretic-2026}, who analyze *should*'s apparent neg-raising as
homogeneity (scopelessness) and classify *must* as the genuine neg-raiser.
The `NegRaisingProfile` structure in `AghaJeretic2026.lean` encodes their
opposing classification. -/

/-- Neg-raising availability for a modal or evaluative predicate,
    following Rubinstein's classification (paper's Table 2, after
    Horn 1989, p. 323). -/
structure NegRaisingClassification where
  predicate : String
  isWeakNecessity : Bool
  negRaises : Bool   -- Rubinstein/Horn classification
  deriving Repr, BEq

def rubinsteinNRClassification : List NegRaisingClassification :=
  [ ⟨"should", true, true⟩       -- weak necessity: neg-raises
  , ⟨"ought", true, true⟩        -- weak necessity: neg-raises
  , ⟨"good", true, true⟩         -- evaluative comp: neg-raises
  , ⟨"better", true, true⟩       -- evaluative comp: neg-raises
  , ⟨"preferable", true, true⟩   -- evaluative comp: neg-raises
  , ⟨"must", false, false⟩       -- strong necessity: does NOT neg-raise
  , ⟨"have to", false, false⟩    -- strong necessity: does NOT neg-raise
  ]

/-- In Rubinstein's classification, weak necessity = neg-raising.
    (Compare `AghaJeretic2026.shouldProfile.higherNeg_narrowScope = false`,
    which represents the competing analysis where should does NOT neg-raise.) -/
theorem weak_necessity_iff_negRaises :
    rubinsteinNRClassification.all
      (fun c => c.isWeakNecessity == c.negRaises) = true := by native_decide

-- ============================================================================
-- §9. The Tax Report Scenario (§3.3, examples 45–47, 51)
-- ============================================================================

/-! ## Negotiable→non-negotiable promotion: should becomes have-to

The paper's central worked example (§3.3): An accountant says "We should
report all our revenue" — promoting a negotiable ideal about international
revenue. The law about domestic revenue is non-negotiable. Later, if the
manager endorses the ideal, the international-revenue clause is promoted
to non-negotiable status, making "We have to report all our revenue"
appropriate.

We model this with two propositions:
- reportDomestic: a non-negotiable legal obligation (in h)
- reportInternational: a negotiable ideal promoted by the speaker (in g)
- reportAll: the conjunction (the prejacent of should/have-to) -/

private def reportDomestic : BProp World := λ w => w == .w0 || w == .w1
private def reportInternational : BProp World := λ w => w == .w0 || w == .w2
private def reportAll : BProp World := λ w => reportDomestic w && reportInternational w

/-- **Scenario A** (ex. 45/51a): "We should report all our revenue."
    Domestic reporting is non-negotiable; international is negotiable. -/
private def taxScenarioA : PriorityTypology where
  circumstances := emptyBackground
  nonNegotiable := λ _ => [reportDomestic]
  negotiable := λ _ => [reportInternational]

/-- **Scenario B** (ex. 46/51b): "We have to report all our revenue."
    Both domestic and international reporting are now non-negotiable
    (the manager endorsed the international ideal). -/
private def taxScenarioB : PriorityTypology where
  circumstances := emptyBackground
  nonNegotiable := λ _ => [reportDomestic, reportInternational]
  negotiable := emptyBackground

/-- In scenario A, weak necessity holds: all BEST favored worlds
    satisfy reportAll (the ordering picks out worlds where international
    revenue is also reported). -/
theorem tax_should_holds :
    weakNecessityR taxScenarioA reportAll .w0 = true := by native_decide

/-- In scenario A, strong necessity FAILS: not all favored worlds
    satisfy reportAll (worlds reporting only domestic revenue survive). -/
theorem tax_must_fails :
    strongNecessityR taxScenarioA reportAll .w0 = false := by native_decide

/-- In scenario B (after promotion), strong necessity holds: all
    favored worlds now satisfy reportAll. -/
theorem tax_must_holds_after_promotion :
    strongNecessityR taxScenarioB reportAll .w0 = true := by native_decide

/-- The should→have-to shift: the SAME proposition goes from weak-only
    to strong necessity when the negotiable ideal is promoted. -/
theorem should_to_haveto_shift :
    strongNecessityR taxScenarioA reportAll .w0 = false ∧
    strongNecessityR taxScenarioB reportAll .w0 = true :=
  ⟨tax_must_fails, tax_must_holds_after_promotion⟩

-- ============================================================================
-- §10. Hebrew Data (§2.1)
-- ============================================================================

/-! ## Hebrew: A language without lexical weak necessity

Hebrew lacks dedicated lexical items comparable to *ought* or *should*,
and cannot derive weak necessity compositionally from strong necessity
modals (unlike Spanish *debería* = *deber*+COND). The best translations
use evaluative comparative language (§2.1.3, examples 21–22).

This supports the claim that weak necessity IS comparative: in a language
where the comparative route is the ONLY route, it surfaces overtly. -/

/-- Strategies for expressing weak necessity crosslinguistically.
    Extends the typology in `AghaJeretic2022.WeakNecessityMorphology`
    with the evaluative comparative strategy. -/
inductive WeakNecessityStrategy where
  | lexical               -- dedicated item (English should/ought)
  | compositional         -- strong + weakening morphology (Spanish debería)
  | evaluativeComparative -- comparative/evaluative language (Hebrew yoter tov)
  deriving DecidableEq, Repr

structure WeakNecessityProfile where
  language : String
  hasLexicalWN : Bool
  hasCompositionalWN : Bool
  primaryStrategy : WeakNecessityStrategy
  examples : List (String × String)  -- (form, gloss)
  deriving Repr

def englishWN : WeakNecessityProfile where
  language := "English"
  hasLexicalWN := true
  hasCompositionalWN := false
  primaryStrategy := .lexical
  examples := [("should", "weak necessity"), ("ought", "weak necessity")]

def spanishWN : WeakNecessityProfile where
  language := "Spanish"
  hasLexicalWN := false
  hasCompositionalWN := true
  primaryStrategy := .compositional
  examples := [("debería (deber+COND)", "should/ought")]

def hebrewWN : WeakNecessityProfile where
  language := "Hebrew"
  hasLexicalWN := false
  hasCompositionalWN := false
  primaryStrategy := .evaluativeComparative
  examples :=
    [ ("yoter tov (more good)", "it is better that")
    , ("adif (preferable)", "it is preferable that")
    , ("kday / ra'uy (worthwhile/fitting)", "it is worthwhile that")
    ]

/-- Hebrew lacks both standard routes to weak necessity. -/
theorem hebrew_no_standard_wn :
    hebrewWN.hasLexicalWN = false ∧ hebrewWN.hasCompositionalWN = false :=
  ⟨rfl, rfl⟩

/-- Hebrew uses evaluative comparatives as its primary strategy. -/
theorem hebrew_uses_evaluative :
    hebrewWN.primaryStrategy = .evaluativeComparative := rfl

-- ============================================================================
-- §11. Cross-Linguistic Typology (Table 1, Narrog 2012)
-- ============================================================================

/-! ## Deontic necessity is not universally split into strong and weak

Narrog (2010, 2012) surveys 200 genealogically diverse languages. Only 62
(31%) have grammaticalized means for expressing weak deontic necessity. This
casts doubt on the universality of weak necessity as a grammatical category,
and supports Rubinstein's claim that it surfaces through evaluative
comparison when dedicated grammatical means are absent.

Data imported from `Core.Modality.DeonticNecessity`. -/

open Core.Modality.DeonticNecessity in
/-- Only 62 of 200 surveyed languages grammaticalize weak deontic necessity.
    The total exceeds 200 because some languages have modals of multiple types. -/
theorem weak_rarity : countOf .weak = 62 := by native_decide

-- ============================================================================
-- §12. Comparative Semantics vs Positive Form (§2.1.3, examples 24–26)
-- ============================================================================

/-! ## Better can do what ought cannot

When multiple alternatives are salient, the morphological comparative
*better* can pairwise compare any two, while modal *ought* can only
pick out the overall best. This follows from the degree semantics:
*better* accesses the ordering directly (comparative), while *ought*
quantifies over the maximal elements (positive/superlative).

Hebrew data (example 25) confirms: *adif* 'preferable' supports
explicit than-clauses (*adif ... me-asher* 'preferable ... than-that'),
making the comparative structure visible. -/

/-- Whether a priority expression supports explicit pairwise comparison
    (comparative morphology with a than-clause). -/
structure ComparisonCapability where
  expression : String
  supportsPairwiseComparison : Bool  -- explicit than-clause
  picksOverallBest : Bool            -- selects unique best option
  deriving Repr

def betterCapability : ComparisonCapability where
  expression := "better"
  supportsPairwiseComparison := true   -- "better that he resign THAN stay"
  picksOverallBest := false            -- just pairwise, not superlative

def goodCapability : ComparisonCapability where
  expression := "good"
  supportsPairwiseComparison := false  -- *"it's good to resign THAN stay"
  picksOverallBest := true             -- positive form picks overall best

def oughtCapability : ComparisonCapability where
  expression := "ought"
  supportsPairwiseComparison := false  -- *"he ought to resign THAN stay"
  picksOverallBest := true             -- picks the best alternative

/-- *better* supports pairwise comparison; *ought* and *good* do not. -/
theorem better_pairwise_ought_not :
    betterCapability.supportsPairwiseComparison = true ∧
    oughtCapability.supportsPairwiseComparison = false ∧
    goodCapability.supportsPairwiseComparison = false := ⟨rfl, rfl, rfl⟩

/-- *ought* and *good* (positive form) pick the overall best;
    *better* (comparative form) just compares pairs. -/
theorem ought_best_better_pairwise :
    oughtCapability.picksOverallBest = true ∧
    goodCapability.picksOverallBest = true ∧
    betterCapability.picksOverallBest = false := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §13. Bridge to English Fragment (FunctionWords.lean)
-- ============================================================================

/-! ## Fragment-layer verification

The English fragment in `FunctionWords.lean` independently classifies
modals by force. We verify that these classifications match Rubinstein's
force assignments: *should*/*ought* are weak necessity (comparative class),
*must* is strong necessity (non-comparative). -/

open Fragments.English.FunctionWords

/-- The English fragment classifies *should* as weak necessity,
    matching its membership in the evaluative comparative class. -/
theorem fragment_should_weak :
    Fragments.English.FunctionWords.should.modalMeaning.any
      (·.force == .weakNecessity) = true := by native_decide

/-- The English fragment classifies *ought* as weak necessity. -/
theorem fragment_ought_weak :
    Fragments.English.FunctionWords.ought.modalMeaning.any
      (·.force == .weakNecessity) = true := by native_decide

/-- The English fragment classifies *must* as strong necessity. -/
theorem fragment_must_strong :
    Fragments.English.FunctionWords.must.modalMeaning.any
      (·.force == .necessity) = true := by native_decide

/-- *must* is NOT classified as weak necessity — confirming it is
    outside the evaluative comparative natural class. -/
theorem fragment_must_not_weak :
    Fragments.English.FunctionWords.must.modalMeaning.any
      (·.force == .weakNecessity) = false := by native_decide

/-- *should* is NOT classified as strong necessity — confirming the
    asymmetry: comparative class members have strictly weaker force. -/
theorem fragment_should_not_strong :
    Fragments.English.FunctionWords.should.modalMeaning.any
      (·.force == .necessity) = false := by native_decide

/-- *need* is classified as strong necessity — matching its exclusion
    from the evaluative comparative class (§2.1.2, note 14). -/
theorem fragment_need_strong :
    Fragments.English.FunctionWords.need.modalMeaning.any
      (·.force == .necessity) = true := by native_decide

/-- *need* is NOT classified as weak necessity — confirming it fails
    the scalar tests (examples 16, 18–19). -/
theorem fragment_need_not_weak :
    Fragments.English.FunctionWords.need.modalMeaning.any
      (·.force == .weakNecessity) = false := by native_decide

end Phenomena.Modality.Studies.Rubinstein2014
