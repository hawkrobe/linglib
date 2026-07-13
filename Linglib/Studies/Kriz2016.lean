import Linglib.Data.Examples.Kriz2015
import Linglib.Data.Generalizations.HomogeneityGap
import Linglib.Studies.Magri2014
import Linglib.Semantics.Plurality.Homogeneity.Basic
import Linglib.Semantics.Plurality.Distributivity
import Linglib.Semantics.Plurality.Trivalent

/-!
# Križ (2016): Homogeneity, Non-Maximality, and All — Plural Instantiation
[kriz-2015] [kriz-2016] [fine-1975]

Homogeneity, Non-Maximality, and All. Journal of Semantics 33(3): 493-539.

This file is the **plural instantiation** of the general homogeneity substrate
in `Semantics.Homogeneity.Basic`. It connects [kriz-2016]'s
plural-definite analysis (atoms as specification points; `all` as gap remover)
to the substrate operators (`removeGap`, `addressesIssue`, `usable`,
`communicatedContent`).

## Related literature engaged

[lasersohn-1999] (the "townspeople asleep" original observation),
[brisson-1998] (non-maximality terminology + `but`/`although` exception
diagnostics), [schwarz-2013] (processing evidence that maximal is the
default reading), [malamud-2012] (decision-theoretic precursor with
issue partitions, criticised in Appendix A.3 of the paper),
[spector-2013] (embedded-plural projection),
[kriz-chemla-2015] (companion experimental data),
[magri-2014] (alternative gap-derivation via double EXH),
[cobreros-etal-2012] (Tolerant/Classical/Strict trivalence; Appendix A.2),
[gajewski-2005] (homogeneity-as-presupposition view, rejected in §4.4),
[roberts-1996] (QUD-stack tradition the §4.5 caveat distinguishes from).

## Core Contributions

Non-maximal readings of plural definites ("The professors smiled" true even if
Smith didn't) arise from the interaction of two independent components:

1. **Homogeneity** (semantic): plural predication yields a three-valued truth
   value — true (all satisfy), false (none satisfy), or gap (some but not all).

2. **Weakened Quality** (pragmatic): the maxim of quality is weakened to "say
   only what is true enough for current purposes," where "current purposes"
   are formalized as an issue (partition of possible worlds).

The semantic effect of `all` is to remove the extension gap, making positive
and negative extensions complementary. This prevents non-maximal readings
because the pragmatic mechanism (Sufficient Trivalent + Addressing) has no gap
to exploit.

## §4.4 caveat — homogeneity is NOT a presupposition

[kriz-2016] §4.4 argues against the [gajewski-2005] (and Schwarzschild
1994, Löbner 2000) view that the homogeneity gap is a presupposition. Križ's
arguments include local accommodation behaviour and projection from conditional
antecedents differing from standard presupposition behaviour. This file
adopts the trivalent-but-not-presuppositional reading: gap-worlds are
"between" true and false, not undefined-in-the-presupposition sense.

## §4.5 caveat — current issue ≠ immediate-last QUD

The variable name `QUD W` here is a substrate convenience and is NOT the
[roberts-1996] QUD-stack notion. [kriz-2016] §4.5 is explicit
(eq. 39, 40 examples) that identifying the current issue with the
immediate-last question on the stack makes wrong predictions. Križ instead
treats the current issue as referring to overarching goals of participants,
underdetermined by linguistic material and not directly manipulable. The
`coarseQ`/`fineQ` partitions in our finite model are pedagogical constructions;
they are NOT meant as a commitment to the manipulable-QUD theory the paper
rejects.

## §4.6 puzzle — numerals block non-maximality

[kriz-2016] §4.6 flags as an unsolved puzzle that "the ten professors
smiled" cannot get non-maximal readings, even though "the professors smiled"
can. The paper offers only speculation. Križ also notes (43a-b) that French
patterns differently. We do not address this puzzle here.

## Contents

- `barePluralTV`, `allPluralTV`: plural-specific instantiations
- Theorems linking gap-removal to `all` semantics
- A 5-world finite model demonstrating end-to-end predictions
  (including §4.2 angry-Smith vs. neutral-Smith distinction)
- §5/§6 bridges to the typed switches data in `Data.Examples.Kriz2015`
  and the pooled `Generalizations.HomogeneityGap` observations
- §7 connection back to the supervaluation framework

## Finite Model

A concrete 5-world model demonstrates end-to-end predictions: "the professors
smiled" is usable at a gap-world (smithNeutral) under a coarse issue but not
under a fine one, AND not at a gap-world (smithAngry) where Smith's anger is
issue-relevant — capturing [kriz-2016] §4.2's distinctive prediction.
Adding "all" blocks non-maximal use entirely.
-/

namespace Kriz2016

open Semantics.Plurality
open Semantics.Plurality.Distributivity
open Semantics.Plurality.Trivalent
open Semantics.Homogeneity

variable {Atom W : Type*} [DecidableEq Atom]

-- ============================================================================
-- Section 1: Plural Predication as Sentence Extension
-- ============================================================================

/-- The bare plural sentence "the Xs are P" as a trivalent sentence. -/
def barePluralTV (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom) : SentenceTV W :=
  λ w => pluralTruthValue P x w

/-- The `all`-sentence "all the Xs are P". Per [kriz-2016] §3.1,
    `all`'s semantic contribution IS gap removal — it adds nothing on top
    of the bare plural's universal truth conditions, only collapses the gap
    into the negative extension. So we *derive* `allPluralTV` from the bare
    plural via `removeGap`, rather than stipulating its semantics. Bivalence
    and the truth-conditional behavior then follow from substrate lemmas. -/
def allPluralTV (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom) : SentenceTV W :=
  removeGap (barePluralTV P x)

omit [DecidableEq Atom] in
/-- `all` IS gap removal — by definition, after the [kriz-2016] §3.1
    refactor. Retained as a named lemma for readability. -/
theorem allPluralTV_eq_removeGap (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom) :
    allPluralTV P x = removeGap (barePluralTV P x) := rfl

omit [DecidableEq Atom] in
/-- `all` eliminates the extension gap. Direct consequence of
`removeGap_not_homogeneous` from the substrate. -/
theorem all_no_gap (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom) :
    gapExt (allPluralTV P x) = ∅ := by
  by_contra h
  exact removeGap_not_homogeneous (barePluralTV P x) h

omit [DecidableEq Atom] in
/-- `all` removes homogeneity: the `all`-sentence is never homogeneous.
Direct consequence of substrate `removeGap_not_homogeneous`. -/
theorem all_not_homogeneous (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom) :
    ¬isHomogeneous (allPluralTV P x) :=
  removeGap_not_homogeneous (barePluralTV P x)

omit [DecidableEq Atom] in
/-- A bare plural is homogeneous whenever a gap-world exists: the existence
of a world where some-but-not-all atoms satisfy P makes the sentence
homogeneous, enabling non-maximal readings via Sufficient Trivalent. -/
theorem bare_plural_homogeneous (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom)
    (w : W) (hGap : barePluralTV P x w = .indet) :
    isHomogeneous (barePluralTV P x) := by
  intro h; rw [Set.eq_empty_iff_forall_notMem] at h
  exact h w hGap

omit [DecidableEq Atom] in
/-- Positive extensions agree: bare plural and `all`-sentence are true
in the same worlds. Substrate consequence of `removeGap_posExt_eq`. -/
theorem all_posExt_eq (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom) :
    posExt (allPluralTV P x) = posExt (barePluralTV P x) :=
  removeGap_posExt_eq (barePluralTV P x)

omit [DecidableEq Atom] in
/-- `all` absorbs the gap into the negative extension: the negative extension
of the `all`-sentence equals the union of the bare plural's negative extension
and gap. Substrate consequence of `removeGap_negExt_eq`. -/
theorem all_negExt_eq (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom) :
    negExt (barePluralTV P x) ∪ gapExt (barePluralTV P x) =
    negExt (allPluralTV P x) :=
  (removeGap_negExt_eq (barePluralTV P x)).symm

-- ============================================================================
-- Section 2: The Effect of `all`
-- ============================================================================

omit [DecidableEq Atom] in
/-- `all`-sentences are bivalent. Substrate consequence of `removeGap_bivalent`. -/
theorem all_bivalent (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom) :
    isBivalent (allPluralTV P x) :=
  removeGap_bivalent (barePluralTV P x)

/-- Gap removal on a plural sentence is true iff all atoms satisfy P.
    Substrate-side bridge between `removeGap` and the `allSatisfy` predicate.
    Used by `all_blocked_by_wide_issue` and downstream consumers
    (`KrizSpector2021.removeGap_iff_forallH`). The `_hne` hypothesis is
    retained for compatibility with consumers; the proof itself doesn't
    need it (the empty case is vacuously true on both sides). -/
theorem removeGap_plural_true_iff (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (_hne : x.Nonempty) (w : W) :
    removeGap (fun w => pluralTruthValue P x w) w = .true ↔
    allSatisfy P x w := by
  rw [← pluralTruthValue_eq_true_iff]
  show Trivalent.metaAssert (pluralTruthValue P x w) = .true ↔
       pluralTruthValue P x w = .true
  generalize pluralTruthValue P x w = t
  cases t <;>
    simp only [Trivalent.metaAssert_true, Trivalent.metaAssert_false, Trivalent.metaAssert_indet,
      iff_self, reduceCtorEq]

/-- `bivalentPred` of an `all`-sentence is true iff `allSatisfy` holds.
    Bridge between the trivalent encoding of `allPluralTV` and the Prop-valued
    `allSatisfy` predicate K&S 2021's strong-relevance machinery works on.
    Used by `KrizSpector2021.all_addressing_iff_relevant`. -/
theorem bivalentPred_allPluralTV_eq_allSatisfy (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom)
    (w : W) : bivalentPred (allPluralTV P x) w = true ↔ allSatisfy P x w := by
  show ((allPluralTV P x w) == .true) = true ↔ allSatisfy P x w
  cases h : allPluralTV P x w with
  | true =>
    refine ⟨fun _ => ?_, fun _ => rfl⟩
    have hPlural : pluralTruthValue P x w = .true := by
      show barePluralTV P x w = .true
      have hMem : w ∈ posExt (allPluralTV P x) := h
      rw [all_posExt_eq P x] at hMem
      exact hMem
    exact (pluralTruthValue_eq_true_iff P x w).mp hPlural
  | false =>
    refine ⟨fun hf => absurd hf (by decide), fun hAS => ?_⟩
    exfalso
    have : allPluralTV P x w = .true := by
      have hPlural : pluralTruthValue P x w = .true :=
        (pluralTruthValue_eq_true_iff P x w).mpr hAS
      have hMem : w ∈ posExt (barePluralTV P x) := hPlural
      rw [← all_posExt_eq P x] at hMem
      exact hMem
    rw [this] at h
    exact absurd h (by decide)
  | indet =>
    exfalso
    cases all_bivalent P x w with
    | inl h' => rw [h'] at h; cases h
    | inr h' => rw [h'] at h; cases h

/-- `all` prevents non-maximal use: if an `all`-sentence is usable at w,
then all atoms literally satisfy P at w.

The proof factors through the substrate: by `removeGap_bivalent` and
usability's `S w ≠ .false` clause, the all-sentence is literally true at w;
by `removeGap_posExt_eq`, the bare plural is also literally true at w; by
`pluralTruthValue_eq_true_iff`, all atoms satisfy P. The `addressesIssue`
clause of `usable` does no work in *this* direction — it's what blocks
`all`-sentences from being USED at all in wide-issue contexts (see
`all_blocked_by_wide_issue`). -/
theorem all_prevents_nonmax (q : QUD W) (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom)
    (w : W) (h : usable q (allPluralTV P x) w) : allSatisfy P x w := by
  -- bivalence + not-false ⇒ true
  have hTrue : allPluralTV P x w = .true :=
    ((bivalent_usable_iff_true q _ (all_bivalent P x) w).mp h).1
  -- removeGap preserves positive extension ⇒ bare plural is also true
  have hBareTrue : barePluralTV P x w = .true := by
    have hMem : w ∈ posExt (allPluralTV P x) := hTrue
    rw [all_posExt_eq P x] at hMem
    exact hMem
  exact (pluralTruthValue_eq_true_iff P x w).mp hBareTrue

/-- `all`-sentences cannot be used in "wide" issues — issues whose cells
straddle the `all`/`not-all` boundary. This is the complementary work
done by `addressesIssue`: while bivalence forces literal truth
(`all_prevents_nonmax`), addressing forces relevance — the `all`-sentence
can only be uttered at all if every QUD cell agrees on whether `allSatisfy`
holds. This is the [kriz-2016] §3.4 wide-issue blocking that completes
the picture: bivalence alone does not derive Križ's headline finding;
Addressing also has to do work, in this complementary direction. -/
theorem all_blocked_by_wide_issue (q : QUD W) (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom)
    (hne : x.Nonempty)
    (hWide : ∃ w₁ w₂, q.r w₁ w₂ ∧ allSatisfy P x w₁ ∧ ¬ allSatisfy P x w₂) :
    ¬ addressesIssue q (allPluralTV P x) := by
  intro hAddr
  obtain ⟨w₁, w₂, hEq, h1, h2⟩ := hWide
  have h1' : allPluralTV P x w₁ = .true :=
    (removeGap_plural_true_iff P x hne w₁).mpr h1
  have h2' : allPluralTV P x w₂ = .false := by
    cases all_bivalent P x w₂ with
    | inl h =>
      have hAll : allSatisfy P x w₂ :=
        (removeGap_plural_true_iff P x hne w₂).mp h
      exact absurd hAll h2
    | inr h => exact h
  exact hAddr ⟨w₁, w₂, hEq, h1', h2'⟩

/-- Unmentionability of exceptions (§4.1): if the `all`-sentence is usable
at w, there are no exceptions to mention. "#Although all the professors
smiled, Smith didn't" is contradictory — `all` forces literal truth, so any
exception makes the sentence false, and false sentences cannot be used. -/
theorem all_exceptions_unmentionable (q : QUD W) (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) (a : Atom) (ha : a ∈ x)
    (h : usable q (allPluralTV P x) w) : P a w := by
  have := all_prevents_nonmax q P x w h
  exact this a ha

-- ============================================================================
-- Section 3: Gap Enables Non-Maximal Use
-- ============================================================================

omit [DecidableEq Atom] in
/-- The gap enables non-maximal use: if the bare plural has a gap at w
and w's cell contains a positive-extension world, then the bare plural
is usable at w (assuming addressing is satisfied). This is the mechanism
Križ 2016 identifies for non-maximality: gap-worlds can be "true enough"
without being literally true.

This is an instance of the general `Semantics.Homogeneity.gap_enables_nonmax`. -/
theorem plural_gap_enables_nonmax (q : QUD W) (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom)
    (w w' : W)
    (hGap : barePluralTV P x w = .indet)
    (hEquiv : q.r w w')
    (hTrue : barePluralTV P x w' = .true)
    (hAddr : addressesIssue q (barePluralTV P x)) :
    usable q (barePluralTV P x) w :=
  Semantics.Homogeneity.gap_enables_nonmax q (barePluralTV P x) w w' hGap hEquiv hTrue hAddr

-- ============================================================================
-- Section 4: Finite Model
-- ============================================================================

/-! A concrete 4-world model demonstrates the theory's predictions end-to-end.
Three professors attend Sue's talk; the predicate is "smiled."

| World          | Smith | Jones | Lee | Bare plural | All   |
|----------------|-------|-------|-----|-------------|-------|
| allSmiled      | ✓     | ✓     | ✓   | TRUE        | true  |
| smithNeutral   | ✗     | ✓     | ✓   | GAP         | false |
| onlyLeeSmiled  | ✗     | ✗     | ✓   | GAP         | false |
| noneSmiled     | ✗     | ✗     | ✗   | FALSE       | false |

Two QUDs:
- **Coarse** ("Was the talk well-received?"): groups allSmiled ≈ smithNeutral
- **Fine** ("Did every professor smile?"): each world in its own cell

Predictions:
- Bare plural usable at smithNeutral under coarse QUD (non-maximal reading)
- Bare plural NOT usable at smithNeutral under fine QUD (maximal only)
- `all`-sentence never usable at smithNeutral (forces literal truth)
-/

section FiniteModel

/-- Worlds in the 5-world finite model. The split between `smithNeutral` and
    `smithAngry` captures [kriz-2016] §4.2: in both worlds Smith fails
    to smile, but his behavior differs in QUD-relevance. Smith looking neutral
    is irrelevant to "was the talk well-received"; Smith looking visibly angry
    is relevant (it pulls reception down). -/
inductive ProfWorld where
  | allSmiled
  | smithNeutral   -- Smith neutral expression (irrelevant exception)
  | smithAngry     -- Smith visibly angry (relevant exception per §4.2)
  | onlyLeeSmiled
  | noneSmiled
  deriving DecidableEq, Repr

inductive Prof where
  | smith | jones | lee
  deriving DecidableEq, Repr

instance : Fintype ProfWorld where
  elems := {.allSmiled, .smithNeutral, .smithAngry, .onlyLeeSmiled, .noneSmiled}
  complete := by intro x; cases x <;> simp

instance : Fintype Prof where
  elems := {.smith, .jones, .lee}
  complete := by intro x; cases x <;> simp

/-- Did this professor smile in this world? Note that Smith fails to smile
    in BOTH `smithNeutral` and `smithAngry`; the worlds differ only in what
    Smith does instead, which matters to QUD relevance (§4.2). -/
def smiled : Prof → ProfWorld → Prop
  | .smith, .allSmiled      => True
  | .smith, .smithNeutral   => False
  | .smith, .smithAngry     => False
  | .smith, .onlyLeeSmiled  => False
  | .smith, .noneSmiled     => False
  | .jones, .allSmiled      => True
  | .jones, .smithNeutral   => True
  | .jones, .smithAngry     => True
  | .jones, .onlyLeeSmiled  => False
  | .jones, .noneSmiled     => False
  | .lee,   .allSmiled      => True
  | .lee,   .smithNeutral   => True
  | .lee,   .smithAngry     => True
  | .lee,   .onlyLeeSmiled  => True
  | .lee,   .noneSmiled     => False

instance smiled.instDecidable : ∀ p w, Decidable (smiled p w) := by
  intro p w; cases p <;> cases w <;> unfold smiled <;> infer_instance

/-- All three professors. -/
def profs : Finset Prof := Finset.univ

/-- Reception grade for the coarse QUD. Per [kriz-2016] §4.2,
    Smith's anger pulls reception down to `mixed`; Smith's neutrality leaves
    it `positive`. This single QUD captures Križ's distinctive prediction
    that *what Smith does instead* of smiling matters. -/
inductive Reception where | positive | mixed | negative
  deriving DecidableEq

def receptionGrade : ProfWorld → Reception
  | .allSmiled => .positive
  | .smithNeutral => .positive
  | .smithAngry => .mixed       -- §4.2: Smith's anger is relevant
  | .onlyLeeSmiled => .mixed
  | .noneSmiled => .negative

/-- Coarse QUD: "Was Sue's talk well-received?"
Groups allSmiled with smithNeutral (both = positive reception). -/
def coarseQ : QUD ProfWorld := QUD.ofDecEq receptionGrade

/-- Fine QUD: "Did every professor smile?"
Each world is its own cell. -/
def fineQ : QUD ProfWorld := QUD.ofDecEq id

-- Trivalent values at each world

theorem bare_allSmiled :
    barePluralTV smiled profs .allSmiled = .true := by decide

theorem bare_smithNeutral :
    barePluralTV smiled profs .smithNeutral = .indet := by decide

theorem bare_onlyLeeSmiled :
    barePluralTV smiled profs .onlyLeeSmiled = .indet := by decide

theorem bare_noneSmiled :
    barePluralTV smiled profs .noneSmiled = .false := by decide

/-- The bare plural sentence about the professors IS homogeneous —
smithNeutral is in the extension gap. -/
theorem bare_profs_homogeneous :
    isHomogeneous (barePluralTV smiled profs) :=
  bare_plural_homogeneous smiled profs .smithNeutral (by decide)

-- End-to-end predictions

/-- The bare plural IS usable at smithNeutral under the coarse QUD.
Smith's failure to smile is irrelevant to whether the talk was well-received,
so the sentence is "true enough." -/
theorem smithNeutral_usable_coarse :
    usable coarseQ (barePluralTV smiled profs) .smithNeutral :=
  ⟨ by decide
  , ⟨.allSmiled, by decide, by decide⟩
  , by intro ⟨w₁, w₂, hEq, hTrue, hFalse⟩
       cases w₁ <;> cases w₂ <;>
         (first | exact absurd hTrue (by decide)
                | exact absurd hFalse (by decide)
                | exact absurd hEq (by decide))
  ⟩

/-- The bare plural is NOT usable at smithNeutral under the fine QUD.
The fine QUD distinguishes allSmiled from smithNeutral, so there is no
literally-true world in smithNeutral's cell. -/
theorem smithNeutral_not_usable_fine :
    ¬usable fineQ (barePluralTV smiled profs) .smithNeutral := by
  intro ⟨_, ⟨w', hEq, hTrue⟩, _⟩
  cases w' <;>
    (first | exact absurd hTrue (by decide)
           | exact absurd hEq (by decide))

/-- The `all`-sentence is never usable at smithNeutral (under any QUD),
because Smith didn't smile. Concrete instance of `all_prevents_nonmax`. -/
theorem all_not_usable_smithNeutral (q : QUD ProfWorld)
    (h : usable q (allPluralTV smiled profs) .smithNeutral) : False := by
  have := all_prevents_nonmax q smiled profs .smithNeutral h
  revert this; decide

/-- Concrete instance of `all_exceptions_unmentionable`: Smith's exception
cannot be mentioned because Smith did smile in every world where the
`all`-sentence is usable. -/
theorem smith_exception_unmentionable (q : QUD ProfWorld) (w : ProfWorld)
    (h : usable q (allPluralTV smiled profs) w) :
    smiled .smith w :=
  all_exceptions_unmentionable q smiled profs w .smith (by simp [profs]) h

/-- Communicated content under the coarse QUD includes the gap-world
smithNeutral — the non-maximal reading is communicated. -/
theorem coarse_communicates_gap :
    .smithNeutral ∈ communicatedContent coarseQ (barePluralTV smiled profs) :=
  ⟨.allSmiled, by decide, by decide⟩

/-- Communicated content under the fine QUD does NOT include smithNeutral. -/
theorem fine_does_not_communicate_gap :
    .smithNeutral ∉ communicatedContent fineQ (barePluralTV smiled profs) := by
  intro ⟨w', hEq, hTrue⟩
  cases w' <;>
    (first | exact absurd hTrue (by decide)
           | exact absurd hEq (by decide))

-- ----------------------------------------------------------------------------
-- §4.2: What exceptions DO matters (Smith neutral vs. Smith angry)
-- ----------------------------------------------------------------------------

/-! [kriz-2016] §4.2 makes a distinctive prediction beyond the basic
    homogeneity-gap analysis: it matters not only *whether* an exception is
    tolerated but also *what the exception does instead*. Smith looking
    neutral is irrelevant to whether the talk was well-received; Smith looking
    visibly angry IS relevant. The model captures this by placing
    `smithNeutral` and `smithAngry` in different cells of `coarseQ`
    (positive vs. mixed reception).

    This is a competing-theory differentiator: theories that locate
    non-maximality in restricted reference (Brisson) or alternative geometry
    (Magri) cannot easily express that *what Smith does instead* changes
    the judgment, because they don't have an issue parameter that interacts
    with individual behavior. -/

theorem bare_smithAngry :
    barePluralTV smiled profs .smithAngry = .indet := by decide

/-- §4.2 distinctive prediction: bare plural is NOT usable at `smithAngry`
under the coarse QUD, even though it IS usable at `smithNeutral` under the
same QUD. The difference is which cell each world inhabits: smithNeutral
shares its cell with allSmiled (positive reception); smithAngry sits in
the `mixed` cell with onlyLeeSmiled, neither of which is in the bare
plural's positive extension. -/
theorem bare_smithAngry_not_usable_coarse :
    ¬ usable coarseQ (barePluralTV smiled profs) .smithAngry := by
  intro ⟨_, ⟨w', hEq, hTrue⟩, _⟩
  cases w' <;>
    (first | exact absurd hTrue (by decide)
           | exact absurd hEq (by decide))

/-- Together, `smithNeutral_usable_coarse` and `bare_smithAngry_not_usable_coarse`
demonstrate Križ §4.2: the SAME bare plural sentence under the SAME QUD is
usable at one gap-world and not at another, depending on what the exception
does. Theories of non-maximality lacking an issue/cell parameter cannot
express this contrast. -/
theorem kriz_4_2_distinctive_prediction :
    usable coarseQ (barePluralTV smiled profs) .smithNeutral ∧
    ¬ usable coarseQ (barePluralTV smiled profs) .smithAngry :=
  ⟨smithNeutral_usable_coarse, bare_smithAngry_not_usable_coarse⟩

end FiniteModel

-- ============================================================================
-- Section 5: Connection to Empirical Data (Data.Examples.Kriz2015)
-- ============================================================================

/-! The finite model captures the same pattern as the typed switches data in
`Data.Examples.Kriz2015`. "Oh no, the switches are on!" is acceptable under
the existential issue (fire risk from any switch — the all/some distinction
is irrelevant) and unacceptable under the universal issue (fire risk only
if all are on), corresponding to `smithNeutral_usable_coarse` vs
`smithNeutral_not_usable_fine`. The "all the switches" variant is
unacceptable even in the permissive context, corresponding to
`all_not_usable_smithNeutral`. -/

open Kriz2015.Examples in
/-- Non-maximality context contrast: the same gap-scenario sentence is
acceptable under the existential issue, unacceptable under the universal. -/
theorem switches_nonmax_contrast :
    switches_nonmax_existential.judgment = .acceptable ∧
    switches_nonmax_universal.judgment = .unacceptable :=
  ⟨rfl, rfl⟩

open Kriz2015.Examples in
/-- `all` blocks non-maximality even in the permissive existential-issue
context: the "all the switches" variant of the acceptable row is
unacceptable. -/
theorem switches_all_blocks :
    switches_nonmax_existential.alternatives =
      [("Oh no, all the switches are on!", .unacceptable)] :=
  rfl

-- ============================================================================
-- Section 6: Connection to Homogeneity-Gap Data (Generalizations.HomogeneityGap)
-- ============================================================================

/-! The switches gap rows of `Data.Examples.Kriz2015` lift to `.indet`
observations in the cross-paper `Generalizations.HomogeneityGap` pool —
the value `barePluralTV` assigns at the model's gap-world
(`bare_smithNeutral`). The gap-removal effect of `all` (gap absorbed into
the negative extension, so the gap scenario comes out clearly false) is
proved structurally by `all_no_gap`, `all_negExt_eq`, and
`all_not_homogeneous`. -/

open Generalizations.HomogeneityGap in
/-- Both switches gap rows (positive and negated) observe the trivalent gap
value `.indet`: the gap is symmetric under negation. -/
theorem switches_gap_observed_indet :
    (fromExample Kriz2015.Examples.switches_pos_gap).map (·.observed) =
      some .indet ∧
    (fromExample Kriz2015.Examples.switches_neg_gap).map (·.observed) =
      some .indet := by
  decide

open Generalizations.HomogeneityGap in
/-- The finite model matches the data: the bare plural's truth value at the
gap-world `smithNeutral` is exactly the value the positive gap row observes. -/
theorem model_matches_gap_row :
    (fromExample Kriz2015.Examples.switches_pos_gap).map (·.observed) =
      some (barePluralTV smiled profs .smithNeutral) := by
  decide

-- ============================================================================
-- Section 7: Connection to Supervaluation Framework
-- ============================================================================

/-! Plural predication is an instance of supervaluation ([fine-1975]).
    Each atom in the plurality is a specification point: the predicate is
    super-true iff satisfied by all atoms, super-false iff by none, and
    indefinite when some-but-not-all satisfy it (the homogeneity gap).

    This unifies several independent literatures, each contributing a
    different specification-space sort:

    - [fine-1975]: varying the *threshold* for vague predicates
    - [kriz-2016]: varying the *atom* for plural predicates
    - `dist` in `Trivalent`: a third implementation of the same pattern
      over `List Bool`
    - `selectional_eq_dist` in `Counterfactual.lean`: closest worlds
    - [haug-dalrymple-2020] §5 (paper eq 109): varying the
      *precisification of the reciprocal's restrictor* (maximal-set vs
      reference-set) for quantified-antecedent reciprocals — see
      `Studies/HaugDalrymple2020.lean`'s
      `quantifiedReciprocalTV_iff_supervaluation`. -/

open Semantics.Supervaluation (SpecSpace superTrue)

omit [DecidableEq Atom] in
/-- **Plural predication = supervaluation over atoms.** The bare plural
    "the Xs are P" at world w has the same truth value as `superTrue`
    with atoms as specification points and `P(·,w)` as the evaluation
    function.

    This is the structural identity connecting homogeneity gaps to
    vagueness gaps: both arise from disagreement across specification
    points (atoms vs thresholds vs comparison classes). -/
theorem barePluralTV_eq_superTrue (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (hne : x.Nonempty) (w : W) :
    barePluralTV P x w = superTrue (fun a => P a w) ⟨x, hne⟩ := by
  simp only [barePluralTV, pluralTruthValue, dif_pos hne]
  rw [Semantics.Supervaluation.superTrue_eq_dist]

omit [DecidableEq Atom] in
/-- Corollary: homogeneity (gap existence) is exactly supervaluation
    indefiniteness. If the bare plural is gapped at w, then `superTrue`
    returns `.indet` — witnesses exist on both sides. -/
theorem homogeneity_gap_is_indefiniteness (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (hne : x.Nonempty) (w : W)
    (hgap : barePluralTV P x w = .indet) :
    superTrue (fun a => P a w) ⟨x, hne⟩ = Trivalent.indet := by
  rw [← barePluralTV_eq_superTrue P x hne w]; exact hgap

omit [DecidableEq Atom] in
/-- Corollary: `all` removes homogeneity by collapsing the specification
    space to a single point (the universal check). This corresponds to
    Fine's fidelity theorem: singleton specification spaces are classical. -/
theorem all_removes_supervaluation_gap (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) :
    allPluralTV P x w ≠ .indet := by
  cases all_bivalent P x w with
  | inl h => rw [h]; decide
  | inr h => rw [h]; decide


-- ============================================================================
-- Section 8: Conjunction overgeneration (cross-framework divergence)
-- ============================================================================

/-! [kriz-2016] §6.2 considers (and explicitly offers no resolution for)
the puzzle that conjunctions of proper names exhibit homogeneity but resist
non-maximal readings. If we model "Bert, Claire and Dora went there" as a
plural-style supervaluation over atoms {Bert, Claire, Dora}, Križ's
`gap_enables_nonmax` predicts non-maximal use at a gap-world that's
QUD-equivalent to a true-world. Empirically this prediction fails — the
conjunction sentence does NOT permit non-maximality in the same gap context
where the corresponding plural definite does. Križ acknowledges this in §6.2
and speculates about "team credit" but offers no formalization;
`conj_modeled_as_plural_predicts_nonmax` makes the overgenerated prediction
kernel-visible. -/

section ConjunctionOvergeneration

inductive ConjAtom where | bert | claire | dora
  deriving DecidableEq, Repr

inductive ConjWorld where | allWent | dorasMissing | onlyBert | noneWent
  deriving DecidableEq, Repr

instance : Fintype ConjAtom where
  elems := {.bert, .claire, .dora}
  complete := by intro x; cases x <;> simp

instance : Fintype ConjWorld where
  elems := {.allWent, .dorasMissing, .onlyBert, .noneWent}
  complete := by intro x; cases x <;> simp

def wentThere : ConjAtom → ConjWorld → Prop
  | .bert,   .allWent       => True
  | .bert,   .dorasMissing  => True
  | .bert,   .onlyBert      => True
  | .bert,   .noneWent      => False
  | .claire, .allWent       => True
  | .claire, .dorasMissing  => True
  | .claire, .onlyBert      => False
  | .claire, .noneWent      => False
  | .dora,   .allWent       => True
  | .dora,   .dorasMissing  => False
  | .dora,   .onlyBert      => False
  | .dora,   .noneWent      => False

instance wentThere.instDecidable : ∀ a w, Decidable (wentThere a w) := by
  intro a w; cases a <;> cases w <;> unfold wentThere <;> infer_instance

def threeCoworkers : Finset ConjAtom := Finset.univ

/-- Coarse "did anyone go?" issue: groups all worlds where someone went
into a single cell, vs. the noneWent cell. -/
inductive ConjPartition where | someWent | noneWent
  deriving DecidableEq

def someWentPartition : ConjWorld → ConjPartition
  | .allWent => .someWent
  | .dorasMissing => .someWent
  | .onlyBert => .someWent
  | .noneWent => .noneWent

def coarseConjQ : QUD ConjWorld := QUD.ofDecEq someWentPartition

theorem conj_dorasMissing_gap :
    barePluralTV wentThere threeCoworkers .dorasMissing = .indet := by decide

/-- Lean prediction: if we model the conjunction "Bert, Claire and Dora went"
as a plural over {Bert, Claire, Dora}, Križ's machinery predicts usability
at the gap-world `dorasMissing` (where Dora missed but the others went),
under the coarse "did someone go?" issue. -/
theorem conj_modeled_as_plural_predicts_nonmax :
    usable coarseConjQ (barePluralTV wentThere threeCoworkers) .dorasMissing := by
  refine ⟨?_, ⟨.allWent, ?_, ?_⟩, ?_⟩
  · decide
  · decide
  · decide
  · intro ⟨w₁, w₂, hEq, hTrue, hFalse⟩
    cases w₁ <;> cases w₂ <;>
      (first | exact absurd hTrue (by decide)
             | exact absurd hFalse (by decide)
             | exact absurd hEq (by decide))

end ConjunctionOvergeneration

-- ============================================================================
-- Section 9: Križ vs Magri formal divergence on the gap's value
-- ============================================================================

/-! [magri-2014] derives homogeneity from double-strengthening on
alternative geometry (`MYSTERY`/`WEAK`/`STRONG` roles, Horn-mate structure).
Magri's `doubleExh .mystery` on a gap scenario is FALSE (theorem
`Magri2014.gap_positive_false`). This is bivalent-FALSE: the gap is
collapsed to the negative extension by the alternative-exhaustification
machinery, before any pragmatics applies.

[kriz-2016]'s `barePluralTV` on the same gap pattern returns `.indet`
(homogeneity gap), and the gap is then PRAGMATICALLY recoverable via
`gap_enables_nonmax` under a coarse QUD. This is the central Križ vs.
Magri disagreement: Magri puts the gap-collapse INSIDE the semantics
(via doubleExh); Križ keeps the gap and lets pragmatics (sufficient truth +
addressing) decide whether non-maximal use is licensed.

Empirically Križ has the upper hand: non-maximal readings DO occur (see the
finite model's `smithNeutral_usable_coarse`). Under Magri's bivalent-FALSE,
the sentence at the gap is unutterable in standard Gricean terms (false
sentences violate Quality); to recover non-maximal readings, Magri needs
additional downstream pragmatic machinery beyond what the alternative-
geometry account itself provides.

This is the cross-framework reconciler's core point: the SAME empirical
gap data (the `Data.Examples.Kriz2015` switches gap rows) gets two
incompatible derivations, and the formalization makes the incompatibility
kernel-checked. -/

section MagriDivergence

open Magri2014

/-- A 3-atom Magri scenario where 2 of 3 atoms satisfy the predicate —
    the count-abstraction analogue of the `smithNeutral` world (Smith
    didn't smile, Jones and Lee did). -/
def magriGapScenario : Scenario :=
  { total := 3, satisfying := 2, valid := by omega }

theorem magriGapScenario_isGap : isGap magriGapScenario = true := by decide

/-- Magri's `doubleExh .mystery` returns FALSE on a 2-of-3 gap. This is the
    bivalent-FALSE assignment: the gap is collapsed semantically. -/
theorem magri_2of3_gap_is_bivalent_false :
    doubleExh .mystery magriGapScenario = false :=
  gap_positive_false magriGapScenario magriGapScenario_isGap

/-- **Križ vs. Magri formal divergence on the gap's status**.

    On the same 2-of-3 gap pattern:
    - **Magri**: `doubleExh .mystery` returns FALSE — the gap is collapsed
      semantically by alternative-exhaustification, pre-pragmatics. False
      sentences are unutterable (violate Quality).
    - **Križ**: `barePluralTV` returns INDET (`bare_smithNeutral`), and the
      bare plural IS USABLE under a coarse QUD (`smithNeutral_usable_coarse`).
      The gap is preserved and pragmatically recoverable.

    Both predictions cannot be right about the empirical fact that
    non-maximal readings exist for plural definites at gap-worlds. The
    theorem packages the disagreement as a kernel-checked conjunction;
    its existence is the formal incompatibility between alternative-geometry
    derivations and supervaluation derivations of homogeneity. -/
theorem kriz_vs_magri_alternative_geometry :
    -- Magri: bivalent-FALSE on the 2-of-3 gap (doubleExh .mystery)
    doubleExh .mystery magriGapScenario = false ∧
    -- Križ: trivalent-INDET on the analogous world AND pragmatically usable
    barePluralTV smiled profs .smithNeutral = .indet ∧
    usable coarseQ (barePluralTV smiled profs) .smithNeutral :=
  ⟨magri_2of3_gap_is_bivalent_false, bare_smithNeutral, smithNeutral_usable_coarse⟩

end MagriDivergence

-- ============================================================================
-- Section 10: Cohen 1999 generics — equivocal "homogeneity"
-- ============================================================================

/-! [kriz-2016] §6.3 claims the homogeneity-plus-pragmatics machinery
extends to bare-plural generics ("Israelis live on the coastal plain" — true
despite exceptions), with subkinds as the specification points. The
`Semantics.Homogeneity.Basic` substrate docstring records this as a
candidate spec-point instantiation.

However, `Cohen1999` uses the word "homogeneity"
for a *different* equation: presupposition failure when conditional probabilities
diverge across partitions of the domain. Cohen's homogeneity returns
"undefined" via *presupposition failure*; Križ's returns `Trivalent.indet` via
*supervaluation gap on subkinds*.

A formal `kriz_vs_cohen_generic_homogeneity` divergence theorem would require
lifting Cohen's presupposition-style machinery into the `Trivalent` framework —
not done here. The substrate docstring's claim that "the framework extends to
generics" should be read with this caveat: it extends to a Križ-style
treatment of generics, which is NOT what `Cohen1999` formalizes. -/

end Kriz2016
