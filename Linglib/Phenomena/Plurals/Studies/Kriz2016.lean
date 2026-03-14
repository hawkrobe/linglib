import Linglib.Theories.Semantics.Lexical.Plural.Distributivity
import Linglib.Theories.Semantics.Supervaluation.Basic
import Linglib.Theories.Semantics.Homogeneity
import Linglib.Phenomena.Plurals.NonMaximality
import Linglib.Phenomena.Plurals.Homogeneity

/-!
# Križ (2016): Homogeneity, Non-Maximality, and All
@cite{kriz-2016}

Homogeneity, Non-Maximality, and All. Journal of Semantics 33(3): 493-539.

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
because the pragmatic mechanism (Sufficient Truth + Addressing) has no gap
to exploit.

## Key Definitions

These general definitions live in `Theories/Semantics/Homogeneity.lean` and
are imported here:

- **SentenceTV**: trivalent sentence denotation (W → Truth3)
- **posExt / negExt / gapExt**: positive, negative, and gap extensions
- **sufficientlyTrue**: S "true enough" at w wrt issue I
- **addressesIssue**: no cell overlaps both ⟦S⟧⁺ and ⟦S⟧⁻
- **usable**: conjunction of not-false, sufficiently true, addresses issue
- **communicatedContent**: worlds indistinguishable from ⟦S⟧⁺ under I
- **removeGap**: collapse gap into negative extension (what `all` does)

This file adds plural-specific instantiations and bridges to Križ & Spector
2021's strong relevance filtering in `Distributivity.lean`.

## Finite Model

A concrete 4-world model demonstrates end-to-end predictions: "the professors
smiled" is usable at a gap-world under a coarse issue but not under a fine one,
and adding "all" blocks non-maximal use entirely.
-/

namespace Phenomena.Plurals.Studies.Kriz2016

open Core.Duality (Truth3)
open Semantics.Lexical.Plural.Distributivity
open Semantics.Homogeneity

variable {Atom W : Type*} [DecidableEq Atom]

-- ============================================================================
-- Section 1: Plural Predication as Sentence Extension
-- ============================================================================

/-- The bare plural sentence "the Xs are P" as a trivalent sentence. -/
def barePluralTV (P : Atom → W → Bool) (x : Finset Atom) : SentenceTV W :=
  λ w => pluralTruthValue P x w

/-- The `all`-sentence "all the Xs are P" as a bivalent sentence.
`all` removes homogeneity: the truth value is always true or false. -/
def allPluralTV (P : Atom → W → Bool) (x : Finset Atom) : SentenceTV W :=
  λ w => if allSatisfy P x w then .true else .false

omit [DecidableEq Atom] in
/-- `all` eliminates the extension gap. -/
theorem all_no_gap (P : Atom → W → Bool) (x : Finset Atom) :
    gapExt (allPluralTV P x) = ∅ := by
  ext w; simp only [gapExt, allPluralTV, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  split <;> simp

omit [DecidableEq Atom] in
/-- `all` removes homogeneity: the `all`-sentence is never homogeneous.
Corresponds to `HomogeneityRemover.all` in `Homogeneity.lean`. -/
theorem all_not_homogeneous (P : Atom → W → Bool) (x : Finset Atom) :
    ¬isHomogeneous (allPluralTV P x) :=
  fun h => h (all_no_gap P x)

omit [DecidableEq Atom] in
/-- A bare plural is homogeneous whenever a gap-world exists: the existence
of a world where some-but-not-all atoms satisfy P makes the sentence
homogeneous, enabling non-maximal readings via Sufficient Truth. -/
theorem bare_plural_homogeneous (P : Atom → W → Bool) (x : Finset Atom)
    (w : W) (hGap : barePluralTV P x w = .gap) :
    isHomogeneous (barePluralTV P x) := by
  intro h; rw [Set.eq_empty_iff_forall_notMem] at h
  exact h w hGap

/-- Positive extensions agree: bare plural and `all`-sentence are true
in the same worlds. -/
theorem all_posExt_eq (P : Atom → W → Bool) (x : Finset Atom) :
    posExt (allPluralTV P x) = posExt (barePluralTV P x) := by
  ext w; simp only [posExt, allPluralTV, barePluralTV, Set.mem_setOf_eq]
  constructor
  · intro h; split_ifs at h <;> simp_all [pluralTruthValue_eq_true_iff]
  · intro h
    rw [pluralTruthValue_eq_true_iff] at h
    simp [h]

omit [DecidableEq Atom] in
/-- `all` absorbs the gap into the negative extension: the negative extension
of the `all`-sentence equals the union of the bare plural's negative extension
and gap. -/
theorem all_negExt_eq (P : Atom → W → Bool) (x : Finset Atom) :
    negExt (barePluralTV P x) ∪ gapExt (barePluralTV P x) =
    negExt (allPluralTV P x) := by
  ext w; simp only [negExt, gapExt, allPluralTV, barePluralTV, Set.mem_union,
    Set.mem_setOf_eq]
  unfold pluralTruthValue Semantics.Supervaluation.superTrue allSatisfy
  simp only [decide_eq_true_eq]
  split_ifs <;> simp_all

-- ============================================================================
-- Section 2: The Effect of `all`
-- ============================================================================

omit [DecidableEq Atom] in
/-- `all`-sentences are bivalent. -/
theorem all_bivalent (P : Atom → W → Bool) (x : Finset Atom) :
    isBivalent (allPluralTV P x) := by
  intro w; simp only [allPluralTV]; split_ifs <;> simp

omit [DecidableEq Atom] in
/-- `all` prevents non-maximal use: if an `all`-sentence is usable at w,
then all atoms literally satisfy P at w.

This is the headline result of the paper's analysis of `all`. The bare
plural "the Xs are P" can be used non-maximally (at gap-worlds where
some but not all Xs satisfy P), but "all the Xs are P" cannot — usability
forces literal truth. -/
theorem all_prevents_nonmax (q : QUD W) (P : Atom → W → Bool) (x : Finset Atom)
    (w : W) (h : usable q (allPluralTV P x) w) : allSatisfy P x w = true := by
  cases h_eq : allSatisfy P x w with
  | true => rfl
  | false => exact absurd (show allPluralTV P x w = .false by simp [allPluralTV, h_eq]) h.1

omit [DecidableEq Atom] in
/-- Unmentionability of exceptions (§4.1): if the `all`-sentence is usable
at w, there are no exceptions to mention. "#Although all the professors
smiled, Smith didn't" is contradictory — `all` forces literal truth, so any
exception makes the sentence false, and false sentences cannot be used. -/
theorem all_exceptions_unmentionable (q : QUD W) (P : Atom → W → Bool)
    (x : Finset Atom) (w : W) (a : Atom) (ha : a ∈ x)
    (h : usable q (allPluralTV P x) w) : P a w = true := by
  have := all_prevents_nonmax q P x w h
  simp only [allSatisfy, decide_eq_true_eq] at this
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
theorem plural_gap_enables_nonmax (q : QUD W) (P : Atom → W → Bool) (x : Finset Atom)
    (w w' : W)
    (hGap : barePluralTV P x w = .gap)
    (hEquiv : q.sameAnswer w w' = true)
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

inductive ProfWorld where
  | allSmiled | smithNeutral | onlyLeeSmiled | noneSmiled
  deriving DecidableEq, Repr

inductive Prof where
  | smith | jones | lee
  deriving DecidableEq, Repr

instance : Fintype ProfWorld where
  elems := {.allSmiled, .smithNeutral, .onlyLeeSmiled, .noneSmiled}
  complete := by intro x; cases x <;> simp

instance : Fintype Prof where
  elems := {.smith, .jones, .lee}
  complete := by intro x; cases x <;> simp

/-- Did this professor smile in this world? -/
def smiled : Prof → ProfWorld → Bool
  | .smith, .allSmiled      => true
  | .smith, .smithNeutral   => false
  | .smith, .onlyLeeSmiled  => false
  | .smith, .noneSmiled     => false
  | .jones, .allSmiled      => true
  | .jones, .smithNeutral   => true
  | .jones, .onlyLeeSmiled  => false
  | .jones, .noneSmiled     => false
  | .lee,   .allSmiled      => true
  | .lee,   .smithNeutral   => true
  | .lee,   .onlyLeeSmiled  => true
  | .lee,   .noneSmiled     => false

/-- All three professors. -/
def profs : Finset Prof := Finset.univ

/-- Reception grade for the coarse QUD. -/
inductive Reception where | positive | mixed | negative
  deriving DecidableEq

def receptionGrade : ProfWorld → Reception
  | .allSmiled => .positive
  | .smithNeutral => .positive
  | .onlyLeeSmiled => .mixed
  | .noneSmiled => .negative

/-- Coarse QUD: "Was Sue's talk well-received?"
Groups allSmiled with smithNeutral (both = positive reception). -/
def coarseQ : QUD ProfWorld := QUD.ofDecEq receptionGrade

/-- Fine QUD: "Did every professor smile?"
Each world is its own cell. -/
def fineQ : QUD ProfWorld := QUD.ofDecEq id

-- Truth values at each world

theorem bare_allSmiled :
    barePluralTV smiled profs .allSmiled = .true := by native_decide

theorem bare_smithNeutral :
    barePluralTV smiled profs .smithNeutral = .gap := by native_decide

theorem bare_onlyLeeSmiled :
    barePluralTV smiled profs .onlyLeeSmiled = .gap := by native_decide

theorem bare_noneSmiled :
    barePluralTV smiled profs .noneSmiled = .false := by native_decide

/-- The bare plural sentence about the professors IS homogeneous —
smithNeutral is in the extension gap. -/
theorem bare_profs_homogeneous :
    isHomogeneous (barePluralTV smiled profs) :=
  bare_plural_homogeneous smiled profs .smithNeutral (by native_decide)

-- End-to-end predictions

/-- The bare plural IS usable at smithNeutral under the coarse QUD.
Smith's failure to smile is irrelevant to whether the talk was well-received,
so the sentence is "true enough." -/
theorem smithNeutral_usable_coarse :
    usable coarseQ (barePluralTV smiled profs) .smithNeutral :=
  ⟨ by native_decide
  , ⟨.allSmiled, by native_decide, by native_decide⟩
  , by intro ⟨w₁, w₂, hEq, hTrue, hFalse⟩
       cases w₁ <;> cases w₂ <;>
         (first | exact absurd hTrue (by native_decide)
                | exact absurd hFalse (by native_decide)
                | exact absurd hEq (by native_decide))
  ⟩

/-- The bare plural is NOT usable at smithNeutral under the fine QUD.
The fine QUD distinguishes allSmiled from smithNeutral, so there is no
literally-true world in smithNeutral's cell. -/
theorem smithNeutral_not_usable_fine :
    ¬usable fineQ (barePluralTV smiled profs) .smithNeutral := by
  intro ⟨_, ⟨w', hEq, hTrue⟩, _⟩
  cases w' <;>
    (first | exact absurd hTrue (by native_decide)
           | exact absurd hEq (by native_decide))

/-- The `all`-sentence is never usable at smithNeutral (under any QUD),
because Smith didn't smile. Concrete instance of `all_prevents_nonmax`. -/
theorem all_not_usable_smithNeutral (q : QUD ProfWorld)
    (h : usable q (allPluralTV smiled profs) .smithNeutral) : False := by
  have := all_prevents_nonmax q smiled profs .smithNeutral h
  revert this; native_decide

/-- Concrete instance of `all_exceptions_unmentionable`: Smith's exception
cannot be mentioned because Smith did smile in every world where the
`all`-sentence is usable. -/
theorem smith_exception_unmentionable (q : QUD ProfWorld) (w : ProfWorld)
    (h : usable q (allPluralTV smiled profs) w) :
    smiled .smith w = true :=
  all_exceptions_unmentionable q smiled profs w .smith (by simp [profs]) h

/-- Communicated content under the coarse QUD includes the gap-world
smithNeutral — the non-maximal reading is communicated. -/
theorem coarse_communicates_gap :
    .smithNeutral ∈ communicatedContent coarseQ (barePluralTV smiled profs) :=
  ⟨.allSmiled, by native_decide, by native_decide⟩

/-- Communicated content under the fine QUD does NOT include smithNeutral. -/
theorem fine_does_not_communicate_gap :
    .smithNeutral ∉ communicatedContent fineQ (barePluralTV smiled profs) := by
  intro ⟨w', hEq, hTrue⟩
  cases w' <;>
    (first | exact absurd hTrue (by native_decide)
           | exact absurd hEq (by native_decide))

end FiniteModel

-- ============================================================================
-- Section 5: Connection to Empirical Data (NonMaximality.lean)
-- ============================================================================

/-! The finite model captures the same pattern as the theory-neutral data
in `NonMaximality.lean`. The switches scenario records that "the switches
are on" is acceptable in a non-maximal context (fire risk from any switch)
but not in a maximal one (fire risk only if all on). This corresponds to
`smithNeutral_usable_coarse` vs `smithNeutral_not_usable_fine`.

Similarly, `switchesAllBlocks` records that "all the switches are on" is
unacceptable even in the permissive context, corresponding to
`all_not_usable_smithNeutral`. -/

open Phenomena.Plurals.NonMaximality in
/-- The switches datum records non-maximal use is acceptable. -/
theorem switches_nonmax_acceptable :
    switchesNonMaximality.acceptableInNonMaximalContext = true := rfl

open Phenomena.Plurals.NonMaximality in
/-- The switches datum records maximal use is not acceptable (in gap scenario). -/
theorem switches_max_not_acceptable :
    switchesNonMaximality.acceptableInMaximalContext = false := rfl

open Phenomena.Plurals.NonMaximality in
/-- "All" blocks non-maximality even in permissive contexts. -/
theorem switches_all_blocks :
    switchesAllBlocks.allAcceptable = false := rfl

open Phenomena.Plurals.NonMaximality in
/-- The coarse issue makes the all/some distinction irrelevant,
which is the precondition for non-maximal readings. -/
theorem coarse_issue_irrelevant :
    switchesNonMaximality.nonMaximalContext.allSomeDistinctionRelevant = false := rfl

-- ============================================================================
-- Section 6: Connection to Homogeneity Data (Homogeneity.lean)
-- ============================================================================

/-! Bridge to the theory-neutral homogeneity data in `Homogeneity.lean`.
The data records `all` as a homogeneity remover and specifies that gap
scenarios yield `.neitherTrueNorFalse` for homogeneous sentences but
`.clearlyFalse` for `all`-sentences. The structural theorems `all_no_gap`
and `all_not_homogeneous` prove this mechanism, and the finite model
demonstrates it concretely via `bare_profs_homogeneous`. -/

open Phenomena.Plurals.Homogeneity in
/-- The homogeneity data lists `all` as a remover. -/
theorem all_is_homogeneity_remover :
    allRemovesHomogeneity.remover = .all := rfl

open Phenomena.Plurals.Homogeneity in
/-- Gap scenarios yield `.neitherTrueNorFalse` for homogeneous sentences:
the signature of the extension gap that enables non-maximal readings. -/
theorem homogeneous_gap_yields_neither :
    allRemovesHomogeneity.homogeneousJudgment = .neitherTrueNorFalse := rfl

open Phenomena.Plurals.Homogeneity in
/-- Adding `all` makes the gap-scenario sentence clearly false — the gap
is absorbed into the negative extension. -/
theorem all_gap_yields_false :
    allRemovesHomogeneity.preciseJudgment = .clearlyFalse := rfl

open Phenomena.Plurals.Homogeneity in
/-- The switches datum records homogeneity in the gap: positive sentence
is neither true nor false when some-but-not-all switches are on. -/
theorem switches_gap_is_neither :
    switchesExample.positiveInGap = .neitherTrueNorFalse := rfl

open Phenomena.Plurals.Homogeneity in
/-- Outside the gap, judgments are clear: all switches on → clearly true. -/
theorem switches_all_on_clearly_true :
    switchesExample.positiveInAll = .clearlyTrue := rfl

-- ============================================================================
-- Section 7: Connection to Supervaluation Framework
-- ============================================================================

/-! Plural predication is an instance of supervaluation (@cite{fine-1975}).
    Each atom in the plurality is a specification point: the predicate is
    super-true iff satisfied by all atoms, super-false iff by none, and
    indefinite when some-but-not-all satisfy it (the homogeneity gap).

    This unifies two independent literatures:
    - @cite{fine-1975}: varying the *threshold* for vague predicates
    - @cite{kriz-2016}: varying the *atom* for plural predicates

    Both are instances of `Semantics.Supervaluation.superTrue`. The `dist`
    operator in `Core.Duality` is a third implementation of the same pattern
    over `List Bool`; `selectional_eq_dist` in `Counterfactual.lean` proves
    yet another instance for closest worlds. -/

open Semantics.Supervaluation (SpecSpace superTrue)

/-- **Plural predication = supervaluation over atoms.** The bare plural
    "the Xs are P" at world w has the same truth value as `superTrue`
    with atoms as specification points and `P(·,w)` as the evaluation
    function.

    This is the structural identity connecting homogeneity gaps to
    vagueness gaps: both arise from disagreement across specification
    points (atoms vs thresholds vs comparison classes). -/
theorem barePluralTV_eq_superTrue (P : Atom → W → Bool)
    (x : Finset Atom) (hne : x.Nonempty) (w : W) :
    barePluralTV P x w = superTrue (fun a => P a w) ⟨x, hne⟩ := by
  simp [barePluralTV, pluralTruthValue, dif_pos hne]

/-- Corollary: homogeneity (gap existence) is exactly supervaluation
    indefiniteness. If the bare plural is gapped at w, then `superTrue`
    returns `.indet` — witnesses exist on both sides. -/
theorem homogeneity_gap_is_indefiniteness (P : Atom → W → Bool)
    (x : Finset Atom) (hne : x.Nonempty) (w : W)
    (hgap : barePluralTV P x w = .gap) :
    superTrue (fun a => P a w) ⟨x, hne⟩ = Truth3.indet := by
  rw [← barePluralTV_eq_superTrue P x hne w]; exact hgap

/-- Corollary: `all` removes homogeneity by collapsing the specification
    space to a single point (the universal check). This corresponds to
    Fine's fidelity theorem: singleton specification spaces are classical. -/
theorem all_removes_supervaluation_gap (P : Atom → W → Bool)
    (x : Finset Atom) (w : W) :
    allPluralTV P x w ≠ .gap := by
  simp only [allPluralTV]; split_ifs <;> simp

end Phenomena.Plurals.Studies.Kriz2016
