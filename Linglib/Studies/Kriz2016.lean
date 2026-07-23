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
in `Semantics.Homogeneity`. It connects [kriz-2016]'s
plural-definite analysis (atoms as specification points; `all` as gap remover)
to the substrate operators (`removeGap`, `addressesIssue`, `usable`,
`communicatedContent`).

## Related literature engaged

[lasersohn-1999] (the "townspeople asleep" original observation; the *although*
exception diagnostic, traced there to [kroch-1974]),
[brisson-1998] (the term "non-maximality"),
[schwarz-2013] (processing evidence that maximal is the default reading),
[malamud-2012] (decision-theoretic precursor with issue partitions,
criticised in the paper's Appendix A.3),
[spector-2013] (embedded-plural projection),
[kriz-chemla-2015] (companion experimental data),
[magri-2014] (alternative gap-derivation via double EXH — engaged by the
paper itself; see the divergence section below),
[cobreros-etal-2012] (Tolerant/Classical/Strict trivalence, discussed in the
paper's Appendix A.2 via Burnett's adaptation),
[gajewski-2005] (homogeneity-as-presupposition view, rejected in §4.4),
[roberts-1996] (QUD-stack tradition the §4.5 caveat distinguishes from).

## Core contributions

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
to exploit. The §4.1 unmentionability of exceptions follows from the same
machinery: an exception-mentioning continuation cannot address any issue
under which the bare plural was used non-maximally
(`Semantics.Homogeneity.exception_unaddressable`, instantiated below).

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
(examples (39)-(40)) that identifying the current issue with the
immediate-last question on the stack makes wrong predictions. Križ instead
treats the current issue as referring to overarching goals of participants,
underdetermined by linguistic material and not directly manipulable. The
`coarseQ`/`fineQ` partitions in our finite model are pedagogical constructions;
they are NOT meant as a commitment to the manipulable-QUD theory the paper
rejects.

## §4.6 puzzle — numerals block non-maximality

[kriz-2016] §4.6 flags as unsolved that "the ten professors smiled" cannot
get non-maximal readings, even though "the professors smiled" can (French,
per the paper's (43a-b), patterns differently). We do not address this
puzzle here.

## Finite model

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
variable (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (x : Finset Atom)

/-! ### Plural predication as sentence extension -/

/-- The bare plural sentence "the Xs are P" as a trivalent sentence. -/
def barePluralTV : SentenceTV W :=
  λ w => pluralTruthValue P x w

/-- The `all`-sentence "all the Xs are P". Per [kriz-2016] §3.1,
    `all`'s semantic contribution IS gap removal — it adds nothing on top
    of the bare plural's universal truth conditions, only collapses the gap
    into the negative extension. So we *derive* `allPluralTV` from the bare
    plural via `removeGap`, rather than stipulating its semantics. Bivalence
    and the truth-conditional behavior then follow from substrate lemmas. -/
def allPluralTV : SentenceTV W :=
  removeGap (barePluralTV P x)

omit [DecidableEq Atom] in
/-- `all` eliminates the extension gap. Direct consequence of
`removeGap_not_homogeneous` from the substrate. -/
theorem all_no_gap : gapExt (allPluralTV P x) = ∅ := by
  by_contra h
  exact removeGap_not_homogeneous (barePluralTV P x) h

omit [DecidableEq Atom] in
/-- `all` removes homogeneity: the `all`-sentence is never homogeneous.
Direct consequence of substrate `removeGap_not_homogeneous`. -/
theorem all_not_homogeneous : ¬isHomogeneous (allPluralTV P x) :=
  removeGap_not_homogeneous (barePluralTV P x)

omit [DecidableEq Atom] in
/-- Positive extensions agree: bare plural and `all`-sentence are true
in the same worlds. Substrate consequence of `removeGap_posExt_eq`. -/
theorem all_posExt_eq : posExt (allPluralTV P x) = posExt (barePluralTV P x) :=
  removeGap_posExt_eq (barePluralTV P x)

omit [DecidableEq Atom] in
/-- `all` absorbs the gap into the negative extension: the negative extension
of the `all`-sentence equals the union of the bare plural's negative extension
and gap. Substrate consequence of `removeGap_negExt_eq`. -/
theorem all_negExt_eq :
    negExt (barePluralTV P x) ∪ gapExt (barePluralTV P x) =
    negExt (allPluralTV P x) :=
  (removeGap_negExt_eq (barePluralTV P x)).symm

/-! ### The effect of `all` -/

omit [DecidableEq Atom] in
/-- `all`-sentences are bivalent. Substrate consequence of `removeGap_bivalent`. -/
theorem all_bivalent : isBivalent (allPluralTV P x) :=
  removeGap_bivalent (barePluralTV P x)

/-- Gap removal on a plural sentence is true iff all atoms satisfy P.
    Substrate-side bridge between `removeGap` and the `allSatisfy` predicate.
    Used by `all_blocked_by_wide_issue` and downstream consumers
    (`KrizSpector2021.removeGap_iff_forallH`). -/
theorem removeGap_plural_true_iff (w : W) :
    removeGap (fun w => pluralTruthValue P x w) w = .true ↔
    allSatisfy P x w := by
  rw [← pluralTruthValue_eq_true_iff]; simp only [removeGap]
  generalize pluralTruthValue P x w = t
  cases t <;> simp

/-- `bivalentPred` of an `all`-sentence is true iff `allSatisfy` holds.
    Bridge between the trivalent encoding of `allPluralTV` and the Prop-valued
    `allSatisfy` predicate K&S 2021's strong-relevance machinery works on.
    Used by `KrizSpector2021.all_addressing_iff_relevant`. -/
theorem bivalentPred_allPluralTV_eq_allSatisfy (w : W) :
    bivalentPred (allPluralTV P x) w = true ↔ allSatisfy P x w := by
  simp only [bivalentPred, beq_iff_eq, allPluralTV]
  exact removeGap_plural_true_iff P x w

/-- `all` prevents non-maximal use: if an `all`-sentence is usable at w,
then all atoms literally satisfy P at w.

The proof factors through the substrate: by `removeGap_bivalent` and
usability's `S w ≠ .false` clause, the all-sentence is literally true at w;
by `removeGap_posExt_eq`, the bare plural is also literally true at w; by
`pluralTruthValue_eq_true_iff`, all atoms satisfy P. The `addressesIssue`
clause of `usable` does no work in *this* direction — it's what blocks
`all`-sentences from being USED at all in wide-issue contexts (see
`all_blocked_by_wide_issue`). -/
theorem all_prevents_nonmax (q : QUD W) (w : W)
    (h : usable q (allPluralTV P x) w) : allSatisfy P x w := by
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
theorem all_blocked_by_wide_issue (q : QUD W)
    (hWide : ∃ w₁ w₂, q.r w₁ w₂ ∧ allSatisfy P x w₁ ∧ ¬ allSatisfy P x w₂) :
    ¬ addressesIssue q (allPluralTV P x) := by
  intro hAddr
  obtain ⟨w₁, w₂, hEq, h1, h2⟩ := hWide
  have h1' : allPluralTV P x w₁ = .true :=
    (removeGap_plural_true_iff P x w₁).mpr h1
  have h2' : allPluralTV P x w₂ = .false := by
    cases all_bivalent P x w₂ with
    | inl h =>
      have hAll : allSatisfy P x w₂ :=
        (removeGap_plural_true_iff P x w₂).mp h
      exact absurd hAll h2
    | inr h => exact h
  exact hAddr ⟨w₁, w₂, hEq, h1', h2'⟩

/-- The `all`-side complement of §4.1: if the `all`-sentence is usable
at w, there are no exceptions at all. "#Although all the professors
smiled, Smith didn't" is contradictory — `all` forces literal truth, so any
exception makes the sentence false, and false sentences cannot be used.
Križ's §4.1 unmentionability result proper concerns the *bare* plural and
is `Semantics.Homogeneity.exception_unaddressable`, instantiated at
`smith_exception_unaddressable` below. -/
theorem all_exceptions_unmentionable (q : QUD W) (w : W) (a : Atom) (ha : a ∈ x)
    (h : usable q (allPluralTV P x) w) : P a w := by
  have := all_prevents_nonmax P x q w h
  exact this a ha

/-! ### Finite model

A concrete 5-world model demonstrates the theory's predictions end-to-end.
Three professors attend Sue's talk; the predicate is "smiled."

| World          | Smith | Jones | Lee | Bare plural | All   |
|----------------|-------|-------|-----|-------------|-------|
| allSmiled      | ✓     | ✓     | ✓   | TRUE        | true  |
| smithNeutral   | ✗     | ✓     | ✓   | GAP         | false |
| smithAngry     | ✗     | ✓     | ✓   | GAP         | false |
| onlyLeeSmiled  | ✗     | ✗     | ✓   | GAP         | false |
| noneSmiled     | ✗     | ✗     | ✗   | FALSE       | false |

`smithNeutral` and `smithAngry` agree on who smiled; they differ in what
Smith does instead, which the coarse QUD is sensitive to (§4.2).

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
  deriving DecidableEq, Repr, Fintype

inductive Prof where
  | smith | jones | lee
  deriving DecidableEq, Repr, Fintype

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

/-! #### Trivalent values at each world -/

theorem bare_allSmiled :
    barePluralTV smiled profs .allSmiled = .true := by decide

theorem bare_smithNeutral :
    barePluralTV smiled profs .smithNeutral = .indet := by decide

theorem bare_onlyLeeSmiled :
    barePluralTV smiled profs .onlyLeeSmiled = .indet := by decide

theorem bare_noneSmiled :
    barePluralTV smiled profs .noneSmiled = .false := by decide

/-- The bare plural sentence about the professors IS homogeneous —
smithNeutral is in the extension gap. Substrate `isHomogeneous_of_gap`. -/
theorem bare_profs_homogeneous :
    isHomogeneous (barePluralTV smiled profs) :=
  isHomogeneous_of_gap (barePluralTV smiled profs) .smithNeutral (by decide)

/-! #### End-to-end predictions -/

/-- The bare plural IS usable at smithNeutral under the coarse QUD.
Smith's failure to smile is irrelevant to whether the talk was well-received,
so the sentence is "true enough." -/
theorem smithNeutral_usable_coarse :
    usable coarseQ (barePluralTV smiled profs) .smithNeutral := by decide

/-- The bare plural is NOT usable at smithNeutral under the fine QUD.
The fine QUD distinguishes allSmiled from smithNeutral, so there is no
literally-true world in smithNeutral's cell. -/
theorem smithNeutral_not_usable_fine :
    ¬usable fineQ (barePluralTV smiled profs) .smithNeutral := by decide

/-- The `all`-sentence is never usable at smithNeutral (under any QUD),
because Smith didn't smile. Concrete instance of `all_prevents_nonmax`. -/
theorem all_not_usable_smithNeutral (q : QUD ProfWorld)
    (h : usable q (allPluralTV smiled profs) .smithNeutral) : False :=
  absurd (all_prevents_nonmax smiled profs q .smithNeutral h) (by decide)

/-- Concrete instance of `all_exceptions_unmentionable`: Smith's exception
cannot be mentioned because Smith did smile in every world where the
`all`-sentence is usable. -/
theorem smith_exception_unmentionable (q : QUD ProfWorld) (w : ProfWorld)
    (h : usable q (allPluralTV smiled profs) w) :
    smiled .smith w :=
  all_exceptions_unmentionable smiled profs q w .smith (by decide) h

/-- Communicated content under the coarse QUD includes the gap-world
smithNeutral — the non-maximal reading is communicated. -/
theorem coarse_communicates_gap :
    .smithNeutral ∈ communicatedContent coarseQ (barePluralTV smiled profs) :=
  ⟨.allSmiled, by decide, by decide⟩

/-- Communicated content under the fine QUD does NOT include smithNeutral. -/
theorem fine_does_not_communicate_gap :
    .smithNeutral ∉ communicatedContent fineQ (barePluralTV smiled profs) := by
  intro ⟨w', hEq, hTrue⟩
  revert hEq hTrue; cases w' <;> decide

/-! #### Unmentionability of exceptions (§4.1)

[kriz-2016] §4.1's striking observation is about the *bare* plural:
"#The professors smiled, but one of them didn't" is infelicitous even where
the non-maximal reading is licensed (the paper's (25a-b), with the *although*
diagnostic traced to [kroch-1974] via [lasersohn-1999]). The derivation is
pure Addressing: non-maximal use requires a cell containing both a
literally-true world and the gap-world, and the exception-mentioning
continuation is true at the latter but false at the former — so it straddles
that cell and cannot address the issue. The general form is the substrate's
`exception_unaddressable`; here is the concrete instance. -/

/-- "Smith didn't smile" — the exception-mentioning continuation, as a
    (bivalent) trivalent sentence. -/
def smithDidntSmile : SentenceTV ProfWorld :=
  λ w => if smiled .smith w then .false else .true

/-- §4.1 unmentionability, bare-plural version: under the coarse issue that
licenses the non-maximal use of "the professors smiled" at `smithNeutral`,
the continuation "…but Smith didn't" cannot address the issue. Instance of
`Semantics.Homogeneity.exception_unaddressable`. -/
theorem smith_exception_unaddressable :
    ¬ addressesIssue coarseQ smithDidntSmile :=
  exception_unaddressable coarseQ (barePluralTV smiled profs) smithDidntSmile
    .smithNeutral smithNeutral_usable_coarse (by decide) (by decide)

/-! #### What exceptions do (§4.2)

[kriz-2016] §4.2 makes a distinctive prediction beyond the basic
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
    ¬ usable coarseQ (barePluralTV smiled profs) .smithAngry := by decide

/-- The §4.2 contrast: the SAME bare plural sentence under the SAME QUD is
usable at one gap-world and not at another, depending on what the exception
does. Theories of non-maximality lacking an issue/cell parameter cannot
express this contrast. -/
theorem bare_usable_neutral_not_angry :
    usable coarseQ (barePluralTV smiled profs) .smithNeutral ∧
    ¬ usable coarseQ (barePluralTV smiled profs) .smithAngry :=
  ⟨smithNeutral_usable_coarse, bare_smithAngry_not_usable_coarse⟩

end FiniteModel

/-! ### Connection to the typed switches data

The finite model captures the same pattern as the typed switches data in
`Data.Examples.Kriz2015`. "Oh no, the switches are on!" is acceptable under
the existential issue (fire risk from any switch — the all/some distinction
is irrelevant) and unacceptable under the universal issue (fire risk only
if all are on), corresponding to `smithNeutral_usable_coarse` vs
`smithNeutral_not_usable_fine`; the "all the switches" variant is
unacceptable even in the permissive context, corresponding to
`all_not_usable_smithNeutral`. The gap rows lift to `.indet` observations
in the cross-paper `Generalizations.HomogeneityGap` pool — the value
`barePluralTV` assigns at the model's gap-world (`bare_smithNeutral`). -/

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

/-! ### Connection to the supervaluation framework

Plural predication is an instance of supervaluation ([fine-1975]).
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
theorem barePluralTV_eq_superTrue (hne : x.Nonempty) (w : W) :
    barePluralTV P x w = superTrue (fun a => P a w) ⟨x, hne⟩ := by
  simp only [barePluralTV, pluralTruthValue]
  rw [Semantics.Supervaluation.superTrue_eq_dist]

omit [DecidableEq Atom] in
/-- Corollary: homogeneity (gap existence) is exactly supervaluation
    indefiniteness. If the bare plural is gapped at w, then `superTrue`
    returns `.indet` — witnesses exist on both sides. -/
theorem homogeneity_gap_is_indefiniteness (hne : x.Nonempty) (w : W)
    (hgap : barePluralTV P x w = .indet) :
    superTrue (fun a => P a w) ⟨x, hne⟩ = Trivalent.indet := by
  rw [← barePluralTV_eq_superTrue P x hne w]; exact hgap

omit [DecidableEq Atom] in
/-- Corollary: `all` removes homogeneity by collapsing the specification
    space to a single point (the universal check). This corresponds to
    Fine's fidelity theorem: singleton specification spaces are classical. -/
theorem all_removes_supervaluation_gap (w : W) :
    allPluralTV P x w ≠ .indet := by
  rcases all_bivalent P x w with h | h <;> simp [h]

/-! ### Conjunction overgeneration (§6.2)

[kriz-2016] §6.2 notes that conjunctions of proper names exhibit
homogeneity (citing Szabolcsi & Haddican 2004 and [magri-2014]) yet
generally resist non-maximal readings — a potential problem for the claimed
correlation between homogeneity and non-maximality. If we model "Bert,
Claire and Dora went there" as a plural-style supervaluation over atoms
{Bert, Claire, Dora}, `gap_enables_nonmax` predicts non-maximal use at a
gap-world that's QUD-equivalent to a true-world; empirically such readings
are at best very rare. Križ's own response is informal: mentioning an
individual in a conjunction prompts the hearer to accommodate a finer
current issue, relative to which no non-maximal reading of the conjunction
survives (he also suggests team credit may itself be non-maximality, which
would make rare counterexamples expected). No formalization of the
accommodation step is offered; `conj_modeled_as_plural_predicts_nonmax`
makes the overgenerated prediction of the accommodation-free plural-style
model kernel-visible. -/

section ConjunctionOvergeneration

inductive ConjAtom where | bert | claire | dora
  deriving DecidableEq, Repr, Fintype

inductive ConjWorld where | allWent | dorasMissing | onlyBert | noneWent
  deriving DecidableEq, Repr, Fintype

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
  decide

end ConjunctionOvergeneration

/-! ### Križ vs Magri: the gap's value (cross-framework divergence)

[magri-2014] derives homogeneity from double-strengthening on
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

Both operators are run on the SAME input: `Magri2014.fromPredicate`
translates the finite model's `(smiled, profs, smithNeutral)` into Magri's
count abstraction, so the divergence is carried by the types, not asserted
in prose. -/

section MagriDivergence

open Magri2014

/-- A 3-atom Magri scenario where 2 of 3 atoms satisfy the predicate. -/
def magriGapScenario : Scenario :=
  { total := 3, satisfying := 2, valid := by omega }

/-- The Magri-side reading of the finite model's gap world: counting
    satisfiers of `smiled` over `profs` at `smithNeutral` yields exactly
    the 2-of-3 scenario. This is what makes the divergence below a
    same-input comparison. -/
theorem fromPredicate_smithNeutral :
    fromPredicate smiled profs .smithNeutral = magriGapScenario := rfl

theorem magriGapScenario_isGap : isGap magriGapScenario = true := by decide

/-- Magri's `doubleExh .mystery` returns FALSE on a 2-of-3 gap. This is the
    bivalent-FALSE assignment: the gap is collapsed semantically. -/
theorem magri_2of3_gap_is_bivalent_false :
    doubleExh .mystery magriGapScenario = false :=
  gap_positive_false magriGapScenario magriGapScenario_isGap

/-- **Križ vs. Magri formal divergence on the gap's status**.

    On the SAME input — the finite model's gap-world, read by Magri through
    `fromPredicate` and by Križ through `barePluralTV`:
    - **Magri**: `doubleExh .mystery` returns FALSE — the gap is collapsed
      semantically by alternative-exhaustification, pre-pragmatics. False
      sentences are unutterable (violate Quality).
    - **Križ**: `barePluralTV` returns INDET (`bare_smithNeutral`), and the
      bare plural IS USABLE under a coarse QUD (`smithNeutral_usable_coarse`).
      The gap is preserved and pragmatically recoverable.

    Both predictions cannot be right about the empirical fact that
    non-maximal readings exist for plural definites at gap-worlds; the
    theorem packages the disagreement as a kernel-checked conjunction over
    a shared input. -/
theorem kriz_vs_magri_alternative_geometry :
    doubleExh .mystery (fromPredicate smiled profs .smithNeutral) = false ∧
    barePluralTV smiled profs .smithNeutral = .indet ∧
    usable coarseQ (barePluralTV smiled profs) .smithNeutral :=
  ⟨fromPredicate_smithNeutral.symm ▸ magri_2of3_gap_is_bivalent_false,
   bare_smithNeutral, smithNeutral_usable_coarse⟩

end MagriDivergence

end Kriz2016
