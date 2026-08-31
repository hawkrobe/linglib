import Linglib.Pragmatics.Implicature.SomeAll
import Linglib.Studies.GeurtsPouscoulous2009
import Linglib.Pragmatics.Implicature.Diagnostics

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
/-!
# Chemla and Spector 2011: experimental evidence for embedded scalar implicatures

This file formalizes the argument of [chemla-spector-2011] that scalar inferences computed in
embedded position are detectable, against [geurts-pouscoulous-2009]. The disagreement turns on
method: a binary truth-value judgment makes a participant pick one reading, while a graded
judgment on a continuous scale lets a picture that satisfies more of a sentence's available
readings be rated higher, which is the paper's §3.2 conjecture and this file's `RatingsMonotone`.

Three positions are at issue. A restricted globalist computes the inference only at the
speech-act level, and so cannot make *every student solved some but not all the problems* a
reading of *every student solved some of the problems*; a localist computes it in embedded
position and can; an unrestricted globalist derives the embedded-looking reading globally, but
only where it entails the literal reading. Experiment 1 embeds under a universal quantifier, where
that entailment holds, and separates the restricted globalist from the other two. Experiment 2
embeds under *exactly one*, where the local reading is logically independent of the literal one,
and separates the localist from both globalists: the condition where only the local reading is
true is rated far above the condition where none is, which an unrestricted globalist predicts to
be the same.

Rates are integer percentages or per-mille, as reported; the statistics stay in the paper.

## Main definitions

* `Theory`, `Theory.admits`, `GloballyDerivable` — the three positions, with the unrestricted
  globalist's reach a semantic condition: a reading is derivable iff it entails the literal one
* `RatingsMonotone` — the §3.2 conjecture, over (rating, reading-count) pairs
* `Exp1Condition`, `Exp2Condition`, with `witness`, `truthSet` and `availableAt` — the
  conditions, the readings their witness pictures make true, and what each theory leaves
  available there

## Main results

* `Exp1Some.local_globallyDerivable`, `Exp2Some.local_not_globallyDerivable` — under the
  universal the local reading entails the literal one; under *exactly one* it is independent
* `exp1_some_monotone_in_readings`, `exp1_or_monotone_in_readings` — ratings rise with the number
  of readings true, which subsumes the headline STRONG > WEAK contrast
* `T1_strong_eq_weak_under_availableReadings`, `T2_strong_strict_superset_weak`,
  `T2_T3_agree_in_exp1` — the restricted globalist predicts no Experiment 1 contrast, the other
  two predict the same one, so the first experiment separates only T1
* `T3_at_local_collapses_to_false`, `T2_at_local_strict_superset_false`, `T2_T3_disagree_at_local`,
  `local_gt_literal_some`, `local_gt_false_both_items` — the Experiment 2 separation
* `cs_gp_agree_on_de_local_far_below_baseline` — the two papers agree on downward-entailing
  contexts even where they disagree elsewhere
* `localReadingExistsExp1_isReinforceable` — the local reading passes the reinforceability
  diagnostic

## References

* [chemla-spector-2011]
* [geurts-pouscoulous-2009]
* [landman-1998]
* [chierchia-2004]
* [recanati-2003]
* [fox-2007]
* [chierchia-fox-spector-2008]
* [spector-2006]
* [vanrooij-schulz-2004]
* [sauerland-2004]
-/

namespace ChemlaSpector2011

-- ============================================================================
-- Shared types
-- ============================================================================

/-- The three readings the two experiments cross. Their entailment lattices differ between the
experiments, which is what the design exploits. -/
inductive ReadingLabel where
  | literal
  | global
  | local_
  deriving DecidableEq, Repr, Fintype

/-- The three theory families the paper distinguishes (§1, page 3).
Exp 1 separates T1 from {T2, T3}; Exp 2 separates T2 from {T1, T3}. -/
inductive Theory where
  | T1_restrictedGlobalist
  | T2_localist
  | T3_unrestrictedGlobalist
  deriving DecidableEq, Repr

/-! ### Theory mechanisms

What separates the theories is what their mechanisms can derive (§1, page 3 and footnote 1). The
restricted globalist computes the implicature only at the speech-act level, so it admits the
matrix readings. The localist computes it anywhere and admits everything. The unrestricted
globalist strengthens the matrix meaning, so a reading is within its reach exactly when it
entails the literal one — a semantic condition on the readings, not a switch set per environment.
The environment-dependence of its predictions falls out: under a universal the local reading
entails the literal one, under *exactly one* it does not. -/

section Mechanisms

variable {P : Type*} [Fintype P] (readings : ReadingLabel → P → Prop)
  [∀ ℓ p, Decidable (readings ℓ p)]

/-- A globalist derivation reaches a reading exactly when that reading entails the literal one:
strengthening the matrix meaning can never yield something the literal reading does not follow
from. -/
def GloballyDerivable (ℓ : ReadingLabel) : Prop :=
  ∀ p, readings ℓ p → readings .literal p

instance (ℓ : ReadingLabel) : Decidable (GloballyDerivable readings ℓ) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- The readings each theory's mechanism admits. -/
def Theory.admits : Theory → ReadingLabel → Prop
  | .T1_restrictedGlobalist, ℓ => ℓ = .literal ∨ ℓ = .global
  | .T2_localist, _ => True
  | .T3_unrestrictedGlobalist, ℓ => GloballyDerivable readings ℓ

instance : (t : Theory) → (ℓ : ReadingLabel) → Decidable (t.admits readings ℓ)
  | .T1_restrictedGlobalist, _ => inferInstanceAs (Decidable (_ ∨ _))
  | .T2_localist, _ => inferInstanceAs (Decidable True)
  | .T3_unrestrictedGlobalist, _ => inferInstanceAs (Decidable (GloballyDerivable _ _))

/-- The readings a theory leaves available at a picture: true there, and within the mechanism's
reach. Per the §3.2 conjecture, this set is what the rating reflects. -/
def availableAt (t : Theory) (p : P) : Finset ReadingLabel :=
  Finset.univ.filter fun ℓ => readings ℓ p ∧ t.admits readings ℓ

end Mechanisms

/-- The §3.2 page-10 conjecture: if at picture `p₂` strictly more of the
sentence's available readings are true than at `p₁`, then the rating
at `p₂` is higher than at `p₁`.

Stated over a list of `(rating, reading-count)` pairs ordered by reading-count, with ratings as
`Nat` percentages so the property is decidable. -/
abbrev RatingsMonotone (data : List (Nat × Nat)) : Prop :=
  data.Pairwise fun d₁ d₂ => d₁.2 < d₂.2 → d₁.1 < d₂.1


-- ============================================================================
-- §3 General features of the experimental design
-- ============================================================================

/-! ## §3 Experimental design

Pictures are letter-grids. Each letter is independently in one of three
states with respect to its circles: connected to none (a *falsifier*),
connected to some-but-not-all (a *strong verifier*), or connected to
all (a *weak verifier*) — paper §Appendix 2 / Figure 14, page 35.

The terminology *weak/strong verifier* is per the predicate "x is
connected with some of its circles" under literal vs strong "some":
- a letter with ALL circles connected makes the literal predicate true
  but the strong "some-but-not-all" predicate false → *weak* verifier
- a letter with SOME-BUT-NOT-ALL connected makes both predicates true
  → *strong* verifier

This mapping aligns with `SomeAllWorld`:
- `.none` = falsifier
- `.someNotAll` = strong verifier
- `.all` = weak verifier -/

/-- A 6-letter picture (Exp 1). Each letter is independently in one of
the three `SomeAllWorld` states with respect to its own set of
circles. -/
abbrev Picture6 := Fin 6 → SomeAllWorld

/-- A 3-letter picture (Exp 2). -/
abbrev Picture3 := Fin 3 → SomeAllWorld

-- ============================================================================
-- §4 Experiment 1 — scalar items in universal sentences
-- ============================================================================

section ExperimentOne

/-! ## §4 Experiment 1

Method (paper §4.1, page 12): 16 native French speakers, ages 19–29 (10
women), no formal-linguistics exposure. Continuous-scale rating task
(cursor 0–100%); responses coded as percent of red-line fill.

Target sentences:
- (8) *Chaque lettre est reliée à certains de ses cercles* — "Each
  letter is connected with some of its circles"
- (9) *Chaque lettre est reliée à son cercle rouge ou à son cercle
  bleu* — "Each letter is connected with its red circle or with its
  blue circle"

Three readings of (8) (paper (10), page 14):
- (10a) **Literal**: Each letter is connected with at least one of its
  circles
- (10b) **Global**: Literal AND ¬(each letter is connected with all its
  circles) — the matrix-level scalar implicature
- (10c) **Local**: Each letter is connected with some-but-not-all of
  its circles — the embedded scalar implicature

Total order: local ⊊ global ⊊ literal (page 5). Crucial for Exp 1's
discriminating logic.

Four target conditions (paper §4.2.1 page 14, Table 1 page 36):
- **FALSE**: 6 falsifiers (no reading true)
- **LITERAL**: 6 weak verifiers (only literal true)
- **WEAK**: 4 weak + 2 strong, or 2 weak + 4 strong (literal AND global true,
  local false)
- **STRONG**: 6 strong verifiers (all three readings true) -/

/-! ### Reading extensions for Exp 1 sentence (8)

Defined as `Prop` predicates over `Picture6`; `Decidable` instances
derive automatically since `Fin 6` is `Fintype` and `SomeAllWorld` is
`DecidableEq`. -/
namespace Exp1Some

/-- Literal (10a): every letter has ≥1 circle connected, i.e. no
falsifiers. Uses `abbrev` so the body unfolds for `decide` and instance
synthesis without explicit unfolds. -/
abbrev literal (p : Picture6) : Prop := ∀ i, p i ≠ .none

/-- Global (10b): literal AND there exists a letter that's not a weak
verifier (i.e., not connected with all its circles). -/
abbrev global (p : Picture6) : Prop := literal p ∧ ∃ i, p i ≠ .all

/-- Local (10c): every letter is a strong verifier. -/
abbrev local_ (p : Picture6) : Prop := ∀ i, p i = .someNotAll

/-- The labelled family of the three readings. -/
def reading : ReadingLabel → Picture6 → Prop
  | .literal => literal
  | .global => global
  | .local_ => local_

instance : (ℓ : ReadingLabel) → (p : Picture6) → Decidable (reading ℓ p)
  | .literal, p => inferInstanceAs (Decidable (literal p))
  | .global, p => inferInstanceAs (Decidable (global p))
  | .local_, p => inferInstanceAs (Decidable (local_ p))

/-- Under the universal the local reading entails the literal one — with the global reading
between them, the chain that keeps the unrestricted globalist abreast of the localist throughout
Experiment 1. -/
theorem local_globallyDerivable : GloballyDerivable reading .local_ :=
  fun p h i => by rw [h i]; simp

end Exp1Some

/-- The four target conditions for Exp 1 (paper §4.2.1 page 14). -/
inductive Exp1Condition where
  | false_      -- FALSE: no reading true
  | literal     -- LITERAL: only literal reading true
  | weak        -- WEAK: literal + global true, local false
  | strong      -- STRONG: all three readings true
  deriving DecidableEq, Repr

/-- Sample picture witnessing each Exp 1 condition. -/
def Exp1Condition.witness : Exp1Condition → Picture6
  | .false_   => fun _ => .none           -- 6 falsifiers
  | .literal  => fun _ => .all             -- 6 weak verifiers
  | .weak     => fun i => if i.val < 4 then .all else .someNotAll
                                            -- 4 weak + 2 strong
  | .strong   => fun _ => .someNotAll     -- 6 strong verifiers

/-- The readings true at a condition, read off its witness picture. The four conditions realize
the chain of Experiment 1: ∅, then {literal}, {literal, global}, and all three. -/
def Exp1Condition.truthSet (c : Exp1Condition) : Finset ReadingLabel :=
  Finset.univ.filter (Exp1Some.reading · c.witness)

/-! Experiment 1 main results (paper Figure 5, page 18, n = 16). Rates
are mean cursor positions in integer percent points, matching the
discipline of `GeurtsPouscoulous2009.lean` (which uses `Nat`
percentages for raw rates and `ℚ` for derived means). Per-condition
functions are defined by direct `match` so `decide` reduces in the
kernel. -/

/-- Mean rating of the 'some'-item universal sentence (8) per condition,
in percent points (paper Figure 5 page 18). -/
def exp1SomeRate : Exp1Condition → Nat
  | .false_  => 12
  | .literal => 44
  | .weak    => 68
  | .strong  => 99

/-- Mean rating of the 'or'-item universal sentence (9) per condition,
in percent points (paper Figure 5 page 18). -/
def exp1OrRate : Exp1Condition → Nat
  | .false_  => 11
  | .literal => 35
  | .weak    => 54
  | .strong  => 86

/-- Ratings rise with the number of readings true at the condition's witness picture — the
monotonicity conjecture of §3.2 on the Exp 1 *some* data, with the reading counts taken from
`Exp1Condition.truthSet` rather than written in. Since the counts are strictly ordered, this
subsumes the headline STRONG > WEAK contrast, a gap of 31 points for *some* and 32 for *or*. -/
theorem exp1_some_monotone_in_readings :
    RatingsMonotone
      [ (exp1SomeRate .false_,  (Exp1Condition.truthSet .false_).card)
      , (exp1SomeRate .literal, (Exp1Condition.truthSet .literal).card)
      , (exp1SomeRate .weak,    (Exp1Condition.truthSet .weak).card)
      , (exp1SomeRate .strong,  (Exp1Condition.truthSet .strong).card) ] := by decide

theorem exp1_or_monotone_in_readings :
    RatingsMonotone
      [ (exp1OrRate .false_,  (Exp1Condition.truthSet .false_).card)
      , (exp1OrRate .literal, (Exp1Condition.truthSet .literal).card)
      , (exp1OrRate .weak,    (Exp1Condition.truthSet .weak).card)
      , (exp1OrRate .strong,  (Exp1Condition.truthSet .strong).card) ] := by decide

/-- The restricted globalist leaves the same readings available at STRONG as at WEAK — local is
true at STRONG, but a matrix-only mechanism does not admit it — so it predicts equal ratings; the
observed 31- and 32-point gaps are the evidence against it. -/
theorem T1_strong_eq_weak_under_availableReadings :
    availableAt Exp1Some.reading .T1_restrictedGlobalist (Exp1Condition.witness .strong) =
      availableAt Exp1Some.reading .T1_restrictedGlobalist (Exp1Condition.witness .weak) := by
  decide

/-- The localist leaves strictly more available at STRONG than at WEAK, so with the §3.2
conjecture it predicts the gap. So does the unrestricted globalist here: under the universal the
local reading entails the literal one (`Exp1Some.local_globallyDerivable`), putting it within a
globalist derivation's reach — which is why Experiment 1 cannot separate them. -/
theorem T2_strong_strict_superset_weak :
    availableAt Exp1Some.reading .T2_localist (Exp1Condition.witness .weak) ⊂
      availableAt Exp1Some.reading .T2_localist (Exp1Condition.witness .strong) := by
  decide

/-- The two theories the first experiment cannot separate agree on every condition there. -/
theorem T2_T3_agree_in_exp1 (c : Exp1Condition) :
    availableAt Exp1Some.reading .T2_localist c.witness =
      availableAt Exp1Some.reading .T3_unrestrictedGlobalist c.witness := by
  cases c <;> decide +kernel

end ExperimentOne


-- ============================================================================
-- §4.2.2 / §5.3.2 DE controls — replication of GP09
-- ============================================================================

section DEControls

/-! ## DE controls

Paper §4.2.2 page 14 + §5.3.2 page 26: DE control sentences (12)/(13)
"Aucune lettre n'est reliée à certains de ses cercles" — "No letter is
connected with some of its circles" — were tested in three conditions:
- **FALSE**: no reading true
- **?LOCAL**: only the (marginal) local reading true
- **BOTH**: literal+local both true

Findings (Figure 6 page 19 / Figure 13 page 29):
- ?LOCAL ratings are LOW (much lower than BOTH), replicating
  [geurts-pouscoulous-2009]'s Exp 4 finding that local readings of
  *some* in DE contexts are not detected
- ?LOCAL is somewhat higher in Exp 2's DE controls than in Exp 1's
  (51%/22% vs 25%/14%) — paper §5.5.4 page 30 attributes this to
  paradigm-priming from the non-monotonic main task -/

/-- DE control conditions tested in Exp 1 (paper §4.2.2, page 14). -/
inductive DEControlCondition where
  | de_false_   -- FALSE: no reading true
  | de_qLocal   -- ?LOCAL: the marginal local reading true
  | de_both     -- BOTH: literal+local both true
  deriving DecidableEq, Repr

/-- DE control 'some' rates (paper Figure 6, page 19), per-mille. -/
def deControlsExp1Some : DEControlCondition → Nat
  | .de_false_  => 65   -- 6.5%
  | .de_qLocal  => 250  -- 25%
  | .de_both    => 920  -- 92%

/-- DE control 'or' rates (paper Figure 6, page 19), per-mille. -/
def deControlsExp1Or : DEControlCondition → Nat
  | .de_false_  => 90
  | .de_qLocal  => 140
  | .de_both    => 930

/-- Replicates [geurts-pouscoulous-2009]'s Exp 4 finding: in DE
contexts the ?LOCAL rate is far below the BOTH rate, supporting the
no-local-SI-in-DE generalization. -/
theorem de_qLocal_below_both :
    deControlsExp1Some .de_qLocal < deControlsExp1Some .de_both ∧
    deControlsExp1Or   .de_qLocal < deControlsExp1Or   .de_both := by decide

end DEControls


-- ============================================================================
-- §5 Experiment 2 — scalar items in non-monotonic environments
-- ============================================================================

section ExperimentTwo

/-! ## §5 Experiment 2 — the killer finding

Method (paper §5.2, page 26): 16 native French speakers, ages 18–35 (9
women), no prior formal-linguistics exposure. Same continuous-scale
task as Exp 1, with 3-letter grids replacing 6-letter grids.

Target sentences:
- (21) *Il y a exactement une lettre reliée à certains de ses cercles*
  — "There is exactly one letter connected with some of its circles"
- (22) *Il y a exactement une lettre reliée à son cercle rouge ou à
  son cercle bleu* — "There is exactly one letter connected with its
  red circle or with its blue circle"

Crucial: *exactly one* creates a **non-monotonic** environment where
the local reading is **logically independent** of the literal reading
(paper page 25):

- (19a) **Literal**: one letter is connected with some-or-all of its
  circles, the others with no circle
- (19b) **Global**: one letter is connected with some-but-not-all of
  its circles, the others with no circle
- (19c) **Local**: one letter is connected with some-but-not-all of
  its circles, the others may be connected with either none or all of
  their circles

Lattice (page 25): global ⊊ literal AND global ⊊ local; literal ⊥
local (logically independent). T1 cannot predict local; T3 (globalist
with multi-alternative negation) cannot predict local because the
local reading does not entail the literal reading. **Only T2
(localist) predicts local in non-monotonic environments.**

Four target conditions (paper §5.3.1 page 26):
- **FALSE**: no reading true
- **LITERAL**: only literal true
- **LOCAL**: only local true (literal AND global both false — this is
  the diagnostic condition)
- **ALL**: all three readings true -/

/-! ### Reading extensions for Exp 2 sentence (21)

Note the entailment lattice differs from Exp 1: literal and local are
logically independent here. The "exactly one" predicates use
`∃ i, P i ∧ ∀ j ≠ i, ¬ P j` spelled out explicitly so that
`Fintype.decidableForallFintype` and `Fintype.decidableExistsFintype`
derive `Decidable` automatically. -/
namespace Exp2Some

/-- Literal (19a): exactly one letter has ≥1 circle, others have none. -/
abbrev literal (p : Picture3) : Prop :=
  ∃ i, p i ≠ .none ∧ ∀ j, j ≠ i → p j = .none

/-- Global (19b): exactly one letter is a strong verifier, no letter is
a weak verifier (the speech-act SI on the *exactly one* sentence). -/
abbrev global (p : Picture3) : Prop :=
  (∃ i, p i = .someNotAll ∧ ∀ j, j ≠ i → p j = .none) ∧ ∀ i, p i ≠ .all

/-- Local (19c): exactly one letter is a strong verifier; the others
may be either falsifiers or weak verifiers. *Logically independent of
literal*: a configuration with one strong verifier and two weak
verifiers makes local true but literal false. -/
abbrev local_ (p : Picture3) : Prop :=
  ∃ i, p i = .someNotAll ∧ ∀ j, j ≠ i → p j ≠ .someNotAll

/-- The labelled family of the three readings. -/
def reading : ReadingLabel → Picture3 → Prop
  | .literal => literal
  | .global => global
  | .local_ => local_

instance : (ℓ : ReadingLabel) → (p : Picture3) → Decidable (reading ℓ p)
  | .literal, p => inferInstanceAs (Decidable (literal p))
  | .global, p => inferInstanceAs (Decidable (global p))
  | .local_, p => inferInstanceAs (Decidable (local_ p))

/-- Under *exactly one* the local reading no longer entails the literal one: one strong verifier
among weak verifiers makes it true while falsifying the literal reading. This is the logical
independence the second experiment exploits, and it puts the local reading beyond a globalist
derivation's reach. -/
theorem local_not_globallyDerivable : ¬ GloballyDerivable reading .local_ := by
  decide +kernel

end Exp2Some

/-- The four target conditions for Exp 2 (paper §5.3.1). -/
inductive Exp2Condition where
  | false_      -- no reading true
  | literal     -- only literal true
  | local_      -- only local true (the diagnostic condition for T2 vs T3)
  | all         -- all three readings true
  deriving DecidableEq, Repr

/-- Sample picture witnessing each Exp 2 condition. -/
def Exp2Condition.witness : Exp2Condition → Picture3
  | .false_  => fun _ => .none
  | .literal => fun i => if i.val = 0 then .all else .none
                            -- one weak verifier (= "all"), others none
  | .local_  => fun i =>
      if i.val = 0 then .someNotAll else .all
                            -- one strong verifier, others weak verifiers
                            -- → literal=F (others not none), local=T
  | .all     => fun i => if i.val = 0 then .someNotAll else .none
                            -- one strong, others none → literal=T, local=T,
                            -- global=T (because the one strong-verifier
                            -- letter satisfies the global pattern)

/-- The readings true at a condition, read off its witness picture. The four sets realize the
asymmetry of Experiment 2: at LOCAL the set is {local}, the literal reading being false there —
the pattern no chain of readings could produce. -/
def Exp2Condition.truthSet (c : Exp2Condition) : Finset ReadingLabel :=
  Finset.univ.filter (Exp2Some.reading · c.witness)

/-! Experiment 2 main results (paper Figure 12, page 28, n = 16),
per-mille `Nat`. -/

/-- Mean rating of the 'some'-item *exactly one* sentence (21) per
condition, per-mille (paper Figure 12 page 28). -/
def exp2SomeRate : Exp2Condition → Nat
  | .false_  => 67   -- 6.7%
  | .literal => 370  -- 37%
  | .local_  => 730  -- 73%
  | .all     => 980  -- 98%

/-- Mean rating of the 'or'-item *exactly one* sentence (22) per
condition, per-mille (paper Figure 12 page 28). -/
def exp2OrRate : Exp2Condition → Nat
  | .false_  => 91
  | .literal => 370
  | .local_  => 580
  | .all     => 900

/-- **The killer finding** (paper page 28): for the 'some' item under
*exactly one*, the LOCAL condition is rated *higher* than the LITERAL
condition (73% vs 37%). Globalist theories (T1, T3) cannot explain
this: in a non-monotonic environment the local reading is logically
independent of the literal reading, and globalist mechanisms cannot
derive readings that don't entail the literal. The fact that
participants rate LOCAL > LITERAL — *despite the literal reading being
false at LOCAL pictures* — is direct positive evidence for the existence
of an embedded local reading. -/
theorem local_gt_literal_some : exp2SomeRate .local_ > exp2SomeRate .literal := by decide

/-- Existence of the local reading in non-monotonic environments: for
both 'some' and 'or', LOCAL is rated far above FALSE (paper Figure
12). For 'or' the LITERAL > LOCAL contrast does not hold (37% vs 58%),
but LOCAL > FALSE holds. -/
theorem local_gt_false_both_items :
    exp2SomeRate .local_ > exp2SomeRate .false_ ∧
    exp2OrRate .local_ > exp2OrRate .false_ := by decide

/-- The unrestricted globalist collapses at the diagnostic condition: the one reading true at
LOCAL is beyond a globalist derivation's reach (`Exp2Some.local_not_globallyDerivable`), so its
available set there is empty, exactly as at FALSE — with the §3.2 conjecture, it predicts
LOCAL = FALSE, against the observed 73% versus 6.7%. -/
theorem T3_at_local_collapses_to_false :
    availableAt Exp2Some.reading .T3_unrestrictedGlobalist (Exp2Condition.witness .local_) =
      availableAt Exp2Some.reading .T3_unrestrictedGlobalist (Exp2Condition.witness .false_) := by
  decide +kernel

/-- The localist keeps the two apart: it admits the local reading, so LOCAL makes strictly more
available than FALSE, and it predicts the observed gap. -/
theorem T2_at_local_strict_superset_false :
    availableAt Exp2Some.reading .T2_localist (Exp2Condition.witness .false_) ⊂
      availableAt Exp2Some.reading .T2_localist (Exp2Condition.witness .local_) := by
  decide

/-- Where Experiment 1 could not separate the two theories, Experiment 2 does. -/
theorem T2_T3_disagree_at_local :
    availableAt Exp2Some.reading .T3_unrestrictedGlobalist (Exp2Condition.witness .local_) ≠
      availableAt Exp2Some.reading .T2_localist (Exp2Condition.witness .local_) := by
  decide +kernel

end ExperimentTwo


-- ============================================================================
-- §5.5.4 DE controls in Exp 2 (paradigm-priming finding)
-- ============================================================================

/-- DE control 'some' rates from Exp 2 (paper Figure 13, page 29),
per-mille. Higher ?LOCAL rates than in Exp 1 (51% vs 25%) — paper
§5.5.4 attributes to paradigm-priming from the non-monotonic main task
making local readings more accessible. -/
def deControlsExp2Some : DEControlCondition → Nat
  | .de_false_  => 33
  | .de_qLocal  => 510
  | .de_both    => 970

/-- DE control 'or' rates from Exp 2 (paper Figure 13, page 29),
per-mille. -/
def deControlsExp2Or : DEControlCondition → Nat
  | .de_false_  => 45
  | .de_qLocal  => 220
  | .de_both    => 950


-- ============================================================================
-- Cross-paper bridges
-- ============================================================================

section Bridges

/-! ## Bridges to GP09 and the Gricean diagnostics

Three connections to existing linglib content:

1. **GP09 paradigm comparison**: CS11 replicates GP09's no-local-SI-in-DE
   finding (in DE controls), but contests GP09's no-local-SI-anywhere
   conclusion via the universal-embedding STRONG > WEAK and the
   non-monotonic LOCAL > LITERAL findings. The disagreement is paradigm
   relative — GP09's binary inference task vs CS11's graded TVJ. We do
   not state "GP09 wrong / CS11 right"; we state the empirical
   complementarity and the methodological argument.
2. **Diagnostics**: the qualitative "embedded local reading exists"
   conclusion is submitted to the Gricean diagnostics over `Picture6`
   (Innocent Exclusion / localist EXH family —
   the [fox-2007] / [chierchia-fox-spector-2008] / T2 cluster).
3. **GP09 *exactly two* connection**: GP09's Exp 3 *exactly two*
   condition is the binary-task analog of CS11's Exp 2 *exactly one*.
   GP09 found ~50% inference rate (chance); CS11 finds 73% LOCAL
   rating. The paradigm shift recovers the localist signal. -/

open GeurtsPouscoulous2009

/-- A real cross-experiment claim: both papers find DE local-SI rates
*well below* their respective high baselines.
- CS11 Exp 1: `de_qLocal` (25% 'some') is far below `de_both` (92%)
- GP09 Exp 4: alleged-SI ambiguity (~6%) is far below genuine-ambiguity
  baseline (70% mean across 5 controls)

Both gaps exceed 50 percentage points; both papers' DE results
qualitatively agree even though their absolute rates differ
(paradigm-relative differences). -/
theorem cs_gp_agree_on_de_local_far_below_baseline :
    deControlsExp1Some .de_qLocal < deControlsExp1Some .de_both ∧
    deControlsExp1Or .de_qLocal < deControlsExp1Or .de_both ∧
    GeurtsPouscoulous2009.exp4NonDeConventionalistConsistent *
        (GeurtsPouscoulous2009.genuineAmbiguityRates.length * 100) <
      GeurtsPouscoulous2009.genuineAmbiguityRates.sum *
        GeurtsPouscoulous2009.exp4NonDeTotalResponses := by decide

/-- The local-reading SI is *reinforceable*: there's a picture (WEAK
condition) where the literal reading holds but the local reading
(`Exp1Some.local_`, the [fox-2007]-style localist EXH reading that T2
represents) fails. The `IsReinforceable` diagnostic (Sadock 1978) thus
applies to the (literal, local) pair. -/
theorem localReadingExistsExp1_isReinforceable :
    Implicature.IsReinforceable Exp1Some.literal Exp1Some.local_ := by
  refine ⟨Exp1Condition.witness .weak, ?_, ?_⟩
  · decide
  · show ¬ Exp1Some.local_ (Exp1Condition.witness .weak)
    decide

end Bridges


-- ============================================================================
-- §6 Conclusions
-- ============================================================================

/-! ## §6 Conclusions

The paper's verdict (page 31): "scalar items in non-monotonic
environments give rise to robust local readings, even more robust than
the literal reading. Importantly, no globalist theory of scalar
implicatures can predict the local reading to be possible in such
cases, where the local reading is logically independent of the literal
meaning. This result thus seems to vindicate the localist approach."

Methodological conclusion: graded judgments reveal ambiguities that
binary judgments mask; CS11 detected what GP09 missed. The
[geurts-pouscoulous-2009] null result is paradigm-relative, not a
fact about the language faculty.

Open questions noted by the paper itself (page 32):
- Which design feature(s) made local readings detectable — graded
  judgments? Better pictures? Inclusion of LOCAL-true conditions?
- Does the paradigm generalize to other ambiguities (scope, etc.)?
- Does this provide *decisive* evidence for grammaticalism, or could a
  localist *pragmatic* account (à la Recanati's free enrichment) do
  the work? -/

end ChemlaSpector2011
