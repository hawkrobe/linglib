import Linglib.Theories.Semantics.Conditionals.Counterfactual
import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Defs

/-!
# @cite{ciardelli-zhang-champollion-2018} — Two switches in the theory of counterfactuals

Ciardelli, I., Zhang, L. & Champollion, L. (2018). Two switches in the
theory of counterfactuals: A study of truth conditionality and minimal
change. *Linguistics and Philosophy* 41(6): 577–621.

## Headline finding

Two truth-conditionally equivalent clauses (`A̅ ∨ B̅` and `¬(A ∧ B)`,
related by De Morgan) make different semantic contributions when
embedded as counterfactual antecedents. This challenges the textbook
truth-conditional view of meaning AND falsifies any minimal-change
semantics of counterfactuals — including Lewis-Stalnaker similarity
semantics and Kratzer-style premise semantics.

## The switches scenario (p. 578, Fig. 1)

Two switches A, B at opposite ends of a hallway. The light is on iff
both switches are in the same position. Currently both are up, light is
on. The crowdsourced experiment elicited truth judgments for five
counterfactuals; the discriminating contrast (Tables 7–8, p. 607):

- **`A̅ > OFF`** ("If A were down, light would be off"): ~78% true
- **`B̅ > OFF`**:                                          ~76% true
- **`A̅ ∨ B̅ > OFF`**:                                     ~79% true
- **`¬(A ∧ B) > OFF`**:                                  ~20% true

`A̅ ∨ B̅` and `¬(A ∧ B)` are de-Morgan equivalent yet diverge sharply.

## What this file proves

1. **De Morgan equivalence**: `(A̅ ∨ B̅) = ¬(A ∧ B)` as sets of worlds.
2. **Concrete predictions across three operators**: instantiating a
   Hamming-distance similarity ordering at the actual world `uu`, all
   three closest-worlds operators in linglib —
   `universalCounterfactual` (Lewis/Stalnaker), `selectionalCounterfactual`
   (Stalnaker + supervaluation, returns `Truth3.true`), and
   `homogeneityCounterfactual` (von Fintel/Križ, returns `assertion =
   some true` with satisfied presupposition) — all predict `¬(A ∧ B) >
   OFF` true. This is the empirically falsified prediction (~20% true,
   Tables 7–8).
3. **Generic structural argument** (CZC §1.2 argument, p. 582):
   the operator-agnostic core
   (`closestWorlds_predicate_forces_notBothUp`) shows that for ANY
   similarity ordering and ANY consequent `B`, joint truth of "every
   closest aDn-world is B" and "every closest bDn-world is B" entails
   "every closest notBothUp-world is B". Three corollaries instantiate
   this for `universalCounterfactual`,  `selectionalCounterfactual`,
   and `homogeneityCounterfactual` — closing CZC's claim that *all*
   minimal-change theories fail.

## Connection to linglib's Kratzer infrastructure

@cite{ciardelli-zhang-champollion-2018} §6.3 extends the argument to
*standard premise semantics* as formulated in @cite{kratzer-1981} (CZC
cite both Kratzer 1981a and 1981b — only the 1981 "Notional Category"
paper is in the linglib bib): "regardless of the particular ordering
source that
we consider, standard premise semantics still predicts that ... `¬(A ∧ B)
> OFF` is true as well, contrary to our experimental findings." Per
Lewis 1981, standard premise semantics is equivalent to ordering
semantics with a weak partial order, which puts it in scope of the §1.2
argument formalized above.

**Whether the argument extends to @cite{kratzer-2012}'s lumping-based
revision (§5.4.4) is open and not addressed by CZC.** The lumping CF
truth condition (§5.4.4) is a quantifier alternation — "for every set
in F_{w,p} there is a superset that implies q" — *not* the
maximization-of-consistency pattern that the §1.2 argument falsifies.
Lumping constrains *which* propositions can accompany an antecedent
into a Crucial Set (the lumping-closure condition); it doesn't relax
the for-all-supersets quantifier. Whether this rescues the analysis on
the switches scenario requires building a properly situation-semantic
switches model and instantiating
`Semantics.Conditionals.PremiseSemantic.wouldCF`; we leave this as
future work.

For the first concrete `wouldCF` instantiation on a situation-semantic
scenario, see
`Phenomena.Conditionals.Studies.Kratzer2012Lumping` — which
formalizes Kratzer's own apple-buying example (§5.4.1–§5.4.3). That
file establishes the template for an eventual situation-semantic
switches model that would settle the question raised here.

The CZC positive proposal — a foreground/background distinction
combined with inquisitive lifting (§4) — and §6.4's SNCA derivation
(Proposition 2 + Lemma 1) are also left as future formalization.
-/

namespace Phenomena.Conditionals.Studies.CiardelliZhangChampollion2018

open Core.Order (SimilarityOrdering)
open Semantics.Conditionals.Counterfactual
  (universalCounterfactual selectionalCounterfactual homogeneityCounterfactual
   PresupStatus PresupResult)
open Core.Duality (Truth3)

/-! ## The switches scenario -/

/-- The four worlds, indexed by (A-position, B-position).
    Naming: `u` = up, `d` = down. So `uu` = both up, etc. -/
inductive World where
  /-- A up, B up — the actual world; light is ON. -/
  | uu
  /-- A up, B down — light is OFF. -/
  | ud
  /-- A down, B up — light is OFF. -/
  | du
  /-- A down, B down — light is ON. -/
  | dd
  deriving Repr, DecidableEq, Fintype

/-- Atomic propositions: switch positions and the light. -/
def aUp : World → Prop | .uu | .ud => True | .du | .dd => False
def bUp : World → Prop | .uu | .du => True | .ud | .dd => False

/-- The wiring law (@cite{ciardelli-zhang-champollion-2018}, p. 578):
    light is on iff both switches are in the same position. -/
def lightOn : World → Prop | .uu | .dd => True | .ud | .du => False

/-! ### Antecedents and consequents

We follow the paper's notation: `A̅` (`aDn`) means "switch A is down"
and so on. The two key antecedents — `A̅ ∨ B̅` (`aOrBdn`) and
`¬(A ∧ B)` (`notBothUp`) — are de-Morgan equivalent. -/

/-- "Switch A is down." -/
def aDn (w : World) : Prop := ¬ aUp w
/-- "Switch B is down." -/
def bDn (w : World) : Prop := ¬ bUp w
/-- "Switch A is down or switch B is down." -/
def aOrBdn (w : World) : Prop := aDn w ∨ bDn w
/-- "Switches A and B are not both up" (= `¬(A ∧ B)`). -/
def notBothUp (w : World) : Prop := ¬ (aUp w ∧ bUp w)
/-- "The light is off." -/
def lightOff (w : World) : Prop := ¬ lightOn w

instance : DecidablePred aUp := fun w => by cases w <;> simp only [aUp] <;> infer_instance
instance : DecidablePred bUp := fun w => by cases w <;> simp only [bUp] <;> infer_instance
instance : DecidablePred lightOn := fun w => by cases w <;> simp only [lightOn] <;> infer_instance
instance : DecidablePred aDn := fun _ => inferInstanceAs (Decidable (¬ _))
instance : DecidablePred bDn := fun _ => inferInstanceAs (Decidable (¬ _))
instance : DecidablePred aOrBdn := fun _ => inferInstanceAs (Decidable (_ ∨ _))
instance : DecidablePred notBothUp := fun _ => inferInstanceAs (Decidable (¬ _))
instance : DecidablePred lightOff := fun _ => inferInstanceAs (Decidable (¬ _))

/-! ## De Morgan equivalence -/

/-- `A̅ ∨ B̅` and `¬(A ∧ B)` are pointwise-equivalent: the two antecedents
    have identical truth conditions across the four worlds. -/
theorem aOrBdn_iff_notBothUp (w : World) : aOrBdn w ↔ notBothUp w := by
  cases w <;> decide

/-- The same equivalence as set equality (the truth-conditional content
    of the two antecedents coincides). -/
theorem aOrBdn_eq_notBothUp : aOrBdn = notBothUp := by
  funext w
  exact propext (aOrBdn_iff_notBothUp w)

/-! ## Concrete similarity ordering: Hamming distance -/

/-- Hamming distance between two worlds: the number of switch positions
    on which they disagree. -/
def hamming : World → World → Nat
  | .uu, .uu | .ud, .ud | .du, .du | .dd, .dd => 0
  | .uu, .ud | .ud, .uu | .du, .dd | .dd, .du => 1
  | .uu, .du | .du, .uu | .ud, .dd | .dd, .ud => 1
  | .uu, .dd | .dd, .uu => 2
  | .ud, .du | .du, .ud => 2

/-- Standard "edit distance" similarity ordering: `w₁` is at least as
    close to `w₀` as `w₂` is iff `hamming w₀ w₁ ≤ hamming w₀ w₂`. This
    is one natural ordering on this scenario; the abstract theorem
    below shows the falsification doesn't depend on this choice. -/
def hammingSim : SimilarityOrdering World where
  closer w₀ w₁ w₂ := hamming w₀ w₁ ≤ hamming w₀ w₂
  closer_refl _ _ := Nat.le_refl _
  closer_trans _ _ _ _ h₁ h₂ := h₁.trans h₂
  closerDec _ _ _ := Nat.decLe _ _

/-! ## Predictions of the universal/Lewis-Stalnaker counterfactual -/

/-- **Prediction 1**: `A̅ > OFF` is true at `uu`. (The closest A̅-world
    to `uu` is `du` — Hamming distance 1 — and the light is off there.)
    Empirically: ~78% true. -/
theorem aDn_off_at_uu :
    universalCounterfactual hammingSim aDn lightOff .uu := by decide

/-- **Prediction 2**: `B̅ > OFF` is true at `uu`. By the symmetric
    argument. Empirically: ~76% true. -/
theorem bDn_off_at_uu :
    universalCounterfactual hammingSim bDn lightOff .uu := by decide

/-- **Prediction 3**: `A̅ ∨ B̅ > OFF` is true at `uu`. The closest
    A̅ ∨ B̅-worlds are `{ud, du}` (both at Hamming distance 1), and the
    light is off in both. Empirically: ~79% true. -/
theorem aOrBdn_off_at_uu :
    universalCounterfactual hammingSim aOrBdn lightOff .uu := by decide

/-- **Prediction 4 (the falsified one)**: `¬(A ∧ B) > OFF` is *also*
    predicted true at `uu`, since `¬(A ∧ B)` and `A̅ ∨ B̅` are
    de-Morgan equivalent. **Empirically: only ~20% true.**

    This is the central empirical contrast of
    @cite{ciardelli-zhang-champollion-2018}: a truth-conditional
    semantics combined with minimal change cannot reproduce the sharp
    divergence between the two predictions, since the two antecedents
    are forced to behave identically. -/
theorem notBothUp_off_at_uu :
    universalCounterfactual hammingSim notBothUp lightOff .uu := by decide

/-! ### Same falsified prediction under selectional and homogeneity

@cite{ciardelli-zhang-champollion-2018}'s argument targets *any*
minimal-change semantics. Both `selectionalCounterfactual` (Stalnaker
+ supervaluation) and `homogeneityCounterfactual` (von Fintel/Križ)
share the same closest-worlds substrate as `universalCounterfactual`,
and so make the same falsified prediction on the switches scenario. -/

/-- **Selectional CF** also predicts `¬(A ∧ B) > OFF` true at `uu`. -/
theorem selectional_notBothUp_off_at_uu :
    selectionalCounterfactual hammingSim notBothUp lightOff .uu = .true := by
  decide

/-- **Homogeneity CF** also predicts `¬(A ∧ B) > OFF` true at `uu`,
    with satisfied presupposition (the closest worlds are not mixed
    on `lightOff`). -/
theorem homogeneity_notBothUp_off_at_uu :
    homogeneityCounterfactual hammingSim notBothUp lightOff .uu =
      { presupposition := .satisfied, assertion := some true } := by
  decide

/-! ## Abstract minimal-change forcing (@cite{ciardelli-zhang-champollion-2018} §1.2, p. 582)

The concrete predictions above used a specific similarity ordering. The
following theorem strengthens the argument: for *any* similarity
ordering whatsoever, if both `A̅ > OFF` and `B̅ > OFF` are true at a
world, then `¬(A ∧ B) > OFF` is forced true at that world. So there is
no choice of similarity that vindicates the empirical pattern — the
fault lies with the minimal-change architecture itself. -/

/-! ### The generic structural argument

CZC's §1.2 proof actually targets *any* operator definable as
"every closest A-world satisfies B". We expose the generic version
first; the universal/selectional/homogeneity instantiations below all
collapse to it. -/

/-- **Generic minimal-change forcing**: for any similarity ordering and
    any consequent predicate `B`, joint truth of "every closest aDn-world
    is B" and "every closest bDn-world is B" entails "every closest
    notBothUp-world is B".

    This is the operator-agnostic core of CZC §1.2 p. 582. The structural
    fact is `SimilarityOrdering.mem_closestWorlds_of_subset`: a closest
    `notBothUp`-world that happens to be `aDn` is also a closest
    `aDn`-world (since `aDn ⊆ notBothUp` as Finsets), so `h_a` applies;
    symmetric for `bDn`. -/
theorem closestWorlds_predicate_forces_notBothUp
    (sim : SimilarityOrdering World) (w₀ : World)
    (B : World → Prop) [DecidablePred B]
    (h_a : ∀ w' ∈ sim.closestWorlds w₀ (Finset.univ.filter aDn), B w')
    (h_b : ∀ w' ∈ sim.closestWorlds w₀ (Finset.univ.filter bDn), B w') :
    ∀ w' ∈ sim.closestWorlds w₀ (Finset.univ.filter notBothUp), B w' := by
  intro w hw
  have hwNAB : notBothUp w := (Finset.mem_filter.mp
    ((SimilarityOrdering.mem_closestWorlds _ _ _ _).mp hw).1).2
  have h_aDn_sub : Finset.univ.filter aDn ⊆ Finset.univ.filter notBothUp := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, fun ⟨hA, _⟩ => hx.2 hA⟩
  have h_bDn_sub : Finset.univ.filter bDn ⊆ Finset.univ.filter notBothUp := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, fun ⟨_, hB⟩ => hx.2 hB⟩
  by_cases hwA : aDn w
  · exact h_a w (sim.mem_closestWorlds_of_subset h_aDn_sub hw
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwA⟩))
  · have hwB : bDn w := fun hbU =>
      hwNAB ⟨by by_contra hnA; exact hwA hnA, hbU⟩
    exact h_b w (sim.mem_closestWorlds_of_subset h_bDn_sub hw
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwB⟩))

/-! ### Operator-specific corollaries

All three of `universalCounterfactual`, `selectionalCounterfactual`,
and `homogeneityCounterfactual` reduce their "true" verdict to the
same `∀ w' ∈ closestWorlds, B w'` condition (the first `if` branch in
each definition). The structural lemma above therefore applies
verbatim, only differing in how each operator packages its truth value. -/

/-- **Universal CF version** (Lewis/Stalnaker). Direct corollary of the
    generic lemma since `universalCounterfactual` *is* the universal
    quantifier over closest worlds. -/
theorem minimal_change_forces_notBothUp_off
    (sim : SimilarityOrdering World) (w₀ : World)
    (h_a : universalCounterfactual sim aDn lightOff w₀)
    (h_b : universalCounterfactual sim bDn lightOff w₀) :
    universalCounterfactual sim notBothUp lightOff w₀ :=
  closestWorlds_predicate_forces_notBothUp sim w₀ lightOff h_a h_b

/-- The "true"-verdict condition for `selectionalCounterfactual` is
    exactly the closest-worlds universal quantifier (the first `if`
    branch in its definition). -/
private theorem selectional_eq_true_iff
    (sim : SimilarityOrdering World) (A B : World → Prop)
    [DecidablePred A] [DecidablePred B] (w : World) :
    selectionalCounterfactual sim A B w = .true ↔
      ∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A), B w' := by
  unfold selectionalCounterfactual
  constructor
  · intro heq
    by_contra h_neg
    rw [if_neg h_neg] at heq
    split_ifs at heq
  · intro h
    rw [if_pos h]

/-- The "true"-verdict condition for `homogeneityCounterfactual` is
    likewise the closest-worlds universal quantifier. -/
private theorem homogeneity_eq_true_iff
    (sim : SimilarityOrdering World) (A B : World → Prop)
    [DecidablePred A] [DecidablePred B] (w : World) :
    homogeneityCounterfactual sim A B w =
        { presupposition := .satisfied, assertion := some true } ↔
      ∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A), B w' := by
  unfold homogeneityCounterfactual
  constructor
  · intro heq
    by_contra h_neg
    rw [if_neg h_neg] at heq
    split_ifs at heq <;> injection heq with h1 h2 <;> cases h2
  · intro h
    rw [if_pos h]

/-- **Selectional CF version** (Stalnaker + supervaluation). When both
    simple counterfactuals return `.true` (every closest world is OFF),
    so does the disjunctive-antecedent counterfactual. -/
theorem selectional_minimal_change_forces_notBothUp_off
    (sim : SimilarityOrdering World) (w₀ : World)
    (h_a : selectionalCounterfactual sim aDn lightOff w₀ = .true)
    (h_b : selectionalCounterfactual sim bDn lightOff w₀ = .true) :
    selectionalCounterfactual sim notBothUp lightOff w₀ = .true :=
  (selectional_eq_true_iff sim notBothUp lightOff w₀).mpr
    (closestWorlds_predicate_forces_notBothUp sim w₀ lightOff
      ((selectional_eq_true_iff sim aDn lightOff w₀).mp h_a)
      ((selectional_eq_true_iff sim bDn lightOff w₀).mp h_b))

/-- **Homogeneity CF version** (von Fintel/Križ). When both simple
    counterfactuals satisfy their presupposition with `assertion = some
    true` (every closest world is OFF), so does the disjunctive-
    antecedent version. -/
theorem homogeneity_minimal_change_forces_notBothUp_off
    (sim : SimilarityOrdering World) (w₀ : World)
    (h_a : homogeneityCounterfactual sim aDn lightOff w₀ =
      { presupposition := .satisfied, assertion := some true })
    (h_b : homogeneityCounterfactual sim bDn lightOff w₀ =
      { presupposition := .satisfied, assertion := some true }) :
    homogeneityCounterfactual sim notBothUp lightOff w₀ =
      { presupposition := .satisfied, assertion := some true } :=
  (homogeneity_eq_true_iff sim notBothUp lightOff w₀).mpr
    (closestWorlds_predicate_forces_notBothUp sim w₀ lightOff
      ((homogeneity_eq_true_iff sim aDn lightOff w₀).mp h_a)
      ((homogeneity_eq_true_iff sim bDn lightOff w₀).mp h_b))

/-! ## Empirical data (Tables 7 and 8, p. 607)

The "True" percentages from the main experiment, separated by
presentation order. Reported as rationals for exact comparison. -/

/-- Table 7: target precedes filler. -/
def percentTrue_aDn_off_T7        : Rat := 80 / 100
def percentTrue_bDn_off_T7        : Rat := 76 / 100
def percentTrue_aOrBdn_off_T7     : Rat := 79 / 100
def percentTrue_notBothUp_off_T7  : Rat := 20 / 100

/-- Table 8: filler precedes target. -/
def percentTrue_aDn_off_T8        : Rat := 53 / 100
def percentTrue_bDn_off_T8        : Rat := 53 / 100
def percentTrue_aOrBdn_off_T8     : Rat := 59 / 100
def percentTrue_notBothUp_off_T8  : Rat := 25 / 100

/-- The discriminating empirical contrast (Table 7, p. 607): the two
    de-Morgan-equivalent antecedents `A̅ ∨ B̅` and `¬(A ∧ B)` produce
    sharply divergent truth-judgment rates when embedded as counterfactual
    antecedents. -/
theorem deMorgan_antecedents_diverge_T7 :
    percentTrue_aOrBdn_off_T7 - percentTrue_notBothUp_off_T7 ≥ 1 / 2 := by
  unfold percentTrue_aOrBdn_off_T7 percentTrue_notBothUp_off_T7
  norm_num

/-- The simple antecedents `A̅ > OFF` and `B̅ > OFF` are robustly judged
    true while `¬(A ∧ B) > OFF` is robustly judged not-true (Table 7).
    This is the contrast that the abstract minimal-change forcing
    theorem rules out for any similarity ordering. -/
theorem prediction_pattern_falsified_T7 :
    percentTrue_aDn_off_T7 ≥ 3 / 4 ∧
    percentTrue_bDn_off_T7 ≥ 3 / 4 ∧
    percentTrue_notBothUp_off_T7 ≤ 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold percentTrue_aDn_off_T7; norm_num
  · unfold percentTrue_bDn_off_T7; norm_num
  · unfold percentTrue_notBothUp_off_T7; norm_num

end Phenomena.Conditionals.Studies.CiardelliZhangChampollion2018
