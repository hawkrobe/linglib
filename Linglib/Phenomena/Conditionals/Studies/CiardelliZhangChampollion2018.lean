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
2. **Concrete prediction**: instantiating a Hamming-distance similarity
   ordering at the actual world `uu`, the existing
   `Conditionals.universalCounterfactual` (Lewis/Stalnaker/Kratzer-style
   minimal-change CF) predicts ALL THREE — `A̅ > OFF`, `B̅ > OFF`, *and*
   `¬(A ∧ B) > OFF`. The third is the empirically falsified one.
3. **Abstract minimal-change forcing** (CZC §1.2 argument, p. 582):
   for ANY similarity ordering, if both `A̅ > OFF` and `B̅ > OFF` are
   true at the actual world, then `¬(A ∧ B) > OFF` is forced true. So
   no choice of similarity ordering rescues the universal/Lewis/
   Stalnaker semantics.

## Connection to linglib's Kratzer infrastructure

@cite{ciardelli-zhang-champollion-2018} §6.3 explicitly extends the
argument to Kratzer-style premise semantics: "regardless of the
particular ordering source that we consider, standard premise semantics
still predicts that ... `¬(A ∧ B) > OFF` is true as well, contrary to
our experimental findings." This applies to @cite{kratzer-2012}'s
lumping-based revision (foundation in
`Theories/Semantics/Conditionals/Kratzer/Lumping.lean`) because lumping
augments premise sets without relaxing the maximization-of-consistency
requirement that drives the wrong prediction.

The CZC alternative — a foreground/background distinction combined
with inquisitive lifting (§4) — is left as future formalization. It
would replace minimal change with a binary distinction between facts
that are at stake (foregrounded) and facts that are held fixed
(backgrounded).
-/

namespace Phenomena.Conditionals.Studies.CiardelliZhangChampollion2018

open Semantics.Conditionals (SimilarityOrdering)
open Semantics.Conditionals.Counterfactual (universalCounterfactual)

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

instance : DecidablePred aUp := fun w => by cases w <;> simp [aUp] <;> infer_instance
instance : DecidablePred bUp := fun w => by cases w <;> simp [bUp] <;> infer_instance
instance : DecidablePred lightOn := fun w => by cases w <;> simp [lightOn] <;> infer_instance
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

/-! ## Abstract minimal-change forcing (@cite{ciardelli-zhang-champollion-2018} §1.2, p. 582)

The concrete predictions above used a specific similarity ordering. The
following theorem strengthens the argument: for *any* similarity
ordering whatsoever, if both `A̅ > OFF` and `B̅ > OFF` are true at a
world, then `¬(A ∧ B) > OFF` is forced true at that world. So there is
no choice of similarity that vindicates the empirical pattern — the
fault lies with the minimal-change architecture itself. -/

private theorem aDn_imp_notBothUp (w : World) (h : aDn w) : notBothUp w :=
  fun ⟨hA, _⟩ => h hA

private theorem bDn_imp_notBothUp (w : World) (h : bDn w) : notBothUp w :=
  fun ⟨_, hB⟩ => h hB

/-- The structural lemma underlying CZC's argument: if `w` is a closest
    `S`-world and `w` belongs to a sub-property `T ⊆ S`, then `w` is also
    a closest `T`-world. (Adding more competitors can only make `w` lose
    its "closest" status, not gain it.) -/
private theorem closestWorlds_inherits {S T : World → Prop}
    [DecidablePred S] [DecidablePred T]
    (sim : SimilarityOrdering World) (w₀ w : World)
    (hST : ∀ x, T x → S x)
    (hw : w ∈ sim.closestWorlds w₀ (Finset.univ.filter S))
    (hwT : T w) :
    w ∈ sim.closestWorlds w₀ (Finset.univ.filter T) := by
  rw [SimilarityOrdering.mem_closestWorlds] at hw ⊢
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwT⟩, ?_⟩
  intro w'' hw''
  rw [Finset.mem_filter] at hw''
  exact hw.2 w'' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hST w'' hw''.2⟩)

/-- **Minimal-change forcing** (the abstract version of CZC's central
    argument, p. 582): for any similarity ordering, joint truth of
    `A̅ > OFF` and `B̅ > OFF` at a world entails truth of `¬(A ∧ B) > OFF`
    at that world.

    Combined with the empirical data (Tables 7–8) — `A̅ > OFF` ~78% true,
    `¬(A ∧ B) > OFF` ~20% true — this theorem shows that no
    minimal-change account can fit the observed pattern. The formal
    contrapositive: if `¬(A ∧ B) > OFF` is *false* (the majority
    judgment), then at least one of `A̅ > OFF`, `B̅ > OFF` is also false
    — but both are robustly judged true. -/
theorem minimal_change_forces_notBothUp_off
    (sim : SimilarityOrdering World) (w₀ : World)
    (h_a : universalCounterfactual sim aDn lightOff w₀)
    (h_b : universalCounterfactual sim bDn lightOff w₀) :
    universalCounterfactual sim notBothUp lightOff w₀ := by
  intro w hw
  have hw' := hw
  rw [SimilarityOrdering.mem_closestWorlds, Finset.mem_filter] at hw'
  obtain ⟨⟨_, hwNAB⟩, _⟩ := hw'
  -- `notBothUp w` decidably splits into `aDn w ∨ bDn w`.
  by_cases hwA : aDn w
  · exact h_a w (closestWorlds_inherits sim w₀ w aDn_imp_notBothUp hw hwA)
  · have hwB : bDn w := by
      intro hbU; exact hwNAB ⟨by by_contra hnA; exact hwA hnA, hbU⟩
    exact h_b w (closestWorlds_inherits sim w₀ w bDn_imp_notBothUp hw hwB)

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
