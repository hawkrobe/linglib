import Linglib.Semantics.Attitudes.Desire.ExpectedValue
import Linglib.Semantics.Attitudes.Desire.Preferential
import Linglib.Semantics.Attitudes.Desire.Conditional
import Mathlib.Algebra.BigOperators.Fin

/-!
# [lassiter-2017] (apparatus) / [lassiter-2011] (want application) — Expected-value desire

[lassiter-2017] ch.7 ("Scalar goodness", *not* a desire chapter)
develops an expected-value semantics for evaluative gradable predicates;
[lassiter-2011] (NYU dissertation, ch.6) applies the apparatus to
*want*. The book extends the *good* analysis to *want* in a single
sentence at §8.13 (p.249) — *want* is gradable like *like, matter,
care, need*.

This study file:

* §1 builds the **bare-threshold conflict-witness model** (4 worlds,
  uniform prior 1/4, V = (10, 4, 4, 0), θ = 3/2, `p = {w₀, w₁}`).
* §2 replicates the conflict predictions: `want_p ∧ want_negp`.
* §3 cross-paper bridge to [condoravdi-lauer-2016]: C&L's
  consistency-driven belief-compatibility forbids the witness; the
  Lassiter bare apparatus exhibits it. **Different mechanisms.**
* §4 cross-paper bridge to [heim-1992]: same configuration is
  `Conditional.Defined`-OK, but `Conditional.Want.not_compl`
  rules out joint truth. **Heim's (40) amendment is the structural
  analog of Lassiter's Sloman.**
* §5 **Sloman's Principle blocks the witness** for Lassiter's *full*
  account. The bare-threshold conflict witness is exactly Cariani's
  Weakening counter-model (Lassiter's Table 8.4 reconstruction of
  the [cariani-2016] actualist Weakening attack, applied to EV;
  Cariani's own counter-model uses actualist closeness, not EV)
  p.239); Lassiter's response is Sloman's Principle, which excludes
  it. The witness is a falsifier of the *bare* form, not of
  Lassiter's actual position.

The chronological-dependency rule applies: this file references
[phillips-brown-2025] only in docstring prose (PB is later);
PhillipsBrown2025.lean already cross-references Lassiter via its
`BeliefBasedDesireSemantics` typology (the paper's own §2 packaging,
formalized in that study file).
-/

namespace Lassiter2017Desire

open Desire Desire.ExpectedValue Core.DecisionTheory

/-! ## §1. The 4-world conflict-witness model

Following [lassiter-2017] §7.6 eq. 7.22 (apparatus) and
[lassiter-2011] ch.6 (*want* application). Uniform prior over
`Fin 4`; value function asymmetric on `{w₀, w₁}` vs `{w₂, w₃}`. -/

/-- Worlds. -/
abbrev W : Type := Fin 4

/-- Uniform prior 1/4 over the 4 worlds. -/
def prior : W → ℚ := fun _ => 1/4

/-- Value function: `V(w₀) = 10`, `V(w₁) = 4`, `V(w₂) = 4`, `V(w₃) = 0`. -/
def value : W → ℚ := fun w =>
  match w with
  | 0 => 10
  | 1 => 4
  | 2 => 4
  | 3 => 0

/-- Threshold for "significantly above neutral" — Lassiter 2017 §7.9
    treats this as contextually supplied. -/
def threshold : ℚ := 3/2

/-- The agent's belief state: total uncertainty (all worlds compatible).
    Matches Lassiter's `D = epistemically possible worlds` convention
    (§7.6 p.187). -/
def belTotal : Set W := Set.univ
instance : DecidablePred (· ∈ belTotal) := fun _ => isTrue trivial

/-- The target proposition `p = {w₀, w₁}`. -/
def targetProp : Set W := {0, 1}
instance : DecidablePred (· ∈ targetProp) :=
  fun w => inferInstanceAs (Decidable (w ∈ ({0, 1} : Set W)))

/-! ## §2. The conflict predictions

`E_V(p | belS) = (1/4 · 10 + 1/4 · 4) / (1/4 + 1/4) = (14/4) / (1/2) = 7`
`E_V(¬p | belS) = (1/4 · 4 + 1/4 · 0) / (1/4 + 1/4) = 1 / (1/2) = 2`
With θ = 3/2, both are above threshold → both are wanted. -/

theorem cell_targetProp : cell belTotal targetProp = {0, 1} := by decide

theorem cell_targetProp_compl : cell belTotal targetPropᶜ = {2, 3} := by decide

theorem want_p : Want prior value threshold belTotal targetProp := by
  have h : HasPositiveBeliefMass prior belTotal targetProp := by
    simp only [HasPositiveBeliefMass, cell_targetProp]; norm_num [prior]
  simp only [Want, expectedValue_eq h, cell_targetProp, threshold]
  norm_num [prior, value]

theorem want_negp : Want prior value threshold belTotal targetPropᶜ := by
  have h : HasPositiveBeliefMass prior belTotal targetPropᶜ := by
    simp only [HasPositiveBeliefMass, cell_targetProp_compl]; norm_num [prior]
  simp only [Want, expectedValue_eq h, cell_targetProp_compl, threshold]
  norm_num [prior, value, Finset.sum_pair (show (2 : W) ≠ 3 by decide)]

theorem conflict_concrete :
    Want prior value threshold belTotal targetProp ∧
      Want prior value threshold belTotal targetPropᶜ :=
  ⟨want_p, want_negp⟩

/-! ## §3. Cross-paper bridge: [condoravdi-lauer-2016]

C&L's `PreferenceStructure.maxElts_pair_belief_compatible` says that
for any preferential background `P` pointwise consistent with the
belief state, `Preferential.Want P a φ w ∧ Preferential.Want P a ψ w`
implies `(φ ∩ ψ) ∩ B(a, w) ≠ ∅`.
Specialized to `ψ = φᶜ`: the intersection is empty, so simultaneous
truth is impossible.

Lassiter's bare-threshold apparatus exhibits exactly such a
configuration. The two frameworks make orthogonal predictions on the
4-world model. -/

/-- C&L blocks any pair `Want φ ∧ Want ¬φ` over a
    consistent background — C&L cannot reproduce Lassiter's witness. -/
theorem condoravdiLauer_blocks_lassiter_witness
    {Agent : Type} {B : Agent → W → Set W}
    (P : Agent → W → PreferenceStructure W)
    (hC : ∀ a w, (P a w).consistent (B a w))
    (a : Agent) (w : W) (φ : Set W)
    (hφ : Preferential.Want P a φ w) (hnegφ : Preferential.Want P a φᶜ w) : False :=
  (P a w).maxElts_pair_belief_compatible (hC a w) hφ hnegφ (by simp)

/-! ## §4. Cross-paper bridge: [heim-1992]

Heim's (40) amendment + comparative-belief semantics block simultaneous
`want p ∧ want ¬p` (substrate's `Conditional.Want.not_compl`). The 4-world
conflict witness configuration is `Conditional.Defined`-OK on `targetProp` (both p-worlds
and ¬p-worlds are in `belTotal`), so Heim's no-go applies — and Heim's
prediction differs from Lassiter's.

This is the analog: Heim's (40) plays the role for comparative-belief
that Sloman plays for Lassiter — both block single-V/single-context
conflict. -/

theorem defined_on_witness : Conditional.Defined belTotal targetProp :=
  ⟨⟨0, trivial, by decide⟩, ⟨2, trivial, by decide⟩⟩

/-- On the witness configuration, Heim's no-go theorem applies — for any frame with
    antisymmetric desirability, `want` cannot make both `targetProp` and its negation
    true. -/
theorem heim_blocks_witness (F : Conditional.Frame W) (w_eval : W)
    [Std.Antisymm (F.pref w_eval)] (h : Conditional.Want F belTotal w_eval targetProp) :
    ¬ Conditional.Want F belTotal w_eval targetPropᶜ :=
  h.not_compl defined_on_witness

/-! ## §5. Sloman's Principle blocks the witness for Lassiter's full account

Per [lassiter-2017] §8.11 (p.245): *"we should not weaken the
semantics to make room for the simultaneous truth of ought(φ) and
ought(¬φ). Instead, we should allow that there are various, possibly
conflicting **sources of value**..."* Sloman's Principle (eq. 8.16,
p.216) is the constraint that excludes single-V conflict.

On the witness model with `alts = [targetProp, ¬targetProp]`:
- E_V(targetProp) = 7, E_V(¬targetProp) = 2.
- Sloman for `targetProp`: requires `7 > 2` ✓.
- Sloman for `¬targetProp`: requires `2 > 7` ✗.

So `WantWithSloman` blocks the conflict on this configuration —
matching Lassiter's actual stated position. The bare-threshold witness
is exhibited by `conflict_concrete` *only because* it ignores Sloman;
Lassiter himself would say this is the wrong way to formalize his
account. -/

/-- The target proposition as a `Finset`, derived from `targetProp`. -/
def targetFinset : Finset W := Finset.univ.filter (· ∈ targetProp)

/-- The two-element alternative set for the witness model. -/
def witnessAlts : List (Finset W) := [targetFinset, targetFinsetᶜ]

/-- **Lassiter's full account blocks the witness** via Sloman's Principle
    (`WantWithSloman.not_compl`). -/
theorem wantWithSloman_blocks_conflict_on_witness
    (h : WantWithSloman prior value threshold belTotal witnessAlts targetFinset) :
    ¬ WantWithSloman prior value threshold belTotal witnessAlts targetFinsetᶜ :=
  h.not_compl (by simp [witnessAlts]) (by simp [witnessAlts]) (by decide)

end Lassiter2017Desire
