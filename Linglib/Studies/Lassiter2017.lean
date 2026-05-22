import Linglib.Theories.Semantics.Attitudes.Desire
import Linglib.Theories.Semantics.Attitudes.CondoravdiLauer

/-!
# @cite{lassiter-2017} (apparatus) / @cite{lassiter-2011} (want application) — Expected-value desire

@cite{lassiter-2017} ch.7 ("Scalar goodness", *not* a desire chapter)
develops an expected-value semantics for evaluative gradable predicates;
@cite{lassiter-2011} (NYU dissertation, ch.6) applies the apparatus to
*want*. The book extends the *good* analysis to *want* in a single
sentence at §8.13 (p.249) — *want* is gradable like *like, matter,
care, need*.

This study file:

* §1 builds the **bare-threshold conflict-witness model** (4 worlds,
  uniform prior 1/4, V = (10, 4, 4, 0), θ = 3/2, `p = {w₀, w₁}`).
* §2 replicates the conflict predictions: `want_p ∧ want_negp`.
* §3 cross-paper bridge to @cite{condoravdi-lauer-2016}: C&L's
  `wantEP_jointly_belief_consistent` forbids the witness; the
  Lassiter bare apparatus exhibits it. **Different mechanisms.**
* §4 cross-paper bridge to @cite{heim-1992}: same configuration is
  `wantHeimDefined`-OK, but `wantHeim_no_simultaneous_pq_and_negpq`
  rules out joint truth. **Heim's (40) amendment is the structural
  analog of Lassiter's Sloman.**
* §5 **Sloman's Principle blocks the witness** for Lassiter's *full*
  account. The bare-threshold conflict witness is exactly Cariani's
  Weakening counter-model (Lassiter's Table 8.4 reconstruction of
  the @cite{cariani-2016} actualist Weakening attack, applied to EV;
  Cariani's own counter-model uses actualist closeness, not EV)
  p.239); Lassiter's response is Sloman's Principle, which excludes
  it. The witness is a falsifier of the *bare* form, not of
  Lassiter's actual position.

The chronological-dependency rule applies: this file references
@cite{phillips-brown-2025} only in docstring prose (PB is later);
PhillipsBrown2025.lean already cross-references Lassiter via the
`BeliefBasedDesireSemantics` typology design.
-/

namespace Lassiter2017Desire

open Semantics.Attitudes.Desire
open Semantics.Attitudes.Desire.Lassiter

/-! ## §1. The 4-world conflict-witness model

Following @cite{lassiter-2017} §7.6 eq. 7.22 (apparatus) and
@cite{lassiter-2011} ch.6 (*want* application). Uniform prior over
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
def belTotal : Set W := fun _ => True
instance : DecidablePred belTotal := fun _ => isTrue trivial

/-- The target proposition `p = {w₀, w₁}`. -/
def targetProp : Set W := fun w => w = 0 ∨ w = 1
instance : DecidablePred targetProp := fun w => by unfold targetProp; infer_instance

/-! ## §2. The conflict predictions

`E_V(p | belS) = (1/4 · 10 + 1/4 · 4) / (1/4 + 1/4) = (14/4) / (1/2) = 7`
`E_V(¬p | belS) = (1/4 · 4 + 1/4 · 0) / (1/4 + 1/4) = 1 / (1/2) = 2`
With θ = 3/2, both are above threshold → both are wanted. -/

theorem want_p : Lassiter.want belTotal prior value threshold targetProp := by
  unfold Lassiter.want Lassiter.expectedValue targetProp belTotal prior value threshold
  simp [Fin.sum_univ_succ]
  norm_num

theorem want_negp :
    Lassiter.want belTotal prior value threshold (fun w => ¬ targetProp w) := by
  unfold Lassiter.want Lassiter.expectedValue targetProp belTotal prior value threshold
  simp [Fin.sum_univ_succ]
  norm_num

theorem conflict_concrete :
    Lassiter.want belTotal prior value threshold targetProp ∧
    Lassiter.want belTotal prior value threshold (fun w => ¬ targetProp w) :=
  ⟨want_p, want_negp⟩

/-! ## §3. Cross-paper bridge: @cite{condoravdi-lauer-2016}

C&L's `wantEP_jointly_belief_consistent` says that for any
`EffectivePreferentialBackground EP` and any agent `a`, world `w`,
`wantEP EP a φ w ∧ wantEP EP a ψ w` implies `(φ ∩ ψ) ∩ B(a, w) ≠ ∅`.
Specialized to `ψ = φᶜ`: the intersection is empty, so simultaneous
truth is impossible.

Lassiter's bare-threshold apparatus exhibits exactly such a
configuration. The two frameworks make orthogonal predictions on the
4-world model. -/

/-- C&L blocks any pair `wantEP φ ∧ wantEP ¬φ`. Specialized form
    showing C&L cannot reproduce Lassiter's witness. -/
theorem condoravdiLauer_blocks_lassiter_witness
    {Agent : Type} {B : Agent → W → Set W}
    (EP : Semantics.Attitudes.CondoravdiLauer.EffectivePreferentialBackground Agent W B)
    (a : Agent) (w : W) (φ : Set W)
    (hφ : Semantics.Attitudes.CondoravdiLauer.wantEP EP a φ w)
    (hnegφ : Semantics.Attitudes.CondoravdiLauer.wantEP EP a (fun w => ¬ φ w) w) :
    False := by
  have h := Semantics.Attitudes.CondoravdiLauer.wantEP_jointly_belief_consistent
              EP hφ hnegφ
  apply h
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun ⟨h1, h2⟩ _ => h2 h1

/-! ## §4. Cross-paper bridge: @cite{heim-1992}

Heim's (40) amendment + comparative-belief semantics block simultaneous
`wantHeim p ∧ wantHeim ¬p` (substrate's
`wantHeim_no_simultaneous_pq_and_negpq`). The 4-world conflict witness
configuration is `wantHeimDefined`-OK on `targetProp` (both p-worlds
and ¬p-worlds are in `belTotal`), so Heim's no-go applies — and Heim's
prediction differs from Lassiter's.

This is the analog: Heim's (40) plays the role for comparative-belief
that Sloman plays for Lassiter — both block single-V/single-context
conflict. -/

theorem wantHeimDefined_on_witness :
    wantHeimDefined belTotal targetProp := by
  refine ⟨⟨0, ?_, ?_⟩, ⟨2, ?_, ?_⟩⟩ <;> decide

/-- On the witness configuration, Heim's no-go theorem applies — for
    any Heim parameters with strictly asymmetric desirability,
    `wantHeim` cannot make both `targetProp` and its negation true.
    Direct application of the substrate theorem. -/
theorem heim_blocks_witness
    (params : HeimDesireParams W) (w_eval : W)
    (hAsym : ∀ x y, params.pref w_eval x y → params.pref w_eval y x → x = y) :
    ¬ (wantHeim belTotal params w_eval targetProp ∧
       wantHeim belTotal params w_eval (fun w => ¬ targetProp w)) :=
  wantHeim_no_simultaneous_pq_and_negpq belTotal params w_eval targetProp
    hAsym wantHeimDefined_on_witness

/-! ## §5. Sloman's Principle blocks the witness for Lassiter's full account

Per @cite{lassiter-2017} §8.11 (p.245): *"we should not weaken the
semantics to make room for the simultaneous truth of ought(φ) and
ought(¬φ). Instead, we should allow that there are various, possibly
conflicting **sources of value**..."* Sloman's Principle (eq. 8.16,
p.216) is the constraint that excludes single-V conflict.

On the witness model with `alts = [targetProp, ¬targetProp]`:
- E_V(targetProp) = 7, E_V(¬targetProp) = 2.
- Sloman for `targetProp`: requires `7 > 2` ✓.
- Sloman for `¬targetProp`: requires `2 > 7` ✗.

So `wantWithSloman` blocks the conflict on this configuration —
matching Lassiter's actual stated position. The bare-threshold witness
is exhibited by `conflict_concrete` *only because* it ignores Sloman;
Lassiter himself would say this is the wrong way to formalize his
account. -/

/-- The two-element alternative set for the witness model. -/
def witnessAlts : List (Σ' (q : Set W), DecidablePred q) :=
  [⟨targetProp, inferInstance⟩,
   ⟨fun w => ¬ targetProp w, inferInstance⟩]

theorem targetProp_ne_negTargetProp : (targetProp : Set W) ≠ (fun w => ¬ targetProp w) := by
  intro h
  have hp : targetProp 0 := by decide
  have h0 := congrFun h 0
  change targetProp 0 = ¬ targetProp 0 at h0
  exact (h0 ▸ hp : ¬ targetProp 0) hp

/-- **Lassiter's full account blocks the witness** via Sloman's
    Principle. Direct instance of the substrate theorem
    `wantWithSloman_blocks_conflict`. -/
theorem wantWithSloman_blocks_conflict_on_witness :
    ¬ (Lassiter.wantWithSloman belTotal prior value threshold witnessAlts targetProp ∧
       Lassiter.wantWithSloman belTotal prior value threshold witnessAlts
         (fun w => ¬ targetProp w)) :=
  Lassiter.wantWithSloman_blocks_conflict belTotal prior value threshold targetProp
    witnessAlts (by simp [witnessAlts]) (by simp [witnessAlts])
    targetProp_ne_negTargetProp

end Lassiter2017Desire
