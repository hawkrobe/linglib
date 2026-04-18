import Linglib.Core.SelectionFunction
import Linglib.Core.Modality.HistoricalAlternatives
import Linglib.Core.FinitePMF

/-!
# Selectional Semantics for *will*
@cite{cariani-santorio-2018}

A **selectional** treatment of the future modal *will*: rather than
quantifying universally or existentially over a modal base of historical
alternatives, *will* applies its prejacent at a single **selected**
world picked out by a Stalnaker-style selection function indexed by a
modal parameter `f`.

`⟦will_f A⟧^{w,s,g} = 1  iff  ⟦A⟧^{s(w, g(f)), s, g} = 1`

where `s : SelectionFunction W` is a contextually supplied selection
function and `g(f)` is the relevant set of historical alternatives.

## Three constraints @cite{cariani-santorio-2018}

@cite{cariani-santorio-2018} argue that an adequate theory of *will*
must satisfy three constraints:

1. **Modal character**: *will* takes scope, interacts with negation and
   quantifiers, and embeds under attitudes — so it cannot be a pure
   present-tense or pure future-tense reference operator.
2. **Scopelessness**: under negation in matrix uses, `will ¬A` and
   `¬will A` are equivalent (Negation Swap, `negation_swap`). Universal
   quantification over a non-trivial modal base cannot deliver this
   (`universal_negation_swap_fails`).
3. **Cognitive role**: a sincere assertion of `will A` is licensed by
   ordinary, non-extreme credence in `A`, not credence 1
   (`cognitive_role`). A homogeneity / domain-width condition that
   requires uniform truth across the modal base would make assertion
   conditions too strong (`universalWill` collapses credence to 0/1).

## What's here

- `willSem`, `willSem_def`: the selectional truth-condition.
- `negation_swap`, `will_excluded_middle`, `unembedded_collapse`:
  the three core scopelessness/CEM/factivity-on-base theorems.
- `will_eq_A_on_modalParam`: **content transparency** §8.1 footnote 30.
  As `Set W`, `‖will A‖` and `‖A‖` agree on every world in the modal
  parameter `f`. This is the substantive transparency claim from
  which the cognitive-role prediction follows.
- `Valid2`: validity₂ from paper §6 (truth at every ⟨s, f, w⟩, not
  just at the context). `valid2_will_excluded_middle` and
  `valid2_negation_swap` recast the matrix theorems in this stronger
  validity notion.
- `willHistorical`: `will` over the metaphysical modal base from
  `Core/Modality/HistoricalAlternatives.lean` — the bridge to the
  branching-time substrate.
- `universalWill`: the universal-quantifier reading used as a foil
  in @cite{cariani-santorio-2018}'s arguments. Shown to violate
  Negation Swap (`universal_negation_swap_fails`).
- `cognitive_role`: under any credence supported on the modal
  parameter, `μ(‖will A‖) = μ(‖A‖)` — the §8.1 prediction that
  decisively distinguishes selectional from universal accounts.
-/

set_option autoImplicit false

namespace Semantics.Modality.Selectional

open _root_.Core (SelectionFunction FinitePMF)
open _root_.Core.Modality.HistoricalAlternatives

variable {W : Type*}

/-! ## §1. The selectional truth-condition -/

/-- Selectional truth-condition for *will* @cite{cariani-santorio-2018}.

    `willSem s A f w` is true iff the prejacent `A` holds at the world
    selected by `s` from the modal parameter `f` at `w`.

    Reading: "will A" at `w` says A holds at the unique selected
    historical alternative `s.sel w f`. -/
def willSem (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) : Prop :=
  A (s.sel w f)

@[simp] theorem willSem_def (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) :
    willSem s A f w ↔ A (s.sel w f) := Iff.rfl

/-- `willSem` is decidable when its prejacent is. -/
instance willSem_decidable (s : SelectionFunction W) (A : W → Prop)
    [DecidablePred A] (f : Set W) (w : W) :
    Decidable (willSem s A f w) :=
  inferInstanceAs (Decidable (A _))

/-- Bool-valued selectional `will` — useful for credence calculations
    via `Core.FinitePMF.probOf` (which takes Bool predicates). -/
def willSemBool (s : SelectionFunction W) (A : W → Bool)
    (f : Set W) (w : W) : Bool :=
  A (s.sel w f)

@[simp] theorem willSemBool_def (s : SelectionFunction W) (A : W → Bool)
    (f : Set W) (w : W) :
    willSemBool s A f w = A (s.sel w f) := rfl

/-! ## §2. Scopelessness, CEM, and unembedded collapse -/

/-- **Negation Swap** @cite{cariani-santorio-2018}: under selectional
    semantics, *will* commutes with negation. `will ¬A ↔ ¬ will A`.

    This follows immediately from the single-valuedness of selection:
    the selected world either satisfies `A` or it doesn't. -/
theorem negation_swap (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) :
    willSem s (fun w' => ¬ A w') f w ↔ ¬ willSem s A f w := Iff.rfl

/-- **Will Excluded Middle** @cite{cariani-santorio-2018}: `will A ∨
    will ¬A` holds at every point of evaluation.

    The classical disjunction holds because `s.sel w f` is a single
    world, on which `A` is either true or false. This is the
    selectional analogue of Conditional Excluded Middle for Stalnaker
    counterfactuals. -/
theorem will_excluded_middle (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) :
    willSem s A f w ∨ willSem s (fun w' => ¬ A w') f w :=
  Classical.em _

/-- **Unembedded collapse** @cite{cariani-santorio-2018} eq. (17):
    when the evaluation world is itself in the modal parameter,
    Centering forces the selected world to be `w`, so `will A`
    reduces to `A w`.

    This explains the apparent factivity of unembedded *will*-claims
    when the speaker presupposes that the actual world is among the
    historical alternatives. -/
theorem unembedded_collapse (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) (w : W) (hw : w ∈ f) :
    willSem s A f w ↔ A w := by
  unfold willSem
  rw [s.centering w f hw]

/-! ## §3. Content transparency

The substantive transparency claim of @cite{cariani-santorio-2018}
§8.1 footnote 30: as a *proposition* (set of worlds), `‖will A‖` is
not just `‖A‖` — they may diverge outside the modal parameter. But
*restricted to the modal parameter*, they agree. This is the
content-level fact from which the cognitive-role prediction follows. -/

/-- **Content transparency** @cite{cariani-santorio-2018} §8.1: on the
    modal parameter `f`, the truth set of `will A` coincides with the
    truth set of `A`. Pointwise consequence of Centering. -/
theorem will_eq_A_on_modalParam (s : SelectionFunction W) (A : W → Prop)
    (f : Set W) :
    ∀ w ∈ f, willSem s A f w ↔ A w :=
  fun w hw => unembedded_collapse s A f w hw

/-- Conjunction transparency: on `f`, `will (A ∧ B)` and `will A ∧
    will B` coincide pointwise. -/
theorem will_and_eq_will_and_will_on_modalParam (s : SelectionFunction W)
    (A B : W → Prop) (f : Set W) :
    ∀ w ∈ f, willSem s (fun w' => A w' ∧ B w') f w ↔
              (willSem s A f w ∧ willSem s B f w) := by
  intro w _
  unfold willSem
  exact Iff.rfl

/-- Disjunction transparency: on `f`, `will (A ∨ B)` and `will A ∨
    will B` coincide pointwise. -/
theorem will_or_eq_will_or_will_on_modalParam (s : SelectionFunction W)
    (A B : W → Prop) (f : Set W) :
    ∀ w ∈ f, willSem s (fun w' => A w' ∨ B w') f w ↔
              (willSem s A f w ∨ willSem s B f w) := by
  intro w _
  unfold willSem
  exact Iff.rfl

/-! ## §4. Validity₂ (paper §6)

@cite{cariani-santorio-2018} distinguish *validity₁* (truth at the
context of utterance) from *validity₂* (truth at *every* index
⟨w, s, g⟩). The matrix scopelessness theorems are validity₁ claims;
the more interesting ones are validity₂. -/

/-- **Validity₂**: a propositional schema is valid₂ when it holds at
    every ⟨selection function, modal parameter, world⟩ triple. -/
def Valid2 (φ : SelectionFunction W → Set W → W → Prop) : Prop :=
  ∀ s f w, φ s f w

/-- Negation Swap is **valid₂** (paper §6). -/
theorem valid2_negation_swap (A : W → Prop) :
    Valid2 (W := W) fun s f w =>
      willSem s (fun w' => ¬ A w') f w ↔ ¬ willSem s A f w :=
  fun s f w => negation_swap s A f w

/-- Will Excluded Middle is **valid₂** (paper §6, §7). -/
theorem valid2_will_excluded_middle (A : W → Prop) :
    Valid2 (W := W) fun s f w =>
      willSem s A f w ∨ willSem s (fun w' => ¬ A w') f w :=
  fun s f w => will_excluded_middle s A f w

/-! ## §5. Bridge to historical alternatives

Selectional `will` parameterized by the metaphysical modal base of
@cite{condoravdi-2002} — the historical-alternatives substrate from
`Core/Modality/HistoricalAlternatives.lean`. -/

/-- **Selectional `will` over historical alternatives.** Evaluates
    the prejacent at the world selected from the metaphysical modal
    base at ⟨w, t⟩. -/
def willHistorical {Time : Type*} (s : SelectionFunction W)
    (history : WorldHistory W Time) (A : W → Prop)
    (w : W) (t : Time) : Prop :=
  willSem s A (metaphysicalBase history w t) w

/-- When the world-history relation is reflexive (the standard case
    @cite{condoravdi-2002} §4.1 condition (i)), `willHistorical`
    collapses to its prejacent: `will_t A` at `w` reduces to `A w`. -/
theorem willHistorical_reflexive_collapse {Time : Type*}
    (s : SelectionFunction W) {history : WorldHistory W Time}
    (hRefl : history.reflexive) (A : W → Prop) (w : W) (t : Time) :
    willHistorical s history A w t ↔ A w := by
  unfold willHistorical
  apply unembedded_collapse
  exact hRefl ⟨w, t⟩

/-! ## §6. The universal-quantifier foil

The universal-quantifier reading is what @cite{cariani-santorio-2018}
argue against. Section 8.1's cognitive-role argument is decisive
because the selectional account validates `μ(‖will A‖) = μ(A)` while
the universal account collapses credence into a 0/1 step function. -/

/-- The universal-quantifier reading of `will`: true at `w` iff `A`
    holds at every world in the modal parameter. The world `w` itself
    is *not* used — universal `will` is index-independent. -/
def universalWill (A : W → Prop) (f : Set W) (_w : W) : Prop :=
  ∀ w' ∈ f, A w'

/-- **Negation Swap fails for universal `will`.** When the modal
    parameter contains both an `A`-world and a `¬A`-world, the
    universal-quantifier reading violates `¬∀ ↔ ∀¬`.

    Witness: ∀A is false (some w₂ ∉ A), but ∀¬A is also false (some
    w₁ ∈ A). So the biconditional is `false ↔ true`. -/
theorem universal_negation_swap_fails {A : W → Prop} {f : Set W} {w : W}
    (h : ∃ w₁ ∈ f, ∃ w₂ ∈ f, A w₁ ∧ ¬ A w₂) :
    ¬ (universalWill (fun w' => ¬ A w') f w ↔ ¬ universalWill A f w) := by
  obtain ⟨w₁, hw₁f, w₂, hw₂f, hA1, hnA2⟩ := h
  unfold universalWill
  intro hiff
  have hLHS_false : ¬ (∀ w' ∈ f, ¬ A w') :=
    fun hAll => hAll w₁ hw₁f hA1
  have hRHS_true : ¬ (∀ w' ∈ f, A w') :=
    fun hAll => hnA2 (hAll w₂ hw₂f)
  exact hLHS_false (hiff.mpr hRHS_true)

/-! ## §7. Cognitive role (paper §8.1)

The selectional analysis predicts `μ(‖will A‖_f) = μ(‖A‖_f)` whenever
the credence `μ` is supported on the modal parameter `f`. This
matches the empirically attested gradedness of *will*-credences and
distinguishes selectional from universal accounts. -/

/-- **Cognitive role** @cite{cariani-santorio-2018} §8.1: under any
    credence `μ` supported on the modal parameter `f` (every world
    outside `f` has zero mass), the credence assigned to `will A`
    equals the credence assigned to `A` itself.

    Reading: assertion of `will A` is licensed by ordinary, non-extreme
    credence in `A`. The universal-quantifier reading instead forces
    `μ(‖∀ A‖) ∈ {0, 1}` (collapsing into a step function on whether
    `f ⊆ A`), which is empirically wrong. -/
theorem cognitive_role [Fintype W] (s : SelectionFunction W)
    (A : W → Bool) (f : Set W) (μ : FinitePMF W)
    (h_supp : ∀ w ∉ f, μ.mass w = 0) :
    μ.probOf (fun w => A (s.sel w f)) = μ.probOf A := by
  unfold FinitePMF.probOf
  apply Finset.sum_congr rfl
  intro w _
  dsimp only
  by_cases hw : w ∈ f
  · congr 1
    rw [s.centering w f hw]
  · rw [h_supp w hw]; simp

end Semantics.Modality.Selectional
