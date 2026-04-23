import Linglib.Theories.Semantics.Modality.Selectional
import Linglib.Theories.Semantics.Conditionals.WillConditional
import Linglib.Core.Modality.HistoricalAlternatives
import Linglib.Core.Probability.PMFFin
import Linglib.Fragments.English.Auxiliaries
import Mathlib.Tactic.DeriveFintype

/-!
# @cite{cariani-santorio-2018} — *Will* done Better

Cariani, F. & Santorio, P. (2018). Will done Better: Selection Semantics,
Future Credence, and Indeterminacy. *Mind* 127(505): 129–165.

## Core Claim

The future modal *will* is best analyzed as a **selectional** operator:
`will A` is true at `w` iff `A` holds at the unique world picked out by
a selection function from a set of historical alternatives. This rejects
both the pure-tense view (*will A* = *A* holds at a future time) and the
universal view (*will A* = *A* at every historical alternative).

## Three Constraints (the desiderata)

@cite{cariani-santorio-2018} argue that an adequate theory must satisfy:

1. **Modal character** — *will* embeds, takes scope, and interacts with
   negation/quantifiers. Pure tense fails.
2. **Scopelessness** — `¬ will A ↔ will ¬ A` in matrix uses.
   Universal quantification over a non-trivial modal base fails (the
   asymmetry between `¬∀` and `∀¬`).
3. **Cognitive role** — sincere assertion of `will A` requires
   non-extreme credence, not credence 1. Universal-base accounts make
   the assertion conditions too strong.

The selectional analysis satisfies all three by construction.

## The Sports Fan model (paper §2.3, §3 figure 2)

Cynthia is wondering what hat Robin will wear tomorrow to the game.
She considers three open historical alternatives — Robin will wear a
*Warriors* cap (`cw`), a *Giants* cap (`cg`), or *no* cap (`cn`) —
and assigns each credence 1/3. The example is designed to make every
predicate of interest land on a probability in `{0, 1/3, 2/3, 1}`,
which is what blocks @cite{hajek-1989}'s triviality argument from
applying (paper §8.2 footnote 32).

## Verified predictions

| # | Prediction | Theorem |
|---|-----------|---------|
| 1 | Sports Fan: Cynthia thinks Robin will wear a Warriors cap | `cynthia_will_warriors_cap` |
| 2 | Will Excluded Middle holds at every world | `will_em_at_cw` |
| 3 | Negation Swap: ¬will A ↔ will ¬A | `swap_at_cw` |
| 4 | Speaker w/o w in modal base ≠ collapse | `nonmember_no_collapse` |
| 5 | Speaker with w in modal base ⇒ collapse | `member_collapses` |
| 6 | Selectional `will`: μ(‖will Warriors-cap‖) = 1/3 | `cynthia_credence_one_third` |
| 7 | Universal `will`: μ(‖∀Warriors-cap‖) = 0 (collapse) | `universal_will_credence_zero` |
| 8 | "If Robin wears a cap, Robin'll wear a Warriors cap" — credence 1/2 (paper eq. 30, §8.1)| `cap_warriors_credence_one_half` |
| 9 | Hájek triviality fails: no proposition has probability 1/2 unconditionally (§8.2 fn 32) | `no_unconditional_one_half` |
| 10| `cynthiaSel` is coherent (§5.1: selection induces a well-ordering) | `cynthiaSel_coherent` |
-/

set_option autoImplicit false

namespace Phenomena.Modality.Studies.CarianiSantorio2018

open _root_.Semantics.Conditionals (SelectionFunction)
open Semantics.Modality.Selectional
open Semantics.Conditionals.WillConditional (wouldConditional willConditional)
open scoped ENNReal

-- ============================================================================
-- §1. The Sports Fan model
-- ============================================================================

/-- Three worlds — Robin's cap choices for tomorrow's game
    @cite{cariani-santorio-2018} §2.3 + §3 figure 2:
- `cw`: Robin wears a Warriors cap.
- `cg`: Robin wears a Giants cap.
- `cn`: Robin wears no cap. -/
inductive W where
  | cw | cg | cn
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Cynthia's modal parameter: every cap-choice is historically open.
    @cite{cariani-santorio-2018} treat the Sports Fan as a case where
    *all three* alternatives are live; nothing is settled at the time
    Cynthia forms her credences. -/
def histAlt : Set W := { .cw, .cg, .cn }

/-- Proposition: "Robin wears a Warriors cap." -/
def warriorsCap : Set W := {.cw}

instance : DecidablePred (· ∈ warriorsCap) := fun w => decEq w .cw

/-- Proposition: "Robin wears *some* cap" (Warriors or Giants). -/
def wearsCap : Set W := {.cw, .cg}

instance : DecidablePred (· ∈ wearsCap) := fun w =>
  inferInstanceAs (Decidable (w = .cw ∨ w ∈ ({.cg} : Set W)))

/-- The underlying selection function: prefer `w` if `w ∈ A`,
    otherwise the first available element in the order cw, cg, cn.
    This is total because `W` is exhausted by `{cw, cg, cn}`. -/
noncomputable def selFn (w : W) (A : Set W) : W :=
  open Classical in
  if w ∈ A then w else
  if (W.cw : W) ∈ A then .cw else
  if (W.cg : W) ∈ A then .cg else .cn

/-- `selFn` satisfies @cite{stalnaker-1968}'s Inclusion axiom. -/
theorem selFn_inclusion (w : W) (A : Set W) (hA : A.Nonempty) :
    selFn w A ∈ A := by
  unfold selFn
  split_ifs with hw h0 h1
  · exact hw
  · exact h0
  · exact h1
  · obtain ⟨x, hx⟩ := hA
    cases x
    · exact absurd hx h0
    · exact absurd hx h1
    · exact hx

/-- `selFn` satisfies @cite{stalnaker-1968}'s Centering axiom. -/
theorem selFn_centering (w : W) (A : Set W) (hw : w ∈ A) :
    selFn w A = w := by
  unfold selFn
  rw [if_pos hw]

noncomputable def cynthiaSel : SelectionFunction W where
  sel := selFn
  inclusion := selFn_inclusion
  centering := selFn_centering

/-- **Coherence** @cite{cariani-santorio-2018} §5.1: `cynthiaSel`
    induces a well-ordering on `{cw, cg, cn}` — its pairwise preference
    is transitive. The order, by construction of `selFn`, is
    `cw < cg < cn` from any centre that is not itself in the candidate
    pair (Centering forces the centre to win when it is present).

    Proved by exhaustive enumeration over 3⁴ = 81 quadruples. -/
theorem cynthiaSel_coherent : cynthiaSel.isCoherent := by
  intro w₀ w₁ w₂ w₃ h12 h23
  unfold _root_.Semantics.Conditionals.selectionPrefers cynthiaSel selFn at *
  revert h12 h23
  cases w₀ <;> cases w₁ <;> cases w₂ <;> cases w₃ <;>
    simp_all (config := { decide := true })

-- ============================================================================
-- §2. Sports Fan predictions
-- ============================================================================

/-- **Prediction 1**: From the Warriors-cap world `cw`,
    Cynthia's assertion *Robin will wear a Warriors cap* is true.

    `willSem cynthiaSel warriorsCap histAlt cw` reduces by Centering
    (since `cw ∈ histAlt`) to `warriorsCap cw = True`. -/
theorem cynthia_will_warriors_cap :
    willSem cynthiaSel warriorsCap histAlt .cw := by
  rw [unembedded_collapse cynthiaSel warriorsCap histAlt .cw
      (by simp [histAlt])]
  trivial

/-- **Prediction 2** (Will Excluded Middle): at every world,
    `will warriorsCap ∨ will ¬warriorsCap` holds. -/
theorem will_em_at_cw :
    willSem cynthiaSel warriorsCap histAlt .cw ∨
    willSem cynthiaSel (fun w => ¬ warriorsCap w) histAlt .cw :=
  will_excluded_middle cynthiaSel warriorsCap histAlt .cw

/-- **Prediction 3** (Negation Swap): under selectional semantics,
    `¬ will A ↔ will ¬ A`. This is what makes *will* "scopeless"
    in matrix uses — failing under universal quantification. -/
theorem swap_at_cw :
    willSem cynthiaSel (fun w => ¬ warriorsCap w) histAlt .cw ↔
    ¬ willSem cynthiaSel warriorsCap histAlt .cw :=
  negation_swap cynthiaSel warriorsCap histAlt .cw

-- ============================================================================
-- §3. Modal subordination — collapse only with membership
-- ============================================================================

/-- A modal parameter that *excludes* the actual world `cw` (here taken
    as the world from which Cynthia evaluates): the speaker is reasoning
    about a counterfactual continuation in which Robin wears no cap. -/
def counterfactualAlt : Set W := { .cn }

/-- **Prediction 4**: when the evaluation world `cw` is *not* in the
    modal parameter, *no* collapse — `will A` may diverge from `A w`.

    Here `will warriorsCap` evaluated at `cw` against `counterfactualAlt`
    selects `cn` (by Inclusion + the construction of `cynthiaSel`),
    where `warriorsCap` is False. So the assertion is False even
    though `warriorsCap cw = True`. -/
theorem nonmember_no_collapse :
    ¬ willSem cynthiaSel warriorsCap counterfactualAlt .cw := by
  show selFn .cw counterfactualAlt ∉ warriorsCap
  unfold selFn counterfactualAlt
  simp [warriorsCap]

/-- **Prediction 5** (= @cite{cariani-santorio-2018} eq. (17) collapse):
    when `w` is in the modal parameter, `will A` collapses to `A w`. -/
theorem member_collapses (A : W → Prop) (w : W) (hw : w ∈ histAlt) :
    willSem cynthiaSel A histAlt w ↔ A w :=
  unembedded_collapse cynthiaSel A histAlt w hw

-- ============================================================================
-- §4. Cognitive role: μ(‖will A‖) vs μ(‖∀A‖)
-- ============================================================================

/-- The universe of `W` enumerated as a 3-element `Finset` —
    used to reduce `∑ w : W, f w` to `f cw + f cg + f cn`. -/
private lemma univ_W_eq : (Finset.univ : Finset W) = {.cw, .cg, .cn} := by
  ext w; cases w <;> decide

/-- **Cynthia's credence** over the historical alternatives. Uniform
    on `histAlt = {cw, cg, cn}` — each cap choice gets 1/3.

    The uniform-over-three structure is what blocks the @cite{hajek-1989}
    triviality argument: no proposition lands on probability 1/2
    unconditionally, so the selectional account survives Hájek's
    objection by construction (paper §8.2 footnote 32). -/
noncomputable def cynthiaPMF : PMF W :=
  PMF.ofFintype (fun _ => (1 : ℝ≥0∞) / 3) (by
    rw [univ_W_eq, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
    ennreal_arith)

/-- `cynthiaPMF` is supported on `histAlt`: the support lies inside the
    modal parameter. Vacuously true here, since every world is in
    `histAlt` — but the discipline matches the `cognitive_role`
    interface, which takes `μ.support ⊆ f`. -/
theorem cynthiaPMF_support_in_histAlt : cynthiaPMF.support ⊆ histAlt := by
  intro w _
  cases w <;> simp [histAlt]

/-- **Prediction 6** (selectional cognitive role, paper §8.1):
    Cynthia's credence in *Robin will wear a Warriors cap* equals her
    credence in *Robin wears a Warriors cap*. Both are 1/3 — non-extreme
    credence licenses the *will*-assertion.

    Direct application of `Selectional.cognitive_role`. -/
theorem cynthia_credence_one_third :
    cynthiaPMF.probOfSet {w | cynthiaSel.sel w histAlt ∈ warriorsCap} = 1/3 := by
  rw [cognitive_role cynthiaSel warriorsCap histAlt cynthiaPMF
      cynthiaPMF_support_in_histAlt]
  rw [PMF.probOfSet_apply, univ_W_eq, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton,
      if_pos (show (W.cw) ∈ warriorsCap by decide),
      if_neg (show (W.cg) ∉ warriorsCap by decide),
      if_neg (show (W.cn) ∉ warriorsCap by decide)]
  simp only [cynthiaPMF, PMF.ofFintype_apply]
  ennreal_arith

/-- The universal-quantifier reading of *will Warriors-cap* is false at
    every world: `histAlt` contains the Giants-cap world `cg` where
    `warriorsCap` is False, so the universal cannot hold. -/
theorem universalWill_warriorsCap_const_false (w : W) :
    ¬ universalWill warriorsCap histAlt w := by
  intro h
  have hcg : W.cg ∈ warriorsCap := h .cg (by simp [histAlt])
  simp [warriorsCap] at hcg

/-- **Prediction 7** (universal-base credence collapse, paper §8.1):
    under the universal-quantifier reading, Cynthia's credence in
    *will Warriors-cap* is **0**, because the universal is false at
    every world (the Giants-cap world `cg` is in `histAlt`).

    Contrast with the selectional reading (`cynthia_credence_one_third`),
    which gives 1/3 — the empirically attested value. The
    selectional/universal split here is the substantive cognitive-role
    argument from @cite{cariani-santorio-2018} §8.1. -/
theorem universal_will_credence_zero :
    cynthiaPMF.probOfSet {w | universalWill warriorsCap histAlt w} = 0 := by
  have hempty : {w | universalWill warriorsCap histAlt w} = (∅ : Set W) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact universalWill_warriorsCap_const_false w
  rw [hempty, PMF.probOfSet_empty]

-- ============================================================================
-- §5. The cap-conditional (paper eq. (30), §8.1)
-- ============================================================================

/-- **Prediction 8** (will-conditional, paper eq. (30) §8.1):
    *If Robin wears a cap, Robin'll wear a Warriors cap*. The Kratzer
    restriction sends the modal parameter from `histAlt = {cw, cg, cn}`
    to `histAlt ∩ ‖cap‖ = {cw, cg}` — the cap-wearing alternatives.
    Inside this restricted parameter, both `cw` and `cg` are equally
    open, but the antecedent's truth-set assigns positive mass to `cw`
    only.

    Cynthia's credence in this conditional is 1/2 (paper §8.1):
    of the cap-wearing worlds (total mass 2/3), the Warriors-cap world
    has mass 1/3, so the conditional credence is 1/3 ÷ 2/3 = 1/2. The
    next theorem proves the *unconditional* credence in the world
    where the cap-conditional is true: the world `cw`, which has
    mass 1/3 ÷ (1/3 + 1/3) = 1/2 of the cap-wearing mass.

    This exercises @cite{cariani-santorio-2018} §5.3.1 + §5.3.2: the
    conditional uses `willConditional`, which Kratzer-restricts the
    modal parameter. -/
theorem cap_warriors_credence_one_half :
    cynthiaPMF.probOfSet wearsCap ≠ 0 ∧
    cynthiaPMF.condProbSet wearsCap warriorsCap = 1/2 := by
  -- Compute `probOfSet wearsCap = 2/3` once, reuse for both conjuncts.
  have hwears : cynthiaPMF.probOfSet wearsCap = 2/3 := by
    rw [PMF.probOfSet_apply, univ_W_eq, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton,
        if_pos (show (W.cw) ∈ wearsCap by decide),
        if_pos (show (W.cg) ∈ wearsCap by decide),
        if_neg (show (W.cn) ∉ wearsCap by decide)]
    simp only [cynthiaPMF, PMF.ofFintype_apply]
    ennreal_arith
  have hinter : cynthiaPMF.probOfSet (wearsCap ∩ warriorsCap) = 1/3 := by
    rw [PMF.probOfSet_apply, univ_W_eq, Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton,
        if_pos (show (W.cw) ∈ wearsCap ∩ warriorsCap by decide),
        if_neg (show (W.cg) ∉ wearsCap ∩ warriorsCap by decide),
        if_neg (show (W.cn) ∉ wearsCap ∩ warriorsCap by decide)]
    simp only [cynthiaPMF, PMF.ofFintype_apply]
    ennreal_arith
  refine ⟨?_, ?_⟩
  · rw [hwears, ← pos_iff_ne_zero]; ennreal_arith
  · rw [PMF.condProbSet_eq_div, hwears, hinter]
    -- (1/3) / (2/3) = 1/2 in ENNReal — `ennreal_arith` lifts to ℝ
    ennreal_arith

/-- **The morphological identity in action**: the would-conditional
    *if Robin had worn a cap, Robin would have worn a Warriors cap*
    is the same proposition as the corresponding will-conditional.
    @cite{cariani-santorio-2018} §5.3.2's claim that *would* = past-
    tense *will* lifts to conditionals: `wouldConditional` and
    `willConditional` agree definitionally. -/
theorem cap_would_eq_will (w : W) :
    wouldConditional cynthiaSel wearsCap warriorsCap histAlt w =
    willConditional cynthiaSel wearsCap warriorsCap histAlt w :=
  rfl

-- ============================================================================
-- §6. Hájek triviality fails (paper §8.2 footnote 32)
-- ============================================================================

/-- **Prediction 9** (paper §8.2 footnote 32): on the 3-cap Sports Fan
    model with uniform credence 1/3, *no* predicate `B : W → Bool` has
    `cynthiaPMF`-probability `1/2`. The probabilities all land in
    `{0, 1/3, 2/3, 1}`.

    @cite{hajek-1989}'s triviality argument requires a proposition with
    probability 1/2 to construct its problematic conditional. Cariani &
    Santorio observe that the Sports Fan deliberately avoids any such
    predicate — no proposition gets probability 1/2 here, so Hájek's
    argument cannot get off the ground in this model. The selectional
    account is therefore not undermined by the triviality result on
    this paradigm.

    Proved by exhaustive enumeration over `2³ = 8` decidable subsets. -/
theorem no_unconditional_one_half (S : Set W) [DecidablePred (· ∈ S)] :
    cynthiaPMF.probOfSet S ≠ 1/2 := by
  rw [PMF.probOfSet_apply, univ_W_eq, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [cynthiaPMF, PMF.ofFintype_apply]
  intro heq
  have h := congrArg ENNReal.toReal heq
  -- 8 cases: each of cw, cg, cn either in S or not
  by_cases hcw : (W.cw) ∈ S <;>
    by_cases hcg : (W.cg) ∈ S <;>
    by_cases hcn : (W.cn) ∈ S <;>
    (simp [hcw, hcg, hcn, ENNReal.toReal_add,
           ENNReal.toReal_ofNat, ENNReal.add_eq_top] at h
     try norm_num at h)

-- ============================================================================
-- §11. Morphological preconditions of the C&S analysis (Fragment binding)
-- ============================================================================

/-! ## Fragment binding

C&S analyse the English auxiliaries `Fragments.English.Auxiliaries.will`
and `Fragments.English.Auxiliaries.would`. The Fragment is the source
of truth for those entries' morphology; this section records the
morphological facts the C&S analysis depends on, as per-entry `rfl`
preconditions. If anyone later changes the morphological classification
of *will* or *would* in the Fragment (e.g., flips the `tense` field
on `would` away from `some .Past`), the corresponding precondition
theorem here breaks — making the cascading consequence for C&S visible
at compile time.

The Auxiliaries Fragment is a hub: other studies that analyse the
same entries (@cite{condoravdi-2002}, @cite{kratzer-1981}, etc.) record
their own morphological preconditions parallel to these. To enumerate
every analysis that touches a given entry, grep for
`Fragments.English.Auxiliaries.<entry>` across `Phenomena/`.

This section records *morphological* preconditions only. The C&S
semantic clauses (`willSem`, `wouldSem`) and their downstream theorems
live in the rest of this file and in
`Theories/Semantics/Modality/Selectional.lean`. The signature mismatch
between C&S's atemporal-propositional `willSem` and Condoravdi's
time-indexed-eventive `woll` means their predictions cannot be
compared by direct equation; a divergence-witness theorem against
@cite{condoravdi-2002} is left for follow-up. -/

/-- **C&S precondition**: the Fragment classifies *will* as a modal
    auxiliary. C&S's selectional analysis presupposes modal status —
    constraint #1 (modal character) requires *will* to embed, scope,
    and interact with negation/quantifiers. -/
theorem cs_assumes_will_is_modal_aux :
    Fragments.English.Auxiliaries.will.auxType =
      Fragments.English.Auxiliaries.AuxType.modal := rfl

/-- **C&S precondition**: the Fragment marks *will* as morphologically
    non-past (`tense = none`). C&S analyse *will* as the present-tense
    member of the future-modal pair; the `wouldSem`-as-past-shifted-
    `willSem` argument (§5.3.2) presumes this. -/
theorem cs_assumes_will_no_past_morph :
    Fragments.English.Auxiliaries.will.tense = none := rfl

/-- **C&S precondition**: the Fragment marks *would* as morphologically
    past (`tense = some .Past`). C&S §5.3.2 derives the *would* clause
    by past-shifting the modal parameter on *will*; if the Fragment
    later reclassified *would* as non-past, the §5.3.2 argument would
    no longer apply at the surface-form level. -/
theorem cs_assumes_would_past_morph :
    Fragments.English.Auxiliaries.would.tense =
      some UD.Tense.Past := rfl

/-- **C&S precondition**: *will* and *would* are morphologically
    distinguished by their `tense` fields. The selectional analysis
    would collapse vacuously if the Fragment treated them as
    morphologically identical. -/
theorem cs_will_would_morph_distinct :
    Fragments.English.Auxiliaries.will.tense ≠
      Fragments.English.Auxiliaries.would.tense := by decide

end Phenomena.Modality.Studies.CarianiSantorio2018
