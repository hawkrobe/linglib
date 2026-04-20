import Linglib.Theories.Semantics.Conditionals.Basic
import Linglib.Theories.Pragmatics.Assertion.ReasonableInference

/-!
# Stalnaker 1975 @cite{stalnaker-1975}

*Indicative Conditionals.* Philosophia 5(3): 269–286.

## Core contributions formalized here

1. **The pragmatic constraint on selection** (§III): if `i ∈ C`, then
   `f(A,i) ∈ C` whenever some `A`-world is in `C`.

2. **Indicative ≠ subjunctive at the pragmatic level** (§III/IV): both have
   the same truth-conditional clause; subjunctive mood signals that the
   pragmatic constraint may be suspended.

3. **Disjunction-appropriateness** (§III): `A or B` is appropriately
   asserted only in contexts where both `¬A∧B` and `A∧¬B` are open.

4. **The direct argument is a reasonable inference but not an entailment**
   (§IV): from `A or B`, infer `if ¬A, B`.
   * `direct_argument_reasonable`: in any context where the disjunction
     can be appropriately asserted, the post-update context makes the
     indicative conditional true at every surviving world.
   * `direct_argument_not_entailment`: a single concrete world model
     exhibits a selection function for which `A∨B` holds at a world but
     `if ¬A, B` fails — so the inference is not semantic entailment.

5. **Fatalism failure** (§V): sketched in `fatalism_remark` as a docstring;
   the formal point is that constructive dilemma is valid only for
   entailments, not for reasonable inferences.

The two universal pragmatic postulates from the Appendix
(`respectsCompatibility`, `changeFn_eq`) are stated in
`Theories/Pragmatics/Assertion/ReasonableInference.lean`.

## Integration

* `pragmaticConstraint`, `selectionConditional`, `moodedConditional`,
  `Mood.admissibleSelection`, `selectionConditional_eq_material_within_context`,
  `moodedConditional_indicative_eq_material_within_context` —
  in `Theories/Semantics/Conditionals/Basic.lean`. The mood distinction lives
  in `Mood.admissibleSelection`, not in two parallel conditional defs:
  `.indicative` requires `pragmaticConstraint`, `.subjunctive` imposes none.
* `Appropriateness`, `changeFn`, `reasonableInference` — in
  `Theories/Pragmatics/Assertion/ReasonableInference.lean`.
* This file: a butler/gardener witness for (4); abstract version of (4)
  parameterised over any constraint-respecting selection function.

## See also

* `Phenomena/Modality/Studies/CarianiSantorio2018.lean` — extends the
  Stalnaker selection-function mechanism from conditionals to bare
  *will*. C&S's `Core.SelectionFunction` infrastructure is exactly the
  one used here for `selectionConditional`; the `would`-conditional /
  Stalnaker-counterfactual identification in C&S §5.3.2 reuses this
  paper's selection-function semantics under universe parameter.
-/

namespace Stalnaker1975

open Core.Mood (GramMood)
open Core.CommonGround (ContextSet)
open _root_.Core (SelectionFunction)
open Semantics.Conditionals
open Pragmatics.Assertion.ReasonableInference

-- § 1. The direct argument is REASONABLE (abstract version)

/--
**Stalnaker's direct argument is reasonable** (@cite{stalnaker-1975} §IV).

Quantified over any selection function `s` and context `C` such that:
- `s` obeys the pragmatic constraint relative to `C`;
- the antecedent `¬A` is open in `C` (some context-set world is `¬A`);
- in `C`, every world satisfies `A ∨ B` (i.e., the disjunction is
  established as common ground after assertion);

the indicative conditional `if ¬A, B` is true at every world in `C`.

This is the substance of §IV: no individual semantic entailment is invoked;
the pragmatic constraint plus the post-update common ground are enough.

Stalnaker's appropriateness condition for disjunction (§III, end) — that
asserting `A or B` requires both `¬A∧B` and `A∧¬B` to be open in the prior
context — is what guarantees `h_open_notA` after the update. -/
theorem direct_argument_reasonable {W : Type*}
    (s : SelectionFunction W) (C : ContextSet W)
    (notA B AorB : W → Prop)
    (h_constraint : pragmaticConstraint s C)
    (h_C_AorB : ∀ w, C w → AorB w)
    (h_AorB_decomp : ∀ w, AorB w → notA w → B w)
    (h_open_notA : ∃ w' ∈ {w' | notA w'}, C w') :
    ∀ w, C w → moodedConditional .indicative s notA B w := by
  intro w hCw
  apply moodedConditional_indicative_eq_material_within_context s C notA B w hCw
    h_open_notA h_constraint
  intro w' hCw' hnotA
  exact h_AorB_decomp w' (h_C_AorB w' hCw') hnotA

/--
**The direct argument is reasonable as a `reasonableInference`**
(@cite{stalnaker-1975} Appendix), in the sense of the change-function
calculus: in every prior context `k` such that asserting `A∨B` lands one
in a Stalnakerian indicative-friendly state, the post-update context
entails the indicative conditional.

The Appropriateness relation here bundles the two contextual facts the
disjunction-appropriateness condition guarantees: the pragmatic constraint
holds, and `¬A` remains open after the update. -/
theorem direct_argument_reasonableInference {W : Type*}
    (s : SelectionFunction W)
    (notA B AorB : W → Prop)
    (h_AorB_decomp : ∀ w, AorB w → notA w → B w)
    (𝒜 : Appropriateness W)
    (h_𝒜 : ∀ k, 𝒜 AorB k →
      pragmaticConstraint s (changeFn AorB k) ∧
      ∃ w' ∈ {w' | notA w'}, changeFn AorB k w') :
    reasonableInference 𝒜 [AorB] (moodedConditional .indicative s notA B) := by
  intro k h_app w hw_post
  -- changeFnSeq [AorB] k = changeFn AorB k.
  -- hw_post : changeFn AorB k w; h_app.1 : 𝒜 AorB k.
  obtain ⟨h_constraint, h_open⟩ := h_𝒜 k h_app.1
  have h_C_AorB : ∀ w', changeFn AorB k w' → AorB w' := by
    intro w' hw'; exact ((changeFn_eq AorB k w').mp hw').2
  exact direct_argument_reasonable s (changeFn AorB k) notA B AorB
    h_constraint h_C_AorB h_AorB_decomp h_open w hw_post

-- § 2. The direct argument is NOT a semantic entailment

/-- Three worlds for the butler/gardener model. The third world makes
    `B` false at a possible selection target, exhibiting the gap. -/
inductive Suspect where
  | butler | gardener | someoneElse
  deriving DecidableEq, Repr

abbrev W3 := Suspect
def A3 : W3 → Prop := λ s => s = .butler
def B3 : W3 → Prop := λ s => s = .gardener
def AorB3 : W3 → Prop := λ s => A3 s ∨ B3 s
def notA3 : W3 → Prop := λ s => ¬ A3 s

instance : DecidablePred A3 := fun s => decEq s .butler
instance : DecidablePred B3 := fun s => decEq s .gardener
instance : DecidablePred AorB3 := fun s => instDecidableOr (p := A3 s) (q := B3 s)
instance : DecidablePred notA3 := fun s => instDecidableNot (p := A3 s)

open Classical in
/-- A "subjunctive" selection function on `W3` that, for any nonempty
    antecedent set, picks `someoneElse` first if available — modelling
    selection that reaches outside the natural context set. -/
noncomputable def s_subj3 : SelectionFunction W3 where
  sel w P :=
    if w ∈ P then w
    else if (Suspect.someoneElse : W3) ∈ P then .someoneElse
    else if (Suspect.gardener : W3) ∈ P then .gardener
    else if (Suspect.butler : W3) ∈ P then .butler
    else w
  inclusion := by
    intro w P hne
    by_cases hw : w ∈ P
    · rw [if_pos hw]; exact hw
    · rw [if_neg hw]
      by_cases hs : (Suspect.someoneElse : W3) ∈ P
      · rw [if_pos hs]; exact hs
      · rw [if_neg hs]
        by_cases hg : (Suspect.gardener : W3) ∈ P
        · rw [if_pos hg]; exact hg
        · rw [if_neg hg]
          by_cases hb : (Suspect.butler : W3) ∈ P
          · rw [if_pos hb]; exact hb
          · exfalso
            obtain ⟨w', hw'⟩ := hne
            cases w' <;> first | exact hs hw' | exact hg hw' | exact hb hw'
  centering := by intro w P hw; rw [if_pos hw]

/-- **Counterexample to the direct argument as a semantic entailment.**

At `w = butler`, `A∨B = true`, but `s_subj3.sel butler {¬A worlds} =
someoneElse`, where `B` fails. So `if ¬A, B` is false at `butler` under
this selection function. -/
theorem direct_argument_not_entailment :
    AorB3 .butler ∧
    ¬ moodedConditional (W := W3) .indicative s_subj3 notA3 B3 .butler := by
  refine ⟨by decide, ?_⟩
  show ¬ B3 (s_subj3.sel Suspect.butler {w | notA3 w})
  have hw : (Suspect.butler : W3) ∉ ({w | notA3 w} : Set W3) :=
    fun h => absurd (h : notA3 .butler) (by decide)
  have hs : (Suspect.someoneElse : W3) ∈ ({w | notA3 w} : Set W3) :=
    show notA3 .someoneElse from by decide
  simp only [s_subj3, if_neg hw, if_pos hs]
  decide

/-- **Sanity check**: with any *indicative* selection function (one that
    obeys the pragmatic constraint relative to `C`), the conditional *does*
    hold at every `C`-world satisfying the disjunction. The contrast with
    `direct_argument_not_entailment` is the pragmatic-vs-semantic gap
    @cite{stalnaker-1975} emphasises. -/
theorem direct_argument_holds_under_indicative_selection :
    ∀ s : SelectionFunction W3,
      pragmaticConstraint s (λ w => w ≠ .someoneElse ∧ AorB3 w) →
      moodedConditional (W := W3) .indicative s notA3 B3 .butler := by
  intro s h_constraint
  apply direct_argument_reasonable s (λ w => w ≠ .someoneElse ∧ AorB3 w)
    notA3 B3 AorB3 h_constraint
  · intro w hw; exact hw.2
  · intro w h_AorB h_notA
    -- butler: ¬A is false, contradicts h_notA.
    -- gardener: B holds. someoneElse: AorB false, contradicts h_AorB.
    cases w with
    | butler => exact absurd h_notA (by decide)
    | gardener => decide
    | someoneElse => exact absurd h_AorB (by decide)
  · exact ⟨.gardener, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide⟩

-- § 3. Note on contraposition, hypothetical syllogism, and fatalism

/-! ### Contraposition / hypothetical syllogism

@cite{stalnaker-1975} observes that contraposition and hypothetical
syllogism fail in general for selection-based conditionals; the
counterexamples all involve **subjunctives** whose antecedents are
presupposed false. For indicatives — which obey `pragmaticConstraint` —
both inference forms come out reasonable in the Appendix's sense.

The semantic-failure side already exists as
`Semantics.Conditionals.perfection_not_entailed_variablyStrict` and can be
adapted directly to selection-based conditionals. The pragmatic-success
side is a clean extension of `direct_argument_reasonable` and is left for
follow-up. -/

/-! ### Fatalism (§V) `fatalism_remark`

Dummett's wartime-Britain fatalism argument has the form:
1. `K ∨ ¬K` (premise: I will be killed or not).
2. From `K`, derive `If P, K` (precautions ineffective).
3. From `¬K`, derive `If ¬P, ¬K` (precautions unnecessary).
4. ∴ `Q ∨ R`.

Steps 2 and 3 are *reasonable inferences* (they exploit the post-update
context where `K` or `¬K` is taken as established). Step 4 applies
constructive dilemma — valid for **entailments**, but not for
reasonable inferences. The argument equivocates the two notions.

Formalising this requires the n-ary `appropriateSeq` machinery already
present, plus a counterexample showing constructive dilemma fails for
reasonable inference. Left for follow-up. -/

end Stalnaker1975
