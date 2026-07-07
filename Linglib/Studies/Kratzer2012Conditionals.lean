import Mathlib.Data.Fin.Basic
import Linglib.Semantics.Modality.Kratzer.Operators

/-!
# §2.9 Conditionals — [kratzer-2012]

[kratzer-2012] §2.9 ("Conditionals", pp. 65-68) presents the *if-clause-as-
modal-base-restrictor* schema `[[if α β]]^{f,g} = [[β]]^{f⁺, g}` where
`f⁺(w) = f(w) ∪ {[[α]]^{f,g}}`, plus a "Sketch of proof" showing the four
conditional types (material, strict, counterfactual, deontic-ordering) fall
out of varying f and g. The chapter's *only concrete worked example* in §2.9
is the German deontic scenario at p. 67 (examples 59-61).

## Sections
1. The §2.9 four-conditional recipe (abstract over predicates): material and
   strict implication theorems. Counterfactual case defers to Ch. 3.
2. Deontic scenario from p. 67: `injustice` / `amended` / `rewarded`
   propositions over a 4-world model, with morally-good ordering source.
3. Predictions on the deontic scenario (Kratzer's analysis of (59)-(61)).
4. **Headline argument** — Kratzer's analysis differentiates (60) from (61);
   the traditional `□(α → β)` analysis collapses them to vacuous truth.

## Kratzer's text (p. 67, paraphrased)

> (59) Jedem Menschen muss Gerechtigkeit widerfahren.
>      "Justice must be done to every person."
> (60) Wenn jemand ungerecht behandelt wurde, muss das Unrecht gesühnt werden.
>      "If someone was treated unjustly, the injustice must be amended."
> (61) Wenn jemand ungerecht behandelt wurde, muss das Unrecht belohnt werden.
>      "If someone was treated unjustly, the injustice must be rewarded."

> "Traditional approaches ... would have to analyze (60) and (61) as
> modalized material implications and assign them the logical form
> `necessarily (α→β)`. This leads to trouble. ... if there is no injustice
> in any morally accessible world, anything you like is true in morally
> accessible worlds where there is injustice." (p. 67)

> "On this analysis [Kratzer's], it is possible for the first two
> propositions [(59) and (60)] to be true, and the third one [(61)] to be
> false. For us, a world where injustice is amended for is not good (since
> there is no injustice in a good world). But it is still closer to what
> is good than any world where injustice is rewarded." (p. 67)
-/

namespace Kratzer2012Conditionals

open Semantics.Modality.Kratzer

/-! ## §1. Four-conditional recipe (abstract) -/

/-- Pointwise-realistic modal base: `f(w) = [(= w)]`, so `⋂f(w) = {w}`.

    NB: This is the *trivial* collapse where one proposition already IS the
    singleton {w}. [kratzer-2012] distinguishes this from totally-realistic
    backgrounds proper (`isTotallyRealistic` in
    `Semantics/Intensional/ConversationalBackground.lean`), which carry many
    propositions — facts about `w` — whose intersection is `{w}`. The
    lumping/dividing of those propositions does theoretical work in
    counterfactuals (Ch. 3 §3.1). For the §2.9 recipe only `⋂f(w) = {w}`
    matters, so the collapse is sound here — but it is NOT Kratzer's
    totally-realistic notion. -/
def pointwiseRealisticBg (W : Type*) [DecidableEq W] : ModalBase W :=
  λ w => [λ w' => w' = w]

/-- **Material implication recipe** (Kratzer 2012 §2.9, p. 65-66 "Sketch of
    proof", Case one). With a pointwise-realistic modal base and empty
    ordering source, the conditional `(if p) (necessarily q)` reduces to
    material implication `p w → q w` at the evaluation world. -/
theorem material_implication_recipe {W : Type*} [DecidableEq W]
    (p q : W → Prop) [DecidablePred p] (w : W) :
    necessity (restrictedBase (pointwiseRealisticBg W) p) emptyBackground q w ↔
    (p w → q w) := by
  rw [necessity_iff_all, empty_ordering_emptyBackground]
  constructor
  · intro h hP
    have hAcc : w ∈ accessibleWorlds (restrictedBase (pointwiseRealisticBg W) p) w := by
      intro r hr
      simp [restrictedBase, pointwiseRealisticBg] at hr
      rcases hr with hr | hr
      · subst hr; exact hP
      · subst hr; rfl
    exact h w hAcc
  · intro hImpl w' hAcc
    have hPW' : p w' := hAcc p (by simp [restrictedBase])
    have hEqW' : w' = w := by
      have hMem : (λ z : W => z = w) ∈ (restrictedBase (pointwiseRealisticBg W) p) w := by
        simp [restrictedBase, pointwiseRealisticBg]
      exact hAcc (λ z : W => z = w) hMem
    subst hEqW'
    exact hImpl hPW'

/-- **Strict implication recipe** (Kratzer 2012 §2.9, p. 66 "Sketch of proof"
    for strict implication). With an empty modal base and empty ordering
    source, the conditional `(if p) (necessarily q)` reduces to logical
    implication: `q` must hold at *every* `p`-world. -/
theorem strict_implication_recipe {W : Type*}
    (p q : W → Prop) [DecidablePred p] (w : W) :
    necessity (restrictedBase emptyBackground p) emptyBackground q w ↔
    (∀ w', p w' → q w') := by
  rw [necessity_iff_all, empty_ordering_emptyBackground]
  constructor
  · intro h w' hPw'
    apply h w'
    intro r hr
    simp [restrictedBase, emptyBackground] at hr
    subst hr
    exact hPw'
  · intro hImpl w' hAcc
    have hPW' : p w' := hAcc p (by simp [restrictedBase])
    exact hImpl w' hPW'

/-! ## §2. Deontic scenario (Kratzer 2012 §2.9 p. 67, ex. 59-61)

Four worlds:

| World | injustice | amended | rewarded | Notes                                |
|-------|-----------|---------|----------|--------------------------------------|
| w0    | no        | n/a     | n/a      | "Morally good" — no injustice exists |
| w1    | yes       | yes     | no       | Injustice amended for                |
| w2    | yes       | no      | yes      | Injustice rewarded                   |
| w3    | yes       | no      | no       | Injustice neither amended nor rewarded |
-/

abbrev World := Fin 4

/-- "Someone was treated unjustly" — true at w1, w2, w3. -/
def injustice : World → Prop
  | 0 => False
  | 1 | 2 | 3 => True

instance : DecidablePred injustice := fun w =>
  match w with
  | 0 => inferInstanceAs (Decidable False)
  | 1 | 2 | 3 => inferInstanceAs (Decidable True)

/-- "The injustice was amended" — true at w1 only. -/
def amended : World → Prop
  | 1 => True
  | 0 | 2 | 3 => False

instance : DecidablePred amended := fun w =>
  match w with
  | 1 => inferInstanceAs (Decidable True)
  | 0 | 2 | 3 => inferInstanceAs (Decidable False)

/-- "The injustice was rewarded" — true at w2 only. -/
def rewarded : World → Prop
  | 2 => True
  | 0 | 1 | 3 => False

instance : DecidablePred rewarded := fun w =>
  match w with
  | 2 => inferInstanceAs (Decidable True)
  | 0 | 1 | 3 => inferInstanceAs (Decidable False)

/-- **Morally-good ordering source.** Two propositions track moral goodness:
    no-injustice (the ideal), and if-injustice-then-amended (the corrective
    ideal). Their joint pattern induces:

    - w0 satisfies both (no injustice; vacuously amends)
    - w1 satisfies only the corrective ideal (injustice + amended)
    - w2, w3 satisfy neither (injustice without amends)

    So `w0 < w1 < {w2, w3}` in the at-least-as-good ordering. Kratzer's
    "morally good" ordering source is left informal in §2.9; this is a
    minimal encoding sufficient for the (60)/(61) contrast. -/
def morallyGood : OrderingSource World :=
  fun _ => [(fun w' => ¬ injustice w'), (fun w' => injustice w' → amended w')]

/-- **Traditional analysis modal base** (the foil Kratzer is arguing against,
    p. 67). Treats "morally accessible worlds" as a single modal base — only
    the morally good world (w0) is accessible. Under this analysis,
    `□(α → β)` becomes vacuously true at the actual world whenever the
    antecedent is false in all accessible worlds. -/
def traditionalMoralBase : ModalBase World := fun _ => [(fun w' => w' = 0)]

/-! ## §3. Predictions on the deontic scenario -/

/-- **(59) "Justice must be done"** under Kratzer's analysis. With empty
    modal base + morally-good ordering, the only best world is w0 (no
    injustice). So necessity of `¬ injustice` holds. -/
theorem ex59_holds (w : World) :
    necessity emptyBackground morallyGood (fun w' => ¬ injustice w') w := by
  rw [necessity_iff_all]
  intro w' ⟨_, hmin⟩
  -- w0 is accessible (vacuously, since emptyBackground gives universal access)
  have hAccW0 : (0 : World) ∈ accessibleWorlds emptyBackground w := by
    intro p hp
    simp [emptyBackground] at hp
  have hP1MemG : (fun w'' => ¬ injustice w'') ∈ morallyGood w := by
    simp [morallyGood]
  -- w0 satisfies every moral ideal, so it is at-least-as-good as anything
  have hTop : atLeastAsGoodAs (morallyGood w) (0 : World) w' := by
    intro q hq _
    simp [morallyGood] at hq
    rcases hq with rfl | rfl
    · decide
    · exact fun h => absurd h (by decide)
  -- minimality returns the comparison; transfer the ideal ¬ injustice
  exact hmin hAccW0 hTop _ hP1MemG (by decide)

/-- **(60) "If injustice, must be amended"** under Kratzer's analysis succeeds.
    With empty modal base restricted by `injustice` + morally-good ordering,
    the only best world is w1 (amended is closer to the moral ideal than
    rewarded or unredressed). So necessity of `amended` holds. -/
theorem ex60_holds (w : World) :
    necessity (restrictedBase emptyBackground injustice) morallyGood amended w := by
  rw [necessity_iff_all]
  intro w' ⟨hAcc, hmin⟩
  -- w' has injustice (it's in the restricted base)
  have hInjW' : injustice w' := hAcc injustice (by simp [restrictedBase])
  -- w1 is accessible (injustice + emptyBackground)
  have hAccW1 : (1 : World) ∈ accessibleWorlds (restrictedBase emptyBackground injustice) w := by
    intro p hp
    simp [restrictedBase, emptyBackground] at hp
    subst hp
    decide
  have hP2MemG : (fun w'' => injustice w'' → amended w'') ∈ morallyGood w := by
    simp [morallyGood]
  -- w1 is at-least-as-good as w' (¬ injustice fails at w', the other ideal holds at w1)
  have hTop : atLeastAsGoodAs (morallyGood w) (1 : World) w' := by
    intro q hq hqw'
    simp [morallyGood] at hq
    rcases hq with rfl | rfl
    · exact absurd hInjW' hqw'
    · exact fun _ => by decide
  exact hmin hAccW1 hTop _ hP2MemG (fun _ => by decide) hInjW'

/-- **(61) "If injustice, must be rewarded"** under Kratzer's analysis fails.
    The best injustice-world is w1, but w1 is NOT rewarded. -/
theorem ex61_fails (w : World) :
    ¬ necessity (restrictedBase emptyBackground injustice) morallyGood rewarded w := by
  intro hNec
  rw [necessity_iff_all] at hNec
  -- Witness: w1 is best, but rewarded w1 = False
  have hAccW1 : (1 : World) ∈ accessibleWorlds (restrictedBase emptyBackground injustice) w := by
    intro p hp
    simp [restrictedBase, emptyBackground] at hp
    subst hp
    decide
  -- Show w1 is at-least-as-good as every accessible world
  have hBestW1 : ∀ u ∈ accessibleWorlds (restrictedBase emptyBackground injustice) w,
      atLeastAsGoodAs (morallyGood w) (1 : World) u := by
    intro u hAccU p hpMemG hpAtU
    -- u has injustice (accessible via restricted base)
    have hInjU : injustice u := hAccU injustice (by simp [restrictedBase])
    simp [morallyGood] at hpMemG
    rcases hpMemG with hp1 | hp2
    · -- p = ¬ injustice. Then `hpAtU : ¬ injustice u`. But u has injustice. Contradiction.
      subst hp1
      exact absurd hInjU hpAtU
    · -- p = injustice → amended. We need w1 satisfies p, i.e., amended (1 : World).
      subst hp2
      intro _; decide
  have : rewarded (1 : World) := hNec 1 ⟨hAccW1, fun {u} hu _ => hBestW1 u hu⟩
  exact absurd this (by decide)

/-! ## §4. Headline: Kratzer differentiates (60) and (61); traditional analysis collapses them. -/

/-- **Kratzer's analysis differentiates (60) and (61).** Per [kratzer-2012]
    p. 67: "On this analysis, it is possible for the first two propositions
    [(59) and (60)] to be true, and the third one [(61)] to be false." -/
theorem kratzer_distinguishes_60_61 :
    (∀ w, necessity (restrictedBase emptyBackground injustice) morallyGood amended w) ∧
    (∀ w, ¬ necessity (restrictedBase emptyBackground injustice) morallyGood rewarded w) :=
  ⟨ex60_holds, ex61_fails⟩

/-- **Traditional `□(α → β)` analysis collapses (60) and (61) at the actual
    world** (where actual = w0, the morally good world). When morally
    accessible worlds = {w0} and w0 has no injustice, both `injustice → amended`
    and `injustice → rewarded` are vacuously true at every accessible world.
    This is the "vacuous truth" problem Kratzer flags on p. 67. -/
theorem traditional_60_vacuously_true :
    necessity traditionalMoralBase emptyBackground
      (fun w' => injustice w' → amended w') (0 : World) := by
  rw [necessity_iff_all, empty_ordering_emptyBackground]
  intro w' hAcc
  -- w' must equal 0 (only morally accessible world)
  have hEq : w' = 0 := hAcc (fun z => z = 0) (by simp [traditionalMoralBase])
  subst hEq
  intro hInj
  -- injustice 0 = False, so this case is vacuous
  exact absurd hInj (by decide)

theorem traditional_61_vacuously_true :
    necessity traditionalMoralBase emptyBackground
      (fun w' => injustice w' → rewarded w') (0 : World) := by
  rw [necessity_iff_all, empty_ordering_emptyBackground]
  intro w' hAcc
  have hEq : w' = 0 := hAcc (fun z => z = 0) (by simp [traditionalMoralBase])
  subst hEq
  intro hInj
  exact absurd hInj (by decide)

/-- **Headline contrast.** The traditional analysis predicts (60) and (61) both
    vacuously true; Kratzer's analysis predicts (60) true and (61) false. So
    the traditional analysis cannot distinguish the two conditionals at the
    morally-good actual world, while Kratzer's analysis does. -/
theorem traditional_collapses_kratzer_distinguishes :
    -- Traditional: both true at actual world
    (necessity traditionalMoralBase emptyBackground
        (fun w' => injustice w' → amended w') (0 : World) ∧
     necessity traditionalMoralBase emptyBackground
        (fun w' => injustice w' → rewarded w') (0 : World)) ∧
    -- Kratzer: (60) true, (61) false (at every world, in particular w0)
    (necessity (restrictedBase emptyBackground injustice) morallyGood amended (0 : World) ∧
     ¬ necessity (restrictedBase emptyBackground injustice) morallyGood rewarded (0 : World)) :=
  ⟨⟨traditional_60_vacuously_true, traditional_61_vacuously_true⟩,
   ⟨ex60_holds 0, ex61_fails 0⟩⟩

end Kratzer2012Conditionals
