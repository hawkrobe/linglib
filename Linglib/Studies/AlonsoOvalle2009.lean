import Linglib.Semantics.Conditionals.Counterfactual.Alternatives
import Linglib.Studies.McKayVanInwagen1977
import Linglib.Syntax.Category.Coordinator

/-!
# Alonso-Ovalle 2009 — "Counterfactuals, correlatives, and disjunction"
[alonso-ovalle-2009]

*Linguistics and Philosophy* 32(2): 207–244.

## Core proposal

The natural interpretation of disjunctive counterfactuals — "if A or B,
would C" — selects from each disjunct's closest worlds, NOT from the
union's closest worlds. [alonso-ovalle-2009] (p. 207) refutes
[lewis-1973]'s standard minimal-change semantics on this reading
without abandoning minimal change. Two refinements:

1. **Disjunctions introduce propositional alternatives** in the
   semantic derivation (Hamblin-style alternative semantics, following
   Aloni 2003a, Simons 2005, and Alonso-Ovalle's own dissertation).
   The Or Rule (10) p. 212: `or` outputs the SET `{⟦B⟧, ⟦C⟧}` as
   alternatives rather than the Boolean union.
2. **Conditionals are correlative constructions** (von Fintel 1994,
   Izvorski 1996, Bhatt & Pancheva 2006, Schlenker 2004). The
   if-clause is a universal quantifier over propositions; `then` is a
   propositional anaphor. This forces universal quantification over
   the disjunct alternatives.

## Truth condition (eqn 25-26 p. 217)

   ⟦if A, would C⟧ = `λw. ∀p ∈ Alt(A): f_{≤,w}(p) ⊆ ⟦C⟧`

Equivalently: every disjunct alternative's closest worlds satisfy the
consequent. **This is structurally [santorio-2018]'s `Distributive`** —
universal-over-per-alternative-conditionals (Simplification reading).

## Connection to linglib substrate

`aoConditional` IS [santorio-2018]'s `Distributive`
(`Studies/Santorio2018.lean`); the bridge is
`rfl`. The frameworks DIFFER in their treatment of the **alternative
set**, not the per-alternative evaluation:

- [alonso-ovalle-2009] (Hamblin Or Rule, eqn 13 p. 213): alts =
  `{⟦disjunct₁⟧, ⟦disjunct₂⟧, ...}` — only the disjuncts themselves.
- [santorio-2018] (Katzir-generated ALT_S + stability algorithm):
  alts include the disjuncts + their conjunction + their disjunction;
  truthmakers are minimal-stable subsets, which can include "mixed"
  truthmakers [alonso-ovalle-2009] cannot generate.

The differential prediction lives in [santorio-2018] §IV.3
(Karenina/W&P 8-alternative example) and is proved as
`santorio_finds_mixed_truthmaker_ao_misses_it` in that file.
-/

namespace AlonsoOvalle2009

open Semantics.Conditionals (SimilarityOrdering)
open Semantics.Conditionals.Counterfactual (universalCounterfactual)
open Semantics.Conditionals.Counterfactual (Distributive universalCounterfactual_mem_filter)
open McKayVanInwagen1977 (CropWorld cropSim goodWeather sunCold bumperCrop
  bumperCrop_lewis_true bumperCrop_conjunction_false)


/-! ## §1 The bumper crop scenario (p. 208)

Same scenario as [mckay-vaninwagen-1977] (a variation of Nute
1975): "If we had had good weather this summer or the sun had grown
cold, we would have had a bumper crop." Standard minimal-change with
Boolean `or` predicts TRUE; intuition says FALSE. Worlds and
similarity ordering already formalised in
`Studies/McKayVanInwagen1977.lean::cropSim` and consumed via the
substrate. -/


/-! ## §2.1–2.2 The analysis -/

/-- [alonso-ovalle-2009] **conditional verdict** for a disjunctive
    antecedent (eqn 25–26 p. 217): every disjunct alternative's
    closest worlds satisfy the consequent.

    Definitionally equal to [santorio-2018]'s `Distributive` — the
    Simplification reading. The two accounts diverge in how the
    alternative SET is generated (see module docstring), not in this
    per-alternative evaluation rule. -/
def aoConditional {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (alts : List (Finset W))
    (C : W → Prop) [DecidablePred C] (w : W) : Prop :=
  Distributive sim alts C w

/-- **Bridge: AO = Santorio's `Distributive`.** Definitionally equal; the
    two formalisations of the per-alternative-conditional reading
    coincide. The substantive difference between
    [alonso-ovalle-2009] and [santorio-2018] is the
    alternative-set construction, not this evaluation rule. -/
theorem aoConditional_eq_distributive {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (alts : List (Finset W))
    (C : W → Prop) [DecidablePred C] (w : W) :
    aoConditional sim alts C w = Distributive sim alts C w := rfl

/-- **Disjunct-only alternative set construction** (Hamblin Or Rule,
    eqn 13 p. 213). For a disjunctive antecedent `A or B`,
    [alonso-ovalle-2009]'s alternative set is exactly
    `[⟨A, _⟩, ⟨B, _⟩]` — the two disjunct denotations bundled with
    decidability. No conjunction, no disjunctive closure, no
    Katzir-generated structural alternatives. This is the locality
    [santorio-2018] §III argues against. -/
def aoAlternatives {W : Type*} (A B : Finset W) : List (Finset W) := [A, B]


/-! ## §2.2.3 Universal force

The two-component analysis — alternative-generating `or` plus
correlative-style universal quantification — entails the conjunction
inference (27a) ⊨ (27b) ∧ (27c). The Lean witness below uses
`sdaEval_iff_forall` from the [santorio-2018] substrate. -/

/-- **Conjunction inference** (eqn 27 p. 218): a disjunctive `would`-
    counterfactual entails each per-disjunct counterfactual. This is
    the SDA validity that [alonso-ovalle-2009]'s analysis
    derives from universal force over alternatives. Consequence of
    `sdaEval_iff_forall`. -/
theorem ao_conjunction_inference {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : Finset W) (C : W → Prop) [DecidablePred C] (w : W)
    (h : aoConditional sim (aoAlternatives A B) C w) :
    universalCounterfactual sim (· ∈ A) C w ∧ universalCounterfactual sim (· ∈ B) C w :=
  ⟨h A (by simp [aoAlternatives]), h B (by simp [aoAlternatives])⟩


/-! ## §1 The divergence: Boolean `or` (`Coordinator.op .disj`) is the wrong meaning

The Coordinator API's disjunction `Coordinator.op .disj` is the Boolean join `⊔` — at the
proposition carrier `CropWorld → Prop`, exactly the *union* `goodWeather ∨ sunCold` whose
minimal-change reading [alonso-ovalle-2009] (p. 208–210, the bumper-crop counterfactual)
refutes. So feeding `op .disj` to a counterfactual antecedent overgenerates: it collapses the
disjuncts into one proposition, predicting the disjunctive counterfactual TRUE, where the
alternative-semantics reading (disjuncts kept as a *set*) correctly predicts FALSE. This is
the disjunction analogue of the [champollion-2016-coordination] `and`-overgeneration: `op` is
faithful at the Boolean carrier, but the rival construal the data demands diverges from it. -/

/-- `Coordinator.op .disj` at the proposition carrier IS the Boolean union of the disjuncts —
    the [lewis-1973] reading [alonso-ovalle-2009] refutes (eqn 6, p. 209). -/
theorem op_disj_eq_union :
    (Coordinator.op .disj goodWeather sunCold : CropWorld → Prop)
      = (fun w => goodWeather w ∨ sunCold w) := rfl

/-- **The payoff** ([alonso-ovalle-2009] §1, p. 208–210): the Boolean disjunction
    `Coordinator.op .disj` (= the union `goodWeather ⊔ sunCold`, `op_disj_eq_union`) fed to the
    minimal-change conditional **overgenerates** — it predicts *"if good weather or the sun grew
    cold, we'd have a bumper crop"* TRUE (`bumperCrop_lewis_true`: the closest union-world is a
    good-weather world), whereas the alternative-semantics reading (disjuncts kept as a *set*)
    correctly predicts it FALSE (the cold-sun alternative gives no crop). So `op .disj` is NOT
    the meaning of `or` in a disjunctive antecedent: the alternatives must stay separate. -/
theorem op_disj_overgenerates_disjunctive_counterfactual :
    universalCounterfactual cropSim (fun w => goodWeather w ∨ sunCold w) bumperCrop .actual ∧
    ¬ aoConditional cropSim
      (aoAlternatives (Finset.univ.filter goodWeather) (Finset.univ.filter sunCold))
      bumperCrop .actual := by
  refine ⟨bumperCrop_lewis_true, fun h => ?_⟩
  have ⟨h₁, h₂⟩ := ao_conjunction_inference cropSim _ _ bumperCrop .actual h
  exact bumperCrop_conjunction_false
    ⟨(universalCounterfactual_mem_filter _ _ _ _).1 h₁,
     (universalCounterfactual_mem_filter _ _ _ _).1 h₂⟩

end AlonsoOvalle2009
