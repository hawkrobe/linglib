import Linglib.Phenomena.Conditionals.Studies.Santorio2018

/-!
# Alonso-Ovalle 2009 — "Counterfactuals, correlatives, and disjunction"
@cite{alonso-ovalle-2009}

*Linguistics and Philosophy* 32(2): 207–244.

## Core proposal

The natural interpretation of disjunctive counterfactuals — "if A or B,
would C" — selects from each disjunct's closest worlds, NOT from the
union's closest worlds. @cite{alonso-ovalle-2009} (p. 207) refutes
@cite{lewis-1973}'s standard minimal-change semantics on this reading
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
consequent. **This is structurally @cite{santorio-2018}'s `sdaEval`** —
universal-over-per-alternative-conditionals (Simplification reading).

## Connection to linglib substrate

`aoConditional` IS @cite{santorio-2018}'s `sdaEval`
(`Phenomena/Conditionals/Studies/Santorio2018.lean`); the bridge is
`rfl`. The frameworks DIFFER in their treatment of the **alternative
set**, not the per-alternative evaluation:

- @cite{alonso-ovalle-2009} (Hamblin Or Rule, eqn 13 p. 213): alts =
  `{⟦disjunct₁⟧, ⟦disjunct₂⟧, ...}` — only the disjuncts themselves.
- @cite{santorio-2018} (Katzir-generated ALT_S + stability algorithm):
  alts include the disjuncts + their conjunction + their disjunction;
  truthmakers are minimal-stable subsets, which can include "mixed"
  truthmakers @cite{alonso-ovalle-2009} cannot generate.

The differential prediction lives in @cite{santorio-2018} §IV.3
(Karenina/W&P 8-alternative example) and is proved as
`santorio_finds_mixed_truthmaker_ao_misses_it` in that file.
-/

namespace Phenomena.Conditionals.Studies.AlonsoOvalle2009

open Core.Order (SimilarityOrdering)
open Semantics.Conditionals.Counterfactual (universalCounterfactual)
open Phenomena.Conditionals.Studies.Santorio2018 (DecAlt sdaEval sdaEval_iff_forall)


/-! ## §1 The bumper crop scenario (p. 208)

Same scenario as @cite{mckay-vaninwagen-1977} (a variation of Nute
1975): "If we had had good weather this summer or the sun had grown
cold, we would have had a bumper crop." Standard minimal-change with
Boolean `or` predicts TRUE; intuition says FALSE. Worlds and
similarity ordering already formalised in
`Studies/McKayVanInwagen1977.lean::cropSim` and consumed via the
substrate. -/


/-! ## §2.1–2.2 The analysis -/

/-- @cite{alonso-ovalle-2009} **conditional verdict** for a disjunctive
    antecedent (eqn 25–26 p. 217): every disjunct alternative's
    closest worlds satisfy the consequent.

    Definitionally equal to @cite{santorio-2018}'s `sdaEval` — the
    Simplification reading. The two accounts diverge in how the
    alternative SET is generated (see module docstring), not in this
    per-alternative evaluation rule. -/
def aoConditional {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (alts : List (DecAlt W))
    (C : W → Prop) [DecidablePred C] (w : W) : Prop :=
  sdaEval sim alts C w

/-- **Bridge: AO = Santorio's `sdaEval`.** Definitionally equal; the
    two formalisations of the per-alternative-conditional reading
    coincide. The substantive difference between
    @cite{alonso-ovalle-2009} and @cite{santorio-2018} is the
    alternative-set construction, not this evaluation rule. -/
theorem aoConditional_eq_sdaEval {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (alts : List (DecAlt W))
    (C : W → Prop) [DecidablePred C] (w : W) :
    aoConditional sim alts C w = sdaEval sim alts C w := rfl

/-- **Disjunct-only alternative set construction** (Hamblin Or Rule,
    eqn 13 p. 213). For a disjunctive antecedent `A or B`,
    @cite{alonso-ovalle-2009}'s alternative set is exactly
    `[⟨A, _⟩, ⟨B, _⟩]` — the two disjunct denotations bundled with
    decidability. No conjunction, no disjunctive closure, no
    Katzir-generated structural alternatives. This is the locality
    @cite{santorio-2018} §III argues against. -/
def aoAlternatives {W : Type*}
    (A B : W → Prop) [DecidablePred A] [DecidablePred B] :
    List (DecAlt W) :=
  [⟨A, inferInstance⟩, ⟨B, inferInstance⟩]


/-! ## §2.2.3 Universal force

The two-component analysis — alternative-generating `or` plus
correlative-style universal quantification — entails the conjunction
inference (27a) ⊨ (27b) ∧ (27c). The Lean witness below uses
`sdaEval_iff_forall` from the @cite{santorio-2018} substrate. -/

/-- **Conjunction inference** (eqn 27 p. 218): a disjunctive `would`-
    counterfactual entails each per-disjunct counterfactual. This is
    the SDA validity that @cite{alonso-ovalle-2009}'s analysis
    derives from universal force over alternatives. Consequence of
    `sdaEval_iff_forall`. -/
theorem ao_conjunction_inference {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (C : W → Prop) [DecidablePred C]
    (w : W) :
    aoConditional sim (aoAlternatives A B) C w →
    universalCounterfactual sim A C w ∧ universalCounterfactual sim B C w := by
  intro h
  have h' := (sdaEval_iff_forall sim (aoAlternatives A B) C w).mp h
  exact ⟨h' ⟨A, inferInstance⟩ (by simp [aoAlternatives]),
         h' ⟨B, inferInstance⟩ (by simp [aoAlternatives])⟩


end Phenomena.Conditionals.Studies.AlonsoOvalle2009
