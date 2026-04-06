import Mathlib.Init

/-!
# Choice Functions for Indefinite Determiners
@cite{reinhart-1997} @cite{kratzer-1998} @cite{winter-1997}

Choice functions provide an alternative to existential quantification for
the semantics of indefinite NPs. A choice function selects a single
individual from a non-empty set, yielding a referential (type *e*) meaning
for the indefinite DP.

## Motivation

The standard ∃-quantifier analysis of indefinites predicts scope via QR
or alternative mechanisms. Choice functions predict scope via the binding
site of the choice function variable itself:

- **Free CF variable** (Reinhart): existentially closed at any scope site
  → flexible scope (wide, intermediate, narrow)
- **Contextually bound CF** (Kratzer): situation parameter determines
  scope → scope fixed by situation binding

## Application to African Languages

@cite{zimmermann-2008} analyses Hausa *wani/wata* as a standard
∃-quantifier, predicting flexible scope via QR.

@cite{owusu-2022} analyses Akan *bí* as a skolemized choice function
with a situation parameter (`SkolemCF`), explaining why *bí* takes
obligatory wide scope under negation: the choice function is evaluated
relative to the resource situation, which negation cannot shift.
-/

namespace Semantics.Lexical.Determiner.ChoiceFunction

-- ════════════════════════════════════════════════════
-- § 1. Choice Functions
-- ════════════════════════════════════════════════════

/-- A choice function selects an individual from a property.
    @cite{reinhart-1997}: type `⟨⟨e,t⟩, e⟩`. -/
def CF (E : Type*) := (E → Prop) → E

/-- A choice function is **correct** if it always selects a member
    of the input set (when non-empty). -/
def CF.isCorrect {E : Type*} (f : CF E) : Prop :=
  ∀ (P : E → Prop), (∃ x, P x) → P (f P)

/-- An indefinite DP with choice function semantics denotes an
    individual: the result of applying the CF to the NP-property.

    ⟦a/some N⟧^f = f(⟦N⟧) -/
def cfIndefSem {E : Type*} (f : CF E) (nounProp : E → Prop) : E :=
  f nounProp

-- ════════════════════════════════════════════════════
-- § 2. Skolemized Choice Functions
-- ════════════════════════════════════════════════════

/-- A situation-indexed (skolemized) choice function.

    @cite{kratzer-1998}: the CF is parameterized by a situation `s`,
    making the selected individual depend on the evaluation situation.

    ⟦bí⟧ = λs.λP. CH(f_s). f_s(P(s))

    Scope is determined by the binding site of `s`:
    - `s` bound by a higher operator → wide scope
    - `s` bound locally (e.g., under a modal) → narrow scope
    - `s` free (contextually resolved) → specific/wide scope -/
def SkolemCF (S E : Type*) := S → CF E

/-- Apply a skolemized CF at a particular situation. -/
def SkolemCF.apply {S E : Type*} (f : SkolemCF S E)
    (s : S) (nounProp : E → Prop) : E :=
  f s nounProp

/-- A skolemized CF is correct if it is correct at every situation. -/
def SkolemCF.isCorrect {S E : Type*} (f : SkolemCF S E) : Prop :=
  ∀ (s : S), (f s).isCorrect

-- ════════════════════════════════════════════════════
-- § 3. Scope via Situation Binding
-- ════════════════════════════════════════════════════

/-- When the situation variable is bound to the resource situation
    (not shifted by an intensional operator), the CF yields wide scope.

    This is the key structural property that distinguishes CF-based
    indefinites (Akan *bí*) from ∃-based indefinites (Hausa *wani*):
    negation is not an intensional operator, so it cannot shift the
    situation variable, forcing wide scope.

    ⟦¬[bí N VP]⟧ = ¬VP(f_{s₀}(N))  — wide scope: ∃ > ¬
    ⟦¬[wani N VP]⟧ = ¬∃x[N(x) ∧ VP(x)]  — narrow scope: ¬ > ∃ -/
theorem cf_wide_scope_under_negation {E : Type*}
    (f : CF E) (hf : f.isCorrect)
    (N : E → Prop) (VP : E → Prop)
    (hNonEmpty : ∃ x, N x) (hAll : ∀ x, N x → VP x) :
    VP (f N) :=
  hAll (f N) (hf N hNonEmpty)

/-- An ∃-quantifier can take narrow scope under negation:
    ¬∃x[N(x) ∧ VP(x)] is satisfiable even when N is non-empty. -/
theorem exists_narrow_scope_under_negation {E : Type*}
    (N : E → Prop) (VP : E → Prop)
    (hNoMatch : ∀ x, N x → ¬VP x) :
    ¬∃ x, N x ∧ VP x :=
  fun ⟨x, hNx, hVPx⟩ => hNoMatch x hNx hVPx

end Semantics.Lexical.Determiner.ChoiceFunction
