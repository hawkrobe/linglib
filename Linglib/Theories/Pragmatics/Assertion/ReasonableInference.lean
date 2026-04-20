import Linglib.Core.Semantics.CommonGround

/-!
# Reasonable Inference @cite{stalnaker-1975}

Stalnaker 1975's Appendix introduces a *pragmatic* notion of inference,
distinct from semantic entailment. The idea: an inference from a sequence
of premise assertions `(P₁, …, Pₙ)` to a conclusion `Q` is *reasonable*
when, in every context in which the premises can appropriately be asserted
in sequence, the resulting context entails `Q`.

The formal apparatus is a triple `(⟦·⟧, A, g)`:

* `⟦P⟧_k`: the proposition expressed by `P` in context `k` (the semantic
  interpretation, here just a `Set W`);
* `A(P, k)`: the **appropriateness** relation — whether asserting `P` in
  context `k` is appropriate;
* `g(P, k) = k ∩ ⟦P⟧_k`: the **change function** — the new context after
  asserting `P`. This is exactly `Core.CommonGround.ContextSet.update`.

This module defines `Appropriateness`, sequential appropriateness `A*`,
sequential update `g*`, and the `reasonableInference` predicate.

Stalnaker's proposal is that **entailment ⊊ reasonable inference** —
inferences like the "direct argument" (A or B; ∴ if not-A, B) are
reasonable without being entailments. The Stalnaker1975 study file
exhibits the gap.
-/

namespace Pragmatics.Assertion.ReasonableInference

open Core.CommonGround

/--
**Appropriateness** of a sentence in a context. Stalnaker leaves this
maximally schematic; concrete theories of conditionals, disjunction,
presupposition fill it in. Two universal constraints from the Appendix
are captured below as `compatible_of_appropriate` and the change-function
identity. -/
abbrev Appropriateness (W : Type*) := Set W → ContextSet W → Prop

/--
The **change function** `g(P, k) = k ∩ ⟦P⟧_k`. Already exists as
`ContextSet.update`; this is the Stalnakerian alias. -/
def changeFn {W : Type*} (P : Set W) (k : ContextSet W) : ContextSet W :=
  ContextSet.update k P

/-- Sequential update along a list of asserted sentences. -/
def changeFnSeq {W : Type*} (σ : List (Set W)) (k : ContextSet W) :
    ContextSet W :=
  σ.foldl (λ acc P => changeFn P acc) k

/-- Sequential appropriateness: each `Pᵢ` is appropriate in the context
    obtained by updating with `P₁, …, Pᵢ₋₁`. Stalnaker's `A(σ, k) = ⋀ᵢ
    A(Pᵢ, kᵢ)`. -/
def appropriateSeq {W : Type*} (A : Appropriateness W)
    (σ : List (Set W)) (k : ContextSet W) : Prop :=
  match σ with
  | [] => True
  | P :: rest => A P k ∧ appropriateSeq A rest (changeFn P k)

/--
**Reasonable inference** (@cite{stalnaker-1975} Appendix).

`σ ⊨ᵣ Q` (reasonable-in-`A`) iff in every context `k` in which the premise
sequence is appropriate, the post-update context entails the conclusion.

This is **distinct from** `ContextSet.entails (changeFnSeq σ k) ⟦Q⟧` for
*arbitrary* `k`: reasonable inference quantifies only over contexts in
which the premises can be asserted in sequence. The premise filter is
exactly what lets pragmatic information (e.g., the disjunction-
appropriateness condition) feed into the inference. -/
def reasonableInference {W : Type*} (A : Appropriateness W)
    (σ : List (Set W)) (Q : Set W) : Prop :=
  ∀ k : ContextSet W,
    appropriateSeq A σ k →
    ContextSet.entails (changeFnSeq σ k) Q

/-- **Entailment ⇒ reasonable inference** for any appropriateness relation:
    if a single premise semantically entails the conclusion, the inference
    is also reasonable. The converse is the substantive Stalnakerian claim
    and fails — see the direct-argument theorem in Stalnaker1975. -/
theorem entailment_implies_reasonable {W : Type*}
    (A : Appropriateness W) (P Q : Set W)
    (h_ent : ∀ w, P w → Q w) :
    reasonableInference A [P] Q := by
  intro k _h_app w hw
  -- changeFnSeq [P] k = changeFn P k = λ w => k w ∧ P w
  exact h_ent w hw.2

/-- **Empty premise sequence**: a reasonable inference from no premises is
    just universal validity of the conclusion. -/
theorem reasonable_nil {W : Type*} (A : Appropriateness W) (Q : Set W) :
    reasonableInference A [] Q ↔ ∀ w, Q w := by
  unfold reasonableInference changeFnSeq appropriateSeq
  refine ⟨λ h w => h ContextSet.trivial trivial (Set.mem_univ w),
          λ h _ _ _ hw => h _⟩

/-- **Stalnaker's first universal constraint** (@cite{stalnaker-1975}
    Appendix, postulate 1): one cannot appropriately assert a proposition
    in a context incompatible with it. Any concrete `A` should satisfy this. -/
def respectsCompatibility {W : Type*} (A : Appropriateness W) : Prop :=
  ∀ P k, A P k → ContextSet.compatible k P

/-- **Stalnaker's second universal constraint** (@cite{stalnaker-1975}
    Appendix, postulate 2): the change function commutes with the
    interpretation — `g(P, k) = k ∩ ⟦P⟧_k`. This holds by construction
    of `changeFn`. -/
theorem changeFn_eq {W : Type*} (P : Set W) (k : ContextSet W) (w : W) :
    changeFn P k w ↔ k w ∧ P w := by
  unfold changeFn ContextSet.update; rfl

end Pragmatics.Assertion.ReasonableInference
