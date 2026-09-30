module

public import Linglib.Semantics.Presupposition.Context

/-!
# Transparency and local contexts

This file defines [schlenker-2009]'s notions of transparency and local context. A syntactic
environment is represented by the set of functions from the denotation of its gap to the
sentence's truth set, one for each continuation of the string that the theory consults. A
restriction `x` on the gap is transparent in a context set `C` when restricting any denotation of
the gap by `x` changes the sentence's truth value at no world of `C`, for every such function
(`Transparent`). The local context is the least transparent restriction (`IsLocalContext`), and a
presupposition is satisfied when it is entailed by the local context (`Satisfied`).

In the propositional case every environment is truth-functional: the sentence's truth value at a
world depends only on the gap's truth value there (`IsTruthFunctional`). The local context of such
an environment always exists: it is the set of worlds of the context at which the sentence's truth
value depends on the gap for some continuation (`isLocalContext_of_isTruthFunctional`), and a
presupposition is satisfied iff it is transparent (`satisfied_iff_transparent`).

## Main definitions

* `Presupposition.Transparent`: a transparent restriction of a gap.
* `Presupposition.IsLocalContext`: the least transparent restriction.
* `Presupposition.Satisfied`: satisfaction of a presupposition in the local context.

## Main results

* `Presupposition.isLocalContext_of_isTruthFunctional`: local contexts of truth-functional
  environments exist.
* `Presupposition.satisfied_iff_transparent`: for them, satisfaction is transparency.

## Implementation notes

The paper states transparency for strings, quantifying over the expressions that may fill the
gap; here the gap's denotation ranges over the whole type, which is the paper's Expressivity
assumption and the reading that its existence proofs require. The local context is restricted to
the context set, so a world outside it constrains nothing.

## References

* [schlenker-2009]
-/

@[expose] public section

namespace Presupposition

variable {W α : Type*} [SemilatticeInf α]

/-- A restriction `x` on the gap of the environment `env` is transparent in the context `C` when
restricting any denotation `d` of the gap by `x` changes the truth value at no world of `C`, for
every continuation in `env`. -/
def Transparent (C : Set W) (env : Set (α → Set W)) (x : α) : Prop :=
  ∀ f ∈ env, ∀ d : α, ∀ w ∈ C, w ∈ f (x ⊓ d) ↔ w ∈ f d

/-- The local context of the gap of `env` in `C` is its least transparent restriction. -/
def IsLocalContext (C : Set W) (env : Set (α → Set W)) (x : α) : Prop :=
  IsLeast {x | Transparent C env x} x

theorem Transparent.anti {C : Set W} {env env' : Set (α → Set W)} {x : α} (h : env' ⊆ env)
    (hx : Transparent C env x) : Transparent C env' x :=
  fun f hf ↦ hx f (h hf)

/-- Transparency holds in a context iff it holds at each of its worlds. -/
theorem transparent_iff_forall_singleton {C : Set W} {env : Set (α → Set W)} {x : α} :
    Transparent C env x ↔ ∀ w ∈ C, Transparent {w} env x :=
  ⟨fun h w hw f hf d _ hv ↦ hv ▸ h f hf d w hw, fun h f hf d w hw ↦ h w hw f hf d w rfl⟩

theorem IsLocalContext.unique {C : Set W} {env : Set (α → Set W)} {x y : α}
    (hx : IsLocalContext C env x) (hy : IsLocalContext C env y) : x = y :=
  IsLeast.unique hx hy

/-- A presupposition `P` on the gap of `env` is satisfied in `C` when the local context exists
and entails it. -/
def Satisfied (C : Set W) (env : Set (α → Set W)) (P : α) : Prop :=
  ∃ x, IsLocalContext C env x ∧ x ≤ P

theorem satisfied_iff {C : Set W} {env : Set (α → Set W)} {x : α} (h : IsLocalContext C env x)
    (P : α) : Satisfied C env P ↔ x ≤ P :=
  ⟨fun ⟨_, hy, hP⟩ ↦ h.unique hy ▸ hP, fun hP ↦ ⟨x, h, hP⟩⟩

/-! ### Truth-functional environments -/

/-- A continuation is truth-functional when the sentence's truth value at a world depends only on
the gap's truth value there. -/
def IsTruthFunctional (f : Set W → Set W) : Prop :=
  ∀ w d d', (w ∈ d ↔ w ∈ d') → (w ∈ f d ↔ w ∈ f d')

/-- The sentence's truth value at `w` depends on the gap of a continuation. -/
def DependsAt (f : Set W → Set W) (w : W) : Prop := ¬ (w ∈ f Set.univ ↔ w ∈ f ∅)

section TruthFunctional

variable {C x : Set W} {env : Set (Set W → Set W)}

theorem IsTruthFunctional.mem_iff_of_mem {f : Set W → Set W} (hf : IsTruthFunctional f)
    {w : W} {d : Set W} (h : w ∈ d) : w ∈ f d ↔ w ∈ f Set.univ :=
  hf w _ _ (by simp [h])

theorem IsTruthFunctional.mem_iff_of_notMem {f : Set W → Set W} (hf : IsTruthFunctional f)
    {w : W} {d : Set W} (h : w ∉ d) : w ∈ f d ↔ w ∈ f ∅ :=
  hf w _ _ (by simp [h])

/-- A restriction is transparent for truth-functional continuations iff it contains every world of
the context at which the truth value depends on the gap for some continuation. -/
theorem transparent_iff_subset (henv : ∀ f ∈ env, IsTruthFunctional f) :
    Transparent C env x ↔ C ∩ {w | ∃ f ∈ env, DependsAt f w} ⊆ x := by
  refine ⟨fun h w ⟨hw, f, hf, hdep⟩ ↦ by_contra fun hx ↦ hdep ?_, fun h f hf d w hw ↦ ?_⟩
  · exact ((h f hf Set.univ w hw).symm.trans
      ((henv f hf).mem_iff_of_notMem (by simpa using hx)))
  · by_cases hx : w ∈ x
    · exact henv f hf w _ _ (by simp [hx])
    · have hind : w ∈ f Set.univ ↔ w ∈ f ∅ := by
        by_contra hdep; exact hx (h ⟨hw, f, hf, hdep⟩)
      rw [(henv f hf).mem_iff_of_notMem (by simp [hx] : w ∉ x ⊓ d)]
      by_cases hd : w ∈ d
      · rw [(henv f hf).mem_iff_of_mem hd, hind]
      · rw [(henv f hf).mem_iff_of_notMem hd]

/-- The local context of truth-functional continuations exists: it is the set of worlds of the
context at which the truth value depends on the gap for some continuation. -/
theorem isLocalContext_of_isTruthFunctional (henv : ∀ f ∈ env, IsTruthFunctional f) :
    IsLocalContext C env (C ∩ {w | ∃ f ∈ env, DependsAt f w}) :=
  ⟨(transparent_iff_subset henv).2 le_rfl, fun _ hy ↦ (transparent_iff_subset henv).1 hy⟩

/-- For truth-functional continuations, a presupposition is satisfied in its local context iff it
is a transparent restriction. -/
theorem satisfied_iff_transparent (henv : ∀ f ∈ env, IsTruthFunctional f) (P : Set W) :
    Satisfied C env P ↔ Transparent C env P := by
  rw [satisfied_iff (isLocalContext_of_isTruthFunctional henv), transparent_iff_subset henv]

end TruthFunctional

end Presupposition
