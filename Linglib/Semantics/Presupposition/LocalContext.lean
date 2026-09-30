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
world depends only on the gap's truth value there (`truthFunctional`). The local context of such an
environment always exists: it is the set of worlds of the context at which some continuation
depends on the gap (`isLocalContext_truthFunctional`).

## Main definitions

* `Presupposition.Transparent`: a transparent restriction of a gap.
* `Presupposition.IsLocalContext`: the least transparent restriction.
* `Presupposition.Satisfied`: satisfaction of a presupposition in the local context.

## Main results

* `Presupposition.isLocalContext_truthFunctional`: local contexts of truth-functional
  environments exist.

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

/-- The presupposition of `p` in the gap of `env` is satisfied in `C` when the local context
exists and entails it. -/
def Satisfied (C : Set W) (env : Set (Set W → Set W)) (p : PartialProp W) : Prop :=
  ∃ x, IsLocalContext C env x ∧ p.Admits x

theorem satisfied_iff {C x : Set W} {env : Set (Set W → Set W)} (h : IsLocalContext C env x)
    (p : PartialProp W) : Satisfied C env p ↔ p.Admits x :=
  ⟨fun ⟨_, hy, hp⟩ ↦ h.unique hy ▸ hp, fun hp ↦ ⟨x, h, hp⟩⟩

/-! ### Truth-functional environments -/

/-- A continuation is truth-functional when the sentence's truth value at a world depends only on
the gap's truth value there. -/
def IsTruthFunctional (f : Set W → Set W) : Prop :=
  ∀ w d d', (w ∈ d ↔ w ∈ d') → (w ∈ f d ↔ w ∈ f d')

/-- The gap of a continuation is live at `w` when the sentence's truth value there depends on
it. -/
def IsLive (f : Set W → Set W) (w : W) : Prop := ¬ (w ∈ f Set.univ ↔ w ∈ f ∅)

section TruthFunctional

variable {C x : Set W} {env : Set (Set W → Set W)}

theorem IsTruthFunctional.mem_iff_of_mem {f : Set W → Set W} (hf : IsTruthFunctional f)
    {w : W} {d : Set W} (h : w ∈ d) : w ∈ f d ↔ w ∈ f Set.univ :=
  hf w _ _ (by simp [h])

theorem IsTruthFunctional.mem_iff_of_notMem {f : Set W → Set W} (hf : IsTruthFunctional f)
    {w : W} {d : Set W} (h : w ∉ d) : w ∈ f d ↔ w ∈ f ∅ :=
  hf w _ _ (by simp [h])

/-- A restriction is transparent for truth-functional continuations iff it contains every world of
the context at which some continuation is live. -/
theorem transparent_iff_subset (henv : ∀ f ∈ env, IsTruthFunctional f) :
    Transparent C env x ↔ C ∩ {w | ∃ f ∈ env, IsLive f w} ⊆ x := by
  refine ⟨fun h w ⟨hw, f, hf, hlive⟩ ↦ by_contra fun hx ↦ hlive ?_, fun h f hf d w hw ↦ ?_⟩
  · exact ((h f hf Set.univ w hw).symm.trans
      ((henv f hf).mem_iff_of_notMem (by simpa using hx)))
  · by_cases hx : w ∈ x
    · exact henv f hf w _ _ (by simp [hx])
    · have hdead : w ∈ f Set.univ ↔ w ∈ f ∅ := by
        by_contra hlive; exact hx (h ⟨hw, f, hf, hlive⟩)
      rw [(henv f hf).mem_iff_of_notMem (by simp [hx] : w ∉ x ⊓ d)]
      by_cases hd : w ∈ d
      · rw [(henv f hf).mem_iff_of_mem hd, hdead]
      · rw [(henv f hf).mem_iff_of_notMem hd]

/-- The local context of truth-functional continuations exists: it is the set of worlds of the
context at which some continuation is live. -/
theorem isLocalContext_of_isTruthFunctional (henv : ∀ f ∈ env, IsTruthFunctional f) :
    IsLocalContext C env (C ∩ {w | ∃ f ∈ env, IsLive f w}) :=
  ⟨(transparent_iff_subset henv).2 le_rfl, fun _ hy ↦ (transparent_iff_subset henv).1 hy⟩

/-- For truth-functional continuations, a presupposition is satisfied in its local context iff it
is a transparent restriction. -/
theorem satisfied_iff_transparent (henv : ∀ f ∈ env, IsTruthFunctional f) (p : PartialProp W) :
    Satisfied C env p ↔ Transparent C env p.presup := by
  rw [satisfied_iff (isLocalContext_of_isTruthFunctional henv), transparent_iff_subset henv]

end TruthFunctional

/-- A truth-functional continuation computes the sentence's truth value at each world from the
gap's truth value at that world. -/
def truthFunctional (φ : W → Prop → Prop) : Set W → Set W := fun d ↦ {w | φ w (w ∈ d)}

/-- The local context of a truth-functional environment always exists: it is the set of context
worlds at which some continuation depends on the gap's truth value. -/
theorem isLocalContext_truthFunctional (C : Set W) (Φ : Set (W → Prop → Prop)) :
    IsLocalContext C (truthFunctional '' Φ)
      (C ∩ {w | ∃ φ ∈ Φ, ¬ (φ w True ↔ φ w False)}) := by
  constructor
  · rintro _ ⟨φ, hφ, rfl⟩ d w hw
    by_cases hx : ∃ φ ∈ Φ, ¬ (φ w True ↔ φ w False)
    · simp [truthFunctional, hw, hx]
    · have hφw : φ w True ↔ φ w False := by
        by_contra h
        exact hx ⟨φ, hφ, h⟩
      by_cases hd : w ∈ d <;> simp [truthFunctional, hd, hx, hφw]
  · rintro x hx w ⟨hw, φ, hφ, hφw⟩
    by_contra hwx
    have h := hx _ ⟨φ, hφ, rfl⟩ Set.univ w hw
    simp [truthFunctional, hwx] at h
    exact hφw h.symm

/-- When some continuation depends on the gap at every context world, the local context is the
global context. -/
theorem isLocalContext_of_forall (C : Set W) (Φ : Set (W → Prop → Prop))
    (h : C ⊆ {w | ∃ φ ∈ Φ, ¬ (φ w True ↔ φ w False)}) :
    IsLocalContext C (truthFunctional '' Φ) C := by
  have := isLocalContext_truthFunctional C Φ
  rwa [Set.inter_eq_left.2 h] at this

end Presupposition
