import Mathlib.Data.Set.Subsingleton

/-!
# Decided domains: the no-gap / force-collapse boundary

A set `A` is *decided* when all its elements agree on every proposition — that is,
`A.Subsingleton`. This is the boundary at which plural predication over `A` stops
exhibiting a homogeneity gap and at which universal and existential force collapse.
It is the bivalent companion to the trivalent treatment in `Homogeneity.Basic`
(`isBivalent` / `gapExt`).

The point of this file is that one condition on the domain — being a subsingleton —
is the shared structural core of several superficially different phenomena:

* attitude **neg-raising** ([gajewski-2007], [horn-2001]):
  `Semantics/Attitudes/NegRaising.lean`;
* modal **weak necessity** — the comparative ([rubinstein-2014]), homogeneity
  ([agha-jeretic-2022]), and domain-restriction analyses surveyed in
  [agha-jeretic-2026] all reduce their neg-raising prediction to it;
* nominal **plural homogeneity** — the same lemmas instantiated over individuals
  rather than worlds ("Ann didn't eat the cookies" = ate none).

The lemmas are stated over an arbitrary `Set W`, so all three are instances.

## Main results

* `negRaising_iff_subsingleton` — the excluded-middle / neg-raising inference
  `¬□p → □¬p` holds for every `p` iff the domain is decided.
* `forceCollapse_iff_subsingleton` — over a nonempty domain, `□p ↔ ◇p` for every
  `p` iff the domain is decided.
* `negRaising_iff_forceCollapse` — the two faces coincide.
-/

namespace Semantics.Homogeneity

variable {W : Type*}

/-- **Neg-raising face.** A universal modal `∀ w ∈ A, p w` validates the
neg-raising inference `¬□p → □¬p` for *every* prejacent `p` iff its domain `A` is
a subsingleton — all elements of `A` agree on every proposition. -/
theorem negRaising_iff_subsingleton (A : Set W) :
    (∀ p : W → Prop, ¬ (∀ w ∈ A, p w) → ∀ w ∈ A, ¬ p w) ↔ A.Subsingleton := by
  constructor
  · intro hEM a ha b hb
    by_contra hab
    have hnotall : ¬ ∀ w ∈ A, w = a := fun hall => hab (hall b hb).symm
    exact (hEM (· = a) hnotall a ha) rfl
  · intro hsub p hnot w hw hpw
    exact hnot fun v hv => by rw [hsub hv hw]; exact hpw

/-- **Force-collapse face.** Over a nonempty domain, the universal and existential
modal forces coincide (`□p ↔ ◇p` for every prejacent) iff the domain is a
subsingleton — the limit at which a strong/weak (universal/existential) force
distinction ceases to be a difference in force. Fully constructive. -/
theorem forceCollapse_iff_subsingleton {A : Set W} (hne : A.Nonempty) :
    (∀ p : W → Prop, (∀ w ∈ A, p w) ↔ (∃ w ∈ A, p w)) ↔ A.Subsingleton := by
  constructor
  · intro hfc a ha b hb
    exact ((hfc (· = a)).mpr ⟨a, ha, rfl⟩ b hb).symm
  · intro hsub p
    obtain ⟨a, ha⟩ := hne
    refine ⟨fun hall => ⟨a, ha, hall a ha⟩, ?_⟩
    rintro ⟨b, hb, hpb⟩ c hc
    rw [hsub hc hb]
    exact hpb

/-- **The two faces are one.** Over a nonempty domain the neg-raising inference
holds (for every prejacent) iff modal force collapses (`□p ↔ ◇p` for every
prejacent) — both iff the domain is decided. Neg-raising is the symptom of the
universal/existential force distinction collapsing. -/
theorem negRaising_iff_forceCollapse {A : Set W} (hne : A.Nonempty) :
    (∀ p : W → Prop, ¬ (∀ w ∈ A, p w) → ∀ w ∈ A, ¬ p w) ↔
    (∀ p : W → Prop, (∀ w ∈ A, p w) ↔ (∃ w ∈ A, p w)) := by
  rw [negRaising_iff_subsingleton, forceCollapse_iff_subsingleton hne]

/-- **Excluded-middle face.** A universal modal is *opinionated* about every
prejacent (`□p ∨ □¬p` for all `p`) iff its domain is a subsingleton. This is the
form the condition takes as Gajewski's excluded-middle presupposition for
neg-raising ([gajewski-2007]). -/
theorem excludedMiddle_iff_subsingleton (A : Set W) :
    (∀ p : W → Prop, (∀ w ∈ A, p w) ∨ (∀ w ∈ A, ¬ p w)) ↔ A.Subsingleton := by
  constructor
  · intro hem a ha b hb
    rcases hem (· = a) with h | h
    · exact (h b hb).symm
    · exact absurd rfl (h a ha)
  · intro hsub p
    by_cases hp : ∀ w ∈ A, p w
    · exact Or.inl hp
    · exact Or.inr ((negRaising_iff_subsingleton A).mpr hsub p hp)

/-! ### The same core is nominal plural homogeneity

Instantiating the domain at a set of individuals rather than worlds gives the
homogeneity of *nominal* plural predication: "the `cookies` are `p`" is decided —
no gap, force collapsed — iff the set of cookies is a subsingleton. This is
[agha-jeretic-2022]'s point that modal *should* patterns like a plural definite
("Ann didn't eat the cookies" = ate none): the shared fact is one lemma at two
domains (worlds vs individuals). -/
example {α : Type*} (cookies : Set α) (hne : cookies.Nonempty) :
    (∀ p : α → Prop, (∀ c ∈ cookies, p c) ↔ (∃ c ∈ cookies, p c)) ↔
      cookies.Subsingleton :=
  forceCollapse_iff_subsingleton hne

end Semantics.Homogeneity
