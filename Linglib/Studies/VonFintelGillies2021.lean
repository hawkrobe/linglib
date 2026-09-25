module

public import Linglib.Studies.VonFintelGillies2010
public import Linglib.Data.Examples.VonFintelGillies2021

/-!
# von Fintel & Gillies (2021): Still Going Strong

This file formalizes [von-fintel-gillies-2021]'s return to the strong *must* of
[von-fintel-gillies-2010]. Two observations about epistemic *can't* pose a dilemma for the
Mantra: *can't* patterns with *must* in its evidential distribution (Observation 4), and
*can't φ* is incompatible with *it's possible that φ* (Observation 5), so *can't* can be the
negation neither of a strong nor of a weak existential modal. Kernel semantics resolves the
dilemma: *can't φ* is *must* of the negation, so its evidential signal is that of *must*, and
its assertion, that the modal base excludes `φ`, contradicts *might φ* and under a realistic
base entails the negation of the prejacent, the thesis S2. On the worked kernel of the earlier
paper *can't not-blue* is defined, true, and excludes *might not-blue* at once, the joint
profile the Mantra cannot assign (`cant_dilemma_resolved`), and direct information that settles
the prejacent gives *can't* presupposition failure as it does *must*. The anti-knowledge
examples of §4.2, Phil who checked dinner himself against Meryl who followed instructions (24)
and (25), are the rows of `Data.Examples.VonFintelGillies2021`.

## References

* [von-fintel-gillies-2021]
* [von-fintel-gillies-2010]
-/

@[expose] public section

namespace VonFintelGillies2021

/-! ### The can't dilemma (§4.1, Observations 4 and 5)

The Mantra faces a dilemma: no assignment of force to *can't* simultaneously
explains its evidential distribution (Observation 4: *can't* patterns like
*must*) and its incompatibility with *it's possible that φ* (Observation 5).
Kernel semantics resolves this: *can't φ* = *must*(¬φ) by definition
(`kernelCant`), so Observation 4's evidential parallelism holds by
construction, while the strong assertion B_K ⊆ ⟦¬φ⟧ delivers Observation 5. -/

open Modality VonFintelGillies2010

variable {W : Type*} (k : Kernel W) (φ : W → Prop) (w : W)

/-- When can't `φ` holds (`B_K ⊆ ⟦¬φ⟧`), might `φ` is false
(Observation 5). -/
theorem cant_might_exclusion (hCant : (kernelCant k φ).assertion w) :
    ¬(kernelMight k φ).assertion w := by
  intro hc
  obtain ⟨w', hw', hφ⟩ := (Kernel.compatibleWith_iff _ _).mp hc
  exact hCant hw' hφ

/-- When `B_K` is realistic and can't `φ` holds, `¬φ` holds
(S2). -/
theorem cant_entails_negation (hReal : w ∈ k.base)
    (hTrue : (kernelCant k φ).assertion w) :
    ¬ φ w :=
  hTrue hReal

/-- A single kernel simultaneously exhibits evidentiality, strength, and
might-exclusion: over `mastermindK`, can't *notBlue* is defined, true, and
excludes might *notBlue* — the joint profile the Mantra cannot assign. -/
theorem cant_dilemma_resolved :
    .w1 ∈ mastermindK.base ∧
    (kernelCant mastermindK notBlue).presup .w1 ∧
    (kernelCant mastermindK notBlue).assertion .w1 ∧
    ¬(kernelMight mastermindK notBlue).assertion .w1 ∧
    ¬ notBlue .w1 := by
  refine ⟨by rw [mastermind_base]; rfl, ?_, ?_, ?_, by decide⟩
  · rintro ⟨x, hx, hxor⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases hxor with h_sub | h_disj
      · exact h_sub (show redOrBlue .w0 from by decide) (by decide)
      · exact Set.disjoint_left.mp h_disj (show redOrBlue .w1 from by decide)
          (show ¬ notBlue .w1 from by decide)
    · rcases List.mem_singleton.mp hx' with rfl
      rcases hxor with h_sub | h_disj
      · exact h_sub (show notRed .w2 from by decide) (by decide)
      · exact Set.disjoint_left.mp h_disj (show notRed .w1 from by decide)
          (show ¬ notBlue .w1 from by decide)
  · rw [show (kernelCant mastermindK notBlue).assertion .w1 =
        mastermindK.FollowsFrom (λ w => ¬ notBlue w) from rfl,
      Kernel.followsFrom_iff, mastermind_base]
    rintro w rfl
    decide
  · intro hc
    obtain ⟨w, hw, hnb⟩ := (Kernel.compatibleWith_iff _ _).mp hc
    rw [mastermind_base] at hw
    rcases hw with rfl
    exact (by decide : ¬ notBlue World.w1) hnb

/-- Direct evidence blocks can't, paralleling must: when `K` settles `¬φ`,
can't `φ` has presupposition failure. -/
theorem cant_direct_evidence_infelicity :
    ¬(kernelCant mastermindK red).presup .w0 := λ h =>
  h ⟨notRed, by simp [mastermindK], Or.inl λ _ hw => hw⟩

end VonFintelGillies2021
