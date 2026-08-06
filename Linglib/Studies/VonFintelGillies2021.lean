import Linglib.Studies.VonFintelGillies2010
import Linglib.Data.Examples.VonFintelGillies2021

/-!
# von Fintel & Gillies (2021): Still Going Strong
[von-fintel-gillies-2021]

Follow-up to [von-fintel-gillies-2010]: the indirectness signal of *must*
is anti-knowledge, not anti-perception — direct-enough *knowledge* blocks
*must* even without perceptual evidence (Phil/Meryl dinner pair) — and
*can't φ* is incompatible with *it's possible that φ* (Observation 5).

## Main declarations

- `evidential_restriction_extends`: the 2010 felicity ↔ indirectness
  biconditional holds on the anti-knowledge rows
- `cant_might_exclusion`: when can't φ holds, might φ is false
  (Observation 5)
- `cant_dilemma_resolved`: a single kernel simultaneously exhibits
  evidentiality, strength, and might-exclusion — the assignment of force
  to *can't* the Mantra cannot deliver
-/

namespace VonFintelGillies2021

open Data.Examples
open VonFintelGillies2010 (evidenceOf EvidenceType)

/-- Rows whose primary text is the modalized member of a bare/modal
    minimal pair. -/
def mustPairs : List LinguisticExample :=
  Examples.all.filter (·.feature? "kind" == some "must_pair")

/-- The evidential restriction extends to rows where "direct" is
    direct-enough knowledge rather than perception: Phil, who checked
    everything himself, cannot say *Dinner must be ready* (ex. 24); Meryl,
    whose information is indirect, can (ex. 25). -/
theorem evidential_restriction_extends :
    ∀ row ∈ mustPairs,
      row.judgment = .acceptable ↔
        (evidenceOf row).map EvidenceType.toCoarseSource ≠ some .direct := by
  decide

/-! ### The can't dilemma ([von-fintel-gillies-2021] §4, Observations 4–5)

The Mantra faces a dilemma: no assignment of force to *can't* simultaneously
explains its evidential distribution (Observation 4: *can't* patterns like
*must*) and its incompatibility with *it's possible that φ* (Observation 5).
Kernel semantics resolves this: *can't φ* = *must*(¬φ) by definition
(`kernelCant`), so Observation 4's evidential parallelism holds by
construction, while the strong assertion B_K ⊆ ⟦¬φ⟧ delivers Observation 5. -/

open Modality
open Intensional.Premise
open VonFintelGillies2010 (World mastermindK redOrBlue notRed blue red notBlue
  mastermind_base)

variable {W : Type*} (k : Kernel W) (φ : W → Prop) (w : W)

/-- When can't `φ` holds (`B_K ⊆ ⟦¬φ⟧`), might `φ` is false
([von-fintel-gillies-2021] Observation 5). -/
theorem cant_might_exclusion (hCant : (kernelCant k φ).assertion w) :
    ¬(kernelMight k φ).assertion w := by
  intro hc
  obtain ⟨w', hw', hφ⟩ := (Kernel.compatibleWith_iff _ _).mp hc
  exact hCant hw' hφ

/-- When `B_K` is realistic and can't `φ` holds, `¬φ` holds
([von-fintel-gillies-2021] via S2). -/
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
        mastermindK.followsFrom (λ w => ¬ notBlue w) from rfl,
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
