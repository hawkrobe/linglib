module

public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Presupposition.Basic

/-!
# Kernel semantics for epistemic modals

Von Fintel and Gillies give epistemic modals an evidential presupposition: the prejacent is not
*directly settled* by the kernel `K`, the direct-information part of the modal base, whose
intersection is the base `B_K`. The presupposition makes *must φ* strong, asserting that `B_K`
entails `φ`, while still signalling indirectness, since `B_K` can entail `φ` without `K`
directly settling it. The partition-based implementation and the worked examples are in
`Studies/VonFintelGillies2010.lean`, the *can't* dilemma in `Studies/VonFintelGillies2021.lean`.

## Main definitions

* `Kernel`: a set of direct-information propositions, with its base `Kernel.base`.
* `Kernel.directlySettles`: some member of the kernel entails or excludes the prejacent.
* `kernelMust`, `kernelMight`, `kernelCant`: the presuppositional operators.

## Main statements

* `explicit_implies_entailment`: direct settling implies entailment, but not conversely.
* `kernelMust_iff_simpleNecessity`: the assertion of `kernelMust` is Kratzer's simple
  necessity over the kernel.

## References

* [von-fintel-gillies-2010]
* [von-fintel-gillies-2021]
-/

@[expose] public section

namespace Modality

open Modality
open Presupposition

variable {W : Type*}

/-! ### Kernel structure ([von-fintel-gillies-2010] Def 4) -/

/-- A *kernel* is a set of direct-information propositions, determining the
    modal base `B_K = ⋂K` ([von-fintel-gillies-2010] Def 4). -/
structure Kernel (W : Type*) where
  /-- The direct-information propositions K. -/
  props : Set (W → Prop)

variable (k : Kernel W) (φ : W → Prop) (w : W)

namespace Kernel

/-- The modal base `B_K = ⋂K` determined by the kernel. -/
def base : Set W := {w | sInf k.props w}

@[simp] theorem mem_base {k : Kernel W} {w : W} : w ∈ k.base ↔ ∀ p ∈ k.props, p w := by
  simp [base]

/-- The kernel as a context-independent modal base. -/
def toConvBackground : ConvBackground W := fun _ ↦ k.props

/-- `K` is consistent iff `B_K ≠ ∅`. -/
def IsConsistent : Prop := k.base.Nonempty

/-- `φ` follows from `K` iff `B_K ⊆ ⟦φ⟧`. -/
def FollowsFrom : Prop := sInf k.props ≤ φ

/-- `φ` is compatible with `K` iff `B_K ∩ ⟦φ⟧ ≠ ∅`. -/
def compatibleWith : Prop := ∃ w ∈ k.base, φ w

theorem followsFrom_iff : k.FollowsFrom φ ↔ ∀ w ∈ k.base, φ w := Iff.rfl

theorem compatibleWith_iff : k.compatibleWith φ ↔ ∃ w ∈ k.base, φ w := Iff.rfl

end Kernel

/-! ### Settling ([von-fintel-gillies-2010] §7.1, Implementation 1) -/

/-- K directly settles P iff some X ∈ K entails P or is incompatible with P. -/
def Kernel.directlySettles : Prop :=
  ∃ x ∈ k.props,
    {w | x w} ⊆ {w | φ w} ∨ Disjoint {w | x w} {w | φ w}

/-- If `K` directly settles `φ` then `B_K ⊆ ⟦φ⟧` or `B_K ⊆ ⟦¬φ⟧`; the
    converse fails (see `VonFintelGillies2010.entailment_settling_gap`). -/
theorem explicit_implies_entailment (h : k.directlySettles φ) :
    k.FollowsFrom φ ∨ k.FollowsFrom (fun w' ↦ ¬ φ w') := by
  obtain ⟨x, hx_mem, h_sub | h_disj⟩ := h
  · exact Or.inl fun w hw ↦ h_sub (sInf_le hx_mem w hw)
  · exact Or.inr fun w hw ↦ h_disj.subset_compl_right (sInf_le hx_mem w hw)

theorem Kernel.directlySettles_mono {k' : Kernel W} (hk : k.props ⊆ k'.props)
    (h : k.directlySettles φ) :
    k'.directlySettles φ :=
  h.imp fun _ ⟨hm, hx⟩ ↦ ⟨hk hm, hx⟩

@[simp]
theorem Kernel.base_singleton (p : W → Prop) :
    (⟨{p}⟩ : Kernel W).base = {w | p w} := by
  ext; simp

@[simp]
theorem Kernel.directlySettles_singleton (p : W → Prop) :
    (⟨{p}⟩ : Kernel W).directlySettles φ ↔
      {w | p w} ⊆ {w | φ w} ∨ Disjoint {w | p w} {w | φ w} := by
  simp [Kernel.directlySettles]

/-! ### Modal operators ([von-fintel-gillies-2010] Defs 5–6) -/

/-- `⟦must φ⟧` presupposes that `K` does not directly settle `φ` and asserts
    `B_K ⊆ ⟦φ⟧`. -/
def kernelMust : PartialProp W where
  presup := fun _ ↦ ¬ k.directlySettles φ
  assertion := fun _ ↦ k.FollowsFrom φ

/-- `⟦might φ⟧` presupposes that `K` does not directly settle `φ` and asserts
    `B_K ∩ ⟦φ⟧ ≠ ∅`. -/
def kernelMight : PartialProp W where
  presup := fun _ ↦ ¬ k.directlySettles φ
  assertion := fun _ ↦ k.compatibleWith φ

/-- `⟦can't φ⟧` is `⟦must ¬φ⟧`. -/
def kernelCant : PartialProp W :=
  kernelMust k (fun w' ↦ ¬ φ w')

/-! ### Core properties -/

/-- Must `φ` entails `φ` when `B_K` is realistic (the T axiom). -/
theorem must_entails_prejacent (hReal : w ∈ k.base)
    (hTrue : (kernelMust k φ).assertion w) :
    φ w :=
  hTrue w hReal

/-- Might `φ` and `¬must ¬φ` have the same assertion content. -/
theorem kernel_duality :
    (kernelMight k φ).assertion w ↔ ¬(kernelMust k (fun w' ↦ ¬ φ w')).assertion w := by
  simp [kernelMight, kernelMust, Kernel.compatibleWith, Kernel.FollowsFrom, Pi.le_def]

/-- The empty kernel settles nothing, so must is always defined. -/
theorem empty_kernel_always_defined : (kernelMust ⟨∅⟩ φ).presup w :=
  fun ⟨_, hx, _⟩ ↦ hx

/-! ### Bridge to Kratzer necessity -/

/-- The assertion of kernel must is Kratzer simple necessity over the induced
    modal base. -/
theorem kernelMust_iff_simpleNecessity :
    (kernelMust k φ).assertion w ↔ simpleNecessity k.toConvBackground φ w :=
  Iff.rfl

/-- The assertion of kernel must is Kratzer necessity with the empty ordering
    source. -/
theorem kernelMust_iff_necessity :
    (kernelMust k φ).assertion w ↔ necessity k.toConvBackground ⊥ φ w :=
  (kernelMust_iff_simpleNecessity k φ w).trans
    (necessity_bot_iff k.toConvBackground φ w).symm

end Modality
