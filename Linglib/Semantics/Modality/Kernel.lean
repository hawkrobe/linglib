import Linglib.Semantics.Modality.Kratzer.Flavor
import Linglib.Semantics.Presupposition.Basic

/-!
# Kernel Semantics for Epistemic Modals

[von-fintel-gillies-2010]'s kernel semantics: epistemic modals carry an
evidential presupposition that the prejacent is not *directly settled* by the
kernel `K` — the privileged direct-information part of the modal base
(Def 4: `B_K = ⋂K`). The presupposition makes *must φ* strong (it asserts
`B_K ⊆ ⟦φ⟧`, Def 5) while still signalling indirectness: `B_K` can entail
`φ` without `K` directly settling it.

This file provides the reusable kernel apparatus: the `Kernel` structure, the
explicit-representation implementation of directly-settles (Implementation 1,
§7.1), the presuppositional operators `kernelMust`/`kernelMight`/`kernelCant`,
and bridges to Kratzer necessity. The paper's second, partition-based
implementation (Def 7, §7.2), the non-equivalence of the two implementations,
and the worked examples live in `Studies/VonFintelGillies2010.lean`; the
*can't* dilemma of [von-fintel-gillies-2021] lives in
`Studies/VonFintelGillies2021.lean`; the nandao-Q felicity conditions built on
this apparatus live in `Studies/Zheng2025.lean`.

## Main declarations

- `Kernel`: direct-information propositions with their modal base `B_K = ⋂K`,
  entailment (`Kernel.followsFrom`), and compatibility (`Kernel.compatibleWith`)
- `Kernel.directlySettles`: Implementation 1 — some `X ∈ K` entails or
  excludes the prejacent
- `explicit_implies_entailment`: settling implies entailment; the converse
  fails, which is what makes the presupposition non-trivial
- `kernelMust`, `kernelMight`, `kernelCant`: the presuppositional operators
  (Defs 5–6), as `PartialProp`s
- `kernelMust_iff_simpleNecessity`, `kernelMust_iff_necessity`: the assertion
  of `kernelMust` is Kratzer necessity over the induced modal base
-/

namespace Modality

open Semantics.Modality.Kratzer
open Semantics.Presupposition
open Intensional.Premise

variable {W : Type*}

/-! ### Kernel structure ([von-fintel-gillies-2010] Def 4) -/

/-- A *kernel* is a set of direct-information propositions, determining the
    modal base `B_K = ⋂K` ([von-fintel-gillies-2010] Def 4). -/
structure Kernel (W : Type*) where
  /-- The direct-information propositions K. -/
  props : List (W → Prop)

variable (k : Kernel W) (φ : W → Prop) (w : W)

namespace Kernel

/-- The modal base `B_K = ⋂K` determined by the kernel. -/
def base : Set W :=
  propIntersection k.props

/-- The kernel as a context-independent modal base. -/
def toModalBase : ModalBase W :=
  λ _ => k.props

/-- `K` is consistent iff `B_K ≠ ∅`. -/
def isConsistent : Prop :=
  Semantics.Modality.Kratzer.isConsistent k.props

/-- `φ` follows from `K` iff `B_K ⊆ ⟦φ⟧`. -/
def followsFrom : Prop :=
  Semantics.Modality.Kratzer.followsFrom φ k.props

/-- `φ` is compatible with `K` iff `B_K ∩ ⟦φ⟧ ≠ ∅`. -/
def compatibleWith : Prop :=
  isCompatibleWith φ k.props

/-- The `EpistemicFlavor` with the kernel's modal base and empty ordering. -/
def toEpistemicFlavor : EpistemicFlavor W where
  evidence := k.toModalBase
  ordering := emptyBackground

theorem followsFrom_iff : k.followsFrom φ ↔ ∀ w ∈ k.base, φ w := Iff.rfl

theorem compatibleWith_iff : k.compatibleWith φ ↔ ∃ w ∈ k.base, φ w :=
  isCompatibleWith_iff_exists

end Kernel

/-! ### Settling ([von-fintel-gillies-2010] §7.1, Implementation 1) -/

/-- K directly settles P iff some X ∈ K entails P or is incompatible with P. -/
def Kernel.directlySettles : Prop :=
  ∃ x ∈ k.props,
    propExtension x ⊆ propExtension φ ∨ Disjoint (propExtension x) (propExtension φ)

/-- If `K` directly settles `φ` then `B_K ⊆ ⟦φ⟧` or `B_K ⊆ ⟦¬φ⟧`; the
    converse fails (see `VonFintelGillies2010.entailment_settling_gap`). -/
theorem explicit_implies_entailment (h : k.directlySettles φ) :
    k.followsFrom φ ∨ k.followsFrom (λ w' => ¬ φ w') := by
  obtain ⟨x, hx_mem, h_sub | h_disj⟩ := h
  · exact Or.inl ((propIntersection_subset_propExtension hx_mem).trans h_sub)
  · exact Or.inr ((propIntersection_subset_propExtension hx_mem).trans
      h_disj.subset_compl_right)

theorem Kernel.directlySettles_mono {k' : Kernel W} (hk : k.props ⊆ k'.props)
    (h : k.directlySettles φ) :
    k'.directlySettles φ :=
  h.imp λ _ ⟨hm, hx⟩ => ⟨hk hm, hx⟩

@[simp]
theorem Kernel.base_singleton (p : W → Prop) :
    (⟨[p]⟩ : Kernel W).base = propExtension p :=
  propIntersection_singleton p

@[simp]
theorem Kernel.directlySettles_singleton (p : W → Prop) :
    (⟨[p]⟩ : Kernel W).directlySettles φ ↔
      propExtension p ⊆ propExtension φ ∨
        Disjoint (propExtension p) (propExtension φ) := by
  simp [Kernel.directlySettles]

/-! ### Modal operators ([von-fintel-gillies-2010] Defs 5–6) -/

/-- `⟦must φ⟧` presupposes that `K` does not directly settle `φ` and asserts
    `B_K ⊆ ⟦φ⟧`. -/
def kernelMust : PartialProp W where
  presup := λ _ => ¬ k.directlySettles φ
  assertion := λ _ => k.followsFrom φ

/-- `⟦might φ⟧` presupposes that `K` does not directly settle `φ` and asserts
    `B_K ∩ ⟦φ⟧ ≠ ∅`. -/
def kernelMight : PartialProp W where
  presup := λ _ => ¬ k.directlySettles φ
  assertion := λ _ => k.compatibleWith φ

/-- `⟦can't φ⟧` is `⟦must ¬φ⟧`. -/
def kernelCant : PartialProp W :=
  kernelMust k (λ w' => ¬ φ w')

/-! ### Core properties -/

/-- Must `φ` entails `φ` when `B_K` is realistic (the T axiom). -/
theorem must_entails_prejacent (hReal : w ∈ k.base)
    (hTrue : (kernelMust k φ).assertion w) :
    φ w :=
  hTrue hReal

/-- Might `φ` and `¬must ¬φ` have the same assertion content. -/
theorem kernel_duality :
    (kernelMight k φ).assertion w ↔ ¬(kernelMust k (λ w' => ¬ φ w')).assertion w :=
  isCompatibleWith_iff_not_followsFrom_not

/-- The empty kernel settles nothing, so must is always defined. -/
theorem empty_kernel_always_defined : (kernelMust ⟨[]⟩ φ).presup w :=
  λ ⟨_, hx, _⟩ => List.not_mem_nil hx

/-! ### Bridge to Kratzer necessity -/

/-- The assertion of kernel must is Kratzer simple necessity over the induced
    modal base. -/
theorem kernelMust_iff_simpleNecessity :
    (kernelMust k φ).assertion w ↔ simpleNecessity k.toModalBase φ w :=
  Iff.rfl

/-- The assertion of kernel must is Kratzer necessity with the empty ordering
    source. -/
theorem kernelMust_iff_necessity :
    (kernelMust k φ).assertion w ↔ necessity k.toModalBase emptyBackground φ w :=
  (kernelMust_iff_simpleNecessity k φ w).trans
    (necessity_empty_iff_simple k.toModalBase φ w).symm

end Modality
