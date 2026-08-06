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
- `directlySettlesExplicit`: Implementation 1 — some `X ∈ K` entails or
  excludes the prejacent
- `explicit_implies_entailment`: settling implies entailment; the converse
  fails, which is what makes the presupposition non-trivial
- `kernelMust`, `kernelMight`, `kernelCant`: the presuppositional operators
  (Defs 5–6), as `PartialProp`s
- `kernelMust_eq_simpleNecessity`, `kernelMust_eq_necessity`: the assertion of
  `kernelMust` is Kratzer necessity over the induced modal base
-/

namespace Modality

open Semantics.Modality.Kratzer
open Semantics.Presupposition
open Intensional.Premise

variable {W : Type*}

/-! ### Kernel structure ([von-fintel-gillies-2010] Def 4) -/

/-- A kernel ([von-fintel-gillies-2010] Def 4): the set of direct-information
    propositions `K`, determining the modal base `B_K = ⋂K` (`Kernel.base`). -/
structure Kernel (W : Type*) where
  /-- The direct-information propositions K. -/
  props : List (W → Prop)

variable (k : Kernel W) (φ : W → Prop) (w : W)

namespace Kernel

/-- The modal base determined by the kernel: B_K = ⋂K (Def 4(ii)). -/
def base : Set W :=
  propIntersection k.props

/-- Convert to a context-independent modal base. -/
def toModalBase : ModalBase W :=
  λ _ => k.props

/-- Consistency: B_K ≠ ∅. -/
def isConsistent : Prop :=
  Semantics.Modality.Kratzer.isConsistent k.props

/-- φ follows from K iff B_K ⊆ ⟦φ⟧. -/
def followsFrom : Prop :=
  Semantics.Modality.Kratzer.followsFrom φ k.props

/-- φ is compatible with K iff B_K ∩ ⟦φ⟧ ≠ ∅. -/
def compatibleWith : Prop :=
  isCompatibleWith φ k.props

/-- Induce an `EpistemicFlavor` for Kratzer modal evaluation. -/
def toEpistemicFlavor : EpistemicFlavor W where
  evidence := k.toModalBase
  ordering := emptyBackground

theorem followsFrom_iff : k.followsFrom φ ↔ ∀ w ∈ k.base, φ w := Iff.rfl

theorem compatibleWith_iff : k.compatibleWith φ ↔ ∃ w ∈ k.base, φ w :=
  isCompatibleWith_iff_exists

end Kernel

/-! ### Settling ([von-fintel-gillies-2010] §7.1, Implementation 1) -/

/-- K directly settles P iff some X ∈ K entails P or is incompatible with P
([von-fintel-gillies-2010] Implementation 1, "Explicit Representation"). -/
def directlySettlesExplicit : Prop :=
  ∃ x ∈ k.props,
    (∀ w ∈ propExtension x, φ w) ∨ (¬ ∃ w ∈ propExtension x, φ w)

/-- Settling implies entailment: if K directly settles φ, then B_K ⊆ ⟦φ⟧ or
    B_K ⊆ ⟦¬φ⟧. If X ∈ K entails φ then B_K ⊆ X ⊆ ⟦φ⟧; if X excludes φ then
    B_K ⊆ X ⊆ ⟦¬φ⟧. The converse fails (see
    `VonFintelGillies2010.entailment_settling_gap`). -/
theorem explicit_implies_entailment (h : directlySettlesExplicit k φ) :
    k.followsFrom φ ∨ k.followsFrom (λ w' => ¬ φ w') := by
  obtain ⟨x, hx_mem, h_ent | h_exc⟩ := h
  · exact Or.inl λ w' hw' =>
      h_ent w' (propIntersection_subset_propExtension hx_mem hw')
  · exact Or.inr λ w' hw' hφ =>
      h_exc ⟨w', propIntersection_subset_propExtension hx_mem hw', hφ⟩

/-- Settling is monotone: more propositions in K means more is settled. -/
theorem settling_monotone (p : W → Prop)
    (hSettled : directlySettlesExplicit k φ) :
    directlySettlesExplicit ⟨p :: k.props⟩ φ := by
  obtain ⟨x, hx_mem, hx⟩ := hSettled
  exact ⟨x, List.mem_cons_of_mem _ hx_mem, hx⟩

/-! ### Modal operators ([von-fintel-gillies-2010] Defs 5–6) -/

/-- ⟦must φ⟧: presupposes K doesn't settle φ; asserts B_K ⊆ ⟦φ⟧. -/
def kernelMust : PartialProp W where
  presup := λ _ => ¬ directlySettlesExplicit k φ
  assertion := λ _ => k.followsFrom φ

/-- ⟦might φ⟧: presupposes K doesn't settle φ; asserts B_K ∩ ⟦φ⟧ ≠ ∅. -/
def kernelMight : PartialProp W where
  presup := λ _ => ¬ directlySettlesExplicit k φ
  assertion := λ _ => k.compatibleWith φ

/-- ⟦can't φ⟧ = must(¬φ). -/
def kernelCant : PartialProp W :=
  kernelMust k (λ w' => ¬ φ w')

/-! ### Core properties -/

/-- T axiom: must φ entails φ when B_K is realistic (w ∈ B_K). -/
theorem must_entails_prejacent (hReal : w ∈ k.base)
    (_hDef : (kernelMust k φ).presup w)
    (hTrue : (kernelMust k φ).assertion w) :
    φ w :=
  hTrue hReal

/-- Duality: might φ ↔ ¬(must ¬φ) in assertion content. -/
theorem kernel_duality :
    (kernelMight k φ).assertion w ↔ ¬(kernelMust k (λ w' => ¬ φ w')).assertion w :=
  isCompatibleWith_iff_not_followsFrom_not

/-- Empty kernel: nothing is settled, so must is always defined. -/
theorem empty_kernel_always_defined :
    (kernelMust ⟨[]⟩ φ).presup w := by
  show ¬ directlySettlesExplicit _ _
  simp [directlySettlesExplicit]

/-- Direct evidence infelicity: when K settles φ, must φ is undefined. -/
theorem direct_evidence_infelicity (hSettled : directlySettlesExplicit k φ) :
    ¬(kernelMust k φ).presup w := by
  intro h; exact h hSettled

/-! ### Bridge to Kratzer necessity -/

/-- Kernel must assertion ↔ Kratzer simple necessity. -/
theorem kernelMust_eq_simpleNecessity :
    (kernelMust k φ).assertion w ↔
      simpleNecessity k.toModalBase φ w := by
  show k.followsFrom φ ↔ _
  simp only [Kernel.followsFrom, Semantics.Modality.Kratzer.followsFrom,
             simpleNecessity_iff_all, accessibleWorlds, Kernel.toModalBase]
  rfl

/-- Kernel must assertion ↔ full Kratzer necessity with empty ordering. -/
theorem kernelMust_eq_necessity :
    (kernelMust k φ).assertion w ↔
      necessity k.toModalBase emptyBackground φ w := by
  rw [kernelMust_eq_simpleNecessity]
  exact (necessity_empty_iff_simple k.toModalBase _ w).symm

end Modality
