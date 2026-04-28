import Linglib.Theories.Semantics.Modality.Orthologic.Frames
import Linglib.Core.IntensionalLogic.RestrictedModality
import Mathlib.Data.Fintype.Pi

/-!
# Modal Compatibility Frames
@cite{holliday-mandelkern-2024}

Modal extension of compatibility frames. Adds an accessibility relation R
and the box/diamond operators whose ortholattice instance validates
Wittgenstein's Law (`¬A ∩ ◇A = ∅`) for epistemic compatibility frames.

This file is the substrate — only general substrate-level definitions
and theorems live here. Concrete paper instantiations (the Epistemic Scale
over `Poss5`, Wittgenstein-sentence verifications, free-choice / orthomodularity
/ pseudocomplementation failures, level-wise classicality theorems, lifting
from W={0,1}) live in
`Phenomena/Modality/Studies/HollidayMandelkern2024.lean`.

## What's here

- `ModalCompatFrame S`: a compatibility frame plus a reflexive accessibility
  relation R. The paper's full Definition 4.20 also requires R-regularity;
  Definition 4.26 adds Knowability (epistemic compatibility frame). The
  current `ModalCompatFrame` records only the reflexivity condition; the
  stronger conditions are properties verified per-instance.
- `box`, `diamond`: modal operators on `Set S`.
- `T_axiom_general`: factivity of `box` from accessibility reflexivity.

Decidability of `access` is *not* bundled — provide a `DecidableRel`
instance separately (mirrors the `CompatFrame` convention).
-/

namespace Semantics.Modality.Orthologic

-- ════════════════════════════════════════════════════
-- § 1. Epistemic Compatibility Frames
-- ════════════════════════════════════════════════════

/-- A modal compatibility frame: a compatibility frame equipped with an
    accessibility relation R satisfying reflexivity (Definition 4.24).
    The paper's full Definition 4.20 also requires R-regularity; the
    epistemic compatibility frame (Definition 4.26) adds Knowability.
    Per-instance frames may witness all three conditions. -/
structure ModalCompatFrame (S : Type*) extends CompatFrame S where
  access : S → S → Prop
  access_refl : ∀ x, access x x

/-- Box operator: `□A = {x | R(x) ⊆ A}`.
    @cite{holliday-mandelkern-2024} eq. (3). -/
def box {S : Type*} (F : ModalCompatFrame S) (A : Set S) : Set S :=
  { x | ∀ y : S, F.access x y → y ∈ A }

@[simp] theorem mem_box {S : Type*} (F : ModalCompatFrame S) (A : Set S) (x : S) :
    x ∈ box F A ↔ ∀ y : S, F.access x y → y ∈ A := Iff.rfl

instance {S : Type*} [Fintype S] (F : ModalCompatFrame S) [DecidableRel F.access]
    (A : Set S) [DecidablePred (· ∈ A)] (x : S) : Decidable (x ∈ box F A) := by
  show Decidable (∀ y : S, F.access x y → y ∈ A); infer_instance

instance box_apply_decidable {S : Type*} [Fintype S] (F : ModalCompatFrame S)
    [DecidableRel F.access] (A : Set S) [DecidablePred A] (x : S) :
    Decidable (box F A x) := by
  show Decidable (∀ y : S, F.access x y → y ∈ A)
  have : DecidablePred (· ∈ A) := inferInstanceAs (DecidablePred A)
  infer_instance

/-- Diamond operator: `◇A = ¬□¬A` (via orthocomplement, NOT Boolean dual).
    @cite{holliday-mandelkern-2024} eq. (4). -/
def diamond {S : Type*} (F : ModalCompatFrame S) (A : Set S) : Set S :=
  orthoNeg F.toCompatFrame (box F (orthoNeg F.toCompatFrame A))

instance {S : Type*} [Fintype S] (F : ModalCompatFrame S)
    [DecidableRel F.toCompatFrame.compat] [DecidableRel F.access]
    (A : Set S) [DecidablePred (· ∈ A)] (x : S) :
    Decidable (x ∈ diamond F A) := by
  unfold diamond; infer_instance

instance diamond_apply_decidable {S : Type*} [Fintype S] (F : ModalCompatFrame S)
    [DecidableRel F.toCompatFrame.compat] [DecidableRel F.access]
    (A : Set S) [DecidablePred A] (x : S) :
    Decidable (diamond F A x) := by
  unfold diamond
  have : DecidablePred (· ∈ A) := inferInstanceAs (DecidablePred A)
  exact orthoNeg_apply_decidable _ _ _

-- ════════════════════════════════════════════════════
-- § 2. T Axiom for Reflexive Frames
-- ════════════════════════════════════════════════════

/-- The T axiom for modal compatibility frames: reflexive accessibility
    means every world accesses itself, so `□A` at x forces A at x.
    @cite{holliday-mandelkern-2024} Proposition 4.25. -/
theorem T_axiom_general {S : Type*}
    (F : ModalCompatFrame S) (A : Set S) (x : S)
    (h : x ∈ box F A) : x ∈ A :=
  h x (F.access_refl x)

end Semantics.Modality.Orthologic
