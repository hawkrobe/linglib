import Linglib.Theories.Semantics.Modality.Orthologic.Frames
import Linglib.Core.Logic.Intensional.RestrictedModality
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
`Studies/HollidayMandelkern2024.lean`.

## What's here

- `ModalCompatFrame S`: a compatibility frame plus a reflexive accessibility
  relation R. The paper's full Definition 4.20 also requires R-regularity;
  Definition 4.26 adds Knowability (epistemic compatibility frame). The
  current `ModalCompatFrame` records only the reflexivity condition.
- `box`, `diamond`: modal operators on `Set S`.
- `T_axiom_general`: factivity of `box` from accessibility reflexivity.
- `IsRRegular`, `IsKnowable`: per-instance conditions completing
  Definitions 4.20 / 4.26.
- `EpistemicCompatFrame`: bundles `ModalCompatFrame` with `IsRRegular` and
  `IsKnowable` (Definition 4.26).
- `wittgensteinLaw`: Proposition 4.27 — the headline structural theorem.
  In any modal compatibility frame satisfying Knowability,
  `¬A ∩ ◇A = ∅` for every set `A`. The algebraic content of "p and
  might-not-p is contradictory."

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

-- ════════════════════════════════════════════════════
-- § 3. R-Regularity, Knowability, Epistemic Frames
-- ════════════════════════════════════════════════════

/-- R-regularity: if `x R y'` and `y' ◇ y`, then there is some `x'`
    with `x ◇ x'` and some `y'' ◇ x'` refining `y`. Loose reading: "if
    `x` can epistemically access a possibility compatible with `y`, then
    `x` is compatible with a possibility according to which `y` might obtain."
    @cite{holliday-mandelkern-2024} Definition 4.20 / Definition 4.26
    (R-regularity clause), page 866 of the published JPL version. -/
def IsRRegular {S : Type*} (F : ModalCompatFrame S) : Prop :=
  ∀ x y' y : S, F.access x y' → F.toCompatFrame.compat y' y →
    ∃ x' : S, F.toCompatFrame.compat x x' ∧
      ∃ y'' : S, F.toCompatFrame.compat x' y'' ∧
        refines F.toCompatFrame y'' y

instance {S : Type*} [Fintype S] (F : ModalCompatFrame S)
    [DecidableRel F.toCompatFrame.compat] [DecidableRel F.access] :
    Decidable (IsRRegular F) := by
  unfold IsRRegular; infer_instance

/-- Knowability: for every possibility `x` there is some `y` such that
    every R-successor of `y` refines `x`. Loose reading: "there is a
    possibility where everything settled true by `x` is known."
    @cite{holliday-mandelkern-2024} Definition 4.26 (Knowability clause),
    page 866. -/
def IsKnowable {S : Type*} (F : ModalCompatFrame S) : Prop :=
  ∀ x : S, ∃ y : S, ∀ z : S, F.access y z → refines F.toCompatFrame z x

instance {S : Type*} [Fintype S] (F : ModalCompatFrame S)
    [DecidableRel F.toCompatFrame.compat] [DecidableRel F.access] :
    Decidable (IsKnowable F) := by
  unfold IsKnowable; infer_instance

/-- An **epistemic compatibility frame**: a modal compatibility frame
    satisfying R-regularity, T (= reflexivity, already in
    `ModalCompatFrame`), and Knowability. This is the substrate over which
    Wittgenstein's Law (`wittgensteinLaw`, Proposition 4.27) holds.
    @cite{holliday-mandelkern-2024} Definition 4.26, page 866. -/
structure EpistemicCompatFrame (S : Type*) extends ModalCompatFrame S where
  /-- R-regularity per Definition 4.20 / 4.26. -/
  rRegular : IsRRegular toModalCompatFrame
  /-- Knowability per Definition 4.26. -/
  knowable : IsKnowable toModalCompatFrame

-- ════════════════════════════════════════════════════
-- § 4. Wittgenstein's Law (Proposition 4.27)
-- ════════════════════════════════════════════════════

/-- **Wittgenstein's Law (Proposition 4.27)**: in any modal compatibility
    frame satisfying Knowability, the orthonegation `¬A` and the modal `◇A`
    are jointly null at every possibility — for *every* set `A`, regular
    or not. The proof needs only Knowability and reflexivity of accessibility
    (which is bundled in `ModalCompatFrame`); R-regularity from the full
    epistemic-frame definition is not used here.

    Linguistic punchline: "A is settled false" and "A might be true" cannot
    both hold at any possibility — the algebraic content of the claim that
    "p and might-not-p" is contradictory.
    @cite{holliday-mandelkern-2024} Proposition 4.27, page 867. -/
theorem wittgensteinLaw {S : Type*} (F : ModalCompatFrame S) (hK : IsKnowable F)
    (A : Set S) :
    orthoNeg F.toCompatFrame A ∩ diamond F A = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hxNegA hxDiam
  obtain ⟨y, hy⟩ := hK x
  -- `y ∈ □¬A`: every z ∈ R(y) refines x, so refines-preservation pushes
  -- `x ∈ ¬A` down to `z ∈ ¬A` and we collect `y ∈ box (orthoNeg A)`.
  have hyBox : y ∈ box F (orthoNeg F.toCompatFrame A) := by
    intro z hyRz w hzCompatW
    exact hxNegA w (hy z hyRz w hzCompatW)
  -- By T, `y ∈ R(y)`, so `refines y x`; reflexivity of compat then gives
  -- `compat x y`. But `◇A = orthoNeg (box (orthoNeg A))`, so `x ∈ ◇A`
  -- forbids any compat-witness in `box (orthoNeg A)`. Contradiction.
  have hxCompatY : F.toCompatFrame.compat x y :=
    hy y (F.access_refl y) y (F.toCompatFrame.compat_refl y)
  exact hxDiam y hxCompatY hyBox

namespace EpistemicCompatFrame

/-- Wittgenstein's Law on epistemic compatibility frames — the
    canonical paper-defined surface. Direct corollary of the substrate
    `wittgensteinLaw`. -/
theorem wittgensteinLaw {S : Type*} (F : EpistemicCompatFrame S) (A : Set S) :
    orthoNeg F.toCompatFrame A ∩ diamond F.toModalCompatFrame A = ∅ :=
  _root_.Semantics.Modality.Orthologic.wittgensteinLaw
    F.toModalCompatFrame F.knowable A

end EpistemicCompatFrame

end Semantics.Modality.Orthologic
