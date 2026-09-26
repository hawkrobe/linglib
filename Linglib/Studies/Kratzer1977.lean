module

public import Linglib.Semantics.Modality.Kratzer.Operators
public import Mathlib.Data.Fintype.Prod

/-!
# Kratzer (1977): What 'must' and 'can' must and can mean

This file formalizes the paper's two worked examples of modality in view of an inconsistent
premise set, on the premise semantics of `Modality.Premise`. In a New Zealand whose
whole common law is three judgments, that murder is a crime and that deer are, and are not,
personally responsible for the damage they inflict on young trees, the premise set is
inconsistent. Under Definitions 5 and 6, which read *must* as consequence and *can* as
compatibility, the substrate's `simpleNecessity` and `simplePossibility`, every proposition
then follows and none is compatible: it must be that murder is not a crime, and deer cannot be
responsible. Definitions 7 and 8, `MustInView` and `CanInView`, quantify over the consistent
sublists of the premise set and recover the verdicts the paper argues for: murder must be a
crime and cannot fail to be one, while deer can be responsible and can fail to be. The revised
operators agree with the original ones on a consistent premise set
(`mustInView_iff_of_consistent`, `canInView_iff_of_consistent`) and are dual to each other
(`canInView_iff_not_mustInView_not`). The second example, the recommendations of the former
principals of a Whare Wananga, shows that the verdicts depend on how premises are
individuated: a single recommendation that the pupils stride and fly is contradicted as a
whole by a ban on striding, so flying is not required, whereas two recommendations, to stride
and to fly, leave flying required.

## Implementation notes

The worlds are the four combinations of the two issues each example turns on, so every
claim about a concrete premise list is decided over `Bool × Bool` once the sublists of the
list are enumerated by `simp`. The premise set is the same at every world, as the scenarios
assume. The paper's sentence numbers are those of the original article; the 2012 revision
renumbers them.

## References

* [kratzer-1977]
* [kratzer-2012] — Chapter 1, the revised version of the paper
-/

@[expose] public section

namespace Kratzer1977

open Modality

/-! ### Definitions 7 and 8: must and can over consistent sublists -/

section Definitions

variable {W : Type*} {f : ModalBase W} {φ : W → Prop} {i : W}

/-- The consistent sublists of a premise set, `X_A = {B ⊆ A : B consistent}`, over which the
revised definitions quantify. -/
def consistentSublists (A : List (W → Prop)) : Set (List (W → Prop)) :=
  {B | B ∈ A.sublists ∧ IsConsistent B}

/-- Definition 7: *must φ in view of f* holds at `i` when every consistent sublist of `f i`
extends to a consistent sublist from which `φ` follows,
`ν(φ, f) = {i : ∀B[B ∈ X_{f(i)} → ∃C[C ∈ X_{f(i)} ∧ B ⊆ C ∧ ⋂C ⊆ φ]]}`. -/
def MustInView (f : ModalBase W) (φ : W → Prop) (i : W) : Prop :=
  ∀ B ∈ consistentSublists (f i),
    ∃ C ∈ consistentSublists (f i), B ⊆ C ∧ FollowsFrom φ C

/-- Definition 8: *can φ in view of f* holds at `i` when some consistent sublist of `f i` has
`φ` compatible with each of its consistent extensions,
`μ(φ, f) = {i : ∃B[B ∈ X_{f(i)} ∧ ∀C[(C ∈ X_{f(i)} ∧ B ⊆ C) → consistent(C ∪ {φ})]]}`. -/
def CanInView (f : ModalBase W) (φ : W → Prop) (i : W) : Prop :=
  ∃ B ∈ consistentSublists (f i),
    ∀ C ∈ consistentSublists (f i), B ⊆ C → IsCompatibleWith φ C

theorem self_mem_consistentSublists {A : List (W → Prop)} (h : IsConsistent A) :
    A ∈ consistentSublists A :=
  ⟨List.mem_sublists.mpr (List.Sublist.refl _), h⟩

theorem subset_of_mem_consistentSublists {A B : List (W → Prop)}
    (h : B ∈ consistentSublists A) : B ⊆ A :=
  (List.mem_sublists.mp h.1).subset

/-- On a consistent premise set the revised necessity is Definition 5: the premise set is
itself the consistent sublist that dominates every other. -/
theorem mustInView_iff_of_consistent (h : IsConsistent (f i)) :
    MustInView f φ i ↔ simpleNecessity f φ i := by
  rw [simpleNecessity_iff_followsFrom]
  unfold MustInView
  refine ⟨fun hAll ↦ ?_, fun hFollows B hB ↦ ?_⟩
  · obtain ⟨C, hC_mem, _, hfollows⟩ := hAll _ (self_mem_consistentSublists h)
    exact followsFrom_mono_of_subset (subset_of_mem_consistentSublists hC_mem) hfollows
  · exact ⟨f i, self_mem_consistentSublists h, subset_of_mem_consistentSublists hB,
      hFollows⟩

/-- On a consistent premise set the revised possibility is Definition 6. -/
theorem canInView_iff_of_consistent (h : IsConsistent (f i)) :
    CanInView f φ i ↔ simplePossibility f φ i := by
  rw [simplePossibility_iff_isCompatibleWith]
  unfold CanInView
  refine ⟨fun ⟨B, hB_mem, hAll⟩ ↦ ?_, fun hCompat ↦ ?_⟩
  · exact hAll (f i) (self_mem_consistentSublists h)
      (subset_of_mem_consistentSublists hB_mem)
  · refine ⟨f i, self_mem_consistentSublists h, fun C hC _ ↦ ?_⟩
    exact isCompatibleWith_anti_of_subset (subset_of_mem_consistentSublists hC) hCompat

/-- *Can* is the negation of *must not*, since compatibility with a premise set is the failure
of the negation to follow from it. -/
theorem canInView_iff_not_mustInView_not (f : ModalBase W) (φ : W → Prop) (i : W) :
    CanInView f φ i ↔ ¬ MustInView f (fun j ↦ ¬ φ j) i := by
  simp only [CanInView, MustInView, isCompatibleWith_iff_not_followsFrom_not, not_forall,
    not_exists, not_and, exists_prop]

theorem mustInView_iff_not_canInView_not (f : ModalBase W) (φ : W → Prop) (i : W) :
    MustInView f φ i ↔ ¬ CanInView f (fun j ↦ ¬ φ j) i := by
  rw [canInView_iff_not_mustInView_not, not_not]
  simp only [MustInView, FollowsFrom, not_not]

/-- A premise in a consistent sublist is possible under Definition 8: every consistent
extension still contains it. -/
theorem canInView_of_mem {B : List (W → Prop)} (hB : B ∈ consistentSublists (f i))
    (hp : φ ∈ B) : CanInView f φ i :=
  ⟨B, hB, fun _ ⟨_, w, hw⟩ hBC ↦ ⟨w, List.forall_mem_cons.mpr ⟨hw φ (hBC hp), hw⟩⟩⟩

/-- The head of the premise set is necessary under Definition 7 when it is compatible with
every consistent sublist: a sublist without it extends by it, one with it entails it. -/
theorem mustInView_of_forall_isCompatibleWith {A : List (W → Prop)} (hf : f i = φ :: A)
    (h : ∀ B ∈ consistentSublists (f i), IsCompatibleWith φ B) : MustInView f φ i := by
  intro B hB
  have hBA : B.Sublist (φ :: A) := hf ▸ List.mem_sublists.mp hB.1
  rcases List.sublist_cons_iff.mp hBA with hBA | ⟨r, rfl, hr⟩
  · exact ⟨φ :: B, ⟨hf ▸ List.mem_sublists.mpr (hBA.cons_cons φ), h B hB⟩,
      List.subset_cons_self φ B, propIntersection_subset List.mem_cons_self⟩
  · exact ⟨φ :: r, hB, List.Subset.refl _, propIntersection_subset List.mem_cons_self⟩

end Definitions

/-! ### The worlds -/

/-- The four worlds: the truth values of the two issues an example turns on. -/
abbrev World := Bool × Bool

/-- The first issue holds. -/
def p : World → Prop := (·.1 = true)

/-- The second issue holds. -/
def q : World → Prop := (·.2 = true)

/-- The negation of a proposition. -/
def neg (r : World → Prop) : World → Prop := fun w ↦ ¬ r w

/-- Decide a claim about concrete premise lists over the four worlds. -/
scoped macro "decide_worlds" : tactic =>
  `(tactic| (simp only [IsConsistent, IsCompatibleWith, FollowsFrom, propIntersection,
      Set.Nonempty, Set.subset_def, Set.mem_ofPred_eq, List.forall_mem_cons, List.mem_nil_iff,
      false_implies, implies_true, and_true, p, q, neg]; decide))

/-! ### The New Zealand judgments (§2.1–§2.2)

`p` is that murder is a crime, the judgment (10); `q` that deer are personally responsible for
damage they inflict on young trees, the Auckland judgment (11); and `neg q` the Wellington
judgment (12). -/

/-- What the New Zealand judgments provide. -/
def judgments : List (World → Prop) := [p, q, neg q]

theorem judgments_inconsistent : ¬ IsConsistent judgments := fun ⟨_, h⟩ ↦
  h (neg q) (by simp [judgments]) (h q (by simp [judgments]))

/-- Under Definition 5 the inconsistent judgments make (7) true: it must be that murder is
not a crime, by ex falso quodlibet. -/
theorem simpleNecessity_neg_p (w : World) :
    simpleNecessity (Function.const World judgments) (neg p) w :=
  fun _ h ↦ absurd (h q (by simp [judgments])) (h (neg q) (by simp [judgments]))

/-- Under Definition 6 nothing is compatible with the judgments, so (8) is false: deer cannot
be personally responsible. -/
theorem not_simplePossibility_q (w : World) :
    ¬ simplePossibility (Function.const World judgments) q w :=
  fun ⟨_, h, hq⟩ ↦ h (neg q) (by simp [judgments]) hq

/-- Definition 7 makes (6) true, murder must be a crime: `p` is compatible with every
consistent subset of the judgments. -/
theorem must_p (w : World) : MustInView (Function.const World judgments) p w := by
  refine mustInView_of_forall_isCompatibleWith rfl ?_
  rintro B ⟨hB, hc⟩
  simp [judgments, List.sublists] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd hc (by decide_worlds) | decide_worlds

/-- Definition 7 makes (7) false: no consistent subset of the judgments entails that murder
is not a crime. -/
theorem not_must_neg_p (w : World) :
    ¬ MustInView (Function.const World judgments) (neg p) w := fun h ↦
  let ⟨C, ⟨hC, hc⟩, _, hf⟩ := h [] ⟨by simp [judgments, List.sublists], by decide_worlds⟩
  by
    simp [judgments, List.sublists] at hC
    rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd hc (by decide_worlds) | exact absurd hf (by decide_worlds)

/-- Definition 8 makes (8) true: the judgment that deer are responsible is itself a consistent
subset. -/
theorem can_q (w : World) : CanInView (Function.const World judgments) q w :=
  canInView_of_mem (B := [q]) ⟨by simp [judgments, List.sublists], by decide_worlds⟩
    List.mem_cons_self

/-- Definition 8 makes (9) true, symmetrically. -/
theorem can_neg_q (w : World) : CanInView (Function.const World judgments) (neg q) w :=
  canInView_of_mem (B := [neg q]) ⟨by simp [judgments, List.sublists], by decide_worlds⟩
    List.mem_cons_self

/-- Definition 8 makes (13) false, it cannot be that murder is not a crime: the dual of
(6). -/
theorem not_can_neg_p (w : World) :
    ¬ CanInView (Function.const World judgments) (neg p) w :=
  (mustInView_iff_not_canInView_not _ _ _).mp (must_p w)

/-! ### The Whare Wananga recommendations (§2.3)

`p` is that the pupils practise striding and `q` that they practise flying. Te Miti's
recommendation is read once as the single proposition (14), that they do both, and once as
two recommendations; Te Kini's is (15), that they do not stride. -/

/-- Te Miti's recommendation as one proposition, with Te Kini's. -/
def recommendations : List (World → Prop) := [fun w ↦ p w ∧ q w, neg p]

/-- Te Miti's recommendation as two propositions, with Te Kini's. -/
def recommendations' : List (World → Prop) := [q, p, neg p]

private theorem neg_p_ne_conj : neg p ≠ fun w ↦ p w ∧ q w := fun h ↦
  absurd (h ▸ show neg p (false, false) from Bool.false_ne_true) fun hc ↦
    Bool.false_ne_true hc.1

/-- On the first reading (16) is false: Te Kini's ban is a consistent subset whose only
consistent extension is itself, and flying does not follow from it. -/
theorem not_must_q (w : World) :
    ¬ MustInView (Function.const World recommendations) q w := fun h ↦
  let ⟨C, ⟨hC, hc⟩, hBC, hf⟩ :=
    h [neg p] ⟨by simp [recommendations, List.sublists], by decide_worlds⟩
  by
    simp [recommendations, List.sublists] at hC
    rcases hC with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd (hBC List.mem_cons_self) List.not_mem_nil
      | exact absurd (List.mem_singleton.mp (hBC List.mem_cons_self)) neg_p_ne_conj
      | exact absurd hf (by decide_worlds)
      | exact absurd hc (by decide_worlds)

/-- On the second reading (16) is true: flying is compatible with every consistent subset. -/
theorem must_q (w : World) : MustInView (Function.const World recommendations') q w := by
  refine mustInView_of_forall_isCompatibleWith rfl ?_
  rintro B ⟨hB, hc⟩
  simp [recommendations', List.sublists] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd hc (by decide_worlds) | decide_worlds

end Kratzer1977
