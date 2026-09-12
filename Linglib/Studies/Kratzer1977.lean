import Linglib.Semantics.Modality.Kratzer.Premise
import Mathlib.Data.Fintype.Prod

/-!
# Kratzer (1977): What 'must' and 'can' must and can mean

This file formalizes the paper's two worked examples of modality in view of an inconsistent
premise set, on the premise semantics of `Modality.Kratzer.Premise`. In a New Zealand whose
whole common law is three judgments, that murder is a crime and that deer are, and are not,
personally responsible for the damage they inflict on young trees, the premise set is
inconsistent. Under Definitions 5 and 6, which read *must* as consequence and *can* as
compatibility, every proposition then follows and none is compatible: it must be that murder
is not a crime, and deer cannot be responsible. Definitions 7 and 8 quantify over the
consistent subsets of the premise set and recover the verdicts the paper argues for: murder
must be a crime and cannot fail to be one, while deer can be responsible and can fail to be.
The second example, the recommendations of the former principals of a Whare Wananga, shows
that the verdicts depend on how premises are individuated: a single recommendation that the
pupils stride and fly is contradicted as a whole by a ban on striding, so flying is not
required, whereas two recommendations, to stride and to fly, leave flying required.

## Implementation notes

The worlds are the four combinations of the two issues each example turns on, so every
claim about a concrete premise list is decided over `Bool × Bool` once the sublists of the
list are enumerated by `simp`. The premise set is the same at every world, as the scenarios assume.
The paper's sentence numbers are those of the original article; the 2012 revision renumbers
them.

## References

* [kratzer-1977]
* [kratzer-2012] — Chapter 1, the revised version of the paper
-/

namespace Kratzer1977

open Modality.Kratzer

/-- The four worlds: the truth values of the two issues an example turns on. -/
abbrev World := Bool × Bool

/-- The first issue holds. -/
def p : World → Prop := (·.1 = true)

/-- The second issue holds. -/
def q : World → Prop := (·.2 = true)

/-- The negation of a proposition. -/
def neg (r : World → Prop) : World → Prop := λ w => ¬ r w

/-- Decide a claim about concrete premise lists over the four worlds. -/
scoped macro "decide_worlds" : tactic =>
  `(tactic| (simp only [isConsistent, isCompatibleWith, followsFrom, propIntersection,
      Set.Nonempty, Set.subset_def, Set.mem_ofPred_eq, List.forall_mem_cons, List.mem_nil_iff,
      false_implies, implies_true, and_true, p, q, neg]; decide))

/-! ### The New Zealand judgments (§2.1–§2.2)

`p` is that murder is a crime, the judgment (10); `q` that deer are personally responsible for
damage they inflict on young trees, the Auckland judgment (11); and `neg q` the Wellington
judgment (12). -/

/-- What the New Zealand judgments provide. -/
def judgments : List (World → Prop) := [p, q, neg q]

theorem judgments_inconsistent : ¬ isConsistent judgments := λ ⟨_, h⟩ =>
  h (neg q) (by simp [judgments]) (h q (by simp [judgments]))

/-- Under Definition 5 the inconsistent judgments make (7) true: it must be that murder is
not a crime, by ex falso quodlibet. -/
theorem must_neg_p (w : World) : mustInView (Function.const World judgments) (neg p) w :=
  λ _ h => absurd (h q (by simp [judgments])) (h (neg q) (by simp [judgments]))

/-- Under Definition 6 nothing is compatible with the judgments, so (8) is false: deer cannot
be personally responsible. -/
theorem not_can_q (w : World) : ¬ canInView (Function.const World judgments) q w :=
  λ ⟨_, h⟩ => h (neg q) (by simp [judgments]) (h q (by simp))

/-- Definition 7 makes (6) true, murder must be a crime: `p` is compatible with every
consistent subset of the judgments. -/
theorem must'_p (w : World) : mustInView' (Function.const World judgments) p w := by
  refine mustInView'_of_forall_isCompatibleWith rfl ?_
  rintro B ⟨hB, hc⟩
  simp [judgments, List.sublists] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd hc (by decide_worlds) | decide_worlds

/-- Definition 7 makes (7) false: no consistent subset of the judgments entails that murder
is not a crime. -/
theorem not_must'_neg_p (w : World) :
    ¬ mustInView' (Function.const World judgments) (neg p) w := λ h =>
  let ⟨C, ⟨hC, hc⟩, _, hf⟩ := h [] ⟨by simp [judgments, List.sublists], by decide_worlds⟩
  by
    simp [judgments, List.sublists] at hC
    rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd hc (by decide_worlds) | exact absurd hf (by decide_worlds)

/-- Definition 8 makes (8) true: the judgment that deer are responsible is itself a consistent
subset. -/
theorem can'_q (w : World) : canInView' (Function.const World judgments) q w :=
  canInView'_of_mem (B := [q]) ⟨by simp [judgments, List.sublists], by decide_worlds⟩
    List.mem_cons_self

/-- Definition 8 makes (9) true, symmetrically. -/
theorem can'_neg_q (w : World) : canInView' (Function.const World judgments) (neg q) w :=
  canInView'_of_mem (B := [neg q]) ⟨by simp [judgments, List.sublists], by decide_worlds⟩
    List.mem_cons_self

/-- Definition 8 makes (13) false, it cannot be that murder is not a crime: the dual of
(6). -/
theorem not_can'_neg_p (w : World) :
    ¬ canInView' (Function.const World judgments) (neg p) w :=
  (mustInView'_iff_not_canInView'_not _ _ _).mp (must'_p w)

/-! ### The Whare Wananga recommendations (§2.3)

`p` is that the pupils practise striding and `q` that they practise flying. Te Miti's
recommendation is read once as the single proposition (14), that they do both, and once as
two recommendations; Te Kini's is (15), that they do not stride. -/

/-- Te Miti's recommendation as one proposition, with Te Kini's. -/
def recommendations : List (World → Prop) := [λ w => p w ∧ q w, neg p]

/-- Te Miti's recommendation as two propositions, with Te Kini's. -/
def recommendations' : List (World → Prop) := [q, p, neg p]

private theorem neg_p_ne_conj : neg p ≠ λ w => p w ∧ q w := λ h =>
  absurd (h ▸ show neg p (false, false) from Bool.false_ne_true) λ hc =>
    Bool.false_ne_true hc.1

/-- On the first reading (16) is false: Te Kini's ban is a consistent subset whose only
consistent extension is itself, and flying does not follow from it. -/
theorem not_must'_q (w : World) : ¬ mustInView' (Function.const World recommendations) q w :=
  λ h =>
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
theorem must'_q (w : World) : mustInView' (Function.const World recommendations') q w := by
  refine mustInView'_of_forall_isCompatibleWith rfl ?_
  rintro B ⟨hB, hc⟩
  simp [recommendations', List.sublists] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd hc (by decide_worlds) | decide_worlds

end Kratzer1977
