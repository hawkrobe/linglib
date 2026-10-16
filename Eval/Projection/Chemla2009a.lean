module

public import Eval.Projection.Account
public import Linglib.Data.Experiments.Chemla2009a
public import Linglib.Semantics.Presupposition.QuantifiedLocalContext

/-!
# Scoring the accounts on Chemla (2009)

Chemla's first experiment asks whether a sentence with a presupposition trigger in the scope of a
quantifier over ten students suggests the universal inference, that every one of them satisfies
the presupposition. The text reports the acceptance rates pooled over two groups of quantifiers,
*each* and *no* on one side and the numerical quantifiers on the other, and the comparison is
scored in four steps. The fact is the order of the two rates (`observed`). The parse of a sentence
is the nuclear scope of its quantifier, restricted to the students (`Presupposition.scopeTruth`).
Each account that the library defines for quantified sentences says which contexts accept it
(`scopeAccepts`); since the trigger ends the sentence, the incremental and symmetric versions
consult the same single continuation. The linking hypothesis, that subjects endorse the inferences
a theory predicts and endorse alike the inferences it predicts alike, turns the acceptance
conditions into a predicted order of the two rates (`predicted`).

Every quantifier of the experiment varies on the row of ten, so each of these accounts predicts the
universal inference from all five quantifiers, and so no difference between the groups
(`predicted_eq`). The universal inference is endorsed more from *each* and *no*, so each of them is
wrong, and the accounts the library defines only for the propositional fragment are silent
(`verdict_eq`). Universal projection by Transparency, in any of its versions, leaves the contrast
that Chemla reports to some other source.

## References

* [chemla-2009a]
* [schlenker-2009]
* [kalomoiros-2023]
-/

@[expose] public section

namespace Eval.Projection.Chemla2009a

open Presupposition Quantifier Account _root_.Chemla2009a

/-- The students of the domain. -/
abbrev Student := Fin domainSize

/-- The quantifiers of a group, on the tree of numbers. -/
def quantifiers : QuantifierGroup → List NumberTree
  | .eachOrNo => [NumberTree.all, NumberTree.no]
  | .numeral => [NumberTree.cardinal {b | b < 3}, NumberTree.cardinal {b | 3 < b},
      NumberTree.cardinal {3}]

/-- The truth set of `(Q these students . _)` as a function of its scope. -/
abbrev sentence (q : NumberTree) {W : Type} : Set (W × Student) → Set W :=
  scopeTruth q fun _ _ ↦ True

/-- The acceptance condition that an account gives a sentence whose trigger, presupposing `π`, is in
the nuclear scope of `q`, for the accounts the library defines on quantified sentences. The trigger
ends the sentence, so incremental and symmetric versions consult the sentence alone, and Limited
Symmetry has a single parse point after the trigger. -/
def scopeAccepts : Account → Option (NumberTree → ∀ {W : Type}, Set W → Set (W × Student) → Prop)
  | transparencyIncremental | transparencySymmetric =>
    some fun q _ C π ↦ Transparent C {sentence q} π
  | satisfactionIncremental | satisfactionSymmetric =>
    some fun q _ C π ↦ Satisfied C {sentence q} π
  | limitedSymmetry => some fun q _ C π ↦ StablyTransparent C {sentence q} π
  | _ => none

/-- The linking hypothesis for one sentence. An acceptance condition predicts the universal
inference when every context that accepts the sentence entails that every student satisfies the
presupposition. -/
def PredictsUniversal (accepts : ∀ {W : Type}, Set W → Set (W × Student) → Prop) : Prop :=
  ∀ (W : Type) (C : Set W) (π : Set (W × Student)), accepts C π → ∀ w ∈ C, ∀ e, (w, e) ∈ π

open Classical in
/-- The linking hypothesis for the comparison of the groups, as a rule. Acceptance conditions
predict the same rate for both groups when they predict the universal inference from every
quantifier of both or from none, a higher rate for the group from whose quantifiers alone they
predict it, and nothing otherwise. -/
noncomputable def orderOf (accepts : NumberTree → ∀ {W : Type}, Set W → Set (W × Student) → Prop) :
    Option Ordering :=
  let all g := ∀ q ∈ quantifiers g, PredictsUniversal (accepts q)
  let none' g := ∀ q ∈ quantifiers g, ¬ PredictsUniversal (accepts q)
  if all .eachOrNo ∧ all .numeral ∨ none' .eachOrNo ∧ none' .numeral then some .eq
  else if all .eachOrNo ∧ none' .numeral then some .gt
  else if none' .eachOrNo ∧ all .numeral then some .lt
  else none

/-- The order an account predicts, by the linking hypothesis, if it is defined on quantified
sentences. -/
noncomputable def predicted (a : Account) : Option Ordering := (scopeAccepts a).bind orderOf

/-- The order of the acceptance rates of the universal inference for *each* and *no* and for the
numerical quantifiers (§2.3.4). -/
def observed : Option Ordering :=
  match experiment1Universal.find? (·.group = .eachOrNo),
      experiment1Universal.find? (·.group = .numeral) with
  | some r, some r' => some (compare r.acceptance.toRat r'.acceptance.toRat)
  | _, _ => none

/-- The verdict on an account. -/
noncomputable def verdict (a : Account) : Eval.Verdict := .of (predicted a) observed

/-! ### Predictions -/

private theorem ncard_students : {_x : Student | True}.ncard = 10 := by simp [domainSize]

/-- Every quantifier of the experiment varies on the row of ten. -/
private theorem not_constantOnRow {g : QuantifierGroup} {q : NumberTree} (hq : q ∈ quantifiers g) :
    ¬ q.ConstantOnRow 10 := by
  cases g <;> simp only [quantifiers, List.mem_cons, List.not_mem_nil, or_false] at hq <;>
    rcases hq with rfl | rfl | rfl <;> intro h
  · have := h 10 0 0 10 rfl rfl; simp [NumberTree.all] at this
  · have := h 10 0 0 10 rfl rfl; simp [NumberTree.no] at this
  · have := h 10 0 0 10 rfl rfl; simp [NumberTree.cardinal] at this
  · have := h 10 0 0 10 rfl rfl; simp [NumberTree.cardinal] at this
  · have := h 10 0 7 3 rfl rfl; simp [NumberTree.cardinal] at this

/-- Transparency predicts the universal inference from every quantifier of the experiment. -/
private theorem predictsUniversal_transparent {g : QuantifierGroup} {q : NumberTree}
    (hq : q ∈ quantifiers g) :
    PredictsUniversal fun C π ↦ Transparent C {sentence q} π := fun _ _ _ h w hw e ↦
  (transparent_scopeTruth_iff q).1 h w hw (by rw [ncard_students]; exact not_constantOnRow hq) e
    trivial

/-- The accounts defined on quantified sentences. -/
def quantified : List Account :=
  [transparencyIncremental, transparencySymmetric, satisfactionIncremental, satisfactionSymmetric,
    limitedSymmetry]

private theorem orderOf_eq (accepts : NumberTree → ∀ {W : Type}, Set W → Set (W × Student) → Prop)
    (h : ∀ q (W : Type) (C : Set W) (π : Set (W × Student)), accepts q C π →
      Transparent C {sentence q} π) :
    orderOf accepts = some .eq := by
  have hall (g : QuantifierGroup) : ∀ q ∈ quantifiers g, PredictsUniversal (accepts q) :=
    fun q hq W C π hC ↦ predictsUniversal_transparent hq W C π (h q W C π hC)
  unfold orderOf
  exact ite_eq_left_of_eq_true _ _ (eq_true (.inl ⟨hall .eachOrNo, hall .numeral⟩))

/-- Each account defined on quantified sentences predicts the universal inference from every
quantifier of the experiment, and so the same rate for both groups. -/
theorem predicted_eq (a : Account) : predicted a = if a ∈ quantified then some .eq else none := by
  cases a <;> simp only [predicted, scopeAccepts, quantified, List.mem_cons, List.not_mem_nil,
    or_false, reduceCtorEq, or_true, true_or, eq_self_iff_true, ite_true, ite_false,
    Option.bind_none, Option.bind_some] <;>
  first
  | exact orderOf_eq _ fun _ _ _ _ h ↦ h
  | exact orderOf_eq _ fun q _ C _ h ↦
      ((isLocalContext_scopeTruth q _ C).satisfied_iff_transparent _).1 h
  | exact orderOf_eq _ fun _ _ _ _ h ↦ stablyTransparent_singleton_iff.1 h

/-- The universal inference is endorsed more from *each* and *no* than from the numerical
quantifiers. -/
theorem observed_eq : observed = some .gt := by decide +kernel

/-- Each account defined on quantified sentences is wrong, and the others are silent. -/
theorem verdict_eq (a : Account) : verdict a = if a ∈ quantified then .wrong else .silent := by
  rw [verdict, predicted_eq, observed_eq]
  split_ifs <;> rfl

end Eval.Projection.Chemla2009a
