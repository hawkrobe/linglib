module

public import Eval.Parser
public import Eval.Projection.Account
public import Studies.Chemla2009a

/-!
# Scoring the accounts on Chemla (2009)

Chemla's first experiment asks whether a sentence with a presupposition trigger in the scope of a
quantifier over ten students suggests the universal inference, that every one of them satisfies
the presupposition. The text reports the acceptance rates pooled over two groups of quantifiers,
*each* and *no* on one side and the numerical quantifiers on the other, and the comparison is
scored in four steps. The fact is the order of the two rates (`observed`). The parse of a sentence
that every theory shares is its quantifier (`Chemla2009a.Determiner.tree`), and a theory parses it
further by where the presupposition of the trigger is accommodated (`ScopeParse`): in the context,
or in the scope, where it joins the assertion and the sentence presupposes nothing. Each account
that the library defines for quantified sentences says which contexts accept a parse
(`acceptsAt`). The linking hypothesis, that subjects endorse the inferences a theory predicts and
endorse alike the inferences it predicts alike, turns the acceptance conditions into a predicted
order of the two rates (`predicted`).

With every presupposition accommodated in the context (`global`), each of these accounts predicts
the universal inference from all five quantifiers, and so no difference between the groups. Each is
then wrong, and the accounts the library defines only for the propositional fragment are silent
(`verdict_global`). Chemla's §4.1.2 considers an amendment: the universal presupposition is not
accommodated after the numerical quantifiers. A parser can stipulate this sentence by sentence, at
the cost of three stipulations (`stipulated`). The section and Appendix F suggest a rule instead:
accommodate the presupposition in the context where transparency derives it in one step
(`oneStep`). The rule parses every sentence as the stipulations do, without any of them
(`parse_oneStep`), and by it each account defined on quantified sentences is right
(`verdict_oneStep`).

## Implementation notes

* A presupposition not accommodated in the context is accommodated in the scope, where the sentence
  no longer presupposes it; §4.1.2 says only that it is weakened or not accommodated.

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

/-- The truth set of `(Q these students . _)` as a function of its scope. -/
abbrev sentence (q : NumberTree) {W : Type} : Set (W × Student) → Set W :=
  scopeTruth q fun _ _ ↦ True

/-- Where the presupposition of a trigger in the nuclear scope is accommodated. -/
inductive Accommodation where
  /-- In the context, so that the sentence presupposes it. -/
  | global
  /-- In the scope, where it joins the assertion, so that the sentence presupposes nothing. -/
  | scope
  deriving DecidableEq

/-- What the sentence presupposes of the scope's individuals when the trigger presupposes `π`. -/
def Accommodation.presupposition {α : Type*} : Accommodation → Set α → Set α
  | global, π => π
  | scope, _ => Set.univ

/-- A theory's parse of a sentence of the experiment. -/
structure ScopeParse where
  /-- The quantifier. -/
  quantifier : NumberTree
  /-- Where the presupposition of the trigger in its scope is accommodated. -/
  accommodation : Accommodation

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

/-- The acceptance condition that an account gives a parse. -/
def acceptsAt (a : Account) (p : ScopeParse) :
    Option (∀ {W : Type}, Set W → Set (W × Student) → Prop) :=
  (scopeAccepts a).map fun acc _ C π ↦ acc p.quantifier C (p.accommodation.presupposition π)

/-- The linking hypothesis for one sentence. An acceptance condition predicts the universal
inference when every context that accepts the sentence entails that every student satisfies the
presupposition. -/
def PredictsUniversal (accepts : ∀ {W : Type}, Set W → Set (W × Student) → Prop) : Prop :=
  ∀ (W : Type) (C : Set W) (π : Set (W × Student)), accepts C π → ∀ w ∈ C, ∀ e, (w, e) ∈ π

open Classical in
/-- The linking hypothesis for the comparison of the groups, as a rule. Acceptance conditions for
the sentences predict the same rate for both groups when they predict the universal inference from
every sentence of both or from none, a higher rate for the group from whose sentences alone they
predict it, and nothing otherwise. -/
noncomputable def orderOf (accepts : Determiner → ∀ {W : Type}, Set W → Set (W × Student) → Prop) :
    Option Ordering :=
  let all g := ∀ d, (experiment1Groups d).group = g → PredictsUniversal (accepts d)
  let none' g := ∀ d, (experiment1Groups d).group = g → ¬ PredictsUniversal (accepts d)
  if all .eachOrNo ∧ all .numeral ∨ none' .eachOrNo ∧ none' .numeral then some .eq
  else if all .eachOrNo ∧ none' .numeral then some .gt
  else if none' .eachOrNo ∧ all .numeral then some .lt
  else none

open Classical in
/-- The order an account predicts, by the linking hypothesis, from a theory's parses of the
sentences, if the account is defined on quantified sentences and every sentence has a parse. -/
noncomputable def predicted (a : Account) (parse : Determiner → Option ScopeParse) :
    Option Ordering :=
  if h : ∀ d, ((parse d).bind (acceptsAt a)).isSome then
    orderOf fun d ↦ ((parse d).bind (acceptsAt a)).get (h d)
  else none

/-- The order of the acceptance rates of the universal inference for *each* and *no* and for the
numerical quantifiers (§2.3.4). -/
def observed : Option Ordering :=
  match experiment1Universal.find? (·.group = .eachOrNo),
      experiment1Universal.find? (·.group = .numeral) with
  | some r, some r' => some (compare r.acceptance.toRat r'.acceptance.toRat)
  | _, _ => none

/-- The verdict on an account under a parser. -/
noncomputable def verdict (a : Account) (π : Parser Determiner NumberTree ScopeParse) :
    Eval.Verdict :=
  .of (predicted a (π.parse Determiner.tree)) observed

/-! ### Parsers -/

/-- Every presupposition accommodated in the context. -/
def global : Parser Determiner NumberTree ScopeParse := .ofRule fun q ↦ some ⟨q, .global⟩

/-- §4.1.2: the universal presupposition is not accommodated after the numerical quantifiers,
stipulated for each of their sentences. -/
def stipulated : Parser Determiner NumberTree ScopeParse where
  rule q := some ⟨q, .global⟩
  table := List.toFinmap
    [⟨.lessThan3, ⟨Determiner.tree .lessThan3, .scope⟩⟩,
     ⟨.moreThan3, ⟨Determiner.tree .moreThan3, .scope⟩⟩,
     ⟨.exactly3, ⟨Determiner.tree .exactly3, .scope⟩⟩]

open Classical in
/-- Appendix F: the presupposition is accommodated in the context where transparency derives it in
one step, and in the scope otherwise. -/
noncomputable def oneStep : Parser Determiner NumberTree ScopeParse :=
  .ofRule fun q ↦ some ⟨q, if OneStep q then .global else .scope⟩

/-- Appendix F's rule parses every sentence as §4.1.2's stipulations do, with none of them. -/
theorem parse_oneStep : oneStep.parse Determiner.tree = stipulated.parse Determiner.tree := by
  refine Parser.parse_ofRule_eq _ _ (fun d p h ↦ ?_) fun d hd ↦ ?_
  · cases d <;> simp_all [stipulated, oneStep_tree_iff, experiment1Groups]
  · cases d <;> simp_all [stipulated, Parser.stipulations, Finmap.mem_keys,
      Finmap.mem_list_toFinmap, oneStep_tree_iff, experiment1Groups]

theorem stipulations_stipulated :
    stipulated.stipulations = {.lessThan3, .moreThan3, .exactly3} := by
  decide

/-! ### Predictions -/

private theorem ncard_students : {_x : Student | True}.ncard = 10 := by simp [domainSize]

/-- Every quantifier of the experiment varies on the row of ten. -/
private theorem not_constantOnRow (d : Determiner) : ¬ d.tree.ConstantOnRow 10 := by
  cases d <;> intro h
  · have := h 10 0 0 10 rfl rfl; simp [Determiner.tree, NumberTree.all] at this
  · have := h 10 0 0 10 rfl rfl; simp [Determiner.tree, NumberTree.no] at this
  · have := h 10 0 0 10 rfl rfl; simp [Determiner.tree, NumberTree.cardinal] at this
  · have := h 10 0 0 10 rfl rfl; simp [Determiner.tree, NumberTree.cardinal] at this
  · have := h 10 0 7 3 rfl rfl; simp [Determiner.tree, NumberTree.cardinal] at this

/-- Transparency predicts the universal inference from every quantifier of the experiment. -/
private theorem predictsUniversal_transparent (d : Determiner) :
    PredictsUniversal fun C π ↦ Transparent C {sentence d.tree} π := fun _ _ _ h w hw e ↦
  (transparent_scopeTruth_iff d.tree).1 h w hw (by rw [ncard_students]; exact not_constantOnRow d)
    e trivial

/-- The accounts defined on quantified sentences. -/
def quantified : List Account :=
  [transparencyIncremental, transparencySymmetric, satisfactionIncremental, satisfactionSymmetric,
    limitedSymmetry]

/-- Each account defined on quantified sentences accepts a sentence only where transparency does,
and accepts every sentence that presupposes nothing. -/
private theorem scopeAccepts_spec {a : Account} (ha : a ∈ quantified) :
    ∃ acc, scopeAccepts a = some acc ∧
      (∀ q (W : Type) (C : Set W) π, @acc q W C π → Transparent C {sentence q} π) ∧
      ∀ q (W : Type) (C : Set W), @acc q W C Set.univ := by
  have htop (q : NumberTree) (W : Type) (C : Set W) : Transparent C {sentence q} Set.univ :=
    fun _ _ _ _ _ ↦ by simp
  simp only [quantified, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, rfl, fun _ _ _ _ h ↦ h, htop⟩
  · exact ⟨_, rfl, fun _ _ _ _ h ↦ h, htop⟩
  · exact ⟨_, rfl, fun q _ C _ h ↦ ((isLocalContext_scopeTruth q _ C).satisfied_iff_transparent _).1
      h, fun q _ C ↦ ⟨_, isLocalContext_scopeTruth q _ C, Set.subset_univ _⟩⟩
  · exact ⟨_, rfl, fun q _ C _ h ↦ ((isLocalContext_scopeTruth q _ C).satisfied_iff_transparent _).1
      h, fun q _ C ↦ ⟨_, isLocalContext_scopeTruth q _ C, Set.subset_univ _⟩⟩
  · exact ⟨_, rfl, fun _ _ _ _ h ↦ stablyTransparent_singleton_iff.1 h,
      fun q W C ↦ (htop q W C).stablyTransparent⟩

private theorem scopeAccepts_eq_none {a : Account} (ha : a ∉ quantified) :
    scopeAccepts a = none := by
  cases a <;> simp_all [quantified, scopeAccepts]

/-- Under parses defined on every sentence, an account defined on quantified sentences predicts the
order its acceptance conditions give the parses. -/
private theorem predicted_of_parse {a : Account} {acc} (hacc : scopeAccepts a = some acc)
    (p : Determiner → ScopeParse) :
    predicted a (fun d ↦ some (p d)) =
      orderOf fun d _ C π ↦ acc (p d).quantifier C ((p d).accommodation.presupposition π) := by
  unfold predicted acceptsAt
  rw [hacc]
  simp

/-- An account not defined on quantified sentences predicts nothing. -/
private theorem predicted_eq_none {a : Account} (ha : a ∉ quantified)
    (parse : Determiner → Option ScopeParse) : predicted a parse = none := by
  unfold predicted acceptsAt
  rw [scopeAccepts_eq_none ha]
  exact dite_eq_right fun h ↦ by simpa using h .each

theorem observed_eq : observed = some .gt := by decide +kernel

/-- With every presupposition accommodated in the context, each account defined on quantified
sentences predicts no difference between the groups and is wrong, and the others are silent. -/
theorem verdict_global (a : Account) :
    verdict a global = if a ∈ quantified then .wrong else .silent := by
  by_cases ha : a ∈ quantified
  · obtain ⟨acc, hacc, hT, -⟩ := scopeAccepts_spec ha
    have : global.parse Determiner.tree = fun d ↦ some ⟨d.tree, .global⟩ := by
      funext d; simp [global]
    rw [ite_eq_left ha, verdict, this, predicted_of_parse hacc, observed_eq]
    have hall (d : Determiner) : PredictsUniversal fun C π ↦ acc d.tree C π :=
      fun W C π h ↦ predictsUniversal_transparent d W C π (hT _ _ _ _ h)
    unfold orderOf
    rw [ite_eq_left (.inl ⟨fun d _ ↦ hall d, fun d _ ↦ hall d⟩)]
    rfl
  · rw [ite_eq_right ha, verdict, predicted_eq_none ha]
    rfl

/-- By Appendix F's rule, each account defined on quantified sentences predicts the universal
inference from *each* and *no* alone and is right, and the others are silent. -/
theorem verdict_oneStep (a : Account) :
    verdict a oneStep = if a ∈ quantified then .correct else .silent := by
  by_cases ha : a ∈ quantified
  · obtain ⟨acc, hacc, hT, hU⟩ := scopeAccepts_spec ha
    have : oneStep.parse Determiner.tree = fun d ↦ some ⟨d.tree,
        if (experiment1Groups d).group = .eachOrNo then .global else .scope⟩ := by
      funext d; simp [oneStep, oneStep_tree_iff]
    rw [ite_eq_left ha, verdict, this, predicted_of_parse hacc, observed_eq]
    have he (d : Determiner) : PredictsUniversal fun C π ↦
        acc d.tree C (Accommodation.global.presupposition π) :=
      fun W C π h ↦ predictsUniversal_transparent d W C π (hT _ _ _ _ h)
    have hn (d : Determiner) : ¬ PredictsUniversal fun C π ↦
        acc d.tree C (Accommodation.scope.presupposition π) := fun h ↦
      (h Unit Set.univ ∅ (hU _ _ _) () trivial ⟨0, by decide⟩).elim
    unfold orderOf
    rw [ite_eq_right, ite_eq_left]
    · rfl
    · refine ⟨fun d hd ↦ ?_, fun d hd ↦ ?_⟩
      · beta_reduce; rw [ite_eq_left hd]; exact he d
      · beta_reduce; rw [ite_eq_right (by rw [hd]; decide)]; exact hn d
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact hn .lessThan3 (by simpa [experiment1Groups] using h .lessThan3 rfl)
      · exact h .each rfl (by simpa [experiment1Groups] using he .each)
  · rw [ite_eq_right ha, verdict, predicted_eq_none ha]
    rfl

/-- §4.1.2's stipulations give every account the verdict that Appendix F's rule gives it. -/
theorem verdict_stipulated (a : Account) : verdict a stipulated = verdict a oneStep := by
  rw [verdict, verdict, parse_oneStep]

end Eval.Projection.Chemla2009a
