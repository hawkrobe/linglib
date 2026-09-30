module

public import Linglib.Semantics.Presupposition.Formula
public import Linglib.Semantics.Presupposition.LocalContext

/-!
# Syntactic environments

A syntactic environment `a _ b` is a formula with a gap ([schlenker-2009]). It is represented by
the steps from the gap to the root, innermost first (`SyntacticEnvironment`): the argument of a
negation, or the first or the second argument of a binary connective whose other argument is given.
Filling the gap gives a formula (`SyntacticEnvironment.fill`), and the environment's meaning is the
function from the gap's truth set to the formula's (`SyntacticEnvironment.truth`). The triggers of a
formula are listed with their environments by `Formula.occurrences`.

The incremental theories of projection consult every good final of the initial string up to a
trigger: `SameInitialString K K'` holds when `K'` keeps the material of `K` before the gap and
replaces what follows it. For the first argument of a conjunction or a disjunction the connective
itself follows the gap in the string, so it may be replaced too, while *if* precedes its
antecedent.

[karttunen-1974-presupposition]'s local context of a gap (`SyntacticEnvironment.localContext`) is
recovered from the good finals: some good final makes the formula's truth value at a world depend on
the gap iff the world is in the local context (`SyntacticEnvironment.exists_dependsAt_iff`), and the
presupposition computed by the filtering connectives holds at a world iff every trigger's
presupposition holds there whenever the world is in the trigger's local context
(`Formula.filter_presup_iff`).

## Main definitions

* `Presupposition.SyntacticEnvironment`: a formula with a gap.
* `Presupposition.SyntacticEnvironment.fill`, `Presupposition.SyntacticEnvironment.truth`: filling
  the gap, and the meaning as a function of the gap's.
* `Presupposition.Formula.occurrences`: the triggers of a formula with their environments.
* `Presupposition.SyntacticEnvironment.SameInitialString`: the environments of the good finals.
* `Presupposition.SyntacticEnvironment.localContext`: [karttunen-1974-presupposition]'s local
  context of the gap.

## References

* [schlenker-2009]
* [karttunen-1974-presupposition]
* [peters-1979]
-/

@[expose] public section

namespace Presupposition

variable {Atom W : Type*}

/-- One step from a gap to the root: the argument of a negation, or the first (`left`) or second
(`right`) argument of a binary connective whose other argument is given. -/
inductive SyntacticEnvironment.Step (Atom : Type*) where
  | not
  | left (c : Connective) (G : Formula Atom)
  | right (c : Connective) (F : Formula Atom)
  deriving DecidableEq

/-- A syntactic environment `a _ b`: a formula with a gap, as the steps from the gap to the root,
innermost first. -/
abbrev SyntacticEnvironment (Atom : Type*) := List (SyntacticEnvironment.Step Atom)

namespace SyntacticEnvironment

namespace Step

/-- Fill the gap of a step. -/
def fill : Step Atom → Formula Atom → Formula Atom
  | not, X => .not X
  | left c G, X => .bin c X G
  | right c F, X => .bin c F X

/-- The meaning of a step as a function of the gap's truth set. -/
def truth (I : Atom → Set W) : Step Atom → Set W → Set W
  | not, d => dᶜ
  | left c G, d => {w | c.eval (w ∈ d) (w ∈ G.truth I)}
  | right c F, d => {w | c.eval (w ∈ F.truth I) (w ∈ d)}

/-- [karttunen-1974-presupposition]'s local context of the gap of a step in the context `C`: the
second argument of a binary connective is evaluated in `C` updated as `Connective.localContext`
prescribes, and any other gap in `C` itself. -/
def localContext (I : Atom → Set W) : Step Atom → Set W → Set W
  | right c F, C => c.localContext C (F.truth I)
  | _, C => C

theorem truth_fill (I : Atom → Set W) (s : Step Atom) (X : Formula Atom) :
    (s.fill X).truth I = s.truth I (X.truth I) := by
  cases s <;> rfl

theorem localContext_eq_inter (I : Atom → Set W) (s : Step Atom) (C : Set W) :
    s.localContext I C = C ∩ s.localContext I Set.univ := by
  cases s with
  | right c F => cases c <;> simp [localContext, Connective.localContext]
  | _ => simp [localContext]

end Step

/-- Fill the gap of an environment. -/
def fill : SyntacticEnvironment Atom → Formula Atom → Formula Atom
  | [], X => X
  | s :: K, X => fill K (s.fill X)

/-- The meaning of an environment as a function of the gap's truth set. -/
def truth (I : Atom → Set W) : SyntacticEnvironment Atom → Set W → Set W
  | [], d => d
  | s :: K, d => truth I K (s.truth I d)

/-- [karttunen-1974-presupposition]'s local context of the gap of an environment, computed from
the root. -/
def localContext (I : Atom → Set W) (K : SyntacticEnvironment Atom) (C : Set W) : Set W :=
  K.foldr (fun s C ↦ s.localContext I C) C

@[simp] theorem fill_nil (X : Formula Atom) : fill [] X = X := rfl

@[simp] theorem fill_cons (s : Step Atom) (K : SyntacticEnvironment Atom) (X : Formula Atom) :
    fill (s :: K) X = fill K (s.fill X) := rfl

theorem fill_append (K K' : SyntacticEnvironment Atom) (X : Formula Atom) :
    fill (K ++ K') X = fill K' (fill K X) := by
  induction K generalizing X with
  | nil => rfl
  | cons s K ih => exact ih _

theorem truth_fill (I : Atom → Set W) (K : SyntacticEnvironment Atom) (X : Formula Atom) :
    (K.fill X).truth I = K.truth I (X.truth I) := by
  induction K generalizing X with
  | nil => rfl
  | cons s K ih => rw [fill_cons, ih, Step.truth_fill]; rfl

@[simp] theorem localContext_nil (I : Atom → Set W) (C : Set W) :
    localContext I [] C = C := rfl

@[simp] theorem localContext_cons (I : Atom → Set W) (s : Step Atom)
    (K : SyntacticEnvironment Atom) (C : Set W) :
    localContext I (s :: K) C = s.localContext I (localContext I K C) := rfl

theorem localContext_append (I : Atom → Set W) (K K' : SyntacticEnvironment Atom) (C : Set W) :
    localContext I (K ++ K') C = localContext I K (localContext I K' C) :=
  List.foldr_append

theorem localContext_eq_inter (I : Atom → Set W) (K : SyntacticEnvironment Atom) (C : Set W) :
    localContext I K C = C ∩ localContext I K Set.univ := by
  induction K with
  | nil => simp
  | cons s K ih =>
    rw [localContext_cons, localContext_cons, Step.localContext_eq_inter, ih,
      Step.localContext_eq_inter I s (localContext I K Set.univ), Set.inter_assoc]

/-- `SameInitialString K K'`: `K'` keeps the material of `K` before the gap and replaces what
follows it, so that it is `K` with another good final. The first argument of a conjunction or a
disjunction is followed by the connective, which may be replaced by either; *if* precedes its
antecedent. -/
inductive SameInitialString : SyntacticEnvironment Atom → SyntacticEnvironment Atom → Prop
  | nil : SameInitialString [] []
  | not {K K' : SyntacticEnvironment Atom} :
      SameInitialString K K' → SameInitialString (.not :: K) (.not :: K')
  | right {K K' : SyntacticEnvironment Atom} (c : Connective) (F : Formula Atom) :
      SameInitialString K K' → SameInitialString (.right c F :: K) (.right c F :: K')
  | left {K K' : SyntacticEnvironment Atom} {c c' : Connective} (hc : c = .cond ↔ c' = .cond)
      (G G' : Formula Atom) :
      SameInitialString K K' → SameInitialString (.left c G :: K) (.left c' G' :: K')

@[refl] theorem SameInitialString.refl (K : SyntacticEnvironment Atom) : SameInitialString K K := by
  induction K with
  | nil => exact .nil
  | cons s K ih =>
    cases s with
    | not => exact .not ih
    | right c F => exact .right c F ih
    | left c G => exact .left Iff.rfl G G ih

end SyntacticEnvironment

namespace Formula

open SyntacticEnvironment

/-- The triggers of a formula, each with its environment and its presupposition and assertion:
`K.fill (trigger p p') = F` for every `(K, p, p')` listed. -/
def occurrences : Formula Atom → List (SyntacticEnvironment Atom × Atom × Atom)
  | atom _ => []
  | trigger p p' => [([], p, p')]
  | not F => (occurrences F).map fun o ↦ (o.1 ++ [.not], o.2)
  | bin c F G => (occurrences F).map (fun o ↦ (o.1 ++ [.left c G], o.2)) ++
      (occurrences G).map fun o ↦ (o.1 ++ [.right c F], o.2)

theorem fill_of_mem_occurrences {F : Formula Atom} {o : SyntacticEnvironment Atom × Atom × Atom}
    (h : o ∈ F.occurrences) : o.1.fill (trigger o.2.1 o.2.2) = F := by
  induction F generalizing o with
  | atom => simp [occurrences] at h
  | trigger p p' => simp only [occurrences, List.mem_singleton] at h; subst h; rfl
  | not F ih =>
    obtain ⟨o', ho', rfl⟩ := List.mem_map.1 h
    rw [fill_append, ih ho']; rfl
  | bin c F G ihF ihG =>
    rcases List.mem_append.1 h with h | h <;> obtain ⟨o', ho', rfl⟩ := List.mem_map.1 h
    · rw [fill_append, ihF ho']; rfl
    · rw [fill_append, ihG ho']; rfl

end Formula

/-! ### Karttunen's local contexts from the good finals -/

namespace SyntacticEnvironment

variable (I : Atom → Set W)

theorem isTruthFunctional_truth (K : SyntacticEnvironment Atom) :
    IsTruthFunctional (K.truth I) := by
  induction K with
  | nil => exact fun _ _ _ h ↦ h
  | cons s K ih =>
    intro w d d' h
    refine ih w _ _ ?_
    cases s <;> simp [Step.truth, h]

/-- The formula's truth value depends on the gap of `s :: K` iff it depends on the gap of `s` and
on the gap of `K`. -/
theorem dependsAt_truth_cons {s : Step Atom} {K : SyntacticEnvironment Atom} {w : W} :
    DependsAt (truth I (s :: K)) w ↔ DependsAt (s.truth I) w ∧ DependsAt (K.truth I) w := by
  have hK := isTruthFunctional_truth I K
  change ¬ (w ∈ K.truth I (s.truth I Set.univ) ↔ w ∈ K.truth I (s.truth I ∅)) ↔ _
  unfold DependsAt
  by_cases ha : w ∈ s.truth I Set.univ <;> by_cases hb : w ∈ s.truth I ∅
  · rw [hK.mem_iff_of_mem ha, hK.mem_iff_of_mem hb]; tauto
  · rw [hK.mem_iff_of_mem ha, hK.mem_iff_of_notMem hb]; tauto
  · rw [hK.mem_iff_of_notMem ha, hK.mem_iff_of_mem hb]; tauto
  · rw [hK.mem_iff_of_notMem ha, hK.mem_iff_of_notMem hb]; tauto

/-- The truth value depends on the second argument of a binary connective exactly in its local
context. -/
theorem dependsAt_right_iff (c : Connective) (F : Formula Atom) (w : W) :
    DependsAt ((Step.right c F).truth I) w ↔ w ∈ (Step.right c F).localContext I Set.univ := by
  cases c <;> simp [DependsAt, Step.truth, Step.localContext, Connective.eval,
    Connective.localContext]

/-- Some second argument makes the truth value depend on the first argument of a binary
connective. -/
theorem exists_dependsAt_left [Nonempty Atom] (c : Connective) (w : W) :
    ∃ G, DependsAt ((Step.left c G).truth I) w := by
  let a := Classical.arbitrary Atom
  let taut : Formula Atom := .bin .cond (.atom a) (.atom a)
  cases c
  · exact ⟨taut, by simp [taut, DependsAt, Step.truth, Connective.eval, Formula.truth]⟩
  · exact ⟨.not taut, by simp [taut, DependsAt, Step.truth, Connective.eval, Formula.truth]⟩
  · exact ⟨.not taut, by simp [taut, DependsAt, Step.truth, Connective.eval, Formula.truth]⟩

private theorem mem_localContext_of_dependsAt {K K' : SyntacticEnvironment Atom}
    (h : SameInitialString K K') {w : W} (hw : DependsAt (K'.truth I) w) :
    w ∈ K.localContext I Set.univ := by
  induction h with
  | nil => trivial
  | not _ ih => exact ih ((dependsAt_truth_cons I).1 hw).2
  | right c F _ ih =>
    obtain ⟨hs, hK⟩ := (dependsAt_truth_cons I).1 hw
    rw [localContext_cons, Step.localContext_eq_inter]
    exact ⟨ih hK, (dependsAt_right_iff I c F w).1 hs⟩
  | left _ _ _ _ ih => exact ih ((dependsAt_truth_cons I).1 hw).2

/-- Some good final makes the truth value at `w` depend on the gap of `K` iff `w` is in
[karttunen-1974-presupposition]'s local context of the gap. -/
theorem exists_dependsAt_iff [Nonempty Atom] (K : SyntacticEnvironment Atom) (w : W) :
    (∃ K', SameInitialString K K' ∧ DependsAt (K'.truth I) w) ↔
      w ∈ K.localContext I Set.univ := by
  refine ⟨fun ⟨_, hK', hw⟩ ↦ mem_localContext_of_dependsAt I hK' hw, fun hw ↦ ?_⟩
  induction K with
  | nil => exact ⟨[], .nil, by simp [DependsAt, truth]⟩
  | cons s K ih =>
    rw [localContext_cons, Step.localContext_eq_inter] at hw
    obtain ⟨K', hK', hdep⟩ := ih hw.1
    cases s with
    | not =>
      exact ⟨.not :: K', .not hK',
        (dependsAt_truth_cons I).2 ⟨by simp [DependsAt, Step.truth], hdep⟩⟩
    | right c F =>
      exact ⟨.right c F :: K', .right c F hK',
        (dependsAt_truth_cons I).2 ⟨(dependsAt_right_iff I c F w).2 hw.2, hdep⟩⟩
    | left c G =>
      obtain ⟨G', hG'⟩ := exists_dependsAt_left I c w
      exact ⟨.left c G' :: K', .left Iff.rfl G G' hK', (dependsAt_truth_cons I).2 ⟨hG', hdep⟩⟩

end SyntacticEnvironment

/-- The presupposition computed by the filtering connectives holds at `w` iff every trigger's
presupposition holds there whenever `w` is in the trigger's [karttunen-1974-presupposition] local
context. -/
theorem Formula.filter_presup_iff (I : Atom → Set W) (F : Formula Atom) (w : W) :
    (F.filter I).presup w ↔
      ∀ o ∈ F.occurrences, w ∈ o.1.localContext I Set.univ → w ∈ I o.2.1 := by
  open SyntacticEnvironment in
  induction F with
  | atom p => simp [filter, occurrences]
  | trigger p p' => simp [filter, occurrences]
  | not F ih =>
    simp only [occurrences, List.forall_mem_map, localContext_append, localContext_cons,
      localContext_nil, Step.localContext]
    exact ih
  | bin c F G ihF ihG =>
    simp only [occurrences, List.forall_mem_append, List.forall_mem_map, localContext_append,
      localContext_cons, localContext_nil, Step.localContext]
    rw [← ihF]
    have hG : (∀ o ∈ G.occurrences, w ∈ o.1.localContext I (c.localContext Set.univ (F.truth I)) →
        w ∈ I o.2.1) ↔ (w ∈ c.localContext Set.univ (F.truth I) → (G.filter I).presup w) := by
      rw [ihG]
      refine ⟨fun h hc o ho hl ↦ h o ho ?_, fun h o ho hl ↦ ?_⟩
      · rw [localContext_eq_inter]; exact ⟨hc, hl⟩
      · rw [localContext_eq_inter] at hl; exact h hl.1 o ho hl.2
    rw [hG]
    have assert {w} (hw : (F.filter I).presup w) := filter_assertion_iff I hw
    cases c
    · exact ⟨fun ⟨hp, h⟩ ↦ ⟨hp, fun hc ↦ h ((assert hp).2 hc.2)⟩,
        fun ⟨hp, h⟩ ↦ ⟨hp, fun ha ↦ h ⟨trivial, (assert hp).1 ha⟩⟩⟩
    · exact ⟨fun ⟨hp, h⟩ ↦ ⟨hp, fun hc ↦ h ((assert hp).2 hc.2)⟩,
        fun ⟨hp, h⟩ ↦ ⟨hp, fun ha ↦ h ⟨trivial, (assert hp).1 ha⟩⟩⟩
    · exact ⟨fun ⟨hp, h⟩ ↦ ⟨hp, fun hc ↦ h fun ha ↦ hc.2 ((assert hp).1 ha)⟩,
        fun ⟨hp, h⟩ ↦ ⟨hp, fun hn ↦ h ⟨trivial, fun ht ↦ hn ((assert hp).2 ht)⟩⟩⟩

end Presupposition
