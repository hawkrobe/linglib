module

public import Linglib.Semantics.Presupposition.LocalContext
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Dynamic.Partial

/-!
# The propositional fragment of presupposition projection

This file defines the language on which theories of presupposition projection are compared: the
propositional fragment of the language L of [schlenker-2009]'s Appendix C, which is also the
language of [kalomoiros-2023]'s System 1. A formula is built from atoms and triggers by negation
and the binary connectives of `Connective`; a trigger `trig p p'` presupposes `p` and asserts `p'`,
and its classical meaning is the conjunction of the two (`Formula.truth`, C.2).

A position in a formula is a one-hole context, a `Frame`: the list of steps from the hole to the
root, innermost first (`Frame.plug`). The triggers of a formula are listed with their frames by
`Formula.occurrences`. Theories differ in which continuations of the string up to a trigger they
consult, and the continuations are fixed by a parse point: `Frame.AgreeUpTo n K K'` holds when
`K'` has the material of `K` to the left of the hole and the first `n` items to its right. At
`n = 0` every good final is admitted, which is the incremental theories' quantification; at
`n = K.rightItems` only the actual sentence is, which is the symmetric theories'; the points in
between are [kalomoiros-2023]'s. For the first argument of a conjunction or a disjunction the
connective itself follows the hole in the string, so at `n = 0` it is free, while *if* precedes
its antecedent.

Each binary connective is interpreted classically (`Connective.eval`), by [peters-1979]'s
filtering connectives (`Connective.filter`), and by the context change potentials of [heim-1983],
with [beaver-2001]'s disjunction (`Connective.ccp`). The fold `Formula.filter` evaluates a formula
into `PartialProp`, and `Formula.ccp` into `CCP.Partial`. The context change potential admits a context iff the context
entails the filtering presupposition, and it updates the context to its worlds at which the formula
is classically true (`Formula.admits_ccp_iff`, `Formula.ccp_get`).

[karttunen-1974-presupposition]'s local context of a position (`Frame.localContext`) is recovered
from the continuations twice. Some good final makes the position matter to the sentence's truth
value at a world iff the world is in the local context (`Frame.exists_isLive_iff`), and the
filtering presupposition holds at a world iff every trigger's presupposition holds there whenever
the world is in the trigger's local context (`Formula.filter_presup_iff`).

## Main definitions

* `Presupposition.Formula`: atoms, triggers, negation and the binary connectives.
* `Presupposition.Formula.truth`: the classical meaning at an interpretation of the atoms.
* `Presupposition.Formula.filter`, `Presupposition.Formula.ccp`: the filtering and dynamic
  evaluations.
* `Presupposition.Frame`, `Presupposition.Frame.plug`, `Presupposition.Frame.toEnv`: one-hole
  contexts, their filling, and their meaning as a function of the hole's meaning.
* `Presupposition.Formula.occurrences`: the triggers of a formula with their frames.
* `Presupposition.Frame.AgreeUpTo`, `Presupposition.Frame.env`: agreement on the material up to a
  parse point, and the continuations it admits.
* `Presupposition.Frame.localContext`: [karttunen-1974-presupposition]'s local context of a
  position.

## Implementation notes

The interpretation of the atoms is a function to `Set W`. [schlenker-2009]'s Expressivity (C.3),
that every proposition is denoted by an atom, is not built in: the theories that need it quantify
over propositions where the paper quantifies over expressions. The conditional is material, as in
the paper.

## References

* [schlenker-2009]
* [kalomoiros-2023]
* [karttunen-1974-presupposition]
* [peters-1979]
* [heim-1983]
* [beaver-2001]
-/

@[expose] public section

namespace Presupposition

open DynamicSemantics

variable {Atom W : Type*}

/-! ### Connectives -/

namespace Connective

/-- The classical truth function of a binary connective. -/
def eval : Connective → Prop → Prop → Prop
  | conj, a, b => a ∧ b
  | cond, a, b => a → b
  | disj, a, b => a ∨ b

/-- The number of items of the string that follow the first argument: the connective and the
second argument for a conjunction or a disjunction, only the second argument for *if*, which
precedes its antecedent. -/
def rightItems : Connective → ℕ
  | cond => 1
  | _ => 2

/-- [peters-1979]'s filtering connectives, the Middle Kleene tables. -/
def filter : Connective → PartialProp W → PartialProp W → PartialProp W
  | conj, p, q => p.andFilter q
  | cond, p, q => p.impFilter q
  | disj, p, q => p.orFilter q

/-- The dynamic connectives: [heim-1983]'s conjunction and conditional, and [beaver-2001]'s
disjunction. -/
noncomputable def ccp : Connective → CCP.Partial W → CCP.Partial W → CCP.Partial W
  | .conj => PartialUpdate.seq
  | .cond => CCP.Partial.cond
  | .disj => CCP.Partial.disj

end Connective

/-! ### Formulas -/

/-- The propositional fragment of L (C.1): a trigger `trig p p'` presupposes `p` and asserts
`p'`. -/
inductive Formula (Atom : Type*) where
  | atom (p : Atom)
  | trig (presup assert : Atom)
  | not (F : Formula Atom)
  | bin (c : Connective) (F G : Formula Atom)
  deriving DecidableEq

namespace Formula

variable (I : Atom → Set W)

/-- C.2: the classical meaning, with a trigger read as the conjunction of its two parts. -/
def truth : Formula Atom → Set W
  | atom p => I p
  | trig p p' => I p ∩ I p'
  | not F => (truth F)ᶜ
  | bin c F G => {w | c.eval (w ∈ truth F) (w ∈ truth G)}

/-- The evaluation by the filtering connectives. -/
def filter : Formula Atom → PartialProp W
  | atom p => ⟨fun _ ↦ True, (· ∈ I p)⟩
  | trig p p' => ⟨(· ∈ I p), (· ∈ I p')⟩
  | not F => (filter F).neg
  | bin c F G => c.filter (filter F) (filter G)

/-- The context change potential of a formula: a trigger is defined in a context that entails its
presupposition. -/
noncomputable def ccp : Formula Atom → CCP.Partial W
  | atom p => CCP.Partial.ofPartialProp ⟨fun _ ↦ True, (· ∈ I p)⟩
  | trig p p' => CCP.Partial.ofPartialProp ⟨(· ∈ I p), (· ∈ I p')⟩
  | not F => CCP.Partial.neg (ccp F)
  | bin c F G => c.ccp (ccp F) (ccp G)

/-- On its presupposition, the filtering evaluation asserts the classical meaning. -/
theorem filter_assertion_iff {F : Formula Atom} {w : W} (h : (F.filter I).presup w) :
    (F.filter I).assertion w ↔ w ∈ F.truth I := by
  induction F with
  | atom p => exact Iff.rfl
  | trig p p' => exact ⟨fun h' ↦ ⟨h, h'⟩, fun h' ↦ h'.2⟩
  | not F ih => exact not_congr (ih h)
  | bin c F G ihF ihG =>
    cases c <;> have hF := ihF h.1
    · exact ⟨fun ⟨a, b⟩ ↦ ⟨hF.1 a, (ihG (h.2 a)).1 b⟩,
        fun ⟨a, b⟩ ↦ ⟨hF.2 a, (ihG (h.2 (hF.2 a))).2 b⟩⟩
    · exact ⟨fun f t ↦ (ihG (h.2 (hF.2 t))).1 (f (hF.2 t)),
        fun g a ↦ (ihG (h.2 a)).2 (g (hF.1 a))⟩
    · by_cases a : (F.filter I).assertion w
      · exact ⟨fun _ ↦ Or.inl (hF.1 a), fun _ ↦ Or.inl a⟩
      · have hG := ihG (h.2 a)
        exact ⟨fun h' ↦ h'.elim (fun a' ↦ absurd a' a) (fun b ↦ Or.inr (hG.1 b)),
          fun h' ↦ h'.elim (fun t ↦ absurd (hF.2 t) a) (fun t ↦ Or.inr (hG.2 t))⟩

private theorem ccp_spec (F : Formula Atom) : ∀ C : Set W,
    ((F.ccp I).Admits C → (F.filter I).Admits C) ∧
      ((F.filter I).Admits C → C ∩ F.truth I ∈ F.ccp I C) := by
  induction F with
  | atom p => exact fun C ↦ ⟨id, fun h ↦ ⟨h, rfl⟩⟩
  | trig p p' =>
    exact fun C ↦ ⟨id, fun h ↦ ⟨h, Set.ext fun w ↦
      ⟨fun ⟨hc, hp'⟩ ↦ ⟨hc, h hc, hp'⟩, fun ⟨hc, _, hp'⟩ ↦ ⟨hc, hp'⟩⟩⟩⟩
  | not F ih =>
    refine fun C ↦ ⟨(ih C).1, fun h ↦ (Part.mem_map_iff _).2 ⟨_, (ih C).2 h, ?_⟩⟩
    rw [Set.sdiff_self_inter, Set.sdiff_eq]; rfl
  | bin c F G ihF ihG =>
    intro C
    have assert {w} (hw : (F.filter I).presup w) := filter_assertion_iff I hw
    cases c
    · refine ⟨fun ⟨hφ, hψ⟩ ↦ ?_, fun h ↦ ?_⟩
      · have hF := (ihF C).1 hφ
        beta_reduce at hψ
        rw [Part.get_eq_of_mem ((ihF C).2 hF) hφ] at hψ
        exact fun w hw ↦ ⟨hF hw, fun a ↦ (ihG _).1 hψ ⟨hw, (assert (hF hw)).1 a⟩⟩
      · have hm := (ihG (C ∩ F.truth I)).2 fun w ⟨hw, t⟩ ↦ (h hw).2 ((assert (h hw).1).2 t)
        rw [Set.inter_assoc] at hm
        exact Part.mem_bind_iff.2 ⟨_, (ihF C).2 fun w hw ↦ (h hw).1, hm⟩
    · refine ⟨fun ⟨hφ, hψ⟩ ↦ ?_, fun h ↦ ?_⟩
      · have hF := (ihF C).1 hφ
        beta_reduce at hψ
        rw [Part.get_eq_of_mem ((ihF C).2 hF) hφ] at hψ
        exact fun w hw ↦ ⟨hF hw, fun a ↦ (ihG _).1 hψ ⟨hw, (assert (hF hw)).1 a⟩⟩
      · refine Part.mem_bind_iff.2 ⟨_, (ihF C).2 fun w hw ↦ (h hw).1,
          (Part.mem_map_iff _).2 ⟨_, (ihG _).2 fun w ⟨hw, t⟩ ↦ (h hw).2 ((assert (h hw).1).2 t),
            ?_⟩⟩
        ext w
        simp only [Set.mem_sdiff, Set.mem_inter_iff, truth, Connective.eval, Set.mem_ofPred_eq]
        tauto
    · refine ⟨fun ⟨hφ, hψ⟩ ↦ ?_, fun h ↦ ?_⟩
      · have hF := (ihF C).1 hφ
        beta_reduce at hψ
        rw [Part.get_eq_of_mem ((ihF C).2 hF) hφ] at hψ
        exact fun w hw ↦ ⟨hF hw, fun a ↦ (ihG _).1 hψ
          ⟨hw, fun ⟨_, t⟩ ↦ a ((assert (hF hw)).2 t)⟩⟩
      · refine Part.mem_bind_iff.2 ⟨_, (ihF C).2 fun w hw ↦ (h hw).1,
          (Part.mem_map_iff _).2 ⟨_, (ihG _).2 fun w ⟨hw, ht⟩ ↦
            (h hw).2 fun a ↦ ht ⟨hw, (assert (h hw).1).1 a⟩, ?_⟩⟩
        ext w
        simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, truth, Connective.eval,
          Set.mem_ofPred_eq]
        tauto

/-- The context change potential of a formula admits a context iff the context entails the
presupposition computed by the filtering connectives. -/
theorem admits_ccp_iff {F : Formula Atom} {C : Set W} :
    (F.ccp I).Admits C ↔ (F.filter I).Admits C :=
  ⟨(ccp_spec I F C).1, fun h ↦ Part.dom_iff_mem.2 ⟨_, (ccp_spec I F C).2 h⟩⟩

/-- The context change potential updates a context to its worlds at which the formula is
classically true. -/
theorem ccp_get {F : Formula Atom} {C : Set W} (h : (F.ccp I).Admits C) :
    (F.ccp I C).get h = C ∩ F.truth I :=
  Part.get_eq_of_mem ((ccp_spec I F C).2 ((admits_ccp_iff I).1 h)) h

end Formula

/-! ### Frames -/

/-- One step from a hole to the root: the argument of a negation, or the first (`left`) or second
(`right`) argument of a binary connective whose other argument is given. -/
inductive Frame.Step (Atom : Type*) where
  | not
  | left (c : Connective) (G : Formula Atom)
  | right (c : Connective) (F : Formula Atom)
  deriving DecidableEq

/-- A one-hole context, innermost step first. -/
abbrev Frame (Atom : Type*) := List (Frame.Step Atom)

namespace Frame

namespace Step

/-- Fill the hole of a step. -/
def fill : Step Atom → Formula Atom → Formula Atom
  | not, X => .not X
  | left c G, X => .bin c X G
  | right c F, X => .bin c F X

/-- The meaning of a step as a function of the hole's meaning. -/
def toEnv (I : Atom → Set W) : Step Atom → Set W → Set W
  | not, d => dᶜ
  | left c G, d => {w | c.eval (w ∈ d) (w ∈ G.truth I)}
  | right c F, d => {w | c.eval (w ∈ F.truth I) (w ∈ d)}

/-- The number of items of the string that a step places after the hole. -/
def rightItems : Step Atom → ℕ
  | left c _ => c.rightItems
  | _ => 0

theorem truth_fill (I : Atom → Set W) (s : Step Atom) (X : Formula Atom) :
    (s.fill X).truth I = s.toEnv I (X.truth I) := by
  cases s <;> rfl

end Step

/-- Fill the hole of a frame. -/
def plug : Frame Atom → Formula Atom → Formula Atom
  | [], X => X
  | s :: K, X => plug K (s.fill X)

/-- The meaning of a frame as a function of the hole's meaning. -/
def toEnv (I : Atom → Set W) : Frame Atom → Set W → Set W
  | [], d => d
  | s :: K, d => toEnv I K (s.toEnv I d)

/-- The number of items of the string after the hole. -/
def rightItems (K : Frame Atom) : ℕ := (K.map Step.rightItems).sum

@[simp] theorem plug_nil (X : Formula Atom) : plug [] X = X := rfl

@[simp] theorem plug_cons (s : Step Atom) (K : Frame Atom) (X : Formula Atom) :
    plug (s :: K) X = plug K (s.fill X) := rfl

theorem plug_append (K K' : Frame Atom) (X : Formula Atom) :
    plug (K ++ K') X = plug K' (plug K X) := by
  induction K generalizing X with
  | nil => rfl
  | cons s K ih => exact ih _

theorem truth_plug (I : Atom → Set W) (K : Frame Atom) (X : Formula Atom) :
    (K.plug X).truth I = K.toEnv I (X.truth I) := by
  induction K generalizing X with
  | nil => rfl
  | cons s K ih => rw [plug_cons, ih, Step.truth_fill]; rfl

/-- [karttunen-1974-presupposition]'s local context of the hole of a step in the context `C`:
the second argument of a binary connective is evaluated in `C` updated as `Connective.localContext`
prescribes, and any other hole in `C` itself. -/
def Step.localContext (I : Atom → Set W) : Step Atom → Set W → Set W
  | right c F, C => c.localContext C (F.truth I)
  | _, C => C

/-- [karttunen-1974-presupposition]'s local context of the hole of a frame, computed from the
root. -/
def localContext (I : Atom → Set W) (K : Frame Atom) (C : Set W) : Set W :=
  K.foldr (fun s C ↦ s.localContext I C) C

@[simp] theorem localContext_nil (I : Atom → Set W) (C : Set W) :
    localContext I [] C = C := rfl

@[simp] theorem localContext_cons (I : Atom → Set W) (s : Step Atom) (K : Frame Atom)
    (C : Set W) : localContext I (s :: K) C = s.localContext I (localContext I K C) := rfl

theorem localContext_append (I : Atom → Set W) (K K' : Frame Atom) (C : Set W) :
    localContext I (K ++ K') C = localContext I K (localContext I K' C) :=
  List.foldr_append

theorem Step.localContext_eq_inter (I : Atom → Set W) (s : Step Atom) (C : Set W) :
    s.localContext I C = C ∩ s.localContext I Set.univ := by
  cases s with
  | right c F => cases c <;> simp [localContext, Connective.localContext]
  | _ => simp [localContext]

theorem localContext_eq_inter (I : Atom → Set W) (K : Frame Atom) (C : Set W) :
    localContext I K C = C ∩ localContext I K Set.univ := by
  induction K with
  | nil => simp
  | cons s K ih =>
    rw [localContext_cons, localContext_cons, Step.localContext_eq_inter, ih,
      Step.localContext_eq_inter I s (localContext I K Set.univ), Set.inter_assoc]

/-- `AgreeUpTo n K K'`: `K'` has the material of `K` to the left of the hole and the first `n`
items to its right. The first argument of a conjunction or a disjunction is followed by the
connective and then the second argument, so with no item fixed either connective may follow;
*if* precedes its antecedent and is left material. -/
inductive AgreeUpTo : ℕ → Frame Atom → Frame Atom → Prop
  | nil (n : ℕ) : AgreeUpTo n [] []
  | not {n : ℕ} {K K' : Frame Atom} : AgreeUpTo n K K' → AgreeUpTo n (.not :: K) (.not :: K')
  | right {n : ℕ} {K K' : Frame Atom} (c : Connective) (F : Formula Atom) :
      AgreeUpTo n K K' → AgreeUpTo n (.right c F :: K) (.right c F :: K')
  /-- No item after the hole is fixed: the second argument is free, and so is the connective
  unless it is *if*. -/
  | left_zero {K K' : Frame Atom} {c c' : Connective} (hc : c = .cond ↔ c' = .cond)
      (G G' : Formula Atom) :
      AgreeUpTo 0 K K' → AgreeUpTo 0 (.left c G :: K) (.left c' G' :: K')
  /-- Only the connective of a conjunction or a disjunction is fixed. -/
  | left_one {K K' : Frame Atom} {c : Connective} (hc : c ≠ .cond) (G G' : Formula Atom) :
      AgreeUpTo 0 K K' → AgreeUpTo 1 (.left c G :: K) (.left c G' :: K')
  /-- The connective and the second argument are fixed. -/
  | left {n : ℕ} {K K' : Frame Atom} (c : Connective) (G : Formula Atom) :
      AgreeUpTo n K K' → AgreeUpTo (n + c.rightItems) (.left c G :: K) (.left c G :: K')

namespace AgreeUpTo

theorem refl (n : ℕ) (K : Frame Atom) : AgreeUpTo n K K := by
  induction K generalizing n with
  | nil => exact .nil n
  | cons s K ih =>
    cases s with
    | not => exact .not (ih n)
    | right c F => exact .right c F (ih n)
    | left c G =>
      by_cases hn : c.rightItems ≤ n
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
        exact .left c G (ih m)
      · rcases n with _ | _ | n
        · exact .left_zero Iff.rfl G G (ih 0)
        · cases c
          · exact .left_one (by decide) G G (ih 0)
          · exact absurd hn (by decide)
          · exact .left_one (by decide) G G (ih 0)
        · cases c <;> exact absurd hn (by simp [Connective.rightItems])

/-- Agreement up to a later point implies agreement up to an earlier one. -/
theorem mono {m n : ℕ} {K K' : Frame Atom} (h : AgreeUpTo m K K') (hnm : n ≤ m) :
    AgreeUpTo n K K' := by
  induction h generalizing n with
  | nil => exact .nil n
  | not _ ih => exact .not (ih hnm)
  | right c F _ ih => exact .right c F (ih hnm)
  | left_zero hc G G' h _ => exact Nat.le_zero.1 hnm ▸ .left_zero hc G G' h
  | left_one hc G G' h _ =>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hnm with rfl | rfl
    · exact .left_zero Iff.rfl G G' h
    · exact .left_one hc G G' h
  | @left m K K' c G h ih =>
    by_cases hn : c.rightItems ≤ n
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
      exact .left c G (ih (by omega))
    · rcases n with _ | _ | n
      · exact .left_zero Iff.rfl G G (ih (Nat.zero_le _))
      · cases c
        · exact .left_one (by decide) G G (ih (Nat.zero_le _))
        · exact absurd hn (by decide)
        · exact .left_one (by decide) G G (ih (Nat.zero_le _))
      · cases c <;> exact absurd hn (by simp [Connective.rightItems])

end AgreeUpTo

@[simp] theorem rightItems_nil : rightItems ([] : Frame Atom) = 0 := rfl

@[simp] theorem rightItems_cons (s : Step Atom) (K : Frame Atom) :
    rightItems (s :: K) = s.rightItems + rightItems K := by
  simp [rightItems]

theorem _root_.Presupposition.Connective.one_le_rightItems (c : Connective) :
    1 ≤ c.rightItems := by
  cases c <;> decide

/-- Past the last parse point only the frame itself agrees. -/
theorem AgreeUpTo.eq_of_rightItems_le {n : ℕ} {K K' : Frame Atom} (h : AgreeUpTo n K K')
    (hn : rightItems K ≤ n) : K' = K := by
  induction h with
  | nil => rfl
  | not _ ih => rw [ih (by simpa [Step.rightItems] using hn)]
  | right c F _ ih => rw [ih (by simpa [Step.rightItems] using hn)]
  | @left_zero _ _ c =>
    simp only [rightItems_cons, Step.rightItems] at hn
    have := Connective.one_le_rightItems c; omega
  | @left_one _ _ c hc =>
    simp only [rightItems_cons, Step.rightItems] at hn
    have : c.rightItems = 2 := by cases c <;> first | rfl | exact absurd rfl hc
    omega
  | left c G _ ih =>
    simp only [rightItems_cons, Step.rightItems] at hn
    rw [ih (by omega)]

/-- At the last parse point only the frame itself agrees. -/
theorem agreeUpTo_rightItems_iff {K K' : Frame Atom} : AgreeUpTo (rightItems K) K K' ↔ K' = K :=
  ⟨fun h ↦ h.eq_of_rightItems_le le_rfl, by rintro rfl; exact .refl _ _⟩

/-- The continuations of `K` consulted at parse point `n`, as functions of the hole's meaning. -/
def env (I : Atom → Set W) (n : ℕ) (K : Frame Atom) : Set (Set W → Set W) :=
  toEnv I '' {K' | AgreeUpTo n K K'}

theorem env_anti (I : Atom → Set W) (K : Frame Atom) : Antitone fun n ↦ K.env I n :=
  fun _ _ hmn _ ⟨K', hK', e⟩ ↦ ⟨K', hK'.mono hmn, e⟩

theorem env_rightItems (I : Atom → Set W) (K : Frame Atom) :
    K.env I K.rightItems = {K.toEnv I} := by
  ext f
  refine ⟨?_, fun h ↦ ⟨K, .refl _ K, h.symm⟩⟩
  rintro ⟨K', hK', rfl⟩
  rw [agreeUpTo_rightItems_iff.1 hK']
  rfl

end Frame

namespace Formula

/-- The triggers of a formula, each with its frame and its presupposition and assertion:
`K.plug (trig p p') = F` for every `(K, p, p')` listed. -/
def occurrences : Formula Atom → List (Frame Atom × Atom × Atom)
  | atom _ => []
  | trig p p' => [([], p, p')]
  | not F => (occurrences F).map fun o ↦ (o.1 ++ [.not], o.2)
  | bin c F G => (occurrences F).map (fun o ↦ (o.1 ++ [.left c G], o.2)) ++
      (occurrences G).map fun o ↦ (o.1 ++ [.right c F], o.2)

theorem plug_of_mem_occurrences {F : Formula Atom} {o : Frame Atom × Atom × Atom}
    (h : o ∈ F.occurrences) : o.1.plug (trig o.2.1 o.2.2) = F := by
  induction F generalizing o with
  | atom => simp [occurrences] at h
  | trig p p' => simp only [occurrences, List.mem_singleton] at h; subst h; rfl
  | not F ih =>
    obtain ⟨o', ho', rfl⟩ := List.mem_map.1 h
    rw [Frame.plug_append, ih ho']; rfl
  | bin c F G ihF ihG =>
    rcases List.mem_append.1 h with h | h <;> obtain ⟨o', ho', rfl⟩ := List.mem_map.1 h
    · rw [Frame.plug_append, ihF ho']; rfl
    · rw [Frame.plug_append, ihG ho']; rfl

end Formula

/-! ### Karttunen's local contexts from continuations -/

namespace Frame

variable (I : Atom → Set W)

theorem isTruthFunctional_toEnv (K : Frame Atom) : IsTruthFunctional (K.toEnv I) := by
  induction K with
  | nil => exact fun _ _ _ h ↦ h
  | cons s K ih =>
    intro w d d' h
    refine ih w _ _ ?_
    cases s <;> simp [Step.toEnv, h]

theorem isTruthFunctional_of_mem_env {n : ℕ} {K : Frame Atom} {f : Set W → Set W}
    (hf : f ∈ K.env I n) : IsTruthFunctional f := by
  obtain ⟨K', -, rfl⟩ := hf
  exact isTruthFunctional_toEnv I K'

/-- The hole of `s :: K` is live iff the hole of `s` is and the hole of `K` is. -/
theorem isLive_toEnv_cons {s : Step Atom} {K : Frame Atom} {w : W} :
    IsLive (toEnv I (s :: K)) w ↔ IsLive (s.toEnv I) w ∧ IsLive (K.toEnv I) w := by
  have hK := isTruthFunctional_toEnv I K
  change ¬ (w ∈ K.toEnv I (s.toEnv I Set.univ) ↔ w ∈ K.toEnv I (s.toEnv I ∅)) ↔ _
  unfold IsLive
  by_cases ha : w ∈ s.toEnv I Set.univ <;> by_cases hb : w ∈ s.toEnv I ∅
  · rw [hK.mem_iff_of_mem ha, hK.mem_iff_of_mem hb]; tauto
  · rw [hK.mem_iff_of_mem ha, hK.mem_iff_of_notMem hb]; tauto
  · rw [hK.mem_iff_of_notMem ha, hK.mem_iff_of_mem hb]; tauto
  · rw [hK.mem_iff_of_notMem ha, hK.mem_iff_of_notMem hb]; tauto

/-- The second argument of a binary connective is live exactly in its local context. -/
theorem isLive_right_iff (c : Connective) (F : Formula Atom) (w : W) :
    IsLive ((Step.right c F).toEnv I) w ↔ w ∈ (Step.right c F).localContext I Set.univ := by
  cases c <;> simp [IsLive, Step.toEnv, Step.localContext, Connective.eval,
    Connective.localContext]

/-- Some second argument makes the first argument of a binary connective live. -/
theorem exists_isLive_left [Nonempty Atom] (c : Connective) (w : W) :
    ∃ G, IsLive ((Step.left c G).toEnv I) w := by
  let a := Classical.arbitrary Atom
  let taut : Formula Atom := .bin .cond (.atom a) (.atom a)
  cases c
  · exact ⟨taut, by simp [taut, IsLive, Step.toEnv, Connective.eval, Formula.truth]⟩
  · exact ⟨.not taut, by simp [taut, IsLive, Step.toEnv, Connective.eval, Formula.truth]⟩
  · exact ⟨.not taut, by simp [taut, IsLive, Step.toEnv, Connective.eval, Formula.truth]⟩

private theorem mem_localContext_of_isLive {n : ℕ} {K K' : Frame Atom} (h : AgreeUpTo n K K')
    {w : W} (hw : IsLive (K'.toEnv I) w) : w ∈ K.localContext I Set.univ := by
  induction h with
  | nil => trivial
  | not _ ih => exact ih ((isLive_toEnv_cons I).1 hw).2
  | right c F _ ih =>
    obtain ⟨hs, hK⟩ := (isLive_toEnv_cons I).1 hw
    rw [localContext_cons, Step.localContext_eq_inter]
    exact ⟨ih hK, (isLive_right_iff I c F w).1 hs⟩
  | left_zero _ _ _ _ ih => exact ih ((isLive_toEnv_cons I).1 hw).2
  | left_one _ _ _ _ ih => exact ih ((isLive_toEnv_cons I).1 hw).2
  | left _ _ _ ih => exact ih ((isLive_toEnv_cons I).1 hw).2

/-- Some good final makes the hole of `K` live at `w` iff `w` is in
[karttunen-1974-presupposition]'s local context of the hole. -/
theorem exists_isLive_iff [Nonempty Atom] (K : Frame Atom) (w : W) :
    (∃ f ∈ K.env I 0, IsLive f w) ↔ w ∈ K.localContext I Set.univ := by
  refine ⟨fun ⟨_, ⟨K', hK', e⟩, hw⟩ ↦ mem_localContext_of_isLive I hK' (e ▸ hw), fun hw ↦ ?_⟩
  induction K with
  | nil => exact ⟨id, ⟨[], .nil 0, rfl⟩, by simp [IsLive]⟩
  | cons s K ih =>
    rw [localContext_cons, Step.localContext_eq_inter] at hw
    obtain ⟨_, ⟨K', hK', rfl⟩, hlive⟩ := ih hw.1
    cases s with
    | not =>
      exact ⟨_, ⟨.not :: K', .not hK', rfl⟩,
        (isLive_toEnv_cons I).2 ⟨by simp [IsLive, Step.toEnv], hlive⟩⟩
    | right c F =>
      exact ⟨_, ⟨.right c F :: K', .right c F hK', rfl⟩,
        (isLive_toEnv_cons I).2 ⟨(isLive_right_iff I c F w).2 hw.2, hlive⟩⟩
    | left c G =>
      obtain ⟨G', hG'⟩ := exists_isLive_left I c w
      exact ⟨_, ⟨.left c G' :: K', .left_zero Iff.rfl G G' hK', rfl⟩,
        (isLive_toEnv_cons I).2 ⟨hG', hlive⟩⟩

end Frame

/-- The presupposition computed by the filtering connectives holds at `w` iff every trigger's
presupposition holds there whenever `w` is in the trigger's [karttunen-1974-presupposition] local
context. -/
theorem Formula.filter_presup_iff (I : Atom → Set W) (F : Formula Atom) (w : W) :
    (F.filter I).presup w ↔
      ∀ o ∈ F.occurrences, w ∈ o.1.localContext I Set.univ → w ∈ I o.2.1 := by
  induction F with
  | atom p => simp [filter, occurrences]
  | trig p p' => simp [filter, occurrences]
  | not F ih =>
    simp only [occurrences, List.forall_mem_map, Frame.localContext_append,
      Frame.localContext_cons, Frame.localContext_nil, Frame.Step.localContext]
    exact ih
  | bin c F G ihF ihG =>
    simp only [occurrences, List.forall_mem_append, List.forall_mem_map,
      Frame.localContext_append, Frame.localContext_cons, Frame.localContext_nil,
      Frame.Step.localContext]
    rw [← ihF]
    have hG : (∀ o ∈ G.occurrences, w ∈ o.1.localContext I (c.localContext Set.univ (F.truth I)) →
        w ∈ I o.2.1) ↔ (w ∈ c.localContext Set.univ (F.truth I) → (G.filter I).presup w) := by
      rw [ihG]
      refine ⟨fun h hc o ho hl ↦ h o ho ?_, fun h o ho hl ↦ ?_⟩
      · rw [Frame.localContext_eq_inter]; exact ⟨hc, hl⟩
      · rw [Frame.localContext_eq_inter] at hl; exact h hl.1 o ho hl.2
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
