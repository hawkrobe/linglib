module

public import Linglib.Semantics.Presupposition.Trivalent
public import Linglib.Semantics.Dynamic.Partial

/-!
# Formulas of the propositional fragment

This file defines the formulas on which theories of presupposition projection are compared: the
propositional fragment of the language L of [schlenker-2009]'s Appendix C, which is also the
language of [kalomoiros-2023]'s System 1 (Definition 3.4.1). A formula is built from atoms and
triggers by negation and the binary connectives of `Connective`; a trigger `trigger p p'`
presupposes `p` and asserts `p'`, and its classical meaning is the conjunction of the two
(`Formula.truth`, C.2).

Each binary connective is interpreted classically (`Connective.eval`), by [peters-1979]'s filtering
connectives (`Connective.filter`), and by the context change potentials of [heim-1983], with
[beaver-2001]'s disjunction (`Connective.ccp`). The fold `Formula.filter` evaluates a formula into
`PartialProp`, and `Formula.ccp` into `CCP.Partial`. The context change potential admits a context
iff the context entails the filtering presupposition, and it updates the context to its worlds at
which the formula is classically true (`Formula.admits_ccp_iff`, `Formula.ccp_get`).

## Main definitions

* `Presupposition.Formula`: atoms, triggers, negation and the binary connectives.
* `Presupposition.Formula.truth`: the classical meaning at an interpretation of the atoms.
* `Presupposition.Formula.strong`, `Presupposition.Formula.filter`, `Presupposition.Formula.ccp`:
  the Strong Kleene, filtering and dynamic evaluations.

## Implementation notes

The interpretation of the atoms is a function to `Set W`. [schlenker-2009]'s Expressivity (C.3),
that every proposition is denoted by an atom, is not built in: the theories that need it quantify
over propositions where the paper quantifies over expressions. The conditional is material, as in
the paper, and its Strong Kleene clause is by interdefinability from negation and disjunction.

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

/-- The Strong Kleene connectives; the conditional is `¬p ∨ q`. -/
def strong : Connective → PartialProp W → PartialProp W → PartialProp W
  | conj, p, q => p.andStrong q
  | cond, p, q => p.neg.orStrong q
  | disj, p, q => p.orStrong q

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

/-- The propositional fragment of L (C.1): a trigger `trigger p p'` presupposes `p` and asserts
`p'`. -/
inductive Formula (Atom : Type*) where
  | atom (p : Atom)
  | trigger (presup assert : Atom)
  | not (F : Formula Atom)
  | bin (c : Connective) (F G : Formula Atom)
  deriving DecidableEq

namespace Formula

variable (I : Atom → Set W)

/-- C.2: the classical meaning, with a trigger read as the conjunction of its two parts. -/
def truth : Formula Atom → Set W
  | atom p => I p
  | trigger p p' => I p ∩ I p'
  | not F => (truth F)ᶜ
  | bin c F G => {w | c.eval (w ∈ truth F) (w ∈ truth G)}

/-- The Strong Kleene evaluation: a trigger is defined where its presupposition holds. -/
def strong : Formula Atom → PartialProp W
  | atom p => ⟨fun _ ↦ True, (· ∈ I p)⟩
  | trigger p p' => ⟨(· ∈ I p), (· ∈ I p')⟩
  | not F => (strong F).neg
  | bin c F G => c.strong (strong F) (strong G)

/-- The evaluation by the filtering connectives. -/
def filter : Formula Atom → PartialProp W
  | atom p => ⟨fun _ ↦ True, (· ∈ I p)⟩
  | trigger p p' => ⟨(· ∈ I p), (· ∈ I p')⟩
  | not F => (filter F).neg
  | bin c F G => c.filter (filter F) (filter G)

/-- The context change potential of a formula: a trigger is defined in a context that entails its
presupposition. -/
noncomputable def ccp : Formula Atom → CCP.Partial W
  | atom p => CCP.Partial.ofPartialProp ⟨fun _ ↦ True, (· ∈ I p)⟩
  | trigger p p' => CCP.Partial.ofPartialProp ⟨(· ∈ I p), (· ∈ I p')⟩
  | not F => CCP.Partial.neg (ccp F)
  | bin c F G => c.ccp (ccp F) (ccp G)

/-- On its presupposition, the filtering evaluation asserts the classical meaning. -/
theorem filter_assertion_iff {F : Formula Atom} {w : W} (h : (F.filter I).presup w) :
    (F.filter I).assertion w ↔ w ∈ F.truth I := by
  induction F with
  | atom p => exact Iff.rfl
  | trigger p p' => exact ⟨fun h' ↦ ⟨h, h'⟩, fun h' ↦ h'.2⟩
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

/-- Every formula contains an atom or a trigger. -/
theorem nonempty_atom : Formula Atom → Nonempty Atom
  | atom p => ⟨p⟩
  | trigger p _ => ⟨p⟩
  | not F => nonempty_atom F
  | bin _ F _ => nonempty_atom F

/-- The filtering presupposition of a binary formula: the first argument's presupposition, and the
second's wherever the world is in the second argument's local context
([karttunen-1974-presupposition]). -/
theorem filter_presup_bin {c : Connective} {F G : Formula Atom} {w : W} :
    ((bin c F G).filter I).presup w ↔
      (F.filter I).presup w ∧
        (w ∈ c.localContext Set.univ (F.truth I) → (G.filter I).presup w) := by
  have assert (hp : (F.filter I).presup w) := filter_assertion_iff I hp
  cases c
  · exact ⟨fun ⟨hp, h⟩ ↦ ⟨hp, fun hc ↦ h ((assert hp).2 hc.2)⟩,
      fun ⟨hp, h⟩ ↦ ⟨hp, fun ha ↦ h ⟨trivial, (assert hp).1 ha⟩⟩⟩
  · exact ⟨fun ⟨hp, h⟩ ↦ ⟨hp, fun hc ↦ h ((assert hp).2 hc.2)⟩,
      fun ⟨hp, h⟩ ↦ ⟨hp, fun ha ↦ h ⟨trivial, (assert hp).1 ha⟩⟩⟩
  · exact ⟨fun ⟨hp, h⟩ ↦ ⟨hp, fun hc ↦ h fun ha ↦ hc.2 ((assert hp).1 ha)⟩,
      fun ⟨hp, h⟩ ↦ ⟨hp, fun hn ↦ h ⟨trivial, fun ht ↦ hn ((assert hp).2 ht)⟩⟩⟩

private theorem ccp_spec (F : Formula Atom) : ∀ C : Set W,
    ((F.ccp I).Admits C → (F.filter I).Admits C) ∧
      ((F.filter I).Admits C → C ∩ F.truth I ∈ F.ccp I C) := by
  induction F with
  | atom p => exact fun C ↦ ⟨id, fun h ↦ ⟨h, rfl⟩⟩
  | trigger p p' =>
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

end Presupposition
