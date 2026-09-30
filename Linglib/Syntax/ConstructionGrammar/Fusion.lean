module

public import Mathlib.Data.Fintype.Card
public import Linglib.Syntax.ConstructionGrammar.Basic

/-!
# Fusion of verbs with argument structure constructions

This file defines the fusion of a verb with an argument structure construction, in Goldberg's
account of argument structure. A construction's meaning is a predicate over argument roles, each
linked to a grammatical function, and a verb brings participant roles; a clause arises when the
two are fused. An argument role is profiled when it is linked to a direct grammatical relation,
and a participant role when the verb must express it. Fusion obeys the Semantic Coherence
Principle, that only compatible roles fuse, and the Correspondence Principle, that a profiled
participant role fuses with a profiled argument role.

## Main definitions

* `LinkedRole`, `ArgStructure`: argument roles with their grammatical functions, and the meaning
  of a construction
* `Participants`: the participant roles of a verb
* `ArgStructure.IsFusion`: a fusion obeying both principles
* `ArgStructure.contributed`: the argument roles a construction adds to a verb
* `VerbRelation`, `ArgStructure.Admits`: how a verb's event may relate to the construction's
* `Construction.Linked`: the form carries the grammatical functions the meaning links to

## Main results

* `ArgStructure.IsFusion.exists_fused`: the Shared Participant Condition
* `ArgStructure.IsFusion.isProfiled`: without the three-role exception, a profiled participant
  role fuses with a profiled argument role

## Implementation notes

Role labels are type parameters, and the argument roles a participant role can be construed as
are data the verb supplies. A fusion is a partial map that need not be injective, since
reflexives merge two participant roles into one argument role. Constructions that shade, cut or
merge a profiled role are not modelled.

## References

* [goldberg-1995]
-/

@[expose] public section

namespace ConstructionGrammar

/-- A `VerbRelation` is a relation the event type a verb designates may bear to the one its
construction designates, which is a subtype of it (the diagrams' "instance"), its means, its
result, a precondition of it, or, "to a very limited extent", its manner, the means of
identifying it or its intended result ([goldberg-1995], p. 65). -/
inductive VerbRelation where
  | subtype
  | means
  | result
  | precondition
  | manner
  | identification
  | intendedResult
  deriving DecidableEq, Repr

/-- A `LinkedRole` is an argument role of a construction with the grammatical function it is
linked to and whether the verb must supply it, drawn as a solid line, or the construction may
contribute it, drawn as a dashed line ([goldberg-1995], p. 51). -/
structure LinkedRole (ρ : Type*) where
  /-- The argument role. -/
  role : ρ
  /-- The grammatical function the role is linked to. -/
  gf : GrammaticalFunction
  /-- Whether the role must be fused with a role of the verb. -/
  obligatory : Bool := true
  deriving DecidableEq, Repr

/-- An `ArgStructure` is the meaning of an argument structure construction, a predicate over
argument roles linked to grammatical functions together with the relations a verb's event may
bear to the construction's, each restricted to the verbs with some features, `∅` for none
([goldberg-1995] §2.4.2, p. 64). -/
structure ArgStructure (Pred ρ K : Type*) where
  /-- The construction's predicate, such as CAUSE-RECEIVE. -/
  pred : Pred
  /-- The argument roles, in the order of the book's diagram. -/
  roles : List (LinkedRole ρ)
  /-- The admissible relations, each with the features it requires of a verb. -/
  relations : List (VerbRelation × Finset K)
  deriving DecidableEq

/-- `Participants π ρ` records the participant roles a verb lexically profiles, which it must
express, and the argument roles each participant role can be construed as an instance of
([goldberg-1995] §2.4.1). -/
structure Participants (π ρ : Type*) where
  /-- The lexically profiled participant roles. -/
  profiled : Finset π
  /-- The argument roles a participant role can be construed as. -/
  construals : π → Finset ρ

namespace ArgStructure

variable {Pred ρ π K : Type*} (C : ArgStructure Pred ρ K)

/-- An argument role is profiled when it is linked to a direct grammatical relation: "Every
argument role linked to a direct grammatical relation (SUBJ, OBJ, or OBJ2) is constructionally
profiled" ([goldberg-1995], p. 48). -/
def IsProfiled (r : ρ) : Prop :=
  ∃ a ∈ C.roles, a.role = r ∧ a.gf.IsDirect

instance [DecidableEq ρ] (r : ρ) : Decidable (C.IsProfiled r) :=
  inferInstanceAs (Decidable (∃ a ∈ C.roles, _))

/-- The construction admits a verb with features `k` under the relation `R`. -/
def Admits (k : Finset K) (R : VerbRelation) : Prop :=
  ∃ x ∈ C.relations, x.1 = R ∧ x.2 ⊆ k

instance [DecidableEq K] (k : Finset K) (R : VerbRelation) : Decidable (C.Admits k R) :=
  inferInstanceAs (Decidable (∃ x ∈ C.relations, _))

variable [DecidableEq ρ]

/-- `f` fuses the participant roles of `V` with the argument roles of the construction
([goldberg-1995], pp. 50–51). -/
structure IsFusion (V : Participants π ρ) (f : π → Option ρ) : Prop where
  /-- By the Semantic Coherence Principle, a participant role fuses only with an argument role it
  can be construed as. -/
  coherent : ∀ p, ∀ r ∈ f p, r ∈ V.construals p
  /-- A participant role fuses only with an argument role of the construction. -/
  mem_roles : ∀ p, ∀ r ∈ f p, r ∈ C.roles.map LinkedRole.role
  /-- By the Correspondence Principle, every profiled participant role is fused. -/
  profiled_fused : ∀ p ∈ V.profiled, (f p).isSome
  /-- By the Correspondence Principle, a profiled participant role fuses with a profiled argument
  role, except that a verb profiling three roles may fuse one with a nonprofiled one. -/
  correspondence :
    (V.profiled.filter fun p ↦ ∃ r ∈ f p, ¬ C.IsProfiled r).card ≤
      if V.profiled.card = 3 then 1 else 0
  /-- Every argument role the verb must supply is fused with a participant role. -/
  obligatory_fused : ∀ a ∈ C.roles, a.obligatory → ∃ p, a.role ∈ f p

theorem isFusion_iff (V : Participants π ρ) (f : π → Option ρ) :
    C.IsFusion V f ↔
      (∀ p, ∀ r ∈ f p, r ∈ V.construals p) ∧ (∀ p, ∀ r ∈ f p, r ∈ C.roles.map LinkedRole.role) ∧
      (∀ p ∈ V.profiled, (f p).isSome) ∧
      (V.profiled.filter fun p ↦ ∃ r ∈ f p, ¬ C.IsProfiled r).card ≤
        (if V.profiled.card = 3 then 1 else 0) ∧
      ∀ a ∈ C.roles, a.obligatory → ∃ p, a.role ∈ f p :=
  ⟨fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩, fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅⟩⟩

instance [Fintype π] (V : Participants π ρ) (f : π → Option ρ) : Decidable (C.IsFusion V f) :=
  decidable_of_iff _ (C.isFusion_iff V f).symm

/-- `contributed f` lists the argument roles no participant role fuses with under `f`, which the
construction contributes: "the construction can add roles not contributed by the verb"
([goldberg-1995], p. 54). -/
def contributed [Fintype π] (f : π → Option ρ) : List ρ :=
  (C.roles.map LinkedRole.role).filter fun r ↦ ∀ p, r ∉ f p

variable {C} {V : Participants π ρ} {f : π → Option ρ}

/-- A construction with a role the verb must supply shares a participant with every verb that
fuses with it, the Shared Participant Condition [goldberg-1995] adopts from Matsumoto (p. 65). -/
theorem IsFusion.exists_fused (h : C.IsFusion V f) (ha : ∃ a ∈ C.roles, a.obligatory) :
    ∃ p, ∃ r, r ∈ f p :=
  let ⟨a, ha, hob⟩ := ha
  let ⟨p, hp⟩ := h.obligatory_fused a ha hob
  ⟨p, a.role, hp⟩

/-- Unless the verb profiles three roles, a profiled participant role fuses with a profiled
argument role. -/
theorem IsFusion.isProfiled (h : C.IsFusion V f) (h3 : V.profiled.card ≠ 3) {p : π}
    (hp : p ∈ V.profiled) {r : ρ} (hr : r ∈ f p) : C.IsProfiled r := by
  by_contra hr'
  have h0 := h.correspondence
  simp only [h3, ↓reduceIte, Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  exact h0 hp ⟨r, hr, hr'⟩

end ArgStructure

/-- An argument structure construction is linked when each grammatical function its meaning
links a role to is borne by a slot of its form, and no two roles share a function. -/
def Construction.Linked {Pred ρ K : Type*} (c : Construction (ArgStructure Pred ρ K)) : Prop :=
  (c.meaning.roles.map LinkedRole.gf).Nodup ∧
    ∀ a ∈ c.meaning.roles, ∃ s ∈ c.form, s.gf = some a.gf

instance {Pred ρ K : Type*} (c : Construction (ArgStructure Pred ρ K)) : Decidable c.Linked :=
  inferInstanceAs (Decidable (_ ∧ _))

end ConstructionGrammar
