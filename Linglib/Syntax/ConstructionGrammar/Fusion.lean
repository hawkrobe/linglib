module

public import Mathlib.Data.Fintype.Card
public import Linglib.Syntax.ConstructionGrammar.Basic

/-!
# Fusion of verbs with argument structure constructions

An argument structure construction pairs a predicate with an array of argument roles, each
linked to a grammatical function, and a verb brings an array of participant roles; a clause
arises when the verb's participant roles fuse with the construction's argument roles
([goldberg-1995] §2.4). An argument role is profiled when it is linked to a direct grammatical
relation (`ArgStructure.IsProfiled`, p. 49), so profiling is read off the linking and not
stored, while a participant role is profiled when the verb obligatorily expresses it, a lexical
fact. `ArgStructure.IsFusion` states the two principles that decide which roles fuse (p. 50):
the Semantic Coherence Principle, that only compatible roles fuse, and the Correspondence
Principle, that every profiled participant role fuses with a profiled argument role, except that
a verb profiling three roles may fuse one of them with a nonprofiled argument role. It adds the
solid lines of the book's diagrams, the argument roles the verb must supply; the others the
construction can contribute (`ArgStructure.contributed`, p. 54). A construction also constrains
the relation a verb's event bears to its own (`VerbRelation`, p. 65), which a construction may
restrict to a class of verbs (`ArgStructure.Admits`, p. 64).

## Main definitions

* `VerbRelation`: the relations a verb's event may bear to a construction's
* `LinkedRole`, `ArgStructure`: an argument role with its grammatical function, and the
  construction's predicate, roles and admissible relations
* `Participants`: a verb's profiled participant roles and the argument roles each can be
  construed as
* `ArgStructure.IsProfiled`, `ArgStructure.IsFusion`, `ArgStructure.contributed`,
  `ArgStructure.Admits`
* `Construction.Linked`: the form bears the grammatical functions the meaning links to

## Main results

* `ArgStructure.IsFusion.exists_fused`: a construction with a role the verb must supply shares
  a participant with every verb that fuses with it, the Shared Participant Condition the book
  adopts from Matsumoto (p. 65)
* `ArgStructure.IsFusion.isProfiled`: without the three-role exception, a fused profiled
  participant role sits in a profiled argument role

## Implementation notes

Role labels have "no theoretical significance" (p. 49), so argument and participant roles are
type parameters, and whether a participant role "can be construed as an instance of" an argument
role, which the book leaves to "general categorization principles" (p. 50), is data the verb
supplies (`Participants.construals`). Fusion is a partial map from participant roles to argument
roles, not required to be injective, since reflexives merge two participant roles into one
argument role (p. 58). The Correspondence Principle's condition that a profiled role be
"expressed" is not modelled: the constructions that shade, cut or merge a profiled role (§2.4.4)
are outside the fragment. The verb classes an admissible relation is restricted to are sets of
the verb's features, of a type the construction leaves open.

## References

* [goldberg-1995]
-/

@[expose] public section

namespace ConstructionGrammar

/-- The relation the event type a verb designates bears to the one its construction designates
([goldberg-1995], p. 65): a subtype of it (the diagrams' "instance"), its means, its result, a
precondition of it, and, "to a very limited extent", its manner, the means of identifying it, or
its intended result. -/
inductive VerbRelation where
  | subtype
  | means
  | result
  | precondition
  | manner
  | identification
  | intendedResult
  deriving DecidableEq, Repr

/-- An argument role of a construction with the grammatical function it is linked to, and
whether the verb must supply it, a solid line in the book's diagrams, or the construction may
contribute it, a dashed line ([goldberg-1995], p. 51). -/
structure LinkedRole (ρ : Type*) where
  /-- The argument role. -/
  role : ρ
  /-- The grammatical function the role is linked to. -/
  gf : GrammaticalFunction
  /-- Whether the role must be fused with a role of the verb. -/
  obligatory : Bool := true
  deriving DecidableEq, Repr

/-- The meaning pole of an argument structure construction ([goldberg-1995] §2.4.2): a
predicate over argument roles linked to grammatical functions, and the relations a verb's event
may bear to the construction's, each with the features a verb must have to bear it, `∅` for none
(p. 64). -/
structure ArgStructure (Pred ρ K : Type*) where
  /-- The construction's predicate, such as CAUSE-RECEIVE. -/
  pred : Pred
  /-- The argument roles, in the order of the book's diagram. -/
  roles : List (LinkedRole ρ)
  /-- The admissible relations, each with the features it requires of a verb. -/
  relations : List (VerbRelation × Finset K)
  deriving DecidableEq

/-- A verb's participant roles ([goldberg-1995] §2.4.1): those it lexically profiles, which it
obligatorily expresses, and the argument roles each can be construed as an instance of. -/
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
  /-- The Semantic Coherence Principle: a participant role fuses only with an argument role it
  can be construed as. -/
  coherent : ∀ p, ∀ r ∈ f p, r ∈ V.construals p
  /-- A participant role fuses only with an argument role of the construction. -/
  mem_roles : ∀ p, ∀ r ∈ f p, r ∈ C.roles.map LinkedRole.role
  /-- The Correspondence Principle: every profiled participant role is fused. -/
  profiled_fused : ∀ p ∈ V.profiled, (f p).isSome
  /-- The Correspondence Principle: a profiled participant role fuses with a profiled argument
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

/-- The argument roles the construction contributes under `f`: those no participant role fuses
with ([goldberg-1995], p. 54, "the construction can add roles not contributed by the verb"). -/
def contributed [Fintype π] (f : π → Option ρ) : List ρ :=
  (C.roles.map LinkedRole.role).filter fun r ↦ ∀ p, r ∉ f p

variable {C} {V : Participants π ρ} {f : π → Option ρ}

/-- The Shared Participant Condition ([goldberg-1995], p. 65, after Matsumoto): a construction
with a role the verb must supply shares a participant with every verb that fuses with it. -/
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

/-- The form of an argument structure construction bears the grammatical functions its meaning
links its roles to, each on its own slot. -/
def Construction.Linked {Pred ρ K : Type*} (c : Construction (ArgStructure Pred ρ K)) : Prop :=
  (c.meaning.roles.map LinkedRole.gf).Nodup ∧
    ∀ a ∈ c.meaning.roles, ∃ s ∈ c.form, s.gf = some a.gf

instance {Pred ρ K : Type*} (c : Construction (ArgStructure Pred ρ K)) : Decidable c.Linked :=
  inferInstanceAs (Decidable (_ ∧ _))

end ConstructionGrammar
