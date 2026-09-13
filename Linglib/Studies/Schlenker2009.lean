import Linglib.Semantics.Presupposition.BeliefEmbedding
import Linglib.Studies.Heim1983

/-!
# Schlenker (2009): Local Contexts

This file formalizes the paper's definition of local contexts and the projection results it
derives from it. A restriction on the denotation of an expression is transparent in a syntactic
environment, relative to a context set, when conjoining it to any denotation of the
expression's type changes the truth value at no world of the context, whatever the sentence's
continuation turns out to be (`Transparent`). The local context is the bottom element of the
transparent restrictions (`IsLocalContext`), and a presupposition is satisfied when the local
context exists and entails it (`Satisfied`). Environments are represented semantically, as the
set of frames sending the gap's denotation to the sentence's, one per good final; the
incremental theory quantifies over every good final, so an initial conjunct or disjunct faces a
frame for every possible continuation (`initial`).

Every propositional environment is pointwise, computing the sentence's truth value at a world
from the gap's truth value there, and for such environments the local context always exists: it
is the set of context worlds at which some frame depends on the gap
(`isLocalContext_pointwise`). Negation, an initial conjunct or disjunct, and an antecedent thus
take the global context as local context; the second conjunct and the consequent take the
context updated with the first clause, and the second disjunct the context updated with the
first disjunct's negation. These are the update-rule local contexts that [heim-1983] and
[beaver-2001] stipulate (`Presupposition.Context.localCtxConsequent`, `localCtxSecondDisjunct`,
`localCtxNegation`), derived here from bivalent meanings alone. Belief reports use
two-dimensional denotations: the local context of the complement of *believe* is the set of
pairs of an utterance world in the context and a world doxastically accessible from it
(`isLocalContext_believe`), which is the substrate's `BeliefLocalCtx.atWorld`. On the King
conditional of [heim-1983], satisfaction in the derived local contexts is admittance by
Heim's context change potential, an instance of the paper's general equivalence with the
dynamic system.

## Implementation notes

The paper defines transparency over strings and good finals; here an environment is the set
of frames those finals denote, and the paper's assumption that every proposition is denoted
appears as the frame for a tautologous continuation, which is what forces the local context
of an initial constituent to include the whole context. Conditionals are material, as in the
paper. Uniqueness of the bottom element is `IsLeast.unique`.

## References

* [schlenker-2009]
* [heim-1983]
* [beaver-2001]
* [heim-1992]
-/

namespace Schlenker2009

open Presupposition
open Presupposition.Context
open Presupposition.BeliefEmbedding
open Heim1983

variable {W α : Type*} [SemilatticeInf α]

/-- A syntactic environment `a _ b` for a gap of type `α`, as the set of frames
`d ↦ ⟦a d b'⟧` over the good finals `b'`. -/
abbrev Environment (α W : Type*) := Set (α → Set W)

/-- (14): a restriction `x` on the gap of `env` is transparent in the context `C` when
restricting any denotation `d` by it changes the truth value at no world of `C`, for every
good final. -/
def Transparent (C : Set W) (env : Environment α W) (x : α) : Prop :=
  ∀ f ∈ env, ∀ d : α, ∀ w ∈ C, w ∈ f (x ⊓ d) ↔ w ∈ f d

/-- (15): the local context of the gap of `env` in `C` is the bottom element of its
transparent restrictions. -/
def IsLocalContext (C : Set W) (env : Environment α W) (x : α) : Prop :=
  IsLeast {x | Transparent C env x} x

theorem IsLocalContext.unique {C : Set W} {env : Environment α W} {x y : α}
    (hx : IsLocalContext C env x) (hy : IsLocalContext C env y) : x = y :=
  IsLeast.unique hx hy

/-- (16): the presupposition of `p` in the gap of `env` is satisfied in `C` when the local
context exists and entails it. -/
def Satisfied (C : Set W) (env : Environment (Set W) W) (p : PartialProp W) : Prop :=
  ∃ x, IsLocalContext C env x ∧ presupSatisfied x p

theorem satisfied_iff {C x : Set W} {env : Environment (Set W) W} (h : IsLocalContext C env x)
    (p : PartialProp W) : Satisfied C env p ↔ presupSatisfied x p :=
  ⟨λ ⟨_, hy, hp⟩ => h.unique hy ▸ hp, λ hp => ⟨x, h, hp⟩⟩

/-! ### Propositional environments (§2.3.1) -/

/-- A pointwise frame computes the sentence's truth value at each world from the gap's truth
value at that world. -/
def pointwise (φ : W → Prop → Prop) : Set W → Set W := λ d => {w | φ w (w ∈ d)}

/-- The local context of a pointwise environment always exists: it is the set of context
worlds at which some frame depends on the gap's truth value. -/
theorem isLocalContext_pointwise (C : Set W) (Φ : Set (W → Prop → Prop)) :
    IsLocalContext C (pointwise '' Φ) (C ∩ {w | ∃ φ ∈ Φ, ¬ (φ w True ↔ φ w False)}) := by
  constructor
  · rintro _ ⟨φ, hφ, rfl⟩ d w hw
    by_cases hx : ∃ φ ∈ Φ, ¬ (φ w True ↔ φ w False)
    · simp [pointwise, hw, hx]
    · have hφw : φ w True ↔ φ w False := by
        by_contra h
        exact hx ⟨φ, hφ, h⟩
      by_cases hd : w ∈ d <;> simp [pointwise, hd, hx, hφw]
  · rintro x hx w ⟨hw, φ, hφ, hφw⟩
    by_contra hwx
    have h := hx _ ⟨φ, hφ, rfl⟩ Set.univ w hw
    simp [pointwise, hwx] at h
    exact hφw h.symm

/-- When some frame depends on the gap at every context world, the local context is the global
context. -/
theorem isLocalContext_of_forall (C : Set W) (Φ : Set (W → Prop → Prop))
    (h : C ⊆ {w | ∃ φ ∈ Φ, ¬ (φ w True ↔ φ w False)}) : IsLocalContext C (pointwise '' Φ) C := by
  have := isLocalContext_pointwise C Φ
  rwa [Set.inter_eq_left.2 h] at this

/-- `(not _)`: the only good final is the closing bracket. -/
def negation : Environment (Set W) W := pointwise '' {λ _ b => ¬ b}

/-- `( _`: a good final conjoins or disjoins any proposition. -/
def initial : Environment (Set W) W :=
  pointwise '' (Set.range (λ h : Set W => λ w b => b ∧ w ∈ h) ∪
    Set.range (λ h : Set W => λ w b => b ∨ w ∈ h))

/-- `(p and _)`. -/
def conjunct (p : W → Prop) : Environment (Set W) W := pointwise '' {λ w b => p w ∧ b}

/-- `(if _ .`: a good final supplies any consequent. -/
def antecedent : Environment (Set W) W :=
  pointwise '' Set.range (λ h : Set W => λ w b => b → w ∈ h)

/-- `(if p . _)`. -/
def consequent (p : W → Prop) : Environment (Set W) W := pointwise '' {λ w b => p w → b}

/-- `(p or _)`. -/
def disjunct (p : W → Prop) : Environment (Set W) W := pointwise '' {λ w b => p w ∨ b}

/-- (21): negation is a hole. -/
theorem isLocalContext_negation (C : Set W) :
    IsLocalContext C negation (localCtxNegation C) :=
  isLocalContext_of_forall C _ λ _ _ => ⟨_, rfl, by simp⟩

/-- (18): an initial conjunct or disjunct takes the global context. -/
theorem isLocalContext_initial (C : Set W) : IsLocalContext C initial C :=
  isLocalContext_of_forall C _ λ _ _ => ⟨_, Or.inl ⟨Set.univ, rfl⟩, by simp⟩

/-- (24): the second conjunct takes the context updated with the first. -/
theorem isLocalContext_conjunct (C : Set W) (p : PartialProp W) :
    IsLocalContext C (conjunct p.assertion) (localCtxConsequent C p) := by
  simpa [conjunct, localCtxConsequent] using
    isLocalContext_pointwise C {λ w b => p.assertion w ∧ b}

/-- (27): an antecedent takes the global context. -/
theorem isLocalContext_antecedent (C : Set W) : IsLocalContext C antecedent C :=
  isLocalContext_of_forall C _ λ _ _ => ⟨_, ⟨∅, rfl⟩, by simp⟩

/-- (30): the consequent takes the context updated with the antecedent. -/
theorem isLocalContext_consequent (C : Set W) (p : PartialProp W) :
    IsLocalContext C (consequent p.assertion) (localCtxConsequent C p) := by
  simpa [consequent, localCtxConsequent] using
    isLocalContext_pointwise C {λ w b => p.assertion w → b}

/-- (33): the second disjunct takes the context updated with the first disjunct's negation. -/
theorem isLocalContext_disjunct (C : Set W) (p : PartialProp W) :
    IsLocalContext C (disjunct p.assertion) (localCtxSecondDisjunct C p) := by
  simpa [disjunct, localCtxSecondDisjunct] using
    isLocalContext_pointwise C {λ w b => p.assertion w ∨ b}

/-! ### Belief reports (§3.1.2) -/

/-- `(believe _)` with two-dimensional denotations, sets of pairs of an utterance world and a
world of evaluation: the report holds at the utterance world when the complement holds at
every world the agent's beliefs there allow. -/
def believe (dox : W → W → Prop) : Environment (Set (W × W)) W :=
  {λ d => {w₀ | ∀ w, dox w₀ w → (w₀, w) ∈ d}}

/-- (52): the local context of the complement of *believe* pairs each utterance world of the
context with the worlds the agent's beliefs there allow, the substrate's
`BeliefLocalCtx.atWorld`. -/
theorem isLocalContext_believe {Agent : Type*} (blc : BeliefLocalCtx W Agent) :
    IsLocalContext blc.globalCtx (believe (blc.dox blc.agent))
      {q | q.2 ∈ blc.atWorld q.1} := by
  constructor
  · rintro _ rfl d w₀ hw₀
    exact ⟨λ h w hw => (h w hw).2, λ h w hw => ⟨⟨hw₀, hw⟩, h w hw⟩⟩
  · rintro x hx ⟨w₀, w⟩ ⟨hw₀, hw⟩
    exact ((hx _ rfl Set.univ w₀ hw₀).2 λ _ _ => trivial) w hw |>.1

/-! ### The King conditional ([heim-1983]) -/

variable {king son bald : W → Prop}

/-- Satisfaction in the derived local contexts of the antecedent and the consequent of "If the
king has a son, the king's son is bald" is admittance by Heim's context change potential:
both hold iff the context entails a king. -/
theorem king_satisfied_iff_admits (C : Set W) :
    Satisfied C antecedent (kingHasSon king son) ∧
        Satisfied C (consequent (kingHasSon king son).assertion) (kingsSonBald king son bald) ↔
      (ifKingHasSon king son bald).admits C := by
  rw [satisfied_iff (isLocalContext_antecedent C), satisfied_iff (isLocalContext_consequent C
    (kingHasSon king son)), king_admits_iff]
  exact ⟨λ h => h.1, λ h => ⟨h, λ w hw => ⟨h w hw.1, hw.2⟩⟩⟩

/-- The derived local contexts agree with the Karttunen filtering conditional
(`PartialProp.impFilter`): a conditional's presuppositions are satisfied in them iff the
context satisfies the presupposition of the filtering connective. -/
theorem satisfied_iff_impFilter (C : Set W) (p q : PartialProp W) :
    Satisfied C antecedent p ∧ Satisfied C (consequent p.assertion) q ↔
      presupSatisfied C (PartialProp.impFilter p q) := by
  rw [satisfied_iff (isLocalContext_antecedent C), satisfied_iff (isLocalContext_consequent C p)]
  exact ⟨λ ⟨hp, hq⟩ _ hw => ⟨hp hw, λ ha => hq ⟨hw, ha⟩⟩,
    λ h => ⟨λ _ hw => (h hw).1, λ _ hw => (h hw.1).2 hw.2⟩⟩

end Schlenker2009
