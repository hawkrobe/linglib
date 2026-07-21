import Linglib.Semantics.Presupposition.Basic
import Linglib.Discourse.CommonGround

/-!
# Presupposition–Context Bridge
[stalnaker-1974] [heim-1983] [lewis-1979]

Canonical operations connecting presuppositions (`PartialProp W`) to contexts
(`ContextSet W`): the shared vocabulary for projection, filtering,
accommodation, and conceivability.

## Main declarations

* `presupSatisfied` — the context entails the presupposition (filtering).
* `presupSatisfiable` — some context world satisfies it (conceivability).
* `presupProjects` — the context does not entail it (projection).
* `accommodate` — restrict the context to presupposition worlds.

## Conceivability

`presupSatisfiable` is the conceivability check needed for
[enguehard-2024]'s conceivability presupposition: a number feature's
presupposition is *conceivable* in the common ground iff there exists some
world in the context set satisfying it.
-/

namespace Semantics.Presupposition.Context

open Semantics.Presupposition
open CommonGround

variable {W : Type*}

/-! ### Core operations -/

/-- A presupposition is **satisfied** (filtered) in context `c` iff the context
    entails it: every world in the context satisfies the presupposition.

    This is Karttunen's filtering condition and Schlenker's local satisfaction. -/
abbrev presupSatisfied (c : ContextSet W) (p : PartialProp W) : Prop := c ⊆ p.presup

/-- A presupposition is **satisfiable** (conceivable) in context `c` iff some
    world in the context satisfies it.

    This is Enguehard's conceivability condition: a singular indefinite's number
    presupposition is conceivable iff the common ground contains a world where
    the witness set has the right cardinality. -/
abbrev presupSatisfiable (c : ContextSet W) (p : PartialProp W) : Prop :=
  (c ∩ p.presup).Nonempty

/-- A presupposition **projects** from context `c` iff it is NOT satisfied
    (not filtered). Projection is the complement of filtering. -/
abbrev presupProjects (c : ContextSet W) (p : PartialProp W) : Prop :=
  ¬ presupSatisfied c p

/-- **Accommodate** a presupposition: restrict the context to worlds where
    the presupposition holds.

    [lewis-1979]: "presupposition P comes into existence." -/
abbrev accommodate (c : ContextSet W) (presup : Set W) : ContextSet W := c ∩ presup

/-- Accommodation is **informative** iff the presupposition is not already
    entailed — accommodation actually changes the context. -/
abbrev accommodationInformative (c : ContextSet W) (presup : Set W) : Prop :=
  ¬ c ⊆ presup

/-- Accommodation is **consistent** iff the restricted context is non-empty —
    the presupposition is compatible with the context. -/
abbrev accommodationConsistent (c : ContextSet W) (presup : Set W) : Prop :=
  (accommodate c presup).Nonempty

/-! ### Theorems -/

/-- Satisfaction implies satisfiability (when the context is non-empty). -/
theorem satisfied_implies_satisfiable (c : ContextSet W) (p : PartialProp W)
    (hne : c.Nonempty) (hsat : presupSatisfied c p) : presupSatisfiable c p := by
  obtain ⟨w, hw⟩ := hne
  exact ⟨w, hw, hsat hw⟩

/-- If the presupposition is not even satisfiable, it projects. -/
theorem not_satisfiable_implies_projects (c : ContextSet W) (p : PartialProp W)
    (hne : c.Nonempty) (h : ¬ presupSatisfiable c p) : presupProjects c p :=
  fun hsat => h (satisfied_implies_satisfiable c p hne hsat)

/-- After accommodation, the presupposition is satisfied. -/
theorem accommodate_entails_presup (c : ContextSet W) (presup : Set W) :
    accommodate c presup ⊆ presup :=
  Set.inter_subset_right

/-- Accommodation is idempotent: accommodating what's already satisfied
    doesn't change the context. -/
theorem accommodate_idempotent (c : ContextSet W) (presup : Set W)
    (h : c ⊆ presup) : accommodate c presup = c :=
  Set.inter_eq_left.mpr h

/-- Accommodation strengthens the context: fewer worlds survive. -/
theorem accommodate_strengthens (c : ContextSet W) (presup : Set W) :
    accommodate c presup ⊆ c :=
  Set.inter_subset_left

/-- Accommodation consistency = presupposition satisfiable in context. -/
theorem accommodationConsistent_iff_satisfiable (c : ContextSet W) (p : PartialProp W) :
    accommodationConsistent c p.presup ↔ presupSatisfiable c p := Iff.rfl

/-- Accommodation via `PartialProp.defined`: accommodating `p.presup` restricts
    to worlds where `p.defined` holds. -/
theorem accommodate_eq_defined (c : ContextSet W) (p : PartialProp W) (w : W) :
    w ∈ accommodate c p.presup ↔ w ∈ c ∧ PartialProp.defined w p :=
  Iff.rfl

/-! ### Local contexts (satisfaction tradition)

Per-connective local contexts, stipulated in the satisfaction tradition
([karttunen-1974], [heim-1983]); [schlenker-2009]'s algorithm reconstructs
these clauses from bivalent meanings plus incremental transparency. A
presupposition is filtered at a position iff the local context there
satisfies it (`presupSatisfied`), and projects otherwise
(`presupProjects`). -/

/-- Local context for the consequent of a conditional — and equally for the
    second conjunct: "If P then Q" / "P and Q" give Q the local context
    c + P.assertion (the shared rule behind
    `PartialProp.impFilter_presup_eq_andFilter_presup`).

    This is why "If the king exists, the king is bald" doesn't presuppose
    king exists: the local context at "the king is bald" already entails it. -/
def localCtxConsequent (c : ContextSet W) (antecedent : PartialProp W) : ContextSet W :=
  ContextSet.update c antecedent.assertion

/-- Local context for the second disjunct: "P or Q" gives Q the local
    context c + ¬P.assertion ([schlenker-2009], reconstructing
    [karttunen-1973]'s asymmetric disjunction rule). -/
def localCtxSecondDisjunct (c : ContextSet W) (first : PartialProp W) : ContextSet W :=
  λ w => c w ∧ ¬first.assertion w

/-- Local context under negation: unchanged — negation is a hole
    ([karttunen-1973]). -/
def localCtxNegation (c : ContextSet W) : ContextSet W := c

/-- Presupposition of the consequent is filtered when the antecedent's
    assertion entails the presupposition throughout the context. -/
theorem conditional_filters_when_entailed (c : ContextSet W) (p q : PartialProp W)
    (h : ∀ w, c w → p.assertion w → q.presup w) :
    presupSatisfied (localCtxConsequent c p) q := by
  intro w hw
  have ⟨hw_in, hp_true⟩ := hw
  exact h w hw_in hp_true

/-- If the antecedent's assertion doesn't entail the consequent's
    presupposition somewhere in the context, it projects. -/
theorem conditional_projects_when_not_entailed (c : ContextSet W) (p q : PartialProp W)
    (h : ∃ w, c w ∧ p.assertion w ∧ ¬q.presup w) :
    presupProjects (localCtxConsequent c p) q := by
  obtain ⟨w, hw_in, hp_true, hq_false⟩ := h
  intro hfilter
  exact hq_false (hfilter ⟨hw_in, hp_true⟩)

/-- The stipulated local-context computation agrees with the Karttunen
    filtering implication formula ([karttunen-1973], [peters-1979]). -/
theorem local_context_matches_impFilter (c : ContextSet W) (p q : PartialProp W) :
    (∀ w, c w → (PartialProp.impFilter p q).presup w) ↔
    (∀ w, c w → p.presup w ∧ (p.assertion w → q.presup w)) :=
  Iff.rfl

/-- Schlenker's local context at the second disjunct derives Karttunen's
    asymmetric disjunction filter (`PartialProp.disjFilterLeft`).

    For "A ∨ B_ψ" in context c:
    - Schlenker: local context at B is c ∧ ¬A; ψ filtered iff c ∧ ¬A ⊧ ψ
    - Karttunen: residual presupposition is ¬A → ψ; satisfied iff ∀w∈c, ¬A(w) → ψ(w)

    These are the same condition (currying/uncurrying the conjunction).
    Analogous to `local_context_matches_impFilter` for conditionals.
    [schlenker-2009], [karttunen-1973] -/
theorem local_context_matches_disjFilterLeft (c : ContextSet W)
    (firstDisjunct : PartialProp W) (second : PartialProp W) :
    presupSatisfied (localCtxSecondDisjunct c firstDisjunct) second ↔
    (∀ w, c w → (PartialProp.disjFilterLeft firstDisjunct.assertion second).presup w) := by
  constructor
  · intro h w hc hn; exact h ⟨hc, hn⟩
  · intro h w ⟨hc, hn⟩; exact h w hc hn

end Semantics.Presupposition.Context
