/-
# Local Context Computation

Formalizes Schlenker (2009)'s local contexts algorithm for computing
presupposition projection compositionally.

## Insight

The "local context" at a position in a sentence determines what
presuppositions are filtered vs. projected. Schlenker shows this
can be computed incrementally from left to right.

## The Algorithm

For a sentence S with embedded clause φ at position i:
1. The local context c_i is the global context c updated with
   all material to the left of position i
2. A presupposition P of φ projects iff c_i ⊭ P
3. If c_i ⊧ P, the presupposition is "filtered" (locally satisfied)

## Examples

"If the king exists, the king is bald"
- Global context: c
- Local context at "the king is bald": c + [the king exists]
- Presupposition "king exists" is entailed by local context
- Therefore: presupposition is filtered, doesn't project globally

"John stopped smoking"
- Global context: c
- No filtering material before "stopped"
- Presupposition "John used to smoke" projects globally

## References

- Schlenker (2009). Local Contexts. Semantics & Pragmatics 2:3.
- Heim (1983). On the Projection Problem for Presuppositions.
- Karttunen (1974). Presupposition and Linguistic Context.
-/

import Linglib.Core.CommonGround
import Linglib.Core.Presupposition

namespace Montague.Sentence.Presupposition.LocalContext

open Core.Presupposition
open Core.Proposition
open Core.CommonGround

variable {W : Type*}


/--
A local context at a position in a sentence.

Tracks:
- The context set (worlds compatible with prior material)
- The position in the sentence
- Whether we're under an operator that affects projection
-/
structure LocalCtx (W : Type*) where
  /-- The set of worlds at this position -/
  worlds : ContextSet W
  /-- Position in the sentence (for tracking) -/
  position : Nat
  /-- Embedding depth (for intermediate accommodation) -/
  depth : Nat := 0

/--
Initial local context: the global context at position 0.
-/
def initialLocalCtx (c : ContextSet W) : LocalCtx W :=
  { worlds := c, position := 0, depth := 0 }


/--
Local context for the consequent of a conditional.

"If P then Q" — the local context at Q is c + P.assertion

This is why "If the king exists, the king is bald" doesn't presuppose
king exists: the local context at "the king is bald" already entails it.
-/
def localCtxConsequent (c : LocalCtx W) (antecedent : PrProp W) : LocalCtx W :=
  { worlds := ContextSet.update c.worlds antecedent.assertion
  , position := c.position + 1
  , depth := c.depth }

/--
Local context for the second conjunct.

"P and Q" — the local context at Q is c + P.assertion
-/
def localCtxSecondConjunct (c : LocalCtx W) (first : PrProp W) : LocalCtx W :=
  { worlds := ContextSet.update c.worlds first.assertion
  , position := c.position + 1
  , depth := c.depth }

/--
Local context under negation.

"not P" — the local context at P is unchanged, but we track depth.
-/
def localCtxNegation (c : LocalCtx W) : LocalCtx W :=
  { worlds := c.worlds
  , position := c.position + 1
  , depth := c.depth + 1 }

/--
Local context for each disjunct.

"P or Q" — Schlenker: local context at Q is c + ¬P.assertion
(and symmetrically for P)
-/
def localCtxSecondDisjunct (c : LocalCtx W) (first : PrProp W) : LocalCtx W :=
  { worlds := λ w => c.worlds w ∧ first.assertion w = false
  , position := c.position + 1
  , depth := c.depth }


/--
A presupposition projects at a local context if it's not entailed.

Projection is the default. Filtering (non-projection) happens when the
local context already satisfies the presupposition.
-/
def presupProjects (lc : LocalCtx W) (p : PrProp W) : Prop :=
  ¬ ContextSet.entails lc.worlds p.presup

/--
A presupposition is filtered at a local context if it IS entailed.
-/
def presupFiltered (lc : LocalCtx W) (p : PrProp W) : Prop :=
  ContextSet.entails lc.worlds p.presup

/--
Projection and filtering are complementary.
-/
theorem projects_iff_not_filtered (lc : LocalCtx W) (p : PrProp W) :
    presupProjects lc p ↔ ¬ presupFiltered lc p := Iff.rfl


/--
Presupposition of consequent is filtered when antecedent assertion
entails the presupposition.

This formalizes the core insight of filtering semantics.
-/
theorem conditional_filters_when_entailed (c : LocalCtx W) (p q : PrProp W)
    (h : ∀ w, c.worlds w → p.assertion w = true → q.presup w = true) :
    presupFiltered (localCtxConsequent c p) q := by
  intro w hw
  have ⟨hw_in, hp_true⟩ := hw
  exact h w hw_in hp_true

/--
If antecedent assertion doesn't entail consequent presupposition,
it projects.
-/
theorem conditional_projects_when_not_entailed (c : LocalCtx W) (p q : PrProp W)
    (h : ∃ w, c.worlds w ∧ p.assertion w = true ∧ q.presup w = false) :
    presupProjects (localCtxConsequent c p) q := by
  obtain ⟨w, hw_in, hp_true, hq_false⟩ := h
  intro hfilter
  have := hfilter w ⟨hw_in, hp_true⟩
  simp [hq_false] at this

/--
Negation doesn't filter presuppositions.
-/
theorem negation_preserves_projection (c : LocalCtx W) (p : PrProp W) :
    presupProjects c p ↔ presupProjects (localCtxNegation c) p := by
  simp [presupProjects, localCtxNegation]


/--
Formalization of "If the king exists, the king is bald".

World type: whether a king exists.
-/
inductive KingWorld' where
  | kingExists
  | noKing
  deriving DecidableEq

/--
"The king exists" — no presupposition.
-/
def kingExists' : PrProp KingWorld' :=
  { presup := λ _ => true
  , assertion := λ w => match w with
      | .kingExists => true
      | .noKing => false }

/--
"The king is bald" — presupposes king exists.
-/
def kingBald' : PrProp KingWorld' :=
  { presup := λ w => match w with
      | .kingExists => true
      | .noKing => false
  , assertion := λ _ => true }

/--
In the conditional, the presupposition is filtered.

The local context at "the king is bald" is c + [king exists],
which entails the presupposition [king exists].
-/
theorem king_conditional_filters (c : ContextSet KingWorld')
    (h : c KingWorld'.noKing ∨ c KingWorld'.kingExists) :
    presupFiltered (localCtxConsequent (initialLocalCtx c) kingExists') kingBald' := by
  intro w hw
  -- w is in {v ∈ c | kingExists'.assertion v = true}
  -- So kingExists'.assertion w = true, meaning w = kingExists
  obtain ⟨_, hw_assert⟩ := hw
  cases w with
  | kingExists => rfl
  | noKing => simp [kingExists'] at hw_assert


/--
The local context theory derives the same result as the filtering
connectives in Core.Presupposition.

This theorem shows the correspondence between:
- Schlenker's local context computation
- Kracht's filtering implication formula
-/
theorem local_context_matches_impFilter (c : ContextSet W) (p q : PrProp W) :
    (∀ w, c w → (PrProp.impFilter p q).presup w = true) ↔
    (∀ w, c w → p.presup w = true ∧ (p.assertion w = true → q.presup w = true)) := by
  constructor
  · intro h w hw
    specialize h w hw
    simp only [PrProp.impFilter] at h
    cases hp : p.presup w
    · simp [hp] at h
    · simp only [hp, Bool.true_and] at h
      constructor
      · rfl
      · intro ha
        cases hq : q.presup w
        · simp [ha, hq] at h
        · rfl
  · intro h w hw
    obtain ⟨hp, himp⟩ := h w hw
    simp only [PrProp.impFilter, hp, Bool.true_and]
    cases ha : p.assertion w
    · simp
    · simp [himp ha]

end Montague.Sentence.Presupposition.LocalContext
