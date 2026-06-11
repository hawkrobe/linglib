import Linglib.Semantics.Presupposition.Context

/-!
# Local Context Computation

Local contexts for presupposition projection, stipulated per connective
in the satisfaction tradition ([karttunen-1974], [heim-1983]).
[schlenker-2009]'s contribution — *deriving* these local contexts from
bivalent meanings plus incremental transparency — is not implemented
here: the per-connective clauses below are the Karttunen/Heim
stipulations that Schlenker's algorithm reconstructs.

## Insight

The "local context" at a position in a sentence determines what
presuppositions are filtered vs. projected, computed incrementally
from left to right.

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

-/

namespace Semantics.Presupposition.LocalContext

open Semantics.Presupposition
open CommonGround
open Semantics.Presupposition.Context

variable {W : Type*}


/--
A local context at a position in a sentence.

Tracks:
- The context set (worlds compatible with prior material)
- The embedding depth (for intermediate accommodation)
-/
structure LocalCtx (W : Type*) where
  /-- The set of worlds at this position -/
  worlds : ContextSet W
  /-- Embedding depth (for intermediate accommodation) -/
  depth : Nat := 0

instance : HasContextSet (LocalCtx W) W where
  toContextSet := LocalCtx.worlds

/--
Initial local context: the global context, unembedded.
-/
def initialLocalCtx (c : ContextSet W) : LocalCtx W :=
  { worlds := c, depth := 0 }


/--
Local context for the consequent of a conditional.

"If P then Q" — the local context at Q is c + P.assertion

This is why "If the king exists, the king is bald" doesn't presuppose
king exists: the local context at "the king is bald" already entails it.
-/
def localCtxConsequent (c : LocalCtx W) (antecedent : PartialProp W) : LocalCtx W :=
  { worlds := ContextSet.update c.worlds antecedent.assertion
  , depth := c.depth }

/--
Local context for the second conjunct.

"P and Q" — the local context at Q is c + P.assertion
-/
def localCtxSecondConjunct (c : LocalCtx W) (first : PartialProp W) : LocalCtx W :=
  { worlds := ContextSet.update c.worlds first.assertion
  , depth := c.depth }

/--
Local context under negation.

"not P" — the local context at P is unchanged, but we track depth.
-/
def localCtxNegation (c : LocalCtx W) : LocalCtx W :=
  { worlds := c.worlds
  , depth := c.depth + 1 }

/--
Local context for each disjunct.

"P or Q" — Schlenker: local context at Q is c + ¬P.assertion
(and symmetrically for P)
-/
def localCtxSecondDisjunct (c : LocalCtx W) (first : PartialProp W) : LocalCtx W :=
  { worlds := λ w => c.worlds w ∧ ¬first.assertion w
  , depth := c.depth }


/-- A presupposition projects at a local context if it's not entailed.
    Delegates to `Semantics.Presupposition.Context.presupProjects`. -/
abbrev presupProjects (lc : LocalCtx W) (p : PartialProp W) : Prop :=
  Semantics.Presupposition.Context.presupProjects lc.worlds p

/-- A presupposition is filtered (satisfied) at a local context if it IS entailed.
    Delegates to `Semantics.Presupposition.Context.presupSatisfied`. -/
abbrev presupFiltered (lc : LocalCtx W) (p : PartialProp W) : Prop :=
  Semantics.Presupposition.Context.presupSatisfied lc.worlds p

/--
Presupposition of consequent is filtered when antecedent assertion
entails the presupposition.

This formalizes the core insight of filtering semantics.
-/
theorem conditional_filters_when_entailed (c : LocalCtx W) (p q : PartialProp W)
    (h : ∀ w, c.worlds w → p.assertion w → q.presup w) :
    presupFiltered (localCtxConsequent c p) q := by
  intro w hw
  have ⟨hw_in, hp_true⟩ := hw
  exact h w hw_in hp_true

/--
If antecedent assertion doesn't entail consequent presupposition,
it projects.
-/
theorem conditional_projects_when_not_entailed (c : LocalCtx W) (p q : PartialProp W)
    (h : ∃ w, c.worlds w ∧ p.assertion w ∧ ¬q.presup w) :
    presupProjects (localCtxConsequent c p) q := by
  obtain ⟨w, hw_in, hp_true, hq_false⟩ := h
  intro hfilter
  exact hq_false (hfilter ⟨hw_in, hp_true⟩)

/--
Negation doesn't filter presuppositions.
-/
theorem negation_preserves_projection (c : LocalCtx W) (p : PartialProp W) :
    presupProjects c p ↔ presupProjects (localCtxNegation c) p := by
  simp [presupProjects, localCtxNegation]


/--
The local context theory derives the same result as the filtering
connectives in Semantics.Presupposition.

This theorem shows the correspondence between:
- the stipulated local context computation
- the Karttunen filtering implication formula ([karttunen-1973], [peters-1979])
-/
theorem local_context_matches_impFilter (c : ContextSet W) (p q : PartialProp W) :
    (∀ w, c w → (PartialProp.impFilter p q).presup w) ↔
    (∀ w, c w → p.presup w ∧ (p.assertion w → q.presup w)) := by
  constructor
  · intro h w hw
    have h' := h w hw
    simp only [PartialProp.impFilter] at h'
    exact h'
  · intro h w hw
    obtain ⟨hp, himp⟩ := h w hw
    simp only [PartialProp.impFilter]
    exact ⟨hp, himp⟩

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
    presupFiltered (localCtxSecondDisjunct (initialLocalCtx c) firstDisjunct) second ↔
    (∀ w, c w → (PartialProp.disjFilterLeft firstDisjunct.assertion second).presup w) := by
  constructor
  · intro h w hc hn; exact h ⟨hc, hn⟩
  · intro h w ⟨hc, hn⟩; exact h w hc hn

end Semantics.Presupposition.LocalContext
