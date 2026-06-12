import Linglib.Semantics.Presupposition.BeliefEmbedding
import Linglib.Studies.Heim1983

/-!
# Schlenker (2009): Local Contexts
[schlenker-2009]

Projection predictions of the local-context theory, applied to the
King and conditional examples from `Studies.Heim1983`. The
per-connective local contexts are substrate
(`Semantics.Presupposition.LocalContext`); belief embedding
([schlenker-2009] §3.1.2) is `Semantics.Presupposition.BeliefEmbedding`.

## Main declarations

- `matrix_local_context_is_global`: at matrix position the local context
  is the global context, so unembedded presuppositions project.
- `belief_local_context_is_holder_beliefs`: under "x believes φ" the local
  context at φ is x's belief state.
- `negation_projects` / `conditional_filters`: the projection asymmetry
  between negation and conditionals.
- `king_conditional_filters`: "If the king exists, the king is bald"
  filters the existence presupposition.
- `king_accounts_agree`: the local-context prediction agrees with the
  Karttunen filtering connective (`PartialProp.impFilter`) on the king
  example.
-/

namespace Schlenker2009

open CommonGround
open Semantics.Presupposition
open Semantics.Presupposition.Context
open Semantics.Presupposition.LocalContext
open Semantics.Presupposition.BeliefEmbedding
open Heim1983

variable {W : Type*} {Agent : Type*}

/-- **Matrix local context = global context.**

In unembedded sentences, the local context is just the global context `c`,
so a matrix presupposition must be entailed by the context set or project. -/
theorem matrix_local_context_is_global (c : ContextSet W) :
    (initialLocalCtx c).worlds = c := rfl

/-- **Local context under belief = attitude holder's beliefs.**

Under "x believes φ", the local context at φ is determined by x's doxastic
state ([schlenker-2009] §3.1.2). -/
theorem belief_local_context_is_holder_beliefs
    (blc : BeliefLocalCtx W Agent) (w_star : W) (h : blc.globalCtx w_star) :
    (beliefToLocalCtx blc w_star h).worlds = blc.atWorld w_star := rfl

/-- **Negation projects**: "not φ" has the same local context at φ as the
unembedded sentence, so φ's presupposition projects unless globally
entailed. -/
theorem negation_projects (c : ContextSet W) (p : PartialProp W) :
    presupProjects (localCtxNegation (initialLocalCtx c)) p ↔
    presupProjects (initialLocalCtx c) p :=
  (negation_preserves_projection (initialLocalCtx c) p).symm

/-- **Conditionals filter**: in "if φ then ψ", the antecedent's assertion
enters ψ's local context; when it entails ψ's presupposition, the
presupposition is filtered. -/
theorem conditional_filters (c : LocalCtx W) (p q : PartialProp W)
    (h : ∀ w, c.worlds w → p.assertion w → q.presup w) :
    presupFiltered (localCtxConsequent c p) q :=
  conditional_filters_when_entailed c p q h

/-- "If the king exists, the king is bald": the local context at
"the king is bald" is `c` + [king exists], which entails the existence
presupposition, so it is filtered. -/
theorem king_conditional_filters (c : ContextSet KingWorld) :
    presupFiltered (localCtxConsequent (initialLocalCtx c) kingExists) kingBald := by
  intro w hw
  obtain ⟨-, hw_assert⟩ := hw
  cases w with
  | kingExists => exact trivial
  | noKing => exact hw_assert.elim

/-- On the king example, the local-context account and the Karttunen
filtering connective agree: both pronounce the conditional
presuppositionless. -/
theorem king_accounts_agree (c : ContextSet KingWorld) :
    presupFiltered (localCtxConsequent (initialLocalCtx c) kingExists) kingBald ∧
    ifKingThenBald.presup = (λ _ => True) :=
  ⟨king_conditional_filters c, ifKingThenBald_no_presup⟩

end Schlenker2009
