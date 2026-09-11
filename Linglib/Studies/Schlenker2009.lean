import Linglib.Semantics.Presupposition.BeliefEmbedding
import Linglib.Studies.Heim1983

/-!
# Schlenker (2009): Local Contexts
[schlenker-2009]

Projection predictions of the local-context theory, applied to the
King and conditional examples from `Studies.Heim1983`. The
per-connective local contexts are substrate
(`Presupposition.LocalContext`); belief embedding
([schlenker-2009] §3.1.2) is `Presupposition.BeliefEmbedding`.

## Main declarations

- `matrix_local_context_is_global`: at matrix position the local context
  is the global context, so unembedded presuppositions project.
- `belief_local_context_is_holder_beliefs`: under "x believes φ" the local
  context at φ is x's belief state.
- `negation_projects` / `conditional_filters`: the projection asymmetry
  between negation and conditionals.
- `king_conditional_filters`: "If the king has a son, the king's son is bald"
  filters the consequent's presupposition in a context that entails a king.
- `local_contexts_agree_impFilter` / `king_accounts_agree`: the local-context
  prediction agrees with the Karttunen filtering connective
  (`PartialProp.impFilter`), on the King example and in general.
-/

namespace Schlenker2009

open Presupposition
open Presupposition.Context
open Presupposition.BeliefEmbedding
open Heim1983

variable {W : Type*} {Agent : Type*}

/-- **Negation projects**: "not φ" has the same local context at φ as the
unembedded sentence (the matrix local context being the global context
itself), so φ's presupposition projects unless globally entailed. -/
theorem negation_projects (c : Set W) (p : PartialProp W) :
    presupProjects (localCtxNegation c) p ↔ presupProjects c p :=
  Iff.rfl

/-- **Conditionals filter**: in "if φ then ψ", the antecedent's assertion
enters ψ's local context; when it entails ψ's presupposition, the
presupposition is filtered. -/
theorem conditional_filters (c : Set W) (p q : PartialProp W)
    (h : ∀ w, c w → p.assertion w → q.presup w) :
    presupSatisfied (localCtxConsequent c p) q :=
  conditional_filters_when_entailed c p q h

/-- "If the king has a son, the king's son is bald" ([heim-1983]'s (3)): in a context that
entails a king, the local context of the consequent, the context plus the antecedent's
assertion, entails the consequent's presupposition, so it is filtered. -/
theorem king_conditional_filters {c : Set W} {king son bald : W → Prop}
    (hc : ∀ w ∈ c, king w) :
    presupSatisfied (localCtxConsequent c (kingHasSon king son))
      (kingsSonBald king son bald) :=
  λ w hw => ⟨hc w hw.1, hw.2⟩

/-- The local-context account and the Karttunen filtering connective agree: a context
satisfies the antecedent's presupposition and the consequent's in its local context iff it
satisfies the presupposition of `PartialProp.impFilter`. -/
theorem local_contexts_agree_impFilter (c : Set W) (p q : PartialProp W) :
    presupSatisfied c p ∧ presupSatisfied (localCtxConsequent c p) q ↔
      presupSatisfied c (PartialProp.impFilter p q) :=
  ⟨λ ⟨hp, hq⟩ _ hw => ⟨hp hw, λ ha => hq ⟨hw, ha⟩⟩,
   λ h => ⟨λ _ hw => (h hw).1, λ _ hw => (h hw.1).2 hw.2⟩⟩

/-- On the King example both accounts make the conditional presuppose exactly that there is
a king. -/
theorem king_accounts_agree (c : Set W) {king son bald : W → Prop} :
    presupSatisfied c (kingHasSon king son) ∧
        presupSatisfied (localCtxConsequent c (kingHasSon king son))
          (kingsSonBald king son bald) ↔
      ∀ w ∈ c, king w :=
  ⟨λ h => h.1, λ hc => ⟨hc, king_conditional_filters hc⟩⟩

end Schlenker2009
