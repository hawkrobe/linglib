import Mathlib.Tactic.Basic

/-!
# Discourse-Act Felicity

A typeclass for "this act is felicitous in this state" — a unifier for
the framework-specific felicity predicates (Gunlogson's CBC, Faller's
evidence-source check, Lauer's credence threshold, Büring-Gunlogson's
contextual bias, etc.) so that cross-framework theorems can be
quantified over `[HasFelicity S A]`.

Instances live with the framework types (e.g. `Dialogue/Gunlogson.lean`
for the CBC; `Studies/Faller2019.lean` for the evidence-source check).
-/

namespace Discourse.SpeechAct

/-- A felicity predicate over discourse states `S` and acts `A`: when
    is performing the act felicitous in the given state? -/
class HasFelicity (S : Type*) (A : outParam (Type*)) where
  /-- The act is felicitous in the state. -/
  Felicitous : A → S → Prop

end Discourse.SpeechAct
