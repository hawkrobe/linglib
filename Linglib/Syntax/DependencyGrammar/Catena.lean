import Linglib.Syntax.DependencyGrammar.NonProjective

/-!
# Catenae

[osborne-gross-2012]'s catena — the unit of syntactic analysis larger than
a word and looser than a constituent: a set of positions connected in the
tree's undirected view. A constituent is the special case of a full
dominance cone. Both are decidable, so fixtures close by `decide`; the
general separation (every non-leaf position forms with a dependent a
catena that is not a constituent) is ported with the study layer.
-/

namespace DependencyGrammar

variable {n : ℕ}

/-- `s` is a **catena**: nonempty and connected under `Linked` within `s`.
    ([osborne-gross-2012]) -/
def IsCatena (g : Graph n) (s : Finset (Fin n)) : Prop :=
  s.Nonempty ∧ ∀ v ∈ s, ∀ w ∈ s,
    Relation.ReflTransGen (λ a b => Linked g a b ∧ a ∈ s ∧ b ∈ s) v w

/-- `s` is a **constituent**: exactly the dominance cone of some position. -/
def IsConstituent (g : Graph n) (s : Finset (Fin n)) : Prop :=
  ∃ v, ∀ w, w ∈ s ↔ Dominates g v w

instance (g : Graph n) (s : Finset (Fin n)) (v w : Fin n) :
    Decidable (Relation.ReflTransGen (λ a b => Linked g a b ∧ a ∈ s ∧ b ∈ s) v w) :=
  Relation.ReflTransGen.decidable_of_finite (List.finRange n)
    (λ _ b _ => List.mem_finRange b) v w

instance (g : Graph n) (s : Finset (Fin n)) : Decidable (IsCatena g s) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (g : Graph n) (s : Finset (Fin n)) : Decidable (IsConstituent g s) :=
  inferInstanceAs (Decidable (∃ _, _))

end DependencyGrammar
