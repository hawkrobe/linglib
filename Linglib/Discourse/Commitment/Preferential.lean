import Linglib.Discourse.Commitment.Basic
import Linglib.Semantics.Attitudes.Desire.Preferential

/-!
# Preferential commitments and effective preferences

A commitment of force `.preferential` is [condoravdi-lauer-2012]'s `PEP(a, p)`, `a`'s public
commitment to act as though `p` were a maximal element of `a`'s effective preference structure,
the consistent ranking of propositions that guides `a`'s actions. A commitment state is sincere
at a world when each of its preferential commitments is an effective preference there,
`Desire.Preferential.Want`: the sincerity condition on a directive use of an imperative. Through
the consistency of the effective preference structure, sincerity is what makes successive
imperatives consistent (`Studies/CondoravdiLauer2012.lean`) and what excludes a
force-augmenting particle from contexts in which the preference it expresses is unrealizable
(`Studies/Deo2025.lean`).

## References

* [condoravdi-lauer-2012]
* [deo-2025-bara]
-/

namespace Commitment

open Desire.Preferential

variable {A W : Type*} (P : A → W → PreferenceStructure W)

/-- The preferential commitments in `K` are effective preferences at `w`. -/
def Sincere (K : State A W) (w : W) : Prop :=
  ∀ c ∈ K, c.force = .preferential → c.polarity = .commit → Want P c.committer c.content w

variable {P} {K L : State A W} {w : W}

theorem Sincere.mono (hL : Sincere P L w) (h : K ⊆ L) : Sincere P K w := λ c hc => hL c (h hc)

theorem Sincere.want (hs : Sincere P K w) {a : A} {p : Set W} (h : commit a p .preferential ∈ K) :
    Want P a p w :=
  hs _ h rfl rfl

end Commitment
