import Mathlib.Data.Set.Basic

/-!
# Focus-sensitive particles: even and only

Truth-conditional semantics for the focus particles *even* and *only*,
with propositions as `Set World`. *Even*'s scalar presupposition
([karttunen-peters-1979]) requires the prejacent to be less likely than
every focus alternative; *only*'s assertion ([rooth-1992]) excludes
every alternative; and `LikelihoodMonotone` — a likelihood ordering
respecting entailment — is the property from which [lahiri-1998]
derives the distribution of *even one* NPIs (cf. [crnic-2014]).
[francescotti-1995] weakens the presupposition's universal force to a
majority threshold — see `Studies/Francescotti1995.lean`.

## Main definitions

* `evenPresup`: the prejacent is less likely than every alternative.
* `onlyAssertion`: no focus alternative holds.
* `LikelihoodMonotone`: entailment-monotonicity of a likelihood
  ordering.
-/

namespace Focus.Particles

variable {World : Type*}

/-- The scalar presupposition of *even* ([karttunen-peters-1979]): the
prejacent `p` is less likely than every focus alternative, where
`r p q` reads "`p` is less likely than `q`". -/
def evenPresup (r : Set World → Set World → Prop) (p : Set World)
    (alts : List (Set World)) : Prop :=
  ∀ q ∈ alts, r p q

/-- The assertion of *only*: no focus alternative holds. The prejacent
is presupposed separately; the alternative list excludes it. -/
def onlyAssertion (alts : List (Set World)) : Set World :=
  {w | ∀ q ∈ alts, w ∉ q}

/-- A likelihood ordering respects entailment: a stronger proposition
is at most as likely. -/
def LikelihoodMonotone (r : Set World → Set World → Prop) : Prop :=
  ∀ ⦃p q : Set World⦄, p ⊆ q → r p q

end Focus.Particles
