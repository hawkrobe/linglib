import Linglib.Core.Question.Basic

/-!
# Question — granularity and the width relation
@cite{deo-thomas-2025}

The Deo–Thomas 2025 *width* relation between inquisitive contents:
two issues with the same informational content can still differ in
**granularity** (how fine the alternatives are). A wider question makes
finer distinctions; its answers are individually more specific, allowing
more informative resolutions. Distinct from question entailment (`≤`):
granularity-based construals generally cannot be ordered by entailment
strength (Deo–Thomas fn. 20).

## Definition

`P.widerThan Q` (over the Set/Question lattice) holds when:
1. Same informational content: `P.info = Q.info`.
2. No `Q`-alternative is properly contained in any `P`-alternative.
3. Some `P`-alternative is properly contained in some `Q`-alternative.

The asymmetry (`P` widens *into* `Q`'s coarser alternatives) reproduces
the Deo–Thomas Bool/List definition over `Core.Question`'s native maximal-
alternatives selector `alt`.
-/

namespace Core

namespace Question

universe u
variable {W : Type u}

/-- The **width relation** between issues (@cite{deo-thomas-2025} (32)).

    `P.widerThan Q` holds when:
    - (a) Same informational content: `P.info = Q.info`.
    - (b) No `Q`-alternative is properly contained in any `P`-alternative.
    - (c) Some `P`-alternative is properly contained in some `Q`-alternative.

    A wider question makes finer distinctions — its answers are
    individually more specific. Weaker than question entailment because
    granularity-based construals generally cannot be ordered by
    entailment strength (@cite{deo-thomas-2025} fn. 20). -/
def widerThan (P Q : Question W) : Prop :=
  P.info = Q.info ∧
  (∀ p₂ ∈ alt Q, ∀ p₁ ∈ alt P, ¬ (p₂ ⊂ p₁)) ∧
  (∃ p₁ ∈ alt P, ∃ p₂ ∈ alt Q, p₁ ⊂ p₂)

end Question

end Core
