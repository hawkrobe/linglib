import Mathlib.Data.Finset.Basic

/-!
# Existential Pluralization Operator (∃-PL)
[bar-lev-2021] [schwarzschild-1996] [krifka-1996]

The existential pluralization operator ∃-PL gives definite plurals a
basic *existential* meaning: "the kids laughed" ≈ "at least one kid
laughed." This contrasts with Link's `*` (`AlgClosure`), which gives
universal closure under join. The choice between ∃-PL and `*`
distinguishes the two main families of homogeneity theories:
implicature accounts ([magri-2014], [bar-lev-2021]) build on
∃-PL + `Exh^{IE+II}` strengthening; trivalent accounts
([schwarzschild-1996], [kriz-2015]) build on `*`/DIST + a
truth-value gap.

## Main declarations

* `existPL` — Bar-Lev's existential pluralization with a domain
  parameter `D`.
* `existPL_full` — collapse to plain existential when `D ⊇ x`.
* `existPL_mono` — monotonicity in `D`.
* `existPL_singleton` — singleton domain reduces to atomic predication.

## Implementation notes

∃-PL takes a domain variable `D`; replacing `D` with `D' ⊆ D` generates
**subdomain alternatives** — a set NOT closed under conjunction.
This non-closure is the structural property shared with Free Choice
disjunction ([fox-2007]).

The plural individual `x` is modelled as `Finset Atom` with `a ∈ x`
for "a is an atomic part of x". The paper uses mereological `≤_AT`
(atomic part-of) over `Semantics/Mereology.lean`'s lattice-based `Atom`
predicate. The `Finset` representation is simpler and adequate for the
exhaustification proofs; a mereological formulation can be added as a
bridge if needed.

## Todo

* Bridge to `CandidateInterpretation.malamudDisjunction` — they agree
  on full domain: `existPL x P x w ↔ malamudDisjunction P x w`.
* Bridge to `Plurality.Distributivity.pluralTruthValue` (K&S
  divergence): `¬ (∀ P x w, existPL x P x w ↔ pluralTruthValue P x w
  = .true)` — counterexample at any mixed-truth `(P, x)`.
* Mereological reformulation against `Mereology.Atom` /
  `Mereology.AlgClosure` for unification with Link's `*P` family.
-/

namespace Semantics.Plurality.Implicature

variable {Atom W : Type*}

/-- ∃-PL: Bar-Lev's existential pluralization operator.

    `⟦∃-PL_D⟧ P x w ↔ ∃ a ∈ x, a ∈ D ∧ P a w`

    `D` is a domain variable restricting which atomic parts of `x` are
    "visible" for predication. Subdomain alternatives arise from
    replacing `D` with `D' ⊆ D`. -/
def existPL (D : Finset Atom) (P : Atom → W → Prop) (x : Finset Atom)
    (w : W) : Prop :=
  ∃ a ∈ x, a ∈ D ∧ P a w

instance [DecidableEq Atom] (D : Finset Atom) (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    Decidable (existPL D P x w) :=
  inferInstanceAs (Decidable (∃ a ∈ x, a ∈ D ∧ P a w))

/-- When D contains all atoms of x, ∃-PL reduces to plain existential
    quantification over atomic parts. -/
theorem existPL_full (D x : Finset Atom) (P : Atom → W → Prop) (w : W)
    (h : x ⊆ D) :
    existPL D P x w ↔ ∃ a ∈ x, P a w := by
  constructor
  · rintro ⟨a, hx, _, hP⟩; exact ⟨a, hx, hP⟩
  · rintro ⟨a, hx, hP⟩; exact ⟨a, hx, h hx, hP⟩

/-- ∃-PL is monotone in D: larger domain variable ⇒ weaker (easier to satisfy). -/
theorem existPL_mono (D D' x : Finset Atom) (P : Atom → W → Prop) (w : W)
    (h : D' ⊆ D) :
    existPL D' P x w → existPL D P x w := by
  rintro ⟨a, hx, hC', hP⟩; exact ⟨a, hx, h hC', hP⟩

/-- Singleton domain variable: ∃-PL reduces to individual predication. -/
theorem existPL_singleton [DecidableEq Atom] (a : Atom) (P : Atom → W → Prop) (x : Finset Atom)
    (w : W) (hx : a ∈ x) :
    existPL {a} P x w ↔ P a w := by
  constructor
  · rintro ⟨b, _, hb_mem, hP⟩
    rwa [Finset.mem_singleton.mp hb_mem] at hP
  · intro hP; exact ⟨a, hx, Finset.mem_singleton_self a, hP⟩

end Semantics.Plurality.Implicature
