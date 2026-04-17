import Mathlib.Data.Finset.Basic

/-!
# Existential Pluralization Operator (∃-PL)

@cite{bar-lev-2021} @cite{schwarzschild-1994} @cite{gajewski-2005}

The existential pluralization operator ∃-PL gives definite plurals a
basic *existential* meaning: "the kids laughed" ≈ "at least one kid laughed."
This contrasts with Link's `*` (`AlgClosure`), which gives *universal*
closure under join.

The choice between ∃-PL and `*` distinguishes the two main families
of Homogeneity theories:

| Operator | Basic meaning | Strengthening | Framework |
|----------|--------------|---------------|-----------|
| ∃-PL     | existential  | Exh^{IE+II}   | Implicature (@cite{magri-2014}, @cite{bar-lev-2021}) |
| `*`/DIST | universal    | truth-value gap | Trivalent (@cite{schwarzschild-1994}, @cite{kriz-2015}) |

## Key Property

∃-PL takes a domain variable D (@cite{bar-lev-2021} §4.2). Replacing D
with subsets D' ⊆ D generates *subdomain alternatives* — a set NOT closed
under conjunction. This non-closure is the structural property shared with
Free Choice disjunction (@cite{fox-2007}).

## Design Note

The plural individual `x` is modeled as `Finset Atom` with `a ∈ x` for
"a is an atomic part of x." The paper uses `y ≤_AT x` (mereological
atomic part-of), which corresponds to `Core/Mereology.lean`'s lattice-based
`Atom` predicate. The `Finset` representation is simpler and adequate for
the exhaustification proofs; a mereological formulation can be added as a
bridge if needed.

## Connection to Existing Infrastructure

- `Core/Mereology.lean`: `AlgClosure` = Link's `*` (the universal dual)
- `Lexical/Plural/Link1983.lean`: `star`, `Distr`
- `Lexical/Plural/Distributivity.lean`: `distMaximal` (∀ atoms satisfy P)
- `Exhaustification/InnocentInclusion.lean`: Exh^{IE+II} that derives
  universality from existential + non-closed alternatives
-/

namespace Semantics.Plurality.ExistentialPL

variable {Atom W : Type*}

/-- ∃-PL: the existential pluralization operator.

    ⟦∃-PL_D⟧(P)(x)(w) ↔ ∃ a ∈ x, a ∈ D ∧ P(a)(w)

    D is a domain variable restricting which atomic parts of x are
    "visible" for predication. Subdomain alternatives arise from
    replacing D with D' ⊆ D.

    @cite{bar-lev-2021} def. (31); see also @cite{schwarzschild-1994},
    @cite{gajewski-2005}. -/
def existPL (D : Finset Atom) (P : Atom → W → Prop) (x : Finset Atom)
    (w : W) : Prop :=
  ∃ a ∈ x, a ∈ D ∧ P a w

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

end Semantics.Plurality.ExistentialPL
