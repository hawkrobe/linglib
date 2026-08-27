import Linglib.Phonology.Constraints.Defs

/-!
# Stratal Optimality Theory
[kiparsky-2000]

Stratal OT is a theory of the phonology–morphology interface where phonological
computation is **cyclic**: it applies at multiple levels (strata) of morphological
structure (Stem → Word → Phrase), with the output of each stratum feeding the next as
input. The crucial property is **constraint reranking**: the same constraint can occupy
different positions in different strata's rankings, capturing level-ordering effects
without ad hoc rules or extrinsic ordering.

Per-stratum evaluation is `OptimalityTheory.Tableau.ofOrder` / `Tableau.optimal` in the
consuming study (e.g. the Telugu weak alternation, [aitha-2026]); a stratum's ranking is
its constraint **order**, a list of labels most dominant first, shared across strata by
label since strata typically score different candidate types. This module provides the
cross-stratal vocabulary over such orders.

## Main definitions

* `rank` — the rank (0 = highest) of a constraint in an order.
* `Outranks` — pairwise domination in one order.
* `Reranked` — the reversal of a pairwise domination between two strata.
-/

namespace OptimalityTheory.Stratal

variable {L : Type*} [DecidableEq L]

/-- The rank of `l` in an order: `0` is the most dominant; `none` if `l` is not active at
this stratum. -/
def rank (l : L) (order : List L) : Option ℕ := order.findIdx? (· = l)

/-- `a` outranks `b` in an order: both are active and `a` is ranked strictly higher. -/
def Outranks (a b : L) (order : List L) : Prop :=
  match rank a order, rank b order with
  | some p, some q => p < q
  | _, _ => False

instance (a b : L) (order : List L) : Decidable (Outranks a b order) := by
  unfold Outranks; split <;> infer_instance

/-- `a` and `b` are reranked between two strata: `a ≫ b` in `r₁` and `b ≫ a` in `r₂` (e.g.
`*DIST-0 ≫ MAX` at the Word level but `MAX ≫ *DIST-0` at the Phrase level in Telugu,
[aitha-2026] §5.3). -/
def Reranked (a b : L) (r₁ r₂ : List L) : Prop := Outranks a b r₁ ∧ Outranks b a r₂

instance (a b : L) (r₁ r₂ : List L) : Decidable (Reranked a b r₁ r₂) := by
  unfold Reranked; infer_instance

end OptimalityTheory.Stratal
