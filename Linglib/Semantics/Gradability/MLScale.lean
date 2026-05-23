import Mathlib.Order.Basic

/-!
# Marginality Scales
@cite{dinis-jacinto-2026}

ML theory enriches a linear order with a primitive "marginally smaller than"
relation M. From R (= `<`) and M one derives L (largely smaller than):
L(x,y) := x < y ∧ ¬ M x y. Five axioms govern M; Theorem 2.2 derives
M-TRANSITIVITY and M-BOUNDEDNESS as consequences.

This sits alongside `DirectedMeasure` (in `Core.Scale`): a `DirectedMeasure`
determines licensing from boundedness, while an `MLScale` adds granularity
structure (marginal vs. large difference) on the same `LinearOrder`.

- Dinis, B. & Jacinto, B. (2026). Marginality scales for gradable
  adjectives. *Linguistics and Philosophy* 49:101–131.
-/

namespace Semantics.Gradability

/-- ML theory (@cite{dinis-jacinto-2026}, Fig. 1): a linear order enriched with
    a primitive "marginally smaller than" relation M satisfying five axioms.
    The strict order `<` from `LinearOrder` is the paper's R;
    L (largely smaller) is derived as R ∧ ¬M. -/
structure MLScale (α : Type*) [LinearOrder α] where
  /-- x is marginally smaller than y (primitive) -/
  M : α → α → Prop
  /-- Axiom 1: ∃ x y, L(x,y) — largely different elements exist -/
  exists_large : ∃ x y, x < y ∧ ¬ M x y
  /-- Axiom 2: M(x,y) → R(x,y) -/
  m_implies_lt : ∀ x y, M x y → x < y
  /-- Axiom 3 (M-IRRELEVANCE): marginal steps preserve large-gap structure -/
  m_irrelevance : ∀ x y z, M x y →
    ((z < y ∧ ¬ M z y → z < x ∧ ¬ M z x) ∧
     (x < z ∧ ¬ M x z → y < z ∧ ¬ M y z))
  /-- Axiom 4: R extends along L — smaller-than propagates through large gaps -/
  r_extends_l : ∀ x y z, x < y →
    ((y < z ∧ ¬ M y z → x < z ∧ ¬ M x z) ∧
     (z < x ∧ ¬ M z x → z < y ∧ ¬ M z y))
  /-- Axiom 5 (DECOMPOSITION): every large gap decomposes via a marginal step -/
  decomposition : ∀ x y, (x < y ∧ ¬ M x y) →
    (∃ z, M x z ∧ z < y ∧ ¬ M z y) ∧ (∃ w, M w y ∧ x < w ∧ ¬ M x w)

namespace MLScale

variable {α : Type*} [LinearOrder α] (ml : MLScale α)

/-- Largely smaller than (Def 2.1): R(x,y) ∧ ¬M(x,y). -/
def L (x y : α) : Prop := x < y ∧ ¬ ml.M x y

/-- Marginal difference (Def 2.3): M(x,y) ∨ M(y,x). -/
def MarginalDiff (x y : α) : Prop := ml.M x y ∨ ml.M y x

/-- At most marginal difference: x = y ∨ MarginalDiff(x,y).
    The equivalence relation on degrees induced by M. -/
def AtMostMarginal (x y : α) : Prop := x = y ∨ ml.MarginalDiff x y

/-- Large difference: L(x,y) ∨ L(y,x). -/
def LargeDiff (x y : α) : Prop := ml.L x y ∨ ml.L y x

/-- **Theorem 2.2, part 1 (M-TRANSITIVITY)**: M is transitive.
    If x is marginally smaller than y and y marginally smaller than z,
    then x is marginally smaller than z.
    Proof: ¬L(y,z) since M(y,z); Axiom 3 contrapositive gives ¬L(x,z);
    since R(x,z), this forces M(x,z). -/
theorem m_transitive (x y z : α) (hxy : ml.M x y) (hyz : ml.M y z) :
    ml.M x z := by
  by_contra h
  exact ((ml.m_irrelevance x y z hxy).2
    ⟨lt_trans (ml.m_implies_lt x y hxy) (ml.m_implies_lt y z hyz), h⟩).2 hyz

/-- **Theorem 2.2, part 2 (M-BOUNDEDNESS)**: if x is marginally smaller
    than z and y is between them (x < y < z), then both gaps are marginal. -/
theorem m_bounded (x y z : α) (hxz : ml.M x z) (hxy : x < y) (hyz : y < z) :
    ml.M x y ∧ ml.M y z := by
  constructor
  · by_contra h
    exact absurd ((ml.m_irrelevance x z y hxz).2 ⟨hxy, h⟩).1
      (not_lt.mpr (le_of_lt hyz))
  · by_contra h
    exact absurd ((ml.m_irrelevance x z y hxz).1 ⟨hyz, h⟩).1
      (not_lt.mpr (le_of_lt hxy))

end MLScale

end Semantics.Gradability
