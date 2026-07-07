import Linglib.Semantics.Degree.Hom
import Linglib.Semantics.Degree.Quantifier

/-!
# Cresswell (1976): The Semantics of Degree
[cresswell-1976]

Degrees of comparison in a λ-categorial possible-worlds semantics: a
degree is a scale-tagged point `⟨u, >⟩` (2.1), *er than* (2.3) compares
degrees only on a **shared** scale (so (23) *taller man than … clever
man* is anomalous — the same-scale restriction [bale-2008]'s universal
scale later removes), the equative *as as* (2.7) is weak `≥` with
*exactly* forcing `=`, and §4 grounds the degree ontology by
constructing degrees from comparison relations: φ-equivalence classes
(4.1) with the induced comparison well-defined (4.2). The construction
is `Degree.cresswellSetoid`/`Degree.CresswellDegree` in
`Semantics/Degree/Hom.lean`; this file checks the paper's claims on its
own examples.

Formalized here: the (4.1)–(4.2) construction on the Arabella/Clarissa
beauty example (62), the same-scale comparative (18) *Bill is a taller
man than Ophidia is a long snake* (heights and lengths share the
spatial-distance scale), the weak equative, and footnote 10's
disjunctive than-clause universality (*taller than Arabella or
Clarissa* = taller than both), derived from `Degree.maxComparative`.
-/

namespace Cresswell1976

open Degree

/-! ### §4: degrees constructed from comparisons (62) -/

/-- Individuals of the beauty example (62)–(63). -/
inductive Person where
  | arabella | clarissa | bill | tom
  deriving DecidableEq, Repr

/-- A comparison relation φ: *x is more beautiful than y*, with Bill and
    Tom equally beautiful (both below Clarissa, who is below Arabella). -/
def moreBeautiful : Person → Person → Prop
  | .arabella, .clarissa | .arabella, .bill | .arabella, .tom => True
  | .clarissa, .bill | .clarissa, .tom => True
  | _, _ => False

instance : DecidableRel moreBeautiful := fun a b => by
  cases a <;> cases b <;> simp only [moreBeautiful] <;> infer_instance

/-- Bill and Tom are φ-indistinguishable, so they determine the **same
    degree of beauty** — (4.1)'s equivalence collapses ties. -/
theorem bill_tom_same_degree :
    (⟦Person.bill⟧ : CresswellDegree moreBeautiful) = ⟦Person.tom⟧ :=
  Quotient.sound ⟨fun c => by cases c <;> simp [moreBeautiful],
                  fun c => by cases c <;> simp [moreBeautiful]⟩

/-- The induced comparison on constructed degrees tracks φ ((4.2) at
    work): Arabella's degree exceeds the shared Bill/Tom degree. -/
example : CresswellDegree.rel
    (⟦Person.arabella⟧ : CresswellDegree moreBeautiful) ⟦Person.tom⟧ :=
  (CresswellDegree.rel_mk _ _).mpr trivial

/-! ### §2: same-scale comparison (18) and the equative (2.7) -/

/-- Heights and lengths in the shared spatial-distance scale (ℚ):
    (2.2)'s point that `tall` and `long` "both involve the same scale"
    is what licenses (18). -/
def extent : Person → ℚ
  | .bill => 6 | .tom => 5 | .arabella => 4 | .clarissa => 3

/-- (18) *Bill is a taller man than Ophidia is a long snake*, in the
    single-scale regime: the comparative reduces to `comparativeSem` on
    the shared measure ((2.3) with unique degree witnesses). -/
theorem er_than_single_scale (a b : Person) :
    (∃ u₁ u₂ : ℚ, u₁ = extent a ∧ u₂ = extent b ∧ u₂ < u₁) ↔
      comparativeSem extent a b .positive := by
  constructor
  · rintro ⟨u₁, u₂, rfl, rfl, h⟩; exact h
  · exact fun h => ⟨extent a, extent b, rfl, rfl, h⟩

/-- (2.7): *as as* is the weak equative — "either u₁ > u₂ or u₁ = u₂" —
    i.e. `equativeSem`; *exactly* (`u₁ = u₂`) is `equativeStrengthened`. -/
theorem as_as_weak (a b : Person) :
    (extent b < extent a ∨ extent a = extent b) ↔
      equativeSem extent a b .positive := by
  constructor
  · rintro (h | h)
    · exact le_of_lt h
    · exact le_of_eq h.symm
  · intro h
    rcases lt_or_eq_of_le h with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'.symm

/-! ### Footnote 10: disjunctive than-clauses are universal -/

/-- *Bill is taller than Arabella or Clarissa* entails taller than
    **both** ((iii)–(v)): the than-clause maximum over a disjunctive
    predicate is the max of the two degrees, so the max-quantified
    comparative decomposes into the conjunction. -/
theorem taller_than_disjunction_iff (x y z : Person) :
    maxComparative (· = x) (fun w => w = y ∨ w = z) extent ↔
      extent y < extent x ∧ extent z < extent x := by
  constructor
  · rintro ⟨δ, ⟨_, hub⟩, w, rfl, hlt⟩
    have hy : extent y ≤ δ := hub ⟨y, Or.inl rfl, le_rfl⟩
    have hz : extent z ≤ δ := hub ⟨z, Or.inr rfl, le_rfl⟩
    exact ⟨lt_of_le_of_lt hy hlt, lt_of_le_of_lt hz hlt⟩
  · rintro ⟨hy, hz⟩
    refine ⟨max (extent y) (extent z), ⟨?_, ?_⟩, x, rfl, max_lt hy hz⟩
    · rcases max_cases (extent y) (extent z) with ⟨heq, _⟩ | ⟨heq, _⟩
      · exact ⟨y, Or.inl rfl, le_of_eq heq⟩
      · exact ⟨z, Or.inr rfl, le_of_eq heq⟩
    · rintro d ⟨w, hw | hw, hle⟩
      · subst hw; exact le_trans hle (le_max_left _ _)
      · subst hw; exact le_trans hle (le_max_right _ _)

end Cresswell1976
