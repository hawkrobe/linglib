module

public import Linglib.Semantics.Plurality.Reciprocal
public import Linglib.Data.Examples.Winter2018

/-!
# Winter (2018): Symmetric Predicates and the Semantics of Reciprocal Alternations

This file formalizes [winter-2018]'s account of reciprocal alternations, which pair a
unary collective predicate with a binary one. An alternation is plain when the collective
holds of a sum of two entities exactly if the binary predicate holds between them in both
directions (7) (`PlainReciprocity`), and the Reciprocity-Symmetry Generalization says that
an alternation is plain if and only if the binary predicate is truth-conditionally symmetric
(18) (`RSG`). The generalization is not a matter of logic, since a one-way binary predicate
paired with an empty collective is vacuously plain
(`exists_plainReciprocity_not_tcSymmetric`); it follows from taking the collective meaning
as basic and the binary predicate as its symmetric image (22), which is symmetric and plain
by the commutativity of sum formation (`rsg_symmetricImage`). Non-symmetric predicates like
*hug* show weaker patterns (`Pr1`, `Pr2`, `Pr4`), of which only the disjunctive entailment
from the collective to one direction of the binary predicate is shared by all alternations
(`Pr5`); plain reciprocity is exactly the conjunction of the first two
(`plainReciprocity_iff_pr1_pr2`). The event-based rule of [dimitriadis-2008] (42), which
derives the collective from two specifying sub-events, leaves the two unidirectional hugs of
(38) without a common event (`exists_dimitriadis_not_pr1`). The paper's own account of the
non-plain cases is preferential: the typicality of an event as a collective one grows with the
number of directed pairs the binary predicate relates in it (58) (`typ`), so that more
directed relations only raise it (`typ_mono`), a positive threshold yields the disjunctive
entailment (`Pr5_of_preferential`), and the threshold of two yields plain reciprocity on a
pair (`two_le_typ_pair_iff`).

## Implementation notes

Sums of two distinct entities are pair finsets, and the typicality of (58) is the count of
directed pairs rather than a value proportional to it. Table 3's per-verb patterns are
judgments about lexical items and are recorded in the paper's examples rather than as a
table; the counting of events and the comparison with [siloni-2012]'s derivation of
reciprocals from transitives are not formalized.

## References

* [winter-2018]
* [dimitriadis-2008]
* [siloni-2012]
-/

@[expose] public section

namespace Winter2018

variable {A : Type*} [DecidableEq A]

/-! ### Plain reciprocity and symmetry -/

/-- Plain reciprocity (7): for distinct entities, the collective holds of their sum exactly
if the binary predicate holds between them in both directions. -/
def PlainReciprocity (P : Finset A → Prop) (R : A → A → Prop) : Prop :=
  ∀ x y : A, x ≠ y → (P {x, y} ↔ R x y ∧ R y x)

/-- Truth-conditional symmetry of a binary predicate. -/
def TCSymmetric (R : A → A → Prop) : Prop := ∀ x y, R x y ↔ R y x

/-- The Reciprocity-Symmetry Generalization (18) for one alternation: it is plain exactly if
its binary predicate is symmetric. -/
def RSG (P : Finset A → Prop) (R : A → A → Prop) : Prop :=
  PlainReciprocity P R ↔ TCSymmetric R

/-- The symmetric image of a collective predicate (22): the binary predicate holding of two
entities when the collective holds of their sum. -/
def symmetricImage (P : Finset A → Prop) : A → A → Prop := λ x y => P {x, y}

/-- The symmetric image is symmetric, by the commutativity of sum formation. -/
theorem symmetricImage_tcSymmetric (P : Finset A → Prop) : TCSymmetric (symmetricImage P) := by
  intro x y
  simp [symmetricImage, Finset.pair_comm]

/-- The symmetric image is in plain reciprocity with its collective. -/
theorem plainReciprocity_symmetricImage (P : Finset A → Prop) :
    PlainReciprocity P (symmetricImage P) := by
  intro x y _
  constructor
  · exact λ h => ⟨h, by simpa [symmetricImage, Finset.pair_comm] using h⟩
  · exact λ h => h.1

/-- A collective predicate with its symmetric image satisfies the generalization: this is
how the paper derives it for plain reciprocals. -/
theorem rsg_symmetricImage (P : Finset A → Prop) : RSG P (symmetricImage P) :=
  iff_of_true (plainReciprocity_symmetricImage P) (symmetricImage_tcSymmetric P)

/-- The generalization is not logically forced: a one-way binary predicate paired with the
empty collective is vacuously plain. -/
theorem exists_plainReciprocity_not_tcSymmetric :
    ∃ (R : Bool → Bool → Prop) (P : Finset Bool → Prop),
      PlainReciprocity P R ∧ ¬ TCSymmetric R := by
  refine ⟨λ x y => x = true ∧ y = false, λ _ => False, ?_, ?_⟩
  · intro x y hxy
    constructor
    · exact False.elim
    · rintro ⟨⟨rfl, rfl⟩, h₂, -⟩
      exact Bool.noConfusion h₂
  · intro h
    have := (h true false).mp ⟨rfl, rfl⟩
    exact Bool.noConfusion this.1

/-! ### The patterns of non-plain alternations (§3.3) -/

/-- (Pr₁): the binary predicate in both directions yields the collective. -/
def Pr1 (P : Finset A → Prop) (R : A → A → Prop) : Prop :=
  ∀ x y : A, x ≠ y → R x y → R y x → P {x, y}

/-- (Pr₂): the collective yields the binary predicate. -/
def Pr2 (P : Finset A → Prop) (R : A → A → Prop) : Prop :=
  ∀ x y : A, x ≠ y → P {x, y} → R x y

/-- (Pr₄): one direction of the binary predicate yields the collective, as with *break up*
(46). -/
def Pr4 (P : Finset A → Prop) (R : A → A → Prop) : Prop :=
  ∀ x y : A, x ≠ y → R x y → P {x, y}

/-- (Pr₅): the collective yields the binary predicate in at least one direction, the pattern
every reciprocal alternation shares. -/
def Pr5 (P : Finset A → Prop) (R : A → A → Prop) : Prop :=
  ∀ x y : A, x ≠ y → P {x, y} → R x y ∨ R y x

variable {P : Finset A → Prop} {R : A → A → Prop}

/-- (Pr₂) delivers both directions, since the sum is commutative. -/
theorem Pr2.both (h : Pr2 P R) {x y : A} (hxy : x ≠ y) (hP : P {x, y}) : R x y ∧ R y x :=
  ⟨h x y hxy hP, h y x hxy.symm (Finset.pair_comm x y ▸ hP)⟩

/-- (Pr₄) is stronger than (Pr₁). -/
theorem Pr4.pr1 (h : Pr4 P R) : Pr1 P R := λ x y hxy hR _ => h x y hxy hR

/-- (Pr₂) is stronger than (Pr₅). -/
theorem Pr2.pr5 (h : Pr2 P R) : Pr5 P R := λ x y hxy hP => Or.inl (h x y hxy hP)

theorem PlainReciprocity.pr5 (h : PlainReciprocity P R) : Pr5 P R :=
  λ x y hxy hP => Or.inl ((h x y hxy).mp hP).1

/-- Plain reciprocity is (Pr₁) together with (Pr₂). -/
theorem plainReciprocity_iff_pr1_pr2 : PlainReciprocity P R ↔ Pr1 P R ∧ Pr2 P R := by
  constructor
  · exact λ h => ⟨λ x y hxy hR hR' => (h x y hxy).mpr ⟨hR, hR'⟩,
      λ x y hxy hP => ((h x y hxy).mp hP).1⟩
  · rintro ⟨h1, h2⟩ x y hxy
    exact ⟨λ hP => h2.both hxy hP, λ h => h1 x y hxy h.1 h.2⟩

/-! ### Events: Dimitriadis's rule and preferential reciprocity -/

section Events

variable {E : Type*}

/-- [dimitriadis-2008]'s rule (42): a collective event of two entities is one specified by
a sub-event of the binary predicate in each direction. -/
def Dimitriadis (spec : E → E → Prop) (R : E → A → A → Prop)
    (P : E → Finset A → Prop) : Prop :=
  ∀ e (x y : A), x ≠ y →
    (P e {x, y} ↔ ∃ e₁ e₂, spec e₁ e ∧ spec e₂ e ∧ R e₁ x y ∧ R e₂ y x)

/-- The rule does not make (38) entail (37): with a domain of events not closed under a
common specified event, the two unidirectional hugs belong to no collective hug. -/
theorem exists_dimitriadis_not_pr1 :
    ∃ (spec : Bool → Bool → Prop) (R : Bool → Bool → Bool → Prop)
      (P : Bool → Finset Bool → Prop),
      Dimitriadis spec R P ∧ (∃ e₁ e₂, R e₁ true false ∧ R e₂ false true) ∧
        ∀ e, ¬ P e {true, false} := by
  refine ⟨(· = ·),
    λ e x y => (e = true ∧ x = true ∧ y = false) ∨ (e = false ∧ x = false ∧ y = true),
    λ _ _ => False, ?_, ⟨true, false, by decide, by decide⟩, λ _ h => h⟩
  intro e x y hxy
  refine iff_of_false id ?_
  rintro ⟨e₁, e₂, rfl, rfl, h₁, h₂⟩
  rcases h₁ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp at h₂

variable (R : E → A → A → Prop) [∀ e, DecidableRel (R e)]

/-- The typicality of an event as a collective event of a group (58): the number of ordered
pairs of distinct members the binary predicate relates in it. -/
def typ (e : E) (s : Finset A) : ℕ := ((s ×ˢ s).filter λ p => p.1 ≠ p.2 ∧ R e p.1 p.2).card

/-- (57): an event with more directed relations is at least as typical. -/
theorem typ_mono {R' : E → A → A → Prop} [∀ e, DecidableRel (R' e)] {e : E}
    (h : ∀ x y, R e x y → R' e x y) (s : Finset A) : typ R e s ≤ typ R' e s :=
  Finset.card_le_card λ p hp => by
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1, h _ _ hp.2.2⟩

/-- On a pair the typicality counts the two directions. -/
theorem typ_pair {x y : A} (hxy : x ≠ y) (e : E) :
    typ R e {x, y} = (if R e x y then 1 else 0) + if R e y x then 1 else 0 := by
  unfold typ
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  simp [hxy, hxy.symm]

/-- A preferential reciprocal with a positive threshold satisfies (Pr₅): the collective
needs some directed relation. -/
theorem Pr5_of_preferential {θ : ℕ} (hθ : 0 < θ) (e : E) :
    Pr5 (λ s => θ ≤ typ R e s) (R e) := by
  intro x y hxy h
  rw [typ_pair R hxy] at h
  by_contra hn
  push Not at hn
  simp [hn.1, hn.2] at h
  omega

/-- The threshold of two is plain reciprocity on a pair: both directions are required. -/
theorem two_le_typ_pair_iff {x y : A} (hxy : x ≠ y) (e : E) :
    2 ≤ typ R e {x, y} ↔ R e x y ∧ R e y x := by
  rw [typ_pair R hxy]
  split_ifs <;> simp_all

end Events

end Winter2018
