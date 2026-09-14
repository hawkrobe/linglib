import Linglib.Semantics.Presupposition.Trivalent
import Linglib.Semantics.Conditionals.SimilarityOrdering
import Linglib.Data.Examples.Sharvit2025

/-!
# Sharvit (2025): Rooth-Partee Conditionals and the Symmetry of Disjunction

This file formalizes the paper's case that *or* is inherently symmetric and its closest-worlds
theory of the connectives. A Rooth-Partee conditional, *If Mia is penniless or proud of her
money, then Sue is*, has an if-over-∃ reading, one conditional with a disjunctive antecedent,
and a ∀-over-if reading, one conditional per disjunct with the ellipsis matched to it
([rooth-partee-1982]); the second reading presupposes that Sue has money if Mia does, and both
readings survive swapping the disjuncts. A disjunction that projects its left disjunct's
presupposition, the K+ connective under CON-asymmetry (16)–(17), cannot deliver this: swapping
the disjuncts changes what the antecedent presupposes (`orAsym_presup_ne`), and the paper argues
that accommodation does not repair it. The symmetric disjunction of [karttunen-peters-1979]
(102) does (`orKPSymmetric_comm`), but its Karttunen conditional presupposition, definedness of
the consequent at the evaluation world if the antecedent is true there (100), is too weak for
the ∀-over-if presupposition (`ifKP_presup_of_not_assertion`), the Proviso Problem.

The proposal replaces the local presupposition by a closest-worlds one after [heim-1992]: a
conditional presupposes that its consequent is defined at the closest antecedent-worlds of the
epistemic state (119), and conjunction and disjunction inherit the condition (127)–(128)
(`clos`, `ifKPstar`, `andKPstar`, `orKPstar`, symmetric by construction, `orKPstar_comm`). A
closest-worlds presupposition strengthens to an unconditional one wherever the laws in force
allow the antecedent without it (`presup_strengthens`, the reasoning of (122)). For the
∀-over-if reading the conditional must quantify over the properties the antecedent disjoins
(142), since a conditional over the disjunction itself checks only the closest
disjunction-worlds and can miss a disjunct altogether (`kpstarForallOverIf_presup_of_closest`,
the paper's Scenario I). The K/P** readings (143) come out as the paper states them
(`ifOverExists_assertion`, `forallOverIf_presup`, `forallOverIf_assertion`), are invariant under
swapping the disjuncts (`forallOverIf_comm`), and for Mia and Sue the ∀-over-if reading
presupposes that Sue has money at the closest worlds where Mia is proud of hers
(`roothPartee_presup`), which strengthens to *if Mia has money, Sue has money*
(`roothPartee_presup_strengthens`). Under a strict conditional the ∀-over-if reading entails the
if-over-∃ reading, the asymmetry of the responses (33) (`forallOverIf_imp_ifOverExists`).

## Implementation notes

* The defined negation of a disjunct in (128) is read as presupposition-free (`definedFalse`);
  read as domain-restricted, the disjunction would presuppose both disjuncts' presuppositions at
  the evaluation world, against (134)–(135).
* The epistemic state `EP` and the similarity ordering the context supplies are parameters; the
  Limit Assumption built into CLOS (120) is not needed for the theorems stated.
* Properties are partial at each world (`Property`); the type-flexible connectives are given at
  the two types the paper uses. The structured-proposition extension (153)–(157), the
  Cooperative Principle (123)–(124), and accommodation as conjunction are not formalized.

## References

* [sharvit-2025]
* [rooth-partee-1982]
* [karttunen-peters-1979]
* [heim-1992]
-/

namespace Sharvit2025

open Presupposition PartialProp Conditional

variable {W E : Type*}

/-! ### CON-asymmetry and the symmetry of *or* -/

/-- The K+ disjunction under CON-asymmetry (16c), (17): defined exactly where its left disjunct
is. -/
def orAsym (p q : PartialProp W) : PartialProp W where
  presup := p.presup
  assertion w := p.assertion w ∨ q.assertion w

/-- Swapping the disjuncts of an asymmetric disjunction changes its presupposition wherever the
disjuncts differ in definedness: the LFs (62) and (64) are not equivalent. -/
theorem orAsym_presup_ne {p q : PartialProp W} {w : W} (hp : p.presup w) (hq : ¬ q.presup w) :
    (orAsym p q).presup w ∧ ¬ (orAsym q p).presup w :=
  ⟨hp, hq⟩

/-- The symmetric disjunction (102) is invariant under swapping its disjuncts. -/
theorem orKPSymmetric_comm (p q : PartialProp W) (w : W) :
    ((orKPSymmetric p q).presup w ↔ (orKPSymmetric q p).presup w) ∧
      ((orKPSymmetric p q).assertion w ↔ (orKPSymmetric q p).assertion w) := by
  simp only [orKPSymmetric]
  exact ⟨and_comm, or_comm⟩

/-! ### Karttunen's conditional presupposition and the closest-worlds one -/

variable (EP : Set W) (sim : SimilarityOrdering W)

/-- The K/P conditional (100): defined when the antecedent is, presupposing the consequent's
definedness at the evaluation world if the antecedent is true there; it asserts that every
antecedent-world of the epistemic state is a consequent-world. -/
def ifKP (p q : PartialProp W) : PartialProp W where
  presup w := p.presup w ∧ (p.assertion w → q.presup w)
  assertion _ := ∀ w' ∈ EP, p.assertion w' → q.assertion w'

/-- Where the antecedent is false, the K/P conditional presupposes nothing of its consequent:
the conditional presupposition that the Proviso Problem finds too weak. -/
theorem ifKP_presup_of_not_assertion {p : PartialProp W} (q : PartialProp W) {w : W}
    (hp : p.presup w) (h : ¬ p.assertion w) : (ifKP EP p q).presup w :=
  ⟨hp, λ ha => absurd ha h⟩

/-- CLOS (120): the closest worlds to `w`, under the similarity ordering the context supplies,
among the `Y`-worlds of the epistemic state. -/
def clos (w : W) (Y : Set W) : Set W := sim.closest w (Y ∩ EP)

theorem clos_subset (w : W) (Y : Set W) : clos EP sim w Y ⊆ Y :=
  (sim.closest_subset w _).trans Set.inter_subset_left

/-- The K/P* conditional (119): defined when the antecedent is and the consequent is defined at
the closest antecedent-worlds, asserting that those are consequent-worlds. -/
def ifKPstar (p q : PartialProp W) : PartialProp W where
  presup w := p.presup w ∧ clos EP sim w {w' | p.assertion w'} ⊆ {w' | q.presup w'}
  assertion w := clos EP sim w {w' | p.assertion w'} ⊆ {w' | q.assertion w'}

/-- The K/P* conjunction (127): the second conjunct is defined at the evaluation world or at
the closest worlds where the first is true. -/
def andKPstar (p q : PartialProp W) : PartialProp W where
  presup w :=
    p.presup w ∧ (q.presup w ∨ clos EP sim w {w' | p.assertion w'} ⊆ {w' | q.presup w'})
  assertion w := p.assertion w ∧ q.assertion w

/-- The presupposition-free proposition that `p` is defined and false. -/
def definedFalse (p : PartialProp W) : PartialProp W :=
  ofProp λ w => p.presup w ∧ ¬ p.assertion w

/-- The K/P* disjunction (128): one disjunct is defined, and each disjunct's defined negation
conjoins with the other. -/
def orKPstar (p q : PartialProp W) : PartialProp W where
  presup w :=
    (p.presup w ∨ q.presup w) ∧ (andKPstar EP sim (definedFalse p) q).presup w ∧
      (andKPstar EP sim (definedFalse q) p).presup w
  assertion w := p.assertion w ∨ q.assertion w

theorem orKPstar_presup (p q : PartialProp W) (w : W) :
    (orKPstar EP sim p q).presup w ↔
      (p.presup w ∨ q.presup w) ∧
        (q.presup w ∨
          clos EP sim w {w' | p.presup w' ∧ ¬ p.assertion w'} ⊆ {w' | q.presup w'}) ∧
        (p.presup w ∨
          clos EP sim w {w' | q.presup w' ∧ ¬ q.assertion w'} ⊆ {w' | p.presup w'}) := by
  simp [orKPstar, andKPstar, definedFalse, ofProp]

/-- The K/P* disjunction is symmetric by construction. -/
theorem orKPstar_comm (p q : PartialProp W) (w : W) :
    ((orKPstar EP sim p q).presup w ↔ (orKPstar EP sim q p).presup w) ∧
      ((orKPstar EP sim p q).assertion w ↔ (orKPstar EP sim q p).assertion w) := by
  refine ⟨?_, or_comm⟩
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> exact ⟨h₁.symm, h₃, h₂⟩

/-- (122): a closest-worlds presupposition `CLOS_w(P) ⊆ Q` holding throughout `M` strengthens
to `Q` throughout `M` when the laws in force allow `P` without `Q`, so that from a `¬Q`-world
the closest `P`-worlds include `¬Q`-worlds; the dissolution of the Proviso Problem. -/
theorem presup_strengthens {M P Q : Set W}
    (hlaw : ∀ w ∈ M, w ∉ Q → ¬ clos EP sim w P ⊆ Q) (h : ∀ w ∈ M, clos EP sim w P ⊆ Q) :
    ∀ w ∈ M, w ∈ Q := by
  intro w hw
  by_contra hq
  exact hlaw w hw hq (h w hw)

/-! ### K/P**: the conditional quantifies over the disjoined properties -/

/-- A property of individuals, partial at each world. -/
abbrev Property (W E : Type*) := E → PartialProp W

/-- The type-flexible disjunction of two properties applied to `x` (142a): a partial function
of properties `Z`, defined for the two disjuncts where the propositional disjunction of the two
applied to `x` is defined, and true of `Z` when `x` has `Z`. -/
def orProps (α β : Property W E) (x : E) (Z : Property W E) : PartialProp W where
  presup w := (orKPstar EP sim (α x) (β x)).presup w ∧ (Z = α ∨ Z = β)
  assertion w := (Z = α ∨ Z = β) ∧ (Z x).assertion w

/-- The type-flexible conditional over property-valued arguments (142b): for every property the
antecedent is defined for, the consequent is defined at the closest antecedent-worlds, and
holds there. -/
def ifProps (O₁ O₂ : Property W E → PartialProp W) : PartialProp W where
  presup w := (∃ Z, (O₁ Z).presup w) ∧
    ∀ Z, (O₁ Z).presup w →
      clos EP sim w {w' | (O₁ Z).assertion w'} ⊆ {w' | (O₂ Z).presup w'}
  assertion w :=
    ∀ Z, (O₁ Z).presup w →
      clos EP sim w {w' | (O₁ Z).assertion w'} ⊆ {w' | (O₂ Z).assertion w'}

/-- The existential closure of (144a). -/
def exists' (O : Property W E → PartialProp W) : PartialProp W where
  presup w := ∃ Z, (O Z).presup w
  assertion w := ∃ Z, (O Z).assertion w

/-- The if-over-∃ LF (143a): the conditional takes the existential closures of the disjoined
properties applied to `x` and to `y`, the ellipsis resolved to the disjunction. -/
def ifOverExists (α β : Property W E) (x y : E) : PartialProp W :=
  ifKPstar EP sim (exists' (orProps EP sim α β x)) (exists' (orProps EP sim α β y))

/-- The ∀-over-if LF (143b): the conditional quantifies over the disjoined properties, the
ellipsis bound to each in turn. -/
def forallOverIf (α β : Property W E) (x y : E) : PartialProp W :=
  ifProps EP sim (orProps EP sim α β x) λ Z => Z y

theorem exists'_orProps_assertion (α β : Property W E) (x : E) (w : W) :
    (exists' (orProps EP sim α β x)).assertion w ↔ (α x).assertion w ∨ (β x).assertion w := by
  simp [exists', orProps]

/-- (145b): the if-over-∃ reading asserts that the closest worlds where `x` has one of the
properties are worlds where `y` has one of them. -/
theorem ifOverExists_assertion (α β : Property W E) (x y : E) (w : W) :
    (ifOverExists EP sim α β x y).assertion w ↔
      clos EP sim w {w' | (α x).assertion w' ∨ (β x).assertion w'} ⊆
        {w' | (α y).assertion w' ∨ (β y).assertion w'} := by
  simp only [ifOverExists, ifKPstar, exists'_orProps_assertion]

/-- (146a): the ∀-over-if reading presupposes the disjunction of the antecedent and, for each
disjoined property, that `y`'s having it is defined at the closest worlds where `x` has it. -/
theorem forallOverIf_presup (α β : Property W E) (x y : E) (w : W) :
    (forallOverIf EP sim α β x y).presup w ↔
      (orKPstar EP sim (α x) (β x)).presup w ∧
        clos EP sim w {w' | (α x).assertion w'} ⊆ {w' | (α y).presup w'} ∧
        clos EP sim w {w' | (β x).assertion w'} ⊆ {w' | (β y).presup w'} := by
  constructor
  · rintro ⟨⟨Z, hP, -⟩, h⟩
    refine ⟨hP, ?_, ?_⟩
    · simpa [orProps] using h α ⟨hP, Or.inl rfl⟩
    · simpa [orProps] using h β ⟨hP, Or.inr rfl⟩
  · rintro ⟨hP, hα, hβ⟩
    refine ⟨⟨α, hP, Or.inl rfl⟩, ?_⟩
    rintro Z ⟨-, rfl | rfl⟩
    · simpa [orProps] using hα
    · simpa [orProps] using hβ

/-- (146b): where defined, the ∀-over-if reading asserts that, for each disjoined property, the
closest worlds where `x` has it are worlds where `y` has it. -/
theorem forallOverIf_assertion (α β : Property W E) (x y : E) (w : W)
    (h : (orKPstar EP sim (α x) (β x)).presup w) :
    (forallOverIf EP sim α β x y).assertion w ↔
      clos EP sim w {w' | (α x).assertion w'} ⊆ {w' | (α y).assertion w'} ∧
        clos EP sim w {w' | (β x).assertion w'} ⊆ {w' | (β y).assertion w'} := by
  constructor
  · intro hall
    exact ⟨by simpa [orProps] using hall α ⟨h, Or.inl rfl⟩,
      by simpa [orProps] using hall β ⟨h, Or.inr rfl⟩⟩
  · rintro ⟨hα, hβ⟩ Z ⟨-, rfl | rfl⟩
    · simpa [orProps] using hα
    · simpa [orProps] using hβ

/-- The disjunction being symmetric, *If x is P or Q, then y is* and *If x is Q or P, then y
is* share their ∀-over-if reading. -/
theorem forallOverIf_comm (α β : Property W E) (x y : E) (w : W) :
    ((forallOverIf EP sim α β x y).presup w ↔ (forallOverIf EP sim β α x y).presup w) ∧
      ((forallOverIf EP sim α β x y).assertion w ↔
        (forallOverIf EP sim β α x y).assertion w) := by
  refine ⟨?_, ?_⟩
  · rw [forallOverIf_presup, forallOverIf_presup]
    constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;>
      exact ⟨(orKPstar_comm EP sim _ _ w).1.mp h₁, h₃, h₂⟩
  · by_cases h : (orKPstar EP sim (α x) (β x)).presup w
    · have h' := (orKPstar_comm EP sim (α x) (β x) w).1.mp h
      rw [forallOverIf_assertion EP sim α β x y w h, forallOverIf_assertion EP sim β α x y w h',
        and_comm]
    · have h' : ¬ (orKPstar EP sim (β x) (α x)).presup w :=
        λ h' => h ((orKPstar_comm EP sim (α x) (β x) w).1.mpr h')
      constructor <;> intro _ Z hZ <;> exact absurd hZ.1 ‹_›

/-- Under a strict conditional, where the closest worlds are all the worlds of the epistemic
state, the ∀-over-if reading entails the if-over-∃ reading; the responses (33) show that the
converse fails, (33b) denying only the ∀-over-if reading. -/
theorem forallOverIf_imp_ifOverExists (hstrict : ∀ w Y, clos EP sim w Y = Y ∩ EP)
    (α β : Property W E) (x y : E) (w : W) (h : (orKPstar EP sim (α x) (β x)).presup w) :
    (forallOverIf EP sim α β x y).assertion w → (ifOverExists EP sim α β x y).assertion w := by
  rw [forallOverIf_assertion EP sim α β x y w h, ifOverExists_assertion, hstrict, hstrict,
    hstrict]
  rintro ⟨hα, hβ⟩ w' ⟨hor, hw'⟩
  rcases hor with hx | hx
  · exact Or.inl (hα ⟨hx, hw'⟩)
  · exact Or.inr (hβ ⟨hx, hw'⟩)

/-! ### Why the conditional must quantify over the disjuncts -/

/-- The consequent of (136) with the ellipsis resolved by the world-dependent property of
(137b): `y` has whichever disjoined property `x` has. -/
def matched (α β : Property W E) (x y : E) : PartialProp W where
  presup w := ((α x).assertion w → (α y).presup w) ∧ ((β x).assertion w → (β y).presup w)
  assertion w :=
    ((α x).assertion w → (α y).assertion w) ∧ ((β x).assertion w → (β y).assertion w)

/-- The K/P* attempt at the ∀-over-if reading, (136) with (137b): a conditional over the
disjunction itself. -/
def kpstarForallOverIf (α β : Property W E) (x y : E) : PartialProp W :=
  ifKPstar EP sim (orKPstar EP sim (α x) (β x)) (matched α β x y)

/-- Scenario I (141): when the closest worlds where `x` has one of the properties are all worlds
where `x` has the first and not the second, the conditional over the disjunction presupposes
nothing about `y` and the second property, which the ∀-over-if reading requires (146). -/
theorem kpstarForallOverIf_presup_of_closest (α β : Property W E) (x y : E) (w : W)
    (hc : clos EP sim w {w' | (α x).assertion w' ∨ (β x).assertion w'} ⊆
      {w' | (α x).assertion w' ∧ ¬ (β x).assertion w'}) :
    (kpstarForallOverIf EP sim α β x y).presup w ↔
      (orKPstar EP sim (α x) (β x)).presup w ∧
        clos EP sim w {w' | (α x).assertion w' ∨ (β x).assertion w'} ⊆
          {w' | (α y).presup w'} := by
  constructor
  · rintro ⟨hP, h⟩
    exact ⟨hP, λ w' hw' => (h hw').1 (hc hw').1⟩
  · rintro ⟨hP, h⟩
    exact ⟨hP, λ w' hw' => ⟨λ _ => h hw', λ hβ => absurd hβ (hc hw').2⟩⟩

/-! ### Mia and Sue (138) -/

variable (hasMoney proudOf : W → E → Prop)

/-- *penniless* (138a): true of `x` when `x` has no money. -/
def penniless (x : E) : PartialProp W := ofProp λ w => ¬ hasMoney w x

/-- *proud of her money* (138b): presupposes that `x` has money. -/
def proudOfMoney (x : E) : PartialProp W := ⟨λ w => hasMoney w x, λ w => proudOf w x⟩

/-- The disjunction *penniless or proud of her money* is presupposition-free, (134a) and
(135a). -/
theorem orKPstar_penniless_proud (x : E) (w : W) :
    (orKPstar EP sim (penniless hasMoney x) (proudOfMoney hasMoney proudOf x)).presup w := by
  simp only [orKPstar_presup, penniless, proudOfMoney, ofProp, true_and, true_or, and_true,
    not_not]
  exact Or.inr (clos_subset EP sim w _)

/-- (146a) for Mia and Sue: the ∀-over-if reading of *If Mia is penniless or proud of her
money, then Sue is* presupposes that Sue has money at the closest worlds where Mia is proud of
hers, (135a-iii) before strengthening. -/
theorem roothPartee_presup (mia sue : E) (w : W) :
    (forallOverIf EP sim (penniless hasMoney) (proudOfMoney hasMoney proudOf) mia sue).presup w
      ↔ clos EP sim w {w' | proudOf w' mia} ⊆ {w' | hasMoney w' sue} := by
  rw [forallOverIf_presup]
  constructor
  · rintro ⟨-, -, h⟩
    exact h
  · exact λ h => ⟨orKPstar_penniless_proud EP sim hasMoney proudOf mia w, λ _ _ => trivial, h⟩

/-- (146a-II), (135a-iii): across the worlds of the epistemic state where Mia has money, if the
laws allow Mia to be proud of her money while Sue has none, the reading presupposes that Sue
has money: *if Mia has money, Sue has money*. -/
theorem roothPartee_presup_strengthens (mia sue : E)
    (hlaw : ∀ w ∈ EP ∩ {w | hasMoney w mia}, ¬ hasMoney w sue →
      ¬ clos EP sim w {w' | proudOf w' mia} ⊆ {w' | hasMoney w' sue})
    (h : ∀ w ∈ EP,
      (forallOverIf EP sim (penniless hasMoney) (proudOfMoney hasMoney proudOf) mia sue).presup
        w) :
    ∀ w ∈ EP ∩ {w | hasMoney w mia}, hasMoney w sue :=
  presup_strengthens EP sim hlaw λ w hw =>
    (roothPartee_presup EP sim hasMoney proudOf mia sue w).mp (h w hw.1)

end Sharvit2025
