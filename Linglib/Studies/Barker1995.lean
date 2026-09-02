import Linglib.Semantics.Possession.Quantifier
import Linglib.Semantics.Quantification.Counting
import Linglib.Data.Examples.Barker1995
import Mathlib.Data.Fintype.Prod

/-!
# Barker (1995): Possessive Descriptions

Possessives are descriptions: a possessor, a possession relation — the noun's
own relation for a relational noun (*John's child*), a contextually resolved
one otherwise (*John's stick*) — and a sortal restrictor. Like definites they
presuppose a unique maximal possessee per possessor; like indefinites they can
introduce novel referents. In a quantificational possessive (*most planets'
rings*) the quantifier binds the possessor and possessee variables together.
Two consequences follow: quantification *narrows* to possessors that have a
possessee, and the possessor-dominant and symmetric construals cannot be told
apart truth-conditionally — uniqueness leaves one instance per case, which is
the book's resolution of the perspective paradox.

## Main statements

* `most_planets_rings_icy`, `not_unnarrowed`: the planets-and-rings model —
  narrowing is truth-conditionally active, and `Poss` builds it in via `dom`.
* `symmetric_iff_possessor_dominant`: with a unique possessee per possessor,
  *most* over possessor–possessee pairs agrees with `Poss most_sem` — the
  perspective paradox resolved.
* `favorite_color_possessor_dominant`, `not_favorite_color_possessee_dominant`:
  *most people's favorite color is blue* counts people, never colors.

## References

* [barker-1995]: Possessive Descriptions. CSLI Publications.
-/

namespace Barker1995

open Quantification Possession

/-! ### Decidability for the toy models -/

instance {α : Type*} [Fintype α] {A : α → Prop} {R : α → α → Prop}
    [DecidablePred A] [∀ x, DecidablePred (R x)] (x : α) :
    Decidable (dom A R x) :=
  decidable_of_iff (∃ b, A b ∧ R x b) Iff.rfl

instance {α : Type*} [Fintype α] {R S : α → Prop}
    [DecidablePred R] [DecidablePred S] :
    Decidable (some_sem R S) :=
  decidable_of_iff (∃ x, R x ∧ S x) Iff.rfl

/-! ### The perspective paradox resolved (Ch. 4)

With a unique possessee per possessor there is one instance per case, whether
or not the possessee variable helps distinguish cases: counting
possessor–possessee pairs agrees with counting possessors. -/

variable {α : Type*} [Fintype α]

/-- `count` does not depend on the choice of `Decidable` instances. -/
private theorem count_irrel {γ : Type*} [Fintype γ] (P : γ → Prop)
    (i1 i2 : DecidablePred P) : @count γ _ P i1 = @count γ _ P i2 :=
  congrArg (fun i => @count γ _ P i)
    (funext fun a => Subsingleton.elim (i1 a) (i2 a))

open Classical in
private theorem count_pair_eq (C A : α → Prop) (R : α → α → Prop)
    (huniq : ∀ x y y', A y → R x y → A y' → R x y' → y = y') (P : α → α → Prop) :
    count (fun p : α × α => (C p.1 ∧ A p.2 ∧ R p.1 p.2) ∧ P p.1 p.2) =
      count (fun x => (C x ∧ dom A R x) ∧ ∃ y, A y ∧ R x y ∧ P x y) := by
  unfold count countOn
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨-, ⟨hC, hA, hR⟩, hP⟩ := hp
    exact ⟨Finset.mem_univ x, ⟨hC, y, hA, hR⟩, y, hA, hR, hP⟩
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq h
    rw [Finset.mem_filter] at hp hq
    obtain ⟨-, ⟨-, hA, hR⟩, -⟩ := hp
    obtain ⟨-, ⟨-, hA', hR'⟩, -⟩ := hq
    dsimp only at h
    subst h
    exact congrArg (Prod.mk x) (huniq x y y' hA hR hA' hR')
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨-, ⟨hC, hdom⟩, y, hA, hR, hP⟩ := hx
    exact ⟨(x, y), Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hC, hA, hR⟩, hP⟩, rfl⟩

open Classical in
/-- The uniqueness presupposition neutralizes the perspective paradox (Ch. 4):
when each possessor has at most one possessee, *most* over
possessor–possessee pairs (the symmetric construal) and `Poss most_sem` (the
possessor-dominant construal) have the same truth conditions. -/
theorem symmetric_iff_possessor_dominant (C A B : α → Prop) (R : α → α → Prop)
    (huniq : ∀ x y y', A y → R x y → A y' → R x y' → y = y') :
    most_sem (fun p : α × α => C p.1 ∧ A p.2 ∧ R p.1 p.2) (fun p => B p.2) ↔
      Poss most_sem C some_sem R A B := by
  unfold Poss most_sem
  beta_reduce
  rw [count_eq_decidable (fun p : α × α => (C p.1 ∧ A p.2 ∧ R p.1 p.2) ∧ B p.2) _,
      count_eq_decidable (fun p : α × α => (C p.1 ∧ A p.2 ∧ R p.1 p.2) ∧ ¬ B p.2) _,
      count_eq_decidable (fun x => (C x ∧ dom A R x) ∧
        some_sem (fun y => A y ∧ R x y) B) _,
      count_eq_decidable (fun x => (C x ∧ dom A R x) ∧
        ¬ some_sem (fun y => A y ∧ R x y) B) _]
  have h1' : count (fun p : α × α => (C p.1 ∧ A p.2 ∧ R p.1 p.2) ∧ B p.2)
      = count (fun x => (C x ∧ dom A R x) ∧ ∃ y, A y ∧ R x y ∧ B y) :=
    (count_irrel _ _ _).trans
      ((count_pair_eq C A R huniq fun _ y => B y).trans (count_irrel _ _ _))
  have h2' : count (fun p : α × α => (C p.1 ∧ A p.2 ∧ R p.1 p.2) ∧ ¬ B p.2)
      = count (fun x => (C x ∧ dom A R x) ∧ ∃ y, A y ∧ R x y ∧ ¬ B y) :=
    (count_irrel _ _ _).trans
      ((count_pair_eq C A R huniq fun _ y => ¬ B y).trans (count_irrel _ _ _))
  have hc1 : count (fun x => (C x ∧ dom A R x) ∧ ∃ y, A y ∧ R x y ∧ B y)
      = count (fun x => (C x ∧ dom A R x) ∧ some_sem (fun y => A y ∧ R x y) B) :=
    count_congr_iff fun x => by unfold some_sem; tauto
  have hc2 : count (fun x => (C x ∧ dom A R x) ∧ ∃ y, A y ∧ R x y ∧ ¬ B y)
      = count (fun x => (C x ∧ dom A R x) ∧ ¬ some_sem (fun y => A y ∧ R x y) B) :=
    count_congr_iff fun x => by
      unfold some_sem
      constructor
      · rintro ⟨⟨hC, hdom⟩, y, hA, hR, hnB⟩
        exact ⟨⟨hC, hdom⟩, fun ⟨y', ⟨hA', hR'⟩, hB'⟩ =>
          hnB (huniq x y' y hA' hR' hA hR ▸ hB')⟩
      · rintro ⟨⟨hC, y, hA, hR⟩, hn⟩
        exact ⟨⟨hC, ⟨y, hA, hR⟩⟩, y, hA, hR, fun hB => hn ⟨y, ⟨hA, hR⟩, hB⟩⟩
  omega

/-! ### Narrowing: the planets and their rings (Ch. 4)

Nine planets, of which only Saturn, Neptune and Uranus have rings; Saturn's
and Neptune's rings are icy, Uranus's are not. *Most planets' rings are made
of ice* is judged true — the quantification ranges only over the three ringed
planets. Entities `0`–`8` are the planets, `9`–`11` their rings. -/

abbrev isPlanet : Fin 12 → Prop := fun x => x.val < 9

abbrev isRing : Fin 12 → Prop := fun x => 9 ≤ x.val

abbrev hasRing : Fin 12 → Fin 12 → Prop := fun x y =>
  (x = 0 ∧ y = 9) ∨ (x = 1 ∧ y = 10) ∨ (x = 2 ∧ y = 11)

abbrev isIcy : Fin 12 → Prop := fun y => y = 9 ∨ y = 10

/-- *Most planets' rings are made of ice* is true: `Poss` narrows the domain
to the three ringed planets, two of which have icy rings. -/
theorem most_planets_rings_icy :
    Poss most_sem isPlanet some_sem hasRing isRing isIcy := by
  unfold Poss most_sem
  beta_reduce
  rw [count_eq_decidable (fun x : Fin 12 => (isPlanet x ∧ dom isRing hasRing x) ∧
        some_sem (fun y => isRing y ∧ hasRing x y) isIcy) _,
      count_eq_decidable (fun x : Fin 12 => (isPlanet x ∧ dom isRing hasRing x) ∧
        ¬ some_sem (fun y => isRing y ∧ hasRing x y) isIcy) _]
  have v1 : count (fun x : Fin 12 => (isPlanet x ∧ dom isRing hasRing x) ∧
      some_sem (fun y => isRing y ∧ hasRing x y) isIcy) = 2 := by
    simp only [count, countOn]; decide
  have v2 : count (fun x : Fin 12 => (isPlanet x ∧ dom isRing hasRing x) ∧
      ¬ some_sem (fun y => isRing y ∧ hasRing x y) isIcy) = 1 := by
    simp only [count, countOn]; decide
  omega

/-- Without narrowing, the quantification is false: only two of the nine
planets have an icy ring. -/
theorem not_unnarrowed :
    ¬ most_sem isPlanet
      (fun x => some_sem (fun y => isRing y ∧ hasRing x y) isIcy) := by
  unfold most_sem
  beta_reduce
  rw [count_eq_decidable (fun x : Fin 12 => isPlanet x ∧
        some_sem (fun y => isRing y ∧ hasRing x y) isIcy) _,
      count_eq_decidable (fun x : Fin 12 => isPlanet x ∧
        ¬ some_sem (fun y => isRing y ∧ hasRing x y) isIcy) _]
  have v1 : count (fun x : Fin 12 => isPlanet x ∧
      some_sem (fun y => isRing y ∧ hasRing x y) isIcy) = 2 := by
    simp only [count, countOn]; decide
  have v2 : count (fun x : Fin 12 => isPlanet x ∧
      ¬ some_sem (fun y => isRing y ∧ hasRing x y) isIcy) = 7 := by
    simp only [count, countOn]; decide
  omega

/-! ### No possessee-dominant reading (Ch. 4)

Five people and three colors: one favors red, one yellow, three blue. *Most
people's favorite color is blue* is true counting people (3 of 5) and would
be false counting colors (1 of 3); the color-counting reading does not exist.
Entities `0`–`4` are the people; `5`, `6`, `7` are red, yellow, blue. -/

abbrev isPerson : Fin 8 → Prop := fun x => x.val < 5

abbrev isColor : Fin 8 → Prop := fun x => 5 ≤ x.val

abbrev favors : Fin 8 → Fin 8 → Prop := fun x y =>
  (x = 0 ∧ y = 5) ∨ (x = 1 ∧ y = 6) ∨ ((x = 2 ∨ x = 3 ∨ x = 4) ∧ y = 7)

abbrev isBlue : Fin 8 → Prop := fun y => y = 7

/-- *Most people's favorite color is blue*, counting people: true, 3 of 5. -/
theorem favorite_color_possessor_dominant :
    Poss most_sem isPerson some_sem favors isColor isBlue := by
  unfold Poss most_sem
  beta_reduce
  rw [count_eq_decidable (fun x : Fin 8 => (isPerson x ∧ dom isColor favors x) ∧
        some_sem (fun y => isColor y ∧ favors x y) isBlue) _,
      count_eq_decidable (fun x : Fin 8 => (isPerson x ∧ dom isColor favors x) ∧
        ¬ some_sem (fun y => isColor y ∧ favors x y) isBlue) _]
  have v1 : count (fun x : Fin 8 => (isPerson x ∧ dom isColor favors x) ∧
      some_sem (fun y => isColor y ∧ favors x y) isBlue) = 3 := by
    simp only [count, countOn]; decide
  have v2 : count (fun x : Fin 8 => (isPerson x ∧ dom isColor favors x) ∧
      ¬ some_sem (fun y => isColor y ∧ favors x y) isBlue) = 2 := by
    simp only [count, countOn]; decide
  omega

/-- Counting favored colors instead of people would make the sentence false —
the reading English does not have. -/
theorem not_favorite_color_possessee_dominant :
    ¬ most_sem (fun c => isColor c ∧ ∃ p, isPerson p ∧ favors p c) isBlue := by
  unfold most_sem
  beta_reduce
  rw [count_eq_decidable (fun c : Fin 8 =>
        (isColor c ∧ ∃ p, isPerson p ∧ favors p c) ∧ isBlue c) _,
      count_eq_decidable (fun c : Fin 8 =>
        (isColor c ∧ ∃ p, isPerson p ∧ favors p c) ∧ ¬ isBlue c) _]
  have v1 : count (fun c : Fin 8 =>
      (isColor c ∧ ∃ p, isPerson p ∧ favors p c) ∧ isBlue c) = 1 := by
    simp only [count, countOn]; decide
  have v2 : count (fun c : Fin 8 =>
      (isColor c ∧ ∃ p, isPerson p ∧ favors p c) ∧ ¬ isBlue c) = 2 := by
    simp only [count, countOn]; decide
  omega

/-- Each person favors at most one color. -/
theorem favors_unique :
    ∀ x y y' : Fin 8, isColor y → favors x y → isColor y' → favors x y' →
      y = y' := by decide

/-- The symmetric construal of the favorite-color sentence, derived from the
possessor-dominant one through `symmetric_iff_possessor_dominant`. -/
theorem favorite_color_symmetric :
    most_sem (fun p : Fin 8 × Fin 8 => isPerson p.1 ∧ isColor p.2 ∧ favors p.1 p.2)
      (fun p => isBlue p.2) :=
  (symmetric_iff_possessor_dominant isPerson isColor isBlue favors
    favors_unique).mpr favorite_color_possessor_dominant

/-! ### Definiteness (Ch. 2)

A definite possessive presupposes a unique possessee: *the boy's cat* in a model where the
boy `0` owns exactly the cat `1` (entities: boy, cat, dog; one situation). -/

/-- *the boy's cat*: the boy `0` owns the cat `1`. -/
def theBoysCat : Possession.Description (Fin 3) Unit where
  possessor := 0
  relation := fun x y _ => x = 0 ∧ y = 1
  restrictor := fun y _ => y = 1

/-- The description has a unique possessee. -/
theorem theBoysCat_unique (s : Unit) : ∃! y, theBoysCat.possesseePred y s :=
  ⟨1, ⟨rfl, rfl, rfl⟩, fun _ h => h.1⟩

/-! ### Narrowing through a description

For a single possessor, narrowing surfaces as existential import: *Mercury's
rings are icy* fails because Mercury (planet `3`) has no ring. -/

/-- "Mercury's rings": possessor `3`, with `hasRing` as the possession
relation. -/
def mercurysRings : Possession.Description (Fin 12) Unit where
  possessor := 3
  relation := fun x y _ => hasRing x y
  restrictor := fun y _ => isRing y

/-- *Mercury's rings are icy* is false: the description denotation carries
existential import, and Mercury has no ring. -/
theorem mercurysRings_not_icy :
    ¬ mercurysRings.toGQ some_sem () isRing isIcy := by
  intro h
  obtain ⟨b, -, hr⟩ := mercurysRings.toGQ_existential_import some_sem () h
  have hb : hasRing 3 b := hr
  rcases hb with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨h3, -⟩ <;> exact absurd h3 (by decide)

end Barker1995
