module

public import Linglib.Logic.Natural.Strawson.Basic
public import Linglib.Semantics.Exhaustification.Excluder
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Data.Examples.Gajewski2011

/-!
# Gajewski (2011): Licensing strong NPIs

This file formalizes [gajewski-2011]'s account of why weak negative polarity items (*any*,
*ever*) and strong ones (*in weeks*, *either*, *until*) part ways under *only*, conditional
antecedents and *sorry*. Those operators are Strawson anti-additive ([von-fintel-1999]), yet
they license only the weak items, although anti-additivity is what strong items were held to
need ([zwarts-1998]); `strawsonAA_not_sufficient` is the puzzle. The paper's answer is that the
two classes inspect different meanings: a weak item needs the plain meaning Strawson downward
entailing, a strong item needs the meaning enriched by [chierchia-2006]'s exhaustivity operator
`Exhaustification.exh`, presuppositions included, downward entailing in the plain sense
(`Licensed`). A determiner at the bottom of its Horn scale, *no*, is its own enriched meaning
and licenses both; one above the bottom, *not every* or *at most five*, exhaustifies to a
meaning with an upward-entailing conjunct and licenses only weak items; and a presupposition
trigger's full meaning fails plain downward entailment for the same reason. So *no* is the only
licenser of strong items and *some* the only non-licenser of weak ones, which is the paper's
pattern of judgments (`rows_predicted`). Horn's Intolerance, the paper's condition for a
non-endpoint to act as an endpoint, sits strictly between anti-additivity and downward
entailment (`IsIntolerant`).

## Implementation notes

* Entailment between scale-mates holds the restrictor fixed and quantifies over scopes, so *no*
  entails *not every* whenever the restrictor is nonempty, which is what makes *no* the bottom
  of its scale; letting the restrictor vary would break the entailment at an empty restrictor.
  The scale is the pair of ends the paper's computation of exhaustified *not every* uses.
* The presupposition triggers have no scale-mates, so their enriched meaning is their full
  meaning, presupposition included, and the strong principle asks for its plain downward
  entailment. The operators and their Strawson properties are the Strawson substrate's.
* *At most five* against *at most four*, and the cardinal *fewer than four* of the
  scale-truncation discussion, are checked on a six-element domain.

## References

* [gajewski-2011]
* [von-fintel-1999]
* [zwarts-1998]
* [chierchia-2006]
* [horn-1989]
-/

@[expose] public section

namespace Gajewski2011

open NaturalLogic Presupposition Quantifier Quantifier.GQ Data.Examples

variable {α : Type*}

/-! ### Enriched meanings -/

/-- The implicature-enriched meaning of a quantified DP, `O` applied to the determiner against
its scale-mates: the plain meaning with every scale-mate true of the scope but not entailed
excluded, where entailment holds the restrictor fixed and quantifies over scopes. -/
def exh (Q : GQ α) (C : Set (GQ α)) : GQ α :=
  λ A => Exhaustification.exh ((· A) '' C) (Q A)

theorem mem_exh {Q : GQ α} {C : Set (GQ α)} {A P : α → Prop} :
    exh Q C A P ↔ Q A P ∧ ∀ Q' ∈ C, Q' A P → Q A ≤ Q' A :=
  ⟨λ ⟨h, h'⟩ => ⟨h, λ Q' hQ' hP => h' _ ⟨Q', hQ', rfl⟩ hP⟩,
    λ ⟨h, h'⟩ => ⟨h, by rintro _ ⟨Q', hQ', rfl⟩ hP; exact h' Q' hQ' hP⟩⟩

/-- A scale-mate that is true but not entailed is excluded. -/
theorem exh_not_of_not_le {Q Q' : GQ α} {C : Set (GQ α)} {A P : α → Prop} (hQ' : Q' ∈ C)
    (hP : Q' A P) (h : ¬ Q A ≤ Q' A) : ¬ exh Q C A P :=
  λ he => h ((mem_exh.1 he).2 Q' hQ' hP)

/-- At the bottom of its scale a determiner is its own enriched meaning. -/
theorem exh_eq_of_forall_le {Q : GQ α} {C : Set (GQ α)} {A : α → Prop}
    (h : ∀ Q' ∈ C, ∀ P, Q' A P → Q A ≤ Q' A) : exh Q C A = Q A :=
  Exhaustification.exh_eq_self_iff.2 (by rintro _ ⟨Q', hQ', rfl⟩ ⟨P, _, hP⟩; exact h Q' hQ' P hP)

/-- Exhaustified *no* is *no*. -/
theorem exh_no : exh (no : GQ α) {everyᶜ} = no := by
  funext A
  refine exh_eq_of_forall_le λ Q' hQ' P hP => ?_
  rw [Set.mem_singleton_iff] at hQ'
  subst hQ'
  obtain ⟨x, hx⟩ := not_forall.mp hP
  exact λ P' hno hev => hx λ hAx => absurd (hev x hAx) (hno x hAx)

/-- Exhaustified *not every* is *some but not every* once the restrictor has two elements. -/
theorem exh_notEvery {A : α → Prop} {x y : α} (hx : A x) (hy : A y) (hxy : x ≠ y) :
    exh (everyᶜ) {no} A = λ P => GQ.some A P ∧ everyᶜ A P := by
  funext P
  refine propext (mem_exh.trans
    ⟨λ ⟨hne, h⟩ => ⟨?_, hne⟩, λ ⟨⟨z, hz, hPz⟩, hne⟩ => ⟨hne, λ Q' hQ' hno => ?_⟩⟩)
  · by_contra hsome
    exact h no (Set.mem_singleton _) (λ z hz hPz => hsome ⟨z, hz, hPz⟩) (· = x)
      (λ hall => hxy (hall y hy).symm) x hx rfl
  · exact ((Set.mem_singleton_iff.mp hQ' ▸ hno) z hz hPz).elim

/-- An enriched meaning satisfiable at a restrictor but excluded at the empty scope is not
downward entailing in its scope. -/
theorem not_scopeDownwardMono_exh {Q : GQ α} {C : Set (GQ α)} {A P : α → Prop}
    (hP : exh Q C A P) (h : ¬ exh Q C A (λ _ => False)) : ¬ ScopeAntitone (exh Q C) :=
  fun hde => h (hde A (show ((fun _ : α => False) : α → Prop) ≤ P from fun _ hf => hf.elim) hP)

/-! ### The licensing principles -/

/-- Exhaustified *no* is downward entailing, so *no* licenses strong items. -/
theorem no_strong : ScopeAntitone (exh (no : GQ α) {everyᶜ}) := by
  rw [exh_no]; exact scopeAntitone_no

/-- Exhaustified *not every* is not downward entailing, since at the empty scope the stronger
scale-mate *no* is true and excluded. -/
theorem notEvery_not_strong [Nontrivial α] :
    ¬ ScopeAntitone (exh (everyᶜ : GQ α) {no}) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  refine not_scopeDownwardMono_exh (A := λ _ => True) (P := (· = x))
    (mem_exh.2 ⟨λ h => hxy (h y trivial).symm, λ Q' hQ' hno =>
      ((Set.mem_singleton_iff.mp hQ' ▸ hno) x trivial rfl).elim⟩)
    (exh_not_of_not_le (Set.mem_singleton _) (λ _ _ hf => hf)
      λ hle => hle (· = x) (λ h => hxy (h y trivial).symm) x trivial rfl)

/-- Exhaustified *some* is not downward entailing, since *some* itself fails at the empty
scope. -/
theorem some_not_strong [Nontrivial α] :
    ¬ ScopeAntitone (exh (GQ.some : GQ α) {every}) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  exact not_scopeDownwardMono_exh (A := λ _ => True) (P := (· = x))
    (mem_exh.2 ⟨⟨x, trivial, rfl⟩, λ Q' hQ' hev =>
      (hxy ((Set.mem_singleton_iff.mp hQ' ▸ hev) y trivial).symm).elim⟩)
    λ h => (mem_exh.1 h).1.elim λ _ h => h.2

/-- *At most five* sits above *at most four* on its scale; excluding the scale-mate leaves
*exactly five*, which is not downward entailing. -/
theorem atMostFive_not_strong :
    ¬ ScopeAntitone (exh (atMost 5 : GQ (Fin 6)) {atMost 4}) := by
  have h4 : ¬ atMost 4 (λ _ : Fin 6 => True) (· ≠ 0) := by
    rw [atMost_iff]; decide
  refine not_scopeDownwardMono_exh (A := λ _ => True) (P := (· ≠ 0))
    (mem_exh.2 ⟨by rw [atMost_iff]; decide,
      λ Q' hQ' h => (h4 (Set.mem_singleton_iff.mp hQ' ▸ h)).elim⟩)
    (exh_not_of_not_le (Set.mem_singleton _) (by rw [atMost_iff]; decide)
      λ hle => h4 (hle (· ≠ 0) (by rw [atMost_iff]; decide)))

/-- The paper's licensers. -/
inductive Licenser
  | no | atMostFive | some | only | conditional | sorryThat
  deriving DecidableEq, Repr

/-- Weak items are *any* and *ever*, strong ones *in weeks*, *either* and *until*. -/
inductive Strength
  | weak | strong
  deriving DecidableEq, Repr

/-- The two licensing principles applied to a licenser's analysis, on which a weak item needs
the plain meaning Strawson downward entailing and a strong item needs the enriched meaning
downward entailing, which for a presupposition trigger without scale-mates is its full
meaning. -/
def Licensed : Licenser → Strength → Prop
  | .no, .weak => ∀ {α : Type}, ScopeAntitone (no : GQ α)
  | .no, .strong => ∀ {α : Type}, ScopeAntitone (exh (no : GQ α) {everyᶜ})
  | .atMostFive, .weak => ∀ {α : Type} [Fintype α], ScopeAntitone (atMost (α := α) 5)
  | .atMostFive, .strong =>
      ∀ {α : Type} [Fintype α], ScopeAntitone (exh (atMost (α := α) 5) {atMost 4})
  | .some, .weak => ∀ {α : Type}, ScopeAntitone (GQ.some : GQ α)
  | .some, .strong => ∀ {α : Type}, ScopeAntitone (exh (GQ.some : GQ α) {every})
  | .only, .weak => ∀ {ι W : Type} (x : ι), IsStrawsonDE (only (W := W) x)
  | .only, .strong => ∀ {ι W : Type} (x : ι), Antitone λ P : ι → Set W => (only x P).truthSet
  | .conditional, .weak => ∀ {W : Type} (domain : W → Set W) (q : Set W),
      IsStrawsonDE (would domain · q)
  | .conditional, .strong => ∀ {W : Type} (domain : W → Set W) (q : Set W),
      Antitone λ p => (would domain p q).truthSet
  | .sorryThat, .weak => ∀ {W : Type} (dox best : W → Set W), IsStrawsonDE (regret dox best)
  | .sorryThat, .strong => ∀ {W : Type} (dox best : W → Set W),
      Antitone λ p => (regret dox best p).truthSet

/-- The puzzle is that *only*, *would* and *sorry* are Strawson anti-additive, the Strawson form
of what strong items were held to need, yet none licenses them. -/
theorem strawsonAA_not_sufficient :
    (∀ {ι W : Type} (x : ι), IsStrawsonAntiAdditive (only (W := W) x)) ∧
      (∀ {W : Type} (domain : W → Set W) (q : Set W),
        IsStrawsonAntiAdditive (would domain · q)) ∧
      (∀ {W : Type} (dox best : W → Set W), IsStrawsonAntiAdditive (regret dox best)) ∧
      ¬ Licensed .only .strong ∧ ¬ Licensed .conditional .strong ∧
        ¬ Licensed .sorryThat .strong :=
  ⟨λ x => only_isStrawsonAA x, λ d q => would_isStrawsonAA d q, λ d b => regret_isStrawsonAA d b,
    λ h => only_not_antitone (h _), λ h => would_not_antitone (h _ _),
    λ h => regret_not_antitone (h _ _)⟩

/-- *No* is the only one of the paper's licensers whose enriched meaning is downward
entailing. -/
theorem licensed_strong_iff (L : Licenser) : Licensed L .strong ↔ L = .no := by
  cases L with
  | no => exact iff_of_true (λ {_} => no_strong) rfl
  | atMostFive => exact iff_of_false (λ h => atMostFive_not_strong h) nofun
  | some => exact iff_of_false (λ h => some_not_strong (α := Bool) h) nofun
  | only => exact iff_of_false strawsonAA_not_sufficient.2.2.2.1 nofun
  | conditional => exact iff_of_false strawsonAA_not_sufficient.2.2.2.2.1 nofun
  | sorryThat => exact iff_of_false strawsonAA_not_sufficient.2.2.2.2.2 nofun

/-- *Some* is the only one of the paper's licensers whose plain meaning is not Strawson
downward entailing. -/
theorem licensed_weak_iff (L : Licenser) : Licensed L .weak ↔ L ≠ .some := by
  cases L with
  | no => exact iff_of_true (λ {_} => scopeAntitone_no) nofun
  | atMostFive => exact iff_of_true (λ {_} => scopeAntitone_atMost 5) nofun
  | some =>
    refine iff_of_false (λ h => ?_) (· rfl)
    exact (h (α := Bool) (fun _ => True)
      (show ((fun _ : Bool => False) : Bool → Prop) ≤ fun _ => True from fun _ hf => hf.elim)
      ⟨true, trivial, trivial⟩).elim fun _ h => h.2
  | only => exact iff_of_true (λ x => only_isStrawsonDE x) nofun
  | conditional => exact iff_of_true (λ d q => would_isStrawsonDE d q) nofun
  | sorryThat => exact iff_of_true (λ d b => regret_isStrawsonDE d b) nofun

theorem licensed_iff (L : Licenser) (s : Strength) :
    Licensed L s ↔ (s = .weak ∧ L ≠ .some) ∨ (s = .strong ∧ L = .no) := by
  cases s <;> simp [licensed_weak_iff, licensed_strong_iff]

/-! ### Intolerance -/

/-- A function of properties is trivial when it is constantly true or constantly false. -/
def IsTrivial (f : Set α → Prop) : Prop := (∀ x, f x) ∨ ∀ x, ¬ f x

/-- A nontrivial function of properties is Intolerant when it never accepts both a property and
its complement: the items above the midpoint of their scale ([horn-1989]). -/
def IsIntolerant (f : Set α → Prop) : Prop := ¬ IsTrivial f → ∀ x, ¬ f x ∨ ¬ f xᶜ

/-- Anti-additivity implies Intolerance, since accepting `x` and `xᶜ` means accepting everything. -/
theorem isIntolerant_of_isAntiAdditive {f : Set α → Prop} (h : IsAntiAdditive f) :
    IsIntolerant f := λ hnt x => by
  by_contra hx
  rw [not_or, not_not, not_not] at hx
  have huniv := (isAntiAdditive_iff_gq.1 h x xᶜ).2 hx
  rw [Set.union_compl_self] at huniv
  exact hnt (Or.inl λ y => h.antitone (Set.subset_univ y) huniv)

open Classical in
/-- Proportional *few* is Intolerant, since fewer than half in and fewer than half out is
impossible. -/
theorem few_isIntolerant [Fintype α] (A : α → Prop) : IsIntolerant (few A) := λ _ x => by
  by_contra hx
  rw [not_or, not_not, not_not, few_iff, few_iff] at hx
  obtain ⟨h₁, h₂⟩ := hx
  rw [count_congr_iff (P := λ z => A z ∧ xᶜ z) (Q := λ z => A z ∧ ¬ x z) λ _ => Iff.rfl,
    count_congr_iff (P := λ z => A z ∧ ¬ xᶜ z) (Q := λ z => A z ∧ x z)
      λ _ => and_congr_right' not_not] at h₂
  omega

/-- Cardinal *fewer than four* is not Intolerant, since with six elements three are in and three
out. -/
theorem atMostThree_not_isIntolerant :
    ¬ IsIntolerant (atMost 3 (λ _ : Fin 6 => True)) := λ h => by
  let _ : DecidablePred λ z : Fin 6 => True ∧ (λ x : Fin 6 => x < 3)ᶜ z :=
    λ z => inferInstanceAs (Decidable (True ∧ ¬ z < 3))
  exact (h (λ ht => ht.elim
      (λ h => absurd (atMost_iff.1 (h (λ _ => True))) (by decide))
      λ h => h (λ _ => False) (atMost_iff.2 (by decide))) (· < 3)).elim
    (· (atMost_iff.2 (by decide))) (· (atMost_iff.2 (by decide)))

/-- Proportional *few* is downward entailing and Intolerant but not anti-additive, so
Intolerance is a proper intermediate between anti-additivity and downward entailment. -/
theorem few_not_rightAntiAdditive : ¬ RightAntiAdditive (few : GQ (Fin 4)) := λ h =>
  absurd ((h (λ _ => True) (· = 0) (· = 1)).mpr
      ⟨few_iff.mpr (by decide), few_iff.mpr (by decide)⟩)
    (few_iff.not.mpr (by decide))

/-! ### The paper's sentences -/

/-- A sentence of the paper records its licenser, the strength of its polarity item, and the
judgment. -/
structure Row where
  licenser : Licenser
  strength : Strength
  judgment : Judgment
  deriving DecidableEq, Repr

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let licenser ← ex.parse? "licenser" [("no", Licenser.no), ("atMostFive", .atMostFive),
    ("some", .some), ("only", .only), ("conditional", .conditional), ("sorry", .sorryThat)]
  let strength ← ex.parse? "strength" [("weak", Strength.weak), ("strong", .strong)]
  pure ⟨licenser, strength, ex.judgment⟩

def rows : List Row := Examples.all.filterMap Row.ofExample

/-- Every judgment in the paper follows from the two licensing principles. -/
theorem rows_predicted :
    ∀ r ∈ rows, (r.judgment = .acceptable ↔ Licensed r.licenser r.strength) := by
  simp only [licensed_iff]
  decide

end Gajewski2011
