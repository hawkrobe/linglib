import Linglib.Logic.Natural.Strawson.Basic
import Linglib.Semantics.Quantification.Counting
import Linglib.Data.Examples.Gajewski2011

/-!
# Gajewski (2011): Licensing strong NPIs

This file formalizes [gajewski-2011]'s account of why weak negative polarity items (*any*,
*ever*) and strong ones (*in weeks*, *either*, *until*) part ways under *only*, conditional
antecedents and *sorry*. Those operators are Strawson anti-additive ([von-fintel-1999]), yet
they license only the weak items, although anti-additivity is what the strong items were held
to need ([zwarts-1998]). The paper's answer is that the two classes inspect different meanings:
a weak item needs a licenser that is Strawson downward entailing, a strong item a licenser whose
meaning enriched by scalar implicature is downward entailing in the plain sense. A determiner at
the bottom of its Horn scale, *no*, is its own enriched meaning and licenses both; one above the
bottom, *not every* or *at most five*, exhaustifies to a meaning with an upward-entailing
conjunct and licenses only weak items; and a presupposition trigger's full meaning fails plain
downward entailment for the same reason.

The exhaustivity operator `exh` enriches a determiner against its scale-mates in the manner of
[fox-2007] over [chierchia-2004]'s alternatives, `Licensed` applies the two principles to each
of the paper's licensers, and `rows_predicted` checks them against the paper's sentences. The
Intolerance property of the paper's appendix ([horn-1989]), which sits strictly between
anti-additivity and downward entailment, is `IsIntolerant`.

## Implementation notes

* Entailment between scale-mates holds the restrictor fixed and quantifies over scopes, so *no*
  entails *not every* whenever the restrictor is nonempty, which is what makes *no* the bottom
  of its scale; letting the restrictor vary would break the entailment at an empty restrictor.
  The scale is the pair of ends the paper's computation of exhaustified *not every* uses; the
  intermediate scale-mates would sharpen that meaning further.
* The presupposition triggers have no scale-mates, so their enriched meaning is their full
  meaning, presupposition included, and the strong principle asks for its plain downward
  entailment. The operators and their Strawson properties are the Strawson substrate's.
* The paper's *at most five* against *at most four*, and the cardinal *fewer than four* of its
  scale-truncation discussion, are checked on a six-element domain.

## References

* [gajewski-2011]
* [von-fintel-1999]
* [zwarts-1998]
* [chierchia-2004]
* [fox-2007]
* [horn-1989]
-/

namespace Gajewski2011

open NaturalLogic Quantification Data.Examples

variable {α : Type*}

/-! ### Enriched meanings -/

/-- The implicature-enriched meaning of a quantified DP: the determiner's plain meaning together
with the exclusion of every scale-mate that is true of the scope without being entailed, where
entailment holds the restrictor fixed and quantifies over scopes. -/
def exh (Q : GQ α) (C : Set (GQ α)) : GQ α :=
  λ A P => Q A P ∧ ∀ Q' ∈ C, Q' A P → Q A ≤ Q' A

/-- A scale-mate that is true but not entailed is excluded. -/
theorem exh_not_of_not_le {Q Q' : GQ α} {C : Set (GQ α)} {A P : α → Prop} (hQ' : Q' ∈ C)
    (hP : Q' A P) (h : ¬ Q A ≤ Q' A) : ¬ exh Q C A P :=
  λ he => h (he.2 Q' hQ' hP)

/-- At the bottom of its scale a determiner is its own enriched meaning. -/
theorem exh_eq_of_forall_le {Q : GQ α} {C : Set (GQ α)} {A : α → Prop}
    (h : ∀ Q' ∈ C, ∀ P, Q' A P → Q A ≤ Q' A) : exh Q C A = Q A :=
  funext λ _ => propext ⟨And.left, λ hQ => ⟨hQ, λ Q' hQ' hP => h Q' hQ' _ hP⟩⟩

/-- Exhaustified *no* is *no*. -/
theorem exh_no : exh (no_sem : GQ α) {outerNeg every_sem} = no_sem := by
  funext A
  refine exh_eq_of_forall_le λ Q' hQ' P hP => ?_
  rw [Set.mem_singleton_iff] at hQ'
  subst hQ'
  obtain ⟨x, hx⟩ := not_forall.mp hP
  exact λ P' hno hev => hx λ hAx => absurd (hev x hAx) (hno x hAx)

/-- Exhaustified *not every* is *some but not every* once the restrictor has two elements. -/
theorem exh_notEvery {A : α → Prop} {x y : α} (hx : A x) (hy : A y) (hxy : x ≠ y) :
    exh (outerNeg every_sem) {no_sem} A = λ P => some_sem A P ∧ outerNeg every_sem A P := by
  funext P
  refine propext ⟨λ ⟨hne, h⟩ => ⟨?_, hne⟩, λ ⟨⟨z, hz, hPz⟩, hne⟩ => ⟨hne, λ Q' hQ' hno => ?_⟩⟩
  · by_contra hsome
    exact h no_sem (Set.mem_singleton _) (λ z hz hPz => hsome ⟨z, hz, hPz⟩) (· = x)
      (λ hall => hxy (hall y hy).symm) x hx rfl
  · exact ((Set.mem_singleton_iff.mp hQ' ▸ hno) z hz hPz).elim

/-- An enriched meaning satisfiable at a restrictor but excluded at the empty scope is not
downward entailing in its scope. -/
theorem not_scopeDownwardMono_exh {Q : GQ α} {C : Set (GQ α)} {A P : α → Prop}
    (hP : exh Q C A P) (h : ¬ exh Q C A (λ _ => False)) : ¬ ScopeDownwardMono (exh Q C) :=
  λ hde => h (hde A _ P (λ _ hf => hf.elim) hP)

/-! ### The licensing principles -/

/-- Exhaustified *no* is downward entailing, so *no* licenses strong items. -/
theorem no_strong : ScopeDownwardMono (exh (no_sem : GQ α) {outerNeg every_sem}) := by
  rw [exh_no]; exact no_scope_down

/-- Exhaustified *not every* is not downward entailing: at the empty scope the stronger
scale-mate *no* is true and excluded. -/
theorem notEvery_not_strong [Nontrivial α] :
    ¬ ScopeDownwardMono (exh (outerNeg every_sem : GQ α) {no_sem}) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  refine not_scopeDownwardMono_exh (A := λ _ => True) (P := (· = x))
    ⟨λ h => hxy (h y trivial).symm, λ Q' hQ' hno =>
      ((Set.mem_singleton_iff.mp hQ' ▸ hno) x trivial rfl).elim⟩
    (exh_not_of_not_le (Set.mem_singleton _) (λ _ _ hf => hf)
      λ hle => hle (· = x) (λ h => hxy (h y trivial).symm) x trivial rfl)

/-- Exhaustified *some* is not downward entailing: *some* itself fails at the empty scope. -/
theorem some_not_strong [Nontrivial α] :
    ¬ ScopeDownwardMono (exh (some_sem : GQ α) {every_sem}) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  exact not_scopeDownwardMono_exh (A := λ _ => True) (P := (· = x))
    ⟨⟨x, trivial, rfl⟩, λ Q' hQ' hev =>
      (hxy ((Set.mem_singleton_iff.mp hQ' ▸ hev) y trivial).symm).elim⟩
    λ h => h.1.elim λ _ h => h.2

/-- Predicate counts with a foreign decidability instance, for the paper's numerals. -/
private theorem count_congr {P Q : α → Prop} [Fintype α] {i : DecidablePred P} [DecidablePred Q]
    (h : ∀ x, P x ↔ Q x) : @count α _ P i = count Q :=
  @count_congr_iff α _ P Q i _ h

private theorem at_most_n_sem_true_iff [Fintype α] {n : ℕ} {P Q : α → Prop} [DecidablePred Q]
    (h : ∀ x, P x ↔ Q x) : at_most_n_sem n (λ _ => True) P ↔ count Q ≤ n := by
  simp only [at_most_n_sem]
  rw [count_congr (Q := Q) λ x => (and_iff_right trivial).trans (h x)]

private theorem few_sem_true_iff [Fintype α] {P Q : α → Prop} [DecidablePred Q]
    (h : ∀ x, P x ↔ Q x) : few_sem (λ _ => True) P ↔ count Q < count (λ x => ¬ Q x) := by
  simp only [few_sem]
  rw [count_congr (Q := Q) λ x => (and_iff_right trivial).trans (h x),
    count_congr (Q := λ x => ¬ Q x) λ x => (and_iff_right trivial).trans (not_congr (h x))]

/-- *At most five* sits above *at most four* on its scale; excluding the scale-mate leaves
*exactly five*, which is not downward entailing. -/
theorem atMostFive_not_strong :
    ¬ ScopeDownwardMono (exh (at_most_n_sem 5 : GQ (Fin 6)) {at_most_n_sem 4}) := by
  have h4 : ¬ at_most_n_sem 4 (λ _ : Fin 6 => True) (· ≠ 0) := by
    rw [at_most_n_sem_true_iff λ _ => Iff.rfl]; decide
  refine not_scopeDownwardMono_exh (A := λ _ => True) (P := (· ≠ 0))
    ⟨by rw [at_most_n_sem_true_iff λ _ => Iff.rfl]; decide,
      λ Q' hQ' h => (h4 (Set.mem_singleton_iff.mp hQ' ▸ h)).elim⟩
    (exh_not_of_not_le (Set.mem_singleton _) (by rw [at_most_n_sem_true_iff λ _ => Iff.rfl]; decide)
      λ hle => h4 (hle (· ≠ 0) (by rw [at_most_n_sem_true_iff λ _ => Iff.rfl]; decide)))

/-- The paper's licensers. -/
inductive Licenser
  | no | atMostFive | some | only | conditional | sorryThat
  deriving DecidableEq, Repr

/-- Weak items are *any* and *ever*, strong ones *in weeks*, *either* and *until*. -/
inductive Strength
  | weak | strong
  deriving DecidableEq, Repr

/-- The two licensing principles applied to a licenser's analysis: a weak item needs the plain
meaning Strawson downward entailing, a strong item needs the enriched meaning downward entailing,
which for a presupposition trigger without scale-mates is its full meaning. -/
def Licensed : Licenser → Strength → Prop
  | .no, .weak => ∀ {α : Type}, ScopeDownwardMono (no_sem : GQ α)
  | .no, .strong => ∀ {α : Type}, ScopeDownwardMono (exh (no_sem : GQ α) {outerNeg every_sem})
  | .atMostFive, .weak => ∀ {α : Type} [Fintype α], ScopeDownwardMono (at_most_n_sem (α := α) 5)
  | .atMostFive, .strong =>
      ∀ {α : Type} [Fintype α], ScopeDownwardMono (exh (at_most_n_sem (α := α) 5) {at_most_n_sem 4})
  | .some, .weak => ∀ {α : Type}, ScopeDownwardMono (some_sem : GQ α)
  | .some, .strong => ∀ {α : Type}, ScopeDownwardMono (exh (some_sem : GQ α) {every_sem})
  | .only, .weak =>
      ∀ {W : Type} (x : W → Prop), IsStrawsonDE (onlyFull x) (λ scope _ => ∃ w', x w' ∧ scope w')
  | .only, .strong => ∀ {W : Type} (x : W → Prop), Antitone (onlyFull x)
  | .conditional, .weak => ∀ {W : Type} (domain : W → Set W) (q : Set W),
      IsStrawsonDE (λ p => wouldFull domain p q) (λ p w => ∃ w' ∈ domain w, p w')
  | .conditional, .strong =>
      ∀ {W : Type} (domain : W → Set W) (q : Set W), Antitone (λ p => wouldFull domain p q)
  | .sorryThat, .weak => ∀ {W : Type} (dox bestOf : W → Set W),
      IsStrawsonDE (sorryFull dox bestOf) (λ p w => ∀ w' ∈ dox w, p w')
  | .sorryThat, .strong => ∀ {W : Type} (dox bestOf : W → Set W), Antitone (sorryFull dox bestOf)

/-- The Strawson anti-additive triggers license weak items but not strong ones: their full
meanings are not downward entailing, the puzzle the two principles resolve. -/
theorem strawsonAA_not_sufficient :
    (Licensed .only .weak ∧ Licensed .conditional .weak ∧ Licensed .sorryThat .weak) ∧
      ¬ Licensed .only .strong ∧ ¬ Licensed .conditional .strong ∧ ¬ Licensed .sorryThat .strong :=
  ⟨⟨λ x => onlyFull_isStrawsonDE x, λ d q => wouldFull_isStrawsonDE d q,
      λ d b => sorryFull_isStrawsonDE d b⟩,
    λ h => onlyFull_not_de (h _), λ h => wouldFull_not_de (h _ _), λ h => sorryFull_not_de (h _ _)⟩

/-! ### Intolerance -/

/-- A function of properties is trivial when it is constantly true or constantly false. -/
def IsTrivial (f : Set α → Prop) : Prop := (∀ x, f x) ∨ ∀ x, ¬ f x

/-- A nontrivial function of properties is Intolerant when it never accepts both a property and
its complement: the items above the midpoint of their scale ([horn-1989]). -/
def IsIntolerant (f : Set α → Prop) : Prop := ¬ IsTrivial f → ∀ x, ¬ f x ∨ ¬ f xᶜ

/-- Anti-additivity implies Intolerance: accepting `x` and `xᶜ` means accepting everything. -/
theorem isIntolerant_of_isAntiAdditive {f : Set α → Prop} (h : IsAntiAdditive f) :
    IsIntolerant f := λ hnt x => by
  by_contra hx
  push Not at hx
  have huniv : f Set.univ := by
    have := (isAntiAdditive_iff_gq.mp h) x xᶜ
    rw [Set.union_compl_self] at this
    exact this.mpr hx
  exact hnt (Or.inl λ y => h.antitone (Set.subset_univ y) huniv)

open Classical in
/-- Proportional *few* is Intolerant: fewer than half in and fewer than half out is impossible. -/
theorem few_isIntolerant [Fintype α] (A : α → Prop) : IsIntolerant (few_sem A) := λ _ x => by
  by_contra hx
  push Not at hx
  obtain ⟨h₁, h₂⟩ := hx
  simp only [few_sem] at h₁ h₂
  rw [count_congr (P := λ z => A z ∧ xᶜ z) (Q := λ z => A z ∧ ¬ x z) λ _ => Iff.rfl,
    count_congr (P := λ z => A z ∧ ¬ xᶜ z) (Q := λ z => A z ∧ x z)
      λ _ => and_congr_right' ⟨λ hn => not_not.mp hn, λ hx hn => hn hx⟩] at h₂
  omega

/-- Cardinal *fewer than four* is not Intolerant: with six elements, three in and three out. -/
theorem atMostThree_not_isIntolerant :
    ¬ IsIntolerant (at_most_n_sem 3 (λ _ : Fin 6 => True)) := λ h =>
  (h (λ ht => ht.elim (λ h => absurd (h (λ _ => True))
      ((at_most_n_sem_true_iff λ _ => Iff.rfl).not.mpr (by decide)))
    λ h => h (λ _ => False) ((at_most_n_sem_true_iff λ _ => Iff.rfl).mpr (by decide))) (· < 3)).elim
    (· ((at_most_n_sem_true_iff λ _ => Iff.rfl).mpr (by decide)))
    (· ((at_most_n_sem_true_iff (Q := (3 ≤ ·)) λ _ => not_lt).mpr (by decide)))

/-- Proportional *few* is downward entailing and Intolerant but not anti-additive, so
Intolerance is a proper intermediate between anti-additivity and downward entailment. -/
theorem few_not_rightAntiAdditive : ¬ RightAntiAdditive (few_sem : GQ (Fin 4)) := λ h =>
  absurd ((h (λ _ => True) (· = 0) (· = 1)).mpr
      ⟨(few_sem_true_iff λ _ => Iff.rfl).mpr (by decide),
        (few_sem_true_iff λ _ => Iff.rfl).mpr (by decide)⟩)
    ((few_sem_true_iff λ _ => Iff.rfl).not.mpr (by decide))

/-! ### The paper's sentences -/

/-- A sentence of the paper: its licenser, the strength of its polarity item, and the judgment. -/
structure Row where
  licenser : Licenser
  strength : Strength
  grammatical : Bool
  deriving DecidableEq, Repr

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let licenser ← ex.parse? "licenser" [("no", Licenser.no), ("atMostFive", .atMostFive),
    ("some", .some), ("only", .only), ("conditional", .conditional), ("sorry", .sorryThat)]
  let strength ← ex.parse? "strength" [("weak", Strength.weak), ("strong", .strong)]
  let grammatical ← ex.parse? "grammatical" [("yes", true), ("no", false)]
  pure ⟨licenser, strength, grammatical⟩

def rows : List Row := Examples.all.filterMap Row.ofExample

theorem rows_eq : rows =
    [⟨.no, .weak, true⟩, ⟨.no, .strong, true⟩, ⟨.atMostFive, .weak, true⟩,
      ⟨.atMostFive, .strong, false⟩, ⟨.some, .weak, false⟩, ⟨.some, .strong, false⟩,
      ⟨.only, .weak, true⟩, ⟨.only, .strong, false⟩, ⟨.only, .strong, false⟩,
      ⟨.only, .strong, false⟩, ⟨.conditional, .weak, true⟩, ⟨.conditional, .strong, false⟩,
      ⟨.conditional, .strong, false⟩, ⟨.conditional, .strong, false⟩, ⟨.sorryThat, .weak, true⟩,
      ⟨.sorryThat, .strong, false⟩, ⟨.sorryThat, .strong, false⟩,
      ⟨.sorryThat, .strong, false⟩] := by
  decide

/-- Every judgment in the paper follows from the two licensing principles. -/
theorem rows_predicted : ∀ r ∈ rows, (r.grammatical = true ↔ Licensed r.licenser r.strength) := by
  obtain ⟨⟨ow, cw, sw⟩, os, cs, ss⟩ := strawsonAA_not_sufficient
  simp only [rows_eq, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true, true_iff, false_iff, Bool.false_eq_true]
  refine ⟨λ {_} => no_scope_down, λ {_} => no_strong, λ {_} => at_most_n_scope_down 5,
    λ h => atMostFive_not_strong h, λ h => ?_, λ h => some_not_strong (α := Bool) h,
    ow, os, os, os, cw, cs, cs, cs, sw, ss, ss, ss⟩
  exact (h (α := Bool) (λ _ => True) (λ _ => False) (λ _ => True) (λ _ hf => hf.elim)
    ⟨true, trivial, trivial⟩).elim λ _ h => h.2

end Gajewski2011
