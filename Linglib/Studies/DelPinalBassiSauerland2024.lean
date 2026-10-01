module

public import Linglib.Semantics.Exhaustification.Presuppositional
public import Linglib.Semantics.Presupposition.Context
public import Linglib.Studies.BarLevFox2020

/-!
# Del Pinal, Bassi and Sauerland (2024): Free choice and presuppositional exhaustification

This file formalizes the derivation of free choice in [delpinal-bassi-sauerland-2024] with
the presuppositional exhaustivity operator `pex^{IE+II}`, which asserts its prejacent and
presupposes the negation of the innocently excludable alternatives together with homogeneity
over the innocently includable ones, the alternatives and includability being those of
[bar-lev-fox-2020]. On `◇(p ∨ q)` the presupposed `◇p ↔ ◇q` with the asserted disjunction
entails `◇p ∧ ◇q`, (14); negation denies the assertion and leaves the presupposition, so
`¬pex[◇(p ∨ q)]` is double prohibition, (16), and the same structure gives negative free
choice for `¬□(p ∧ q)`, (19a), and for `¬pex[□(p ∧ q)]`, (20), where `□p` and `□q` are
includable. The split between the two components is what the flat `exh^{IE+II}` lacks, and
the embedded puzzles turn on it. Under a negative factive, §3, the factive presupposes the
whole `pex` output, so free choice is presupposed, (21a), while the assertion denies belief
in the bare prejacent and so in either disjunct, (21b); a flat `exh` complement only denies
belief in the exhaustified conjunction, which someone who believes one disjunct satisfies,
(24a). In a disjunction, §4, the homogeneity presupposition projects out of the negated
first disjunct and the second disjunct's free-choice presupposition is satisfied in its
local context, since the negation of the first disjunct is free choice, (53c), which neither
parse of a flat `exh` achieves, (46c) and (47), and likewise for negative free choice, (57c).
Under quantifiers, §5, universal projection of the homogeneity presupposition gives
universal free choice, (67), universal negative free choice, (68), universal double
prohibition, (71), and existential free choice under either projection, (74) and (75), and
under *exactly one* the readings of [gotzner-romoli-santorio-2020], (83) and (84).

## Implementation notes

The disjunction rule (45), that `p ∨ q_r` presupposes `¬p → r`, is rendered through the
substrate's local context of a second disjunct, the global context restricted to the
negation of the first disjunct's assertion, with the first disjunct's own presupposition
assumed in the global context. The quantifier cases are stated as the paper states them,
with the universally projected homogeneity presupposition as a premise; *exactly one* is
`∃!`.

## References

* [delpinal-bassi-sauerland-2024]
* [bar-lev-fox-2020]
* [gotzner-romoli-santorio-2020]
* [heim-1982]
-/

@[expose] public section

namespace DelPinalBassiSauerland2024

open Presupposition
open Exhaustification Exhaustification.Presuppositional BarLevFox2020 ModalLogic
open SetRel
open scoped ModalLogic

/-! ### `pex^{IE+II}` on `◇(p ∨ q)`, §2 -/

section FreeChoice

variable {W : Type*} (R : SetRel W W) (a b : Set W)

/-- (14): `pex^{IE+II}[◇(p ∨ q)]`. -/
def pexFC : PartialProp W := pexIEII_full (fcAlts R a b) (R.preimage (a ∪ b))

variable {R a b} (h₁ : ∃ w ∈ R.preimage a, w ∉ R.preimage b)
  (h₂ : ∃ w ∈ R.preimage b, w ∉ R.preimage a)
  (h : ∃ w ∈ R.preimage a ∩ R.preimage b, w ∉ R.preimage (a ∩ b)) {w : W}
include h₁ h₂ h

theorem poss_left_mem_II :
    IsInnocentlyIncludable (fcAlts R a b) (R.preimage (a ∪ b)) (R.preimage a) := by
  rw [IsInnocentlyIncludable, II_fcAlts h₁ h₂ h]; simp

theorem poss_right_mem_II :
    IsInnocentlyIncludable (fcAlts R a b) (R.preimage (a ∪ b)) (R.preimage b) := by
  rw [IsInnocentlyIncludable, II_fcAlts h₁ h₂ h]; simp

/-- (14): the presupposed homogeneity `◇p ↔ ◇q` with the asserted `◇(p ∨ q)` gives free
choice. -/
theorem pex_fc (hw : (pexFC R a b).holds w) : w ∈ R.preimage a ∧ w ∈ R.preimage b := by
  have hiff : w ∈ R.preimage a ↔ w ∈ R.preimage b :=
    hw.1.2 (R.preimage a) ⟨poss_left_mem_II h₁ h₂ h, by simp [fcAlts]⟩ (R.preimage b)
      ⟨poss_right_mem_II h₁ h₂ h, by simp [fcAlts]⟩
  rcases (preimage_union ..).le hw.2 with hA | hB
  exacts [⟨hA, hiff.1 hA⟩, ⟨hiff.2 hB, hB⟩]

omit h₁ h₂ h in
/-- (16): negation denies the prejacent and leaves the presupposition, so `¬pex[◇(p ∨ q)]`
is double prohibition. -/
theorem pex_double_prohibition (hw : (pexFC R a b).neg.holds w) :
    w ∉ R.preimage a ∧ w ∉ R.preimage b :=
  ⟨fun hA ↦ hw.2 ((preimage_union ..).ge (.inl hA)),
    fun hB ↦ hw.2 ((preimage_union ..).ge (.inr hB))⟩

omit h₁ h₂ h in
/-- (19a): `¬□(T ∧ B)` is `◇(¬T ∨ ¬B)`, whose alternatives `¬□T`, `¬□B`, `¬□(T ∨ B)` have the
structure of those of `◇(p ∨ q)`, so `pex^{IE+II}` gives negative free choice. -/
theorem pex_negative_fc {T B : Set W} (h₁ : ∃ w ∈ R.preimage Tᶜ, w ∉ R.preimage Bᶜ)
    (h₂ : ∃ w ∈ R.preimage Bᶜ, w ∉ R.preimage Tᶜ)
    (h : ∃ w ∈ R.preimage Tᶜ ∩ R.preimage Bᶜ, w ∉ R.preimage (Tᶜ ∩ Bᶜ))
    (hw : (pexFC R Tᶜ Bᶜ).holds w) :
    w ∉ R.core T ∧ w ∉ R.core B := by
  simpa only [preimage_compl, Set.mem_compl_iff] using pex_fc h₁ h₂ h hw

end FreeChoice

section NegativeFreeChoice

variable {W : Type*} (R : SetRel W W) (T B : Set W)

/-- The alternatives of `□(T ∧ B)`: the conjunction replaced by its conjuncts and their
disjunction. -/
def necAlts : Set (Set W) := {R.core (T ∩ B), R.core T, R.core B, R.core (T ∪ B)}

/-- (20): `pex^{IE+II}[□(T ∧ B)]`. -/
def pexNec : PartialProp W := pexIEII_full (necAlts R T B) (R.core (T ∩ B))

variable {R T B}

/-- Every alternative of `□(T ∧ B)` is entailed by it, so none is excludable and, given a
world where it holds, `□T` and `□B` are includable. -/
theorem nec_mem_II (hsat : ∃ w, w ∈ R.core (T ∩ B)) :
    R.core T ∈ II (necAlts R T B) (R.core (T ∩ B)) ∧
      R.core B ∈ II (necAlts R T B) (R.core (T ∩ B)) := by
  obtain ⟨w₀, hw₀⟩ := hsat
  have hsub : ∀ q ∈ necAlts R T B, R.core (T ∩ B) ⊆ q := by
    intro q hq
    simp only [necAlts, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact le_rfl
    · exact box_mono R Set.inter_subset_left
    · exact box_mono R Set.inter_subset_right
    · exact box_mono R (Set.inter_subset_left.trans Set.subset_union_left)
  have hfin : (necAlts R T B).Finite :=
    ((Set.finite_singleton _).insert _).insert _ |>.insert _
  have hcell : cell (necAlts R T B) (R.core (T ∩ B)) w₀ :=
    ⟨hw₀, λ q hq => absurd hq (not_isInnocentlyExcludable_of_phi_subset hfin ⟨w₀, hw₀⟩
      (hsub q hq.1)), λ r hr => hsub r hr.1 hw₀⟩
  exact ⟨mem_II_of_cell_witness _ _ (by simp [necAlts]) w₀ hcell
      (hsub (R.core T) (by simp [necAlts]) hw₀),
    mem_II_of_cell_witness _ _ (by simp [necAlts]) w₀ hcell
      (hsub (R.core B) (by simp [necAlts]) hw₀)⟩

/-- (20): `¬pex^{IE+II}[□(T ∧ B)]` gives negative free choice, the homogeneity `□T ↔ □B`
projecting out of the negation of the strong prejacent. -/
theorem pex_negative_fc_under_neg (hsat : ∃ w, w ∈ R.core (T ∩ B)) {w : W}
    (hw : (pexNec R T B).neg.holds w) : w ∉ R.core T ∧ w ∉ R.core B := by
  obtain ⟨hT, hB⟩ := nec_mem_II hsat
  have hiff : w ∈ R.core T ↔ w ∈ R.core B :=
    hw.1.2 (R.core T) ⟨hT, by simp [necAlts]⟩ (R.core B) ⟨hB, by simp [necAlts]⟩
  have hne : w ∉ R.core (T ∩ B) := hw.2
  rw [SetRel.core_inter] at hne
  exact ⟨λ h => hne ⟨h, hiff.1 h⟩, λ h => hne ⟨hiff.2 h, h⟩⟩

end NegativeFreeChoice

/-! ### Free choice under negative factives, §3 -/

section NegativeFactive

variable {W : Type*} {R : SetRel W W} {a b : Set W}
  (h₁ : ∃ w ∈ R.preimage a, w ∉ R.preimage b) (h₂ : ∃ w ∈ R.preimage b, w ∉ R.preimage a)
  (h : ∃ w ∈ R.preimage a ∩ R.preimage b, w ∉ R.preimage (a ∩ b)) {w : W}
include h₁ h₂ h

/-- (21a): under a negative factive the whole `pex` output is presupposed, so free choice is
presupposed. -/
theorem fc_presupposed_under_neg_factive (believes : (W → Prop) → W → Prop)
    (hw : (PartialProp.negFactive (pexFC R a b) believes).presup w) :
    w ∈ R.preimage a ∧ w ∈ R.preimage b :=
  pex_fc h₁ h₂ h hw

omit h₁ h₂ h in
/-- (21b): the factive's assertion denies belief in the prejacent `◇(p ∨ q)`, hence belief in
either disjunct. -/
theorem pex_unaware_target (R' : SetRel W W)
    (hw : (PartialProp.negFactive (pexFC R a b) (Box R')).assertion w) :
    ¬ □[R'] (· ∈ R.preimage a) w ∧ ¬ □[R'] (· ∈ R.preimage b) w :=
  ⟨fun hA ↦ hw (box_mono R' (fun _ hv ↦ (preimage_union ..).ge (.inl hv)) w hA),
   fun hB ↦ hw (box_mono R' (fun _ hv ↦ (preimage_union ..).ge (.inr hv)) w hB)⟩

/-- (24a): with a flat `exh` complement the factive only denies belief in the exhaustified
conjunction, which an attitude holder who believes Olivia can take Logic but not Algebra
satisfies, so the target that he believes neither is missed. -/
theorem exh_unaware_too_weak :
    ∃ R' : SetRel W W, □[R'] (· ∈ R.preimage a) w ∧
      ¬ □[R'] (· ∈ exhIEII (fcAlts R a b) (R.preimage (a ∪ b))) w := by
  obtain ⟨w₁, hw₁a, hw₁b⟩ := id h₁
  refine ⟨.ofSuccessors fun _ ↦ {w₁}, fun v (hv : v = w₁) ↦ hv ▸ hw₁a, fun hbox ↦ ?_⟩
  have := hbox w₁ (Set.mem_singleton w₁)
  rw [freeChoice h₁ h₂ h] at this
  exact hw₁b this.1.2

end NegativeFactive

/-! ### Filtering free choice, §4 -/

section Filtering

variable {W : Type*} {R : SetRel W W} {a b A B : Set W} (hA : a ⊆ A) (hB : b ⊆ B)
include hA hB

/-- (53c): in `¬pex[◇(a ∨ b)] ∨ C`, with `C` presupposing `◇A ∧ ◇B` for `a ⊆ A` and `b ⊆ B`,
the presupposition is satisfied in `C`'s local context once the first disjunct's own
presupposition is in the global context: the negation of the first disjunct is free choice
for `a` and `b`. So the disjunction rule (45) filters it. -/
theorem filtering (h₁ : ∃ w ∈ R.preimage a, w ∉ R.preimage b)
    (h₂ : ∃ w ∈ R.preimage b, w ∉ R.preimage a)
    (h : ∃ w ∈ R.preimage a ∩ R.preimage b, w ∉ R.preimage (a ∩ b)) {c : Set W}
    (hc : c ⊆ (pexFC R a b).presup) (C : W → Prop) :
    PartialProp.Admits ⟨fun w ↦ w ∈ R.preimage A ∧ w ∈ R.preimage B, C⟩
      (Connective.disj.localContext c (pexFC R a b).neg.assertion) := by
  intro w ⟨hcw, hna⟩
  have hfc := pex_fc h₁ h₂ h ⟨hc hcw, not_not.1 hna⟩
  exact ⟨preimage_mono hA hfc.1, preimage_mono hB hfc.2⟩

omit hA hB in
/-- (46c): without exhaustification under the negation the antecedent of the conditional
presupposition is only `◇(a ∨ b)`, which does not entail `◇A ∧ ◇B`: a world permitting `a`
but not `B` refutes it. -/
theorem no_filtering_without_pex (hw : ∃ w ∈ R.preimage a, w ∉ R.preimage B) :
    ¬ ∀ w, w ∈ R.preimage (a ∪ b) → w ∈ R.preimage A ∧ w ∈ R.preimage B :=
  fun hall ↦ let ⟨w, hwa, hwB⟩ := hw; hwB (hall w (preimage_mono Set.subset_union_left hwa)).2

omit hA hB in
/-- (47): a flat `exh` under the negation filters but loses double prohibition, since the
negated exhaustified disjunction is compatible with permitting `a`. -/
theorem exh_loses_double_prohibition (h₁ : ∃ w ∈ R.preimage a, w ∉ R.preimage b)
    (h₂ : ∃ w ∈ R.preimage b, w ∉ R.preimage a)
    (h : ∃ w ∈ R.preimage a ∩ R.preimage b, w ∉ R.preimage (a ∩ b)) :
    ∃ w, w ∉ exhIEII (fcAlts R a b) (R.preimage (a ∪ b)) ∧ w ∈ R.preimage a := by
  obtain ⟨w₁, hw₁a, hw₁b⟩ := id h₁
  exact ⟨w₁, λ hex => by rw [freeChoice h₁ h₂ h] at hex; exact hw₁b hex.1.2, hw₁a⟩

/-- (57c): in `pex[□(A ∧ B)] ∨ C`, with `C` presupposing `¬□a ∧ ¬□b`, the negation of the
first disjunct is negative free choice for `A` and `B`, which entails it, so the disjunction
rule filters it. -/
theorem filtering_negative (hsat : ∃ w, w ∈ R.core (A ∩ B)) {c : Set W}
    (hc : c ⊆ (pexNec R A B).presup) (C : W → Prop) :
    PartialProp.Admits ⟨fun w ↦ w ∉ R.core a ∧ w ∉ R.core b, C⟩
      (Connective.disj.localContext c (pexNec R A B).assertion) := by
  intro w ⟨hcw, hna⟩
  have := pex_negative_fc_under_neg hsat (w := w) ⟨hc hcw, hna⟩
  exact ⟨λ ha => this.1 (box_mono R hA w ha), λ hb => this.2 (box_mono R hB w hb)⟩

end Filtering

/-! ### Free choice under quantifiers, §5 -/

variable {Student : Type*} (S : Student → Prop)

/-- (67): universal projection of homogeneity with the universal assertion gives universal
free choice. -/
theorem universal_fc (permC permIC : Student → Prop)
    (hassert : ∀ x, S x → permC x ∨ permIC x) (hhomog : ∀ x, S x → (permC x ↔ permIC x)) :
    (∀ x, S x → permC x) ∧ ∀ x, S x → permIC x :=
  ⟨λ x hx => (hassert x hx).elim id (hhomog x hx).2,
   λ x hx => (hassert x hx).elim (hhomog x hx).1 id⟩

/-- (68): with a negated existential assertion, universal negative free choice. -/
theorem universal_negative_fc (reqA reqB : Student → Prop)
    (hassert : ¬ ∃ x, S x ∧ reqA x ∧ reqB x) (hhomog : ∀ x, S x → (reqA x ↔ reqB x)) :
    (¬ ∃ x, S x ∧ reqA x) ∧ ¬ ∃ x, S x ∧ reqB x :=
  ⟨λ ⟨x, hx, hA⟩ => hassert ⟨x, hx, hA, (hhomog x hx).1 hA⟩,
   λ ⟨x, hx, hB⟩ => hassert ⟨x, hx, (hhomog x hx).2 hB, hB⟩⟩

/-- (71): with a negated existential disjunctive assertion, universal double prohibition, the
reading the elided second sentence of (69) needs. -/
theorem universal_double_prohibition (permC permIC : Student → Prop)
    (hassert : ¬ ∃ x, S x ∧ (permC x ∨ permIC x)) :
    (¬ ∃ x, S x ∧ permC x) ∧ ¬ ∃ x, S x ∧ permIC x :=
  ⟨λ ⟨x, hx, hC⟩ => hassert ⟨x, hx, .inl hC⟩, λ ⟨x, hx, hIC⟩ => hassert ⟨x, hx, .inr hIC⟩⟩

/-- (74): with an existential assertion and universal projection, existential free choice. -/
theorem existential_fc (permC permIC : Student → Prop)
    (hassert : ∃ x, S x ∧ (permC x ∨ permIC x)) (hhomog : ∀ x, S x → (permC x ↔ permIC x)) :
    ∃ x, S x ∧ permC x ∧ permIC x :=
  let ⟨x, hx, h⟩ := hassert
  ⟨x, hx, h.elim (λ hC => ⟨hC, (hhomog x hx).1 hC⟩) λ hIC => ⟨(hhomog x hx).2 hIC, hIC⟩⟩

/-- (75): with existential projection bound by the quantifier, existential free choice
again. -/
theorem existential_fc_bound (permC permIC : Student → Prop)
    (hassert : ∃ x, S x ∧ (permC x ↔ permIC x) ∧ (permC x ∨ permIC x)) :
    ∃ x, S x ∧ permC x ∧ permIC x :=
  let ⟨x, hx, hiff, h⟩ := hassert
  ⟨x, hx, h.elim (λ hC => ⟨hC, hiff.1 hC⟩) λ hIC => ⟨hiff.2 hIC, hIC⟩⟩

/-- (83): under *exactly one*, universal homogeneity turns the assertion that exactly one
student may take Logic or Calculus into exactly one having free choice, every other student
having double prohibition. -/
theorem exactly_one_fc (permL permC : Student → Prop)
    (hassert : ∃! x, S x ∧ (permL x ∨ permC x)) (hhomog : ∀ x, S x → (permL x ↔ permC x)) :
    (∃! x, S x ∧ permL x ∧ permC x) ∧
      ∀ x, S x → ¬ (permL x ∨ permC x) → ¬ permL x ∧ ¬ permC x := by
  obtain ⟨x₀, ⟨hx₀, hor⟩, huniq⟩ := hassert
  refine ⟨⟨x₀, ⟨hx₀, hor.elim (λ h => ⟨h, (hhomog x₀ hx₀).1 h⟩) λ h => ⟨(hhomog x₀ hx₀).2 h, h⟩⟩,
    λ y ⟨hy, hL, _⟩ => huniq y ⟨hy, .inl hL⟩⟩, λ _ _ hn => ⟨λ h => hn (.inl h), λ h => hn (.inr h)⟩⟩

/-- (84): under *exactly one … can't*, exactly one student has double prohibition and every
other has free choice. -/
theorem exactly_one_double_prohibition (permL permC : Student → Prop)
    (hassert : ∃! x, S x ∧ ¬ (permL x ∨ permC x)) (hhomog : ∀ x, S x → (permL x ↔ permC x)) :
    (∃! x, S x ∧ ¬ permL x ∧ ¬ permC x) ∧ ∀ x, S x → permL x ∨ permC x → permL x ∧ permC x := by
  obtain ⟨x₀, ⟨hx₀, hn⟩, huniq⟩ := hassert
  refine ⟨⟨x₀, ⟨hx₀, λ h => hn (.inl h), λ h => hn (.inr h)⟩,
    λ y ⟨hy, hL, hC⟩ => huniq y ⟨hy, λ h => h.elim hL hC⟩⟩,
    λ x hx h => h.elim (λ h => ⟨h, (hhomog x hx).1 h⟩) λ h => ⟨(hhomog x hx).2 h, h⟩⟩

end DelPinalBassiSauerland2024
