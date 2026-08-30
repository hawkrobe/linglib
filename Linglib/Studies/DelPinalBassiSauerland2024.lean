import Linglib.Semantics.Exhaustification.Presuppositional
import Linglib.Semantics.Presupposition.BeliefEmbedding
import Linglib.Studies.BarLevFox2020

/-!
# Del Pinal, Bassi & Sauerland (2024): free choice and presuppositional exhaustification

[delpinal-bassi-sauerland-2024] derive free choice with `pex^{IE+II}`
(`Exhaustification.Presuppositional.pexIEII`), which asserts its prejacent and
*presupposes* the negation of the innocently excludable alternatives together with
homogeneity over the innocently includable ones. On `◇(p ∨ q)` this is (14): the
presupposed `◇p ↔ ◇q` with the asserted disjunction entails `◇p ∧ ◇q` (`pex_fc`), and the
same structure gives double prohibition under negation (16) (`pex_double_prohibition`) and,
with the necessity alternatives relabelled, negative free choice (19a)–(20)
(`pex_negative_fc`, `pex_double_requirement`). The split is what flat `exh^{IE+II}`
lacks, and the paper's embedded puzzles turn on it. Under a negative factive (§3), the
factive presupposes the whole `pex` output, so free choice is presupposed
(`fc_presupposed_under_neg_factive`), while the assertion denies belief in the bare
prejacent, which denies belief in either disjunct (`pex_unaware_target`); a flat `exh`
complement yields only denial of belief in the exhaustified conjunction, which a believer
in free choice can satisfy (`exh_unaware_too_weak`). In a disjunction (§4) the homogeneity
presupposition of the second disjunct is filtered in its local context
([schlenker-2009]) and free choice follows there (`filtering_fc`), whereas flat `exh`
leaves nothing to project (`exh_filtering_trivial`). Under quantifiers (§5.1) universal
projection of the presupposition gives universal, universal-negative, and existential
free choice, (62), (63), (75) (`universal_fc`, `universal_negative_fc`, `existential_fc`),
and under *exactly one* (§5.2) the salient readings of (76)–(77) of
[gotzner-romoli-santorio-2020] (`exactly_one_fc`, `exactly_one_double_prohibition`).
The alternative set and the free-choice strengthening are [bar-lev-fox-2020]'s.
-/

namespace DelPinalBassiSauerland2024

open Presupposition
open Exhaustification Exhaustification.Presuppositional BarLevFox2020 ModalLogic
open Presupposition.Context

/-! ### `pex^{IE+II}` on `◇(p ∨ q)` (§2) -/

section FreeChoice

variable {W : Type*} (R : W → W → Prop) (a b : Set W)

/-- (14): `pex^{IE+II}[◇(p ∨ q)]`. -/
def pexFC : PartialProp W := pexIEII_full (fcAlts R a b) (poss R (a ∪ b))

variable {R a b} (h₁ : ∃ w ∈ poss R a, w ∉ poss R b) (h₂ : ∃ w ∈ poss R b, w ∉ poss R a)
  (h : ∃ w ∈ poss R a ∩ poss R b, w ∉ poss R (a ∩ b)) {w : W}
include h₁ h₂ h

theorem poss_left_mem_II : IsInnocentlyIncludable (fcAlts R a b) (poss R (a ∪ b)) (poss R a) := by
  rw [IsInnocentlyIncludable, II_fcAlts h₁ h₂ h]; simp

theorem poss_right_mem_II : IsInnocentlyIncludable (fcAlts R a b) (poss R (a ∪ b)) (poss R b) := by
  rw [IsInnocentlyIncludable, II_fcAlts h₁ h₂ h]; simp

/-- (14): the presupposed homogeneity `◇p ↔ ◇q` with the asserted `◇(p ∨ q)` gives free
choice. -/
theorem pex_fc (hw : (pexFC R a b).holds w) : w ∈ poss R a ∧ w ∈ poss R b := by
  have hiff : w ∈ poss R a ↔ w ∈ poss R b :=
    hw.1.2 (poss R a) ⟨poss_left_mem_II h₁ h₂ h, by simp [fcAlts]⟩ (poss R b)
      ⟨poss_right_mem_II h₁ h₂ h, by simp [fcAlts]⟩
  rcases poss_union.le hw.2 with hA | hB
  exacts [⟨hA, hiff.1 hA⟩, ⟨hiff.2 hB, hB⟩]

omit h₁ h₂ h in
/-- (16): negation denies the prejacent and leaves the presupposition, so `¬pex[◇(p ∨ q)]`
is double prohibition. -/
theorem pex_double_prohibition (hw : (pexFC R a b).neg.holds w) :
    w ∉ poss R a ∧ w ∉ poss R b :=
  ⟨fun hA => hw.2 (poss_union.ge (.inl hA)), fun hB => hw.2 (poss_union.ge (.inr hB))⟩

omit h₁ h₂ h in
/-- (19a): `¬□(T ∧ B)` is `◇(¬T ∨ ¬B)`, whose alternatives `¬□T`, `¬□B`, `¬□(T ∨ B)` have the
structure of those of `◇(p ∨ q)`, so `pex^{IE+II}` gives negative free choice. -/
theorem pex_negative_fc {T B : Set W} (h₁ : ∃ w ∈ poss R Tᶜ, w ∉ poss R Bᶜ)
    (h₂ : ∃ w ∈ poss R Bᶜ, w ∉ poss R Tᶜ)
    (h : ∃ w ∈ poss R Tᶜ ∩ poss R Bᶜ, w ∉ poss R (Tᶜ ∩ Bᶜ)) (hw : (pexFC R Tᶜ Bᶜ).holds w) :
    w ∉ nec R T ∧ w ∉ nec R B := by
  simpa only [poss_compl, Set.mem_compl_iff] using pex_fc h₁ h₂ h hw

omit h₁ h₂ h in
/-- (20): `¬pex^{IE+II}[¬□(T ∧ B)]` gives double requirement. -/
theorem pex_double_requirement {T B : Set W} (hw : (pexFC R Tᶜ Bᶜ).neg.holds w) :
    w ∈ nec R T ∧ w ∈ nec R B := by
  simpa only [poss_compl, Set.mem_compl_iff, not_not] using pex_double_prohibition hw

/-! ### Free choice under negative factives (§3) -/

/-- Under a negative factive the whole `pex` output is presupposed, so free choice is
presupposed, (21a). -/
theorem fc_presupposed_under_neg_factive (believes : (W → Prop) → W → Prop)
    (hw : (PartialProp.negFactive (pexFC R a b) believes).presup w) :
    w ∈ poss R a ∧ w ∈ poss R b :=
  pex_fc h₁ h₂ h hw

omit h₁ h₂ h in
/-- The factive's assertion denies belief in the prejacent `◇(p ∨ q)`, hence belief in either
disjunct, (21b). -/
theorem pex_unaware_target (R' : W → W → Prop)
    (hw : (PartialProp.negFactive (pexFC R a b) (box R')).assertion w) :
    ¬ box R' (poss R a) w ∧ ¬ box R' (poss R b) w :=
  ⟨fun hA => hw (box_mono R' (λ _ hv => poss_union.ge (.inl hv)) w hA),
   fun hB => hw (box_mono R' (λ _ hv => poss_union.ge (.inr hv)) w hB)⟩

/-- With a flat `exh` complement the factive's assertion only denies belief in the
exhaustified conjunction, which an attitude holder who believes free choice but not
exclusivity satisfies (§3.1): given a world permitting `p ∧ q`, believing only it. -/
theorem exh_unaware_too_weak (hboth : ∃ w, w ∈ poss R (a ∩ b)) :
    ∃ R' : W → W → Prop, (box R' (poss R a) w ∧ box R' (poss R b) w) ∧
      ¬ box R' (exhIEII (fcAlts R a b) (poss R (a ∪ b))) w := by
  obtain ⟨w₀, hw₀⟩ := hboth
  refine ⟨fun _ v => v = w₀, ⟨fun _ hv => hv ▸ (poss_inter_subset hw₀).1,
    fun _ hv => hv ▸ (poss_inter_subset hw₀).2⟩, fun hbox => ?_⟩
  have := hbox w₀ rfl
  rw [freeChoice h₁ h₂ h] at this
  exact this.2 hw₀

/-! ### Filtering free choice (§4) -/

/-- In `A or pex[◇(p ∨ q)]` the homogeneity presupposition is satisfied in the second
disjunct's local context `c ∧ ¬A`, and free choice follows there. -/
theorem filtering_fc (c : Set W) (A : PartialProp W) (hc : w ∈ c)
    (hA : ¬ A.assertion w) (hf : presupSatisfied (localCtxSecondDisjunct c A) (pexFC R a b))
    (hassert : (pexFC R a b).assertion w) : w ∈ poss R a ∧ w ∈ poss R b :=
  pex_fc h₁ h₂ h ⟨hf ⟨hc, hA⟩, hassert⟩

omit h₁ h₂ h in
/-- A flat `exh` second disjunct has nothing to filter: its free-choice content is
assertive and stays inside the disjunct (§4.1). -/
theorem exh_filtering_trivial (c : Set W) (A : PartialProp W) :
    presupSatisfied (localCtxSecondDisjunct c A)
      (PartialProp.ofProp (exhIEII (fcAlts R a b) (poss R (a ∪ b)))) :=
  fun _ _ => trivial

end FreeChoice

/-! ### Free choice under quantifiers (§5) -/

variable {Student : Type*} (S : Student → Prop)

/-- (62): universal projection of homogeneity and the universal assertion give universal free
choice. -/
theorem universal_fc (permC permIC : Student → Prop)
    (hassert : ∀ x, S x → permC x ∨ permIC x) (hhomog : ∀ x, S x → (permC x ↔ permIC x)) :
    (∀ x, S x → permC x) ∧ ∀ x, S x → permIC x :=
  ⟨fun x hx => (hassert x hx).elim id (hhomog x hx).2,
   fun x hx => (hassert x hx).elim (hhomog x hx).1 id⟩

/-- (63): with a negated existential assertion, universal negative free choice. -/
theorem universal_negative_fc (reqA reqB : Student → Prop)
    (hassert : ¬ ∃ x, S x ∧ reqA x ∧ reqB x) (hhomog : ∀ x, S x → (reqA x ↔ reqB x)) :
    (¬ ∃ x, S x ∧ reqA x) ∧ ¬ ∃ x, S x ∧ reqB x :=
  ⟨fun ⟨x, hx, hA⟩ => hassert ⟨x, hx, hA, (hhomog x hx).1 hA⟩,
   fun ⟨x, hx, hB⟩ => hassert ⟨x, hx, (hhomog x hx).2 hB, hB⟩⟩

/-- (75): with an existential assertion, existential free choice. -/
theorem existential_fc (permC permIC : Student → Prop)
    (hassert : ∃ x, S x ∧ (permC x ∨ permIC x)) (hhomog : ∀ x, S x → (permC x ↔ permIC x)) :
    ∃ x, S x ∧ permC x ∧ permIC x :=
  let ⟨x, hx, h⟩ := hassert
  ⟨x, hx, h.elim (fun hC => ⟨hC, (hhomog x hx).1 hC⟩) fun hIC => ⟨(hhomog x hx).2 hIC, hIC⟩⟩

/-- (76a): under *exactly one*, the witness has free choice and every other student double
prohibition. -/
theorem exactly_one_fc (permL permC : Student → Prop) (x₀ : Student) (hx₀ : S x₀)
    (hpos : permL x₀ ∨ permC x₀) (hneg : ∀ x, S x → x ≠ x₀ → ¬ (permL x ∨ permC x))
    (hhomog : ∀ x, S x → (permL x ↔ permC x)) :
    (permL x₀ ∧ permC x₀) ∧ ∀ x, S x → x ≠ x₀ → ¬ permL x ∧ ¬ permC x :=
  ⟨hpos.elim (fun h => ⟨h, (hhomog x₀ hx₀).1 h⟩) fun h => ⟨(hhomog x₀ hx₀).2 h, h⟩,
   fun x hx hne => ⟨fun h => hneg x hx hne (.inl h), fun h => hneg x hx hne (.inr h)⟩⟩

/-- (77a): under *exactly one … can't*, the witness has double prohibition and every other
student free choice. -/
theorem exactly_one_double_prohibition (permL permC : Student → Prop) (x₀ : Student)
    (hneg : ¬ (permL x₀ ∨ permC x₀)) (hpos : ∀ x, S x → x ≠ x₀ → permL x ∨ permC x)
    (hhomog : ∀ x, S x → (permL x ↔ permC x)) :
    (¬ permL x₀ ∧ ¬ permC x₀) ∧ ∀ x, S x → x ≠ x₀ → permL x ∧ permC x :=
  ⟨⟨fun h => hneg (.inl h), fun h => hneg (.inr h)⟩,
   fun x hx hne => (hpos x hx hne).elim (fun h => ⟨h, (hhomog x hx).1 h⟩)
     fun h => ⟨(hhomog x hx).2 h, h⟩⟩

end DelPinalBassiSauerland2024
