module

public import Linglib.Semantics.Exhaustification.Presuppositional
public import Linglib.Semantics.Presupposition.Quantified
public import Linglib.Semantics.Homogeneity.Plural
public import Linglib.Studies.BarLevFox2020

/-!
# Del Pinal, Bassi and Sauerland (2024): Free choice and presuppositional exhaustification

Del Pinal, Bassi and Sauerland's operator `pex^{IE+II}` asserts its prejacent and presupposes
that the relevant includable alternatives are homogeneous. On `◇(p ∨ q)` it presupposes
`◇p ↔ ◇q`, so free choice is the presupposition and the assertion together, while negation
denies only the assertion and leaves double prohibition. The flat `exh^{IE+II}` of Bar-Lev and
Fox yields the same overall content without the split, and the paper's puzzles about free choice
under negative factives, in disjunctions and under quantifiers all turn on the split.

## Main results

* `basic_scalar`: `pex` presupposes the negation of a non-entailed alternative, (11a).
* `free_choice`, `double_prohibition`, `negative_free_choice`,
  `negative_free_choice_under_negation`: the readings (14), (16), (19a) and (20), exactly.
* `eval_pexPossOr`, `homogeneity_gap`: `pex[◇(p ∨ q)]` is Križ's homogeneous plural predication
  over the disjuncts, the structure the paper compares with Goldstein's in §2.2, with the
  presupposition failures of fn. 2.
* `pex_and_exh_agree`: with every alternative relevant, `pex` and `exh` agree, (12e)–(13).
* `free_choice_presupposed`, `unaware_disbelieves_each_disjunct`: negative factives, §3.
* `free_choice_filtered`, `negative_free_choice_filtered`: Karttunen's filtering disjunction
  filters free choice, (53), (57c), unlike flat `exh` or local accommodation.
* `universal_free_choice`, `universal_double_prohibition`, `existential_free_choice_bound`,
  `exactly_one_free_choice`: free choice under quantifiers, with Fox's strong Kleene
  existential for (75) and the readings of Gotzner, Romoli and Santorio for (83), (84).

## Implementation notes

Each `pex` uses the paper's relevance set, which leaves out the conjunctive alternative of
`◇(p ∨ q)` and the disjunctive one of `□(p ∧ q)`; with every alternative relevant,
`¬pex[□(T ∧ B)]` would entail `¬□(T ∨ B)`. `¬□(p ∧ q)` is rendered as `◇(¬p ∨ ¬q)`. The witness
hypotheses supply the worlds that make the alternatives independent, which the paper assumes
implicitly. Negative factives use the transparent projection rule (30b), as `negFactive` does,
and *exactly one* is `∃!`.

## References

* [delpinal-bassi-sauerland-2024]
* [bar-lev-fox-2020]
* [gotzner-romoli-santorio-2020]
* [goldstein-2019]
* [kriz-2016]
* [fox-2013]
* [karttunen-1973]
-/

@[expose] public section

namespace DelPinalBassiSauerland2024

open Presupposition PartialProp
open Exhaustification Homogeneity BarLevFox2020 ModalLogic SetRel
open scoped ModalLogic

variable {W : Type*}

/-! ### Basic scalar sentences, §2.1 -/

/-- On a prejacent with one other alternative, which it does not entail, as *some* has *all*,
`pex^{IE+II}` presupposes that the alternative is false, (10)–(11a). -/
theorem basic_scalar {φ ψ : Set W} (h : ¬ φ ⊆ ψ) {w : W} :
    (pexIEII {φ, ψ} φ {φ, ψ}).presup w ↔ w ∉ ψ := by
  obtain ⟨w₀, hw₀, hw₀ψ⟩ := Set.not_subset.1 h
  have hM : IsMinimalCover {φ, ψ} φ {w₀} :=
    .singleton hw₀ (by rintro q (rfl | rfl) hq; exacts [le_rfl, absurd hq hw₀ψ])
  rw [pexIEII_presup_of_inter_eq_empty (by rw [hM.II_eq ⟨w₀, hw₀, by simp⟩]; grind)]
  grind [hM.isInnocentlyExcludable_iff]

/-! ### `pex^{IE+II}` on `◇(p ∨ q)`, §2.2 -/

section FreeChoice

variable (R : SetRel W W) (a b : Set W)

/-- `pexPossOr R a b` is `pex^{IE+II}[◇(a ∨ b)]` with the conjunctive alternative irrelevant,
as in (12) and (14). -/
def pexPossOr : PartialProp W :=
  pexIEII (fcAlts R a b) (R.preimage (a ∪ b)) {R.preimage (a ∪ b), R.preimage a, R.preimage b}

variable {R a b} {w : W}

/-- Negation denies the prejacent of `pex^{IE+II}[◇(a ∨ b)]` and leaves its presupposition, so
the negation holds exactly where double prohibition does, (16); the presupposition holds there
whatever the includable alternatives are. -/
theorem double_prohibition :
    (pexPossOr R a b).neg.holds w ↔ w ∉ R.preimage a ∧ w ∉ R.preimage b := by
  simp only [holds, neg, pexPossOr, pexIEII, preimage_union]
  grind [Homogeneous]

variable (hF : FreeChoiceWitnesses R a b)
include hF

/-- Apart from the prejacent, the innocently includable alternatives of `◇(a ∨ b)` are `◇a` and
`◇b`, (12d). -/
theorem II_fcAlts_sdiff :
    II (fcAlts R a b) (R.preimage (a ∪ b)) \ {R.preimage (a ∪ b)} =
      {R.preimage a, R.preimage b} := by
  rw [II_fcAlts hF, Set.insert_sdiff_of_mem _ (Set.mem_singleton _),
    Set.sdiff_singleton_eq_self]
  obtain ⟨w₁, hw₁a, hw₁b⟩ := hF.only_left
  obtain ⟨w₂, hw₂b, hw₂a⟩ := hF.only_right
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨fun he ↦ hw₂a (he ▸ preimage_mono Set.subset_union_right hw₂b),
    fun he ↦ hw₁b (he ▸ preimage_mono Set.subset_union_left hw₁a)⟩

private theorem II_fcAlts_sdiff_inter :
    II (fcAlts R a b) (R.preimage (a ∪ b)) \ {R.preimage (a ∪ b)} ∩
      {R.preimage (a ∪ b), R.preimage a, R.preimage b} = {R.preimage a, R.preimage b} := by
  rw [II_fcAlts_sdiff hF, Set.inter_eq_left]
  exact Set.subset_insert _ _

/-- `pex^{IE+II}[◇(a ∨ b)]` presupposes `◇a ↔ ◇b`, (14); its one excludable alternative,
`◇(a ∧ b)` (12c), is irrelevant. -/
theorem pexPossOr_presup :
    (pexPossOr R a b).presup w ↔ (w ∈ R.preimage a ↔ w ∈ R.preimage b) := by
  refine (and_iff_right fun ψ hψ hR ↦ ?_).trans
    (by rw [II_fcAlts_sdiff_inter hF, homogeneous_pair])
  obtain rfl := (isInnocentlyExcludable_fcAlts_iff hF).1 hψ
  obtain ⟨w₀, ⟨hw₀a, hw₀b⟩, hw₀⟩ := hF.not_both
  grind [preimage_mono Set.subset_union_left hw₀a]

/-- `pex^{IE+II}[◇(a ∨ b)]` holds exactly where free choice does, (14), since `◇(a ∨ b)` lies
between `◇a ∧ ◇b` and `◇a ∨ ◇b`. -/
theorem free_choice : (pexPossOr R a b).holds w ↔ w ∈ R.preimage a ∧ w ∈ R.preimage b := by
  have hl : ⋂₀ (II (fcAlts R a b) (R.preimage (a ∪ b)) \ {R.preimage (a ∪ b)} ∩
      {R.preimage (a ∪ b), R.preimage a, R.preimage b}) ⊆ R.preimage (a ∪ b) := by
    rw [II_fcAlts_sdiff_inter hF, Set.sInter_pair, preimage_union]
    exact inf_le_sup
  have hu : R.preimage (a ∪ b) ⊆ ⋃₀ (II (fcAlts R a b) (R.preimage (a ∪ b)) \ {R.preimage (a ∪ b)} ∩
      {R.preimage (a ∪ b), R.preimage a, R.preimage b}) := by
    rw [II_fcAlts_sdiff_inter hF, Set.sUnion_pair, preimage_union]
  rw [pexPossOr, pexIEII_holds_iff hl hu, ← pexPossOr, pexPossOr_presup hF,
    II_fcAlts_sdiff_inter hF]
  grind

open Classical in
/-- As a trivalent proposition, `pex^{IE+II}[◇(a ∨ b)]` is the plural predication that `a` and
`b` are permitted, true where both are, false where neither is, and undefined in between. -/
theorem eval_pexPossOr :
    (pexPossOr R a b).eval = barePlural (fun x w ↦ w ∈ R.preimage x) {a, b} := by
  funext w
  have hq : (pexPossOr R a b).assertion w ↔ w ∈ R.preimage a ∨ w ∈ R.preimage b := by
    change w ∈ R.preimage (a ∪ b) ↔ _
    rw [preimage_union, Set.mem_union]
  simp only [eval, barePlural, Trivalent.supervaluation, pexPossOr_presup hF, hq,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, exists_eq_or_imp,
    exists_eq_left]
  split_ifs <;> grind

/-- `pex^{IE+II}[◇(a ∨ b)]` is undefined exactly where one of `◇a` and `◇b` holds without the
other, the presupposition failure fn. 2 predicts. -/
theorem homogeneity_gap :
    (pexPossOr R a b).eval.gapExt = symmDiff (R.preimage a) (R.preimage b) := by
  ext w
  simp only [Trivalent.Prop3.mem_gapExt, eval_eq_indet_iff, pexPossOr_presup hF,
    Set.mem_symmDiff]
  tauto

/-- The negation `¬pex^{IE+II}[◇(a ∨ b)]` is undefined at the same worlds, fn. 2. -/
theorem homogeneity_gap_neg :
    (pexPossOr R a b).neg.eval.gapExt = symmDiff (R.preimage a) (R.preimage b) := by
  rw [← homogeneity_gap hF]
  ext w
  simp

/-- `pex^{IE+II}[◇(a ∨ b)]` is homogeneous, since a world permitting only `a` lies in its gap. -/
theorem isHomogeneous_pexPossOr : isHomogeneous (pexPossOr R a b).eval := by
  obtain ⟨w, hwa, hwb⟩ := hF.only_left
  exact ⟨w, by rw [homogeneity_gap hF]; exact .inl ⟨hwa, hwb⟩⟩

/-- With every alternative relevant, `pex^{IE+II}[◇(a ∨ b)]` holds exactly where
`exh^{IE+II}[◇(a ∨ b)]` is true, (12e) and (13); the two differ only in what they presuppose. -/
theorem pex_and_exh_agree :
    (pexIEII (fcAlts R a b) (R.preimage (a ∪ b)) (fcAlts R a b)).holds w ↔
      w ∈ exhIEII (fcAlts R a b) (R.preimage (a ∪ b)) := by
  have hII : II (fcAlts R a b) (R.preimage (a ∪ b)) \ {R.preimage (a ∪ b)} ∩ fcAlts R a b =
      {R.preimage a, R.preimage b} := by
    rw [Set.inter_eq_left.2 fun _ h ↦ h.1.1, II_fcAlts_sdiff hF]
  have hc : R.preimage (a ∩ b) ∈ fcAlts R a b := by simp [fcAlts]
  rw [freeChoice hF]
  change ((∀ ψ, _ → _ → w ∉ ψ) ∧ Homogeneous _ w) ∧ w ∈ R.preimage (a ∪ b) ↔ _
  rw [hII, homogeneous_pair]
  grind [isInnocentlyExcludable_fcAlts_iff hF, preimage_union]

omit hF in
/-- The alternatives of `◇(¬T ∨ ¬B)` are those of `¬□(T ∧ B)` in (18b). -/
theorem fcAlts_compl (R : SetRel W W) (T B : Set W) :
    fcAlts R Tᶜ Bᶜ = {(R.core (T ∩ B))ᶜ, (R.core T)ᶜ, (R.core B)ᶜ, (R.core (T ∪ B))ᶜ} := by
  simp only [fcAlts, preimage_compl, ← Set.compl_inter, ← Set.compl_union]

omit hF in
/-- `pex^{IE+II}[¬□(T ∧ B)]` holds exactly where negative free choice does, (18) and (19a). -/
theorem negative_free_choice {T B : Set W} (hF : FreeChoiceWitnesses R Tᶜ Bᶜ) :
    (pexPossOr R Tᶜ Bᶜ).holds w ↔ w ∉ R.core T ∧ w ∉ R.core B := by
  simpa only [preimage_compl, Set.mem_compl_iff] using free_choice hF

end FreeChoice

/-- Where world `4` permits both `0` and `1`, world `2` only `0`, world `3` only `1`, and world
`0` neither, `pex^{IE+II}[◇(p ∨ q)]` holds at `4`, suffers presupposition failure at `2` as fn. 2
predicts, and is false at `0`. -/
example :
    let R : SetRel (Fin 5) (Fin 5) := {(2, 0), (3, 1), (4, 0), (4, 1)}
    (pexPossOr R {0} {1}).holds 4 ∧ ¬ (pexPossOr R {0} {1}).presup 2 ∧
      (pexPossOr R {0} {1}).neg.holds 0 := by
  intro R
  have hF : FreeChoiceWitnesses R {0} {1} :=
    ⟨⟨2, by simp [R], by simp [R]⟩, ⟨3, by simp [R], by simp [R]⟩, ⟨4, by simp [R], by simp [R]⟩⟩
  refine ⟨(free_choice hF).2 (by simp [R]), fun hp ↦ ?_, double_prohibition.2 (by simp [R])⟩
  simpa [R] using (pexPossOr_presup hF).1 hp

/-! ### `pex^{IE+II}` on `□(p ∧ q)`, §2.2 -/

section NegativeFreeChoice

variable (R : SetRel W W) (T B : Set W)

/-- The alternatives of `□(T ∧ B)` replace the conjunction by its conjuncts and their
disjunction. -/
def necAlts : Set (Set W) := {R.core (T ∩ B), R.core T, R.core B, R.core (T ∪ B)}

/-- `pexNecAnd R T B` is `pex^{IE+II}[□(T ∧ B)]` with the disjunctive alternative irrelevant, as
in (20) and (57). -/
def pexNecAnd : PartialProp W :=
  pexIEII (necAlts R T B) (R.core (T ∩ B)) {R.core (T ∩ B), R.core T, R.core B}

variable {R T B}

/-- `□(T ∧ B)` entails each of its alternatives. -/
theorem subset_of_mem_necAlts {q : Set W} (hq : q ∈ necAlts R T B) : R.core (T ∩ B) ⊆ q := by
  simp only [necAlts, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl
  exacts [le_rfl, core_mono Set.inter_subset_left, core_mono Set.inter_subset_right,
    core_mono (Set.inter_subset_left.trans Set.subset_union_left)]

/-- `□(T ∧ B)` entails its alternatives, so `exh^{IE+II}` is vacuous on it, (56). -/
theorem exhIEII_necAlts (h : (R.core (T ∩ B)).Nonempty) :
    exhIEII (necAlts R T B) (R.core (T ∩ B)) = R.core (T ∩ B) :=
  exhIEII_eq_self_of_forall_subset (fun _ ↦ subset_of_mem_necAlts) h

/-- No alternative of `□(T ∧ B)` is excludable. -/
theorem not_isInnocentlyExcludable_necAlts (h : (R.core (T ∩ B)).Nonempty) (q : Set W) :
    ¬ IsInnocentlyExcludable (necAlts R T B) (R.core (T ∩ B)) q := fun hq ↦
  not_isInnocentlyExcludable_of_phi_subset
    (((Set.finite_singleton _).insert _).insert _ |>.insert _) h (subset_of_mem_necAlts hq.1) hq

variable (h₁ : ∃ w ∈ R.core T, w ∉ R.core B) (h₂ : ∃ w ∈ R.core B, w ∉ R.core T)
  (h : (R.core (T ∩ B)).Nonempty) {w : W}
include h₁ h₂ h

/-- Apart from the prejacent, every alternative of `□(T ∧ B)` is innocently includable, (20). -/
theorem II_necAlts_sdiff :
    II (necAlts R T B) (R.core (T ∩ B)) \ {R.core (T ∩ B)} =
      {R.core T, R.core B, R.core (T ∪ B)} := by
  obtain ⟨w₀, hw₀⟩ := id h
  have hII : II (necAlts R T B) (R.core (T ∩ B)) = necAlts R T B :=
    (Set.sep_subset _ _).antisymm fun q hq ↦ mem_II_of_cell_witness _ _ hq w₀
      ⟨hw₀, fun q hq ↦ absurd hq (not_isInnocentlyExcludable_necAlts h q),
        fun r hr ↦ subset_of_mem_necAlts hr.1 hw₀⟩ (subset_of_mem_necAlts hq hw₀)
  rw [hII, necAlts, Set.insert_sdiff_of_mem _ (Set.mem_singleton _),
    Set.sdiff_singleton_eq_self]
  obtain ⟨wT, hwT, hwTB⟩ := h₁
  obtain ⟨wB, hwB, hwBT⟩ := h₂
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨fun he ↦ hwTB ?_, fun he ↦ hwBT ?_, fun he ↦ hwTB ?_⟩
  · exact core_mono Set.inter_subset_right (he ▸ hwT)
  · exact core_mono Set.inter_subset_left (he ▸ hwB)
  · exact core_mono Set.inter_subset_right (he ▸ core_mono Set.subset_union_left hwT)

private theorem II_necAlts_sdiff_inter :
    II (necAlts R T B) (R.core (T ∩ B)) \ {R.core (T ∩ B)} ∩ {R.core (T ∩ B), R.core T, R.core B} =
      {R.core T, R.core B} := by
  have hne : R.core (T ∪ B) ≠ R.core (T ∩ B) := fun he ↦ by
    obtain ⟨wT, hwT, hwTB⟩ := h₁
    exact hwTB (core_mono Set.inter_subset_right (he ▸ core_mono Set.subset_union_left hwT))
  rw [II_necAlts_sdiff h₁ h₂ h]
  ext α
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  grind

/-- `pex^{IE+II}[□(T ∧ B)]` presupposes `□T ↔ □B`, (20). -/
theorem pexNecAnd_presup : (pexNecAnd R T B).presup w ↔ (w ∈ R.core T ↔ w ∈ R.core B) :=
  (and_iff_right fun ψ hψ _ ↦ absurd hψ (not_isInnocentlyExcludable_necAlts h ψ)).trans
    (by rw [II_necAlts_sdiff_inter h₁ h₂ h, homogeneous_pair])

/-- The homogeneity `□T ↔ □B` projects out of the negation of the strong prejacent, so
`¬pex^{IE+II}[□(T ∧ B)]` holds exactly where negative free choice does, (20). -/
theorem negative_free_choice_under_negation :
    (pexNecAnd R T B).neg.holds w ↔ w ∉ R.core T ∧ w ∉ R.core B := by
  have hl : ⋂₀ (II (necAlts R T B) (R.core (T ∩ B)) \ {R.core (T ∩ B)} ∩
      {R.core (T ∩ B), R.core T, R.core B}) ⊆ R.core (T ∩ B) := by
    rw [II_necAlts_sdiff_inter h₁ h₂ h, Set.sInter_pair, core_inter]
  have hu : R.core (T ∩ B) ⊆ ⋃₀ (II (necAlts R T B) (R.core (T ∩ B)) \ {R.core (T ∩ B)} ∩
      {R.core (T ∩ B), R.core T, R.core B}) := by
    rw [II_necAlts_sdiff_inter h₁ h₂ h, Set.sUnion_pair, core_inter]
    exact inf_le_sup
  rw [pexNecAnd, pexIEII_neg_holds_iff hl hu, ← pexNecAnd, pexNecAnd_presup h₁ h₂ h,
    II_necAlts_sdiff_inter h₁ h₂ h]
  grind

end NegativeFreeChoice

/-! ### Free choice under negative factives, §3 -/

section NegativeFactive

variable {R : SetRel W W} {a b : Set W} {w : W}

/-- Under a negative factive the whole output of `pex` is presupposed, and that is free choice,
(21a) and (31c). -/
theorem free_choice_presupposed (hF : FreeChoiceWitnesses R a b)
    (believes : (W → Prop) → W → Prop) :
    (negFactive (pexPossOr R a b) believes).presup w ↔ w ∈ R.preimage a ∧ w ∈ R.preimage b :=
  free_choice hF

/-- Under a negative factive `pex^{IE+II}[¬□(T ∧ B)]` presupposes negative free choice, (33a)
and (34c). -/
theorem negative_free_choice_presupposed {T B : Set W} (hF : FreeChoiceWitnesses R Tᶜ Bᶜ)
    (believes : (W → Prop) → W → Prop) :
    (negFactive (pexPossOr R Tᶜ Bᶜ) believes).presup w ↔ w ∉ R.core T ∧ w ∉ R.core B :=
  negative_free_choice hF

/-- The assertion of a negative factive denies belief in the prejacent `◇(a ∨ b)`, hence belief
in either disjunct, (21b) and (31d′); at `Tᶜ` and `Bᶜ` this is (33b) and (34d). -/
theorem unaware_disbelieves_each_disjunct (R' : SetRel W W)
    (hw : (negFactive (pexPossOr R a b) (Box R')).assertion w) :
    ¬ □[R'] (· ∈ R.preimage a) w ∧ ¬ □[R'] (· ∈ R.preimage b) w :=
  ⟨fun hA ↦ hw (box_mono R' (fun _ hv ↦ (preimage_union ..).ge (.inl hv)) w hA),
   fun hB ↦ hw (box_mono R' (fun _ hv ↦ (preimage_union ..).ge (.inr hv)) w hB)⟩

/-- With a flat `exh` complement the factive only denies belief in the strengthened content,
which an attitude holder who believes Olivia can take Logic but not Algebra satisfies, so the
target reading that he believes neither is missed, (24a). -/
theorem exh_unaware_too_weak (hF : FreeChoiceWitnesses R a b) :
    ∃ R' : SetRel W W, □[R'] (· ∈ R.preimage a) w ∧
      ¬ □[R'] (· ∈ exhIEII (fcAlts R a b) (R.preimage (a ∪ b))) w := by
  obtain ⟨w₁, hw₁a, hw₁b⟩ := hF.only_left
  refine ⟨.ofSuccessors fun _ ↦ {w₁}, fun v (hv : v = w₁) ↦ hv ▸ hw₁a, fun hbox ↦ ?_⟩
  have := hbox w₁ (Set.mem_singleton w₁)
  rw [freeChoice hF] at this
  exact hw₁b this.1.2

end NegativeFactive

/-! ### Filtering free choice, §4 -/

section Filtering

variable {R : SetRel W W} {a b A B : Set W} (C : W → Prop)

/-- In `¬pex[◇(a ∨ b)] ∨ C`, with `C` presupposing `◇A ∧ ◇B` for `a ⊆ A` and `b ⊆ B`, the
filtering disjunction (45) filters the free-choice presupposition, since the negation of the
first disjunct is free choice, and only the homogeneity of the first disjunct projects, (53) and
§4.4. -/
theorem free_choice_filtered (hA : a ⊆ A) (hB : b ⊆ B) (hF : FreeChoiceWitnesses R a b) :
    ((pexPossOr R a b).neg.orFilter ⟨fun w ↦ w ∈ R.preimage A ∧ w ∈ R.preimage B, C⟩).presup =
      (pexPossOr R a b).presup := by
  funext w
  refine propext ⟨And.left, fun hp ↦ ⟨hp, fun hna ↦ ?_⟩⟩
  have := (free_choice hF).1 ⟨hp, not_not.1 hna⟩
  exact ⟨preimage_mono hA this.1, preimage_mono hB this.2⟩

/-- Without exhaustification under the negation, the antecedent of the conditional
presupposition is only `◇(a ∨ b)`, and a world permitting `a` but not `B` refutes it, (46c). -/
theorem no_filtering_without_pex (hw : ∃ w ∈ R.preimage a, w ∉ R.preimage B) :
    ∃ w, ¬ ((ofProp (· ∈ R.preimage (a ∪ b))).neg.orFilter
      ⟨fun w ↦ w ∈ R.preimage A ∧ w ∈ R.preimage B, C⟩).presup w := by
  obtain ⟨w, hwa, hwB⟩ := hw
  exact ⟨w, fun ⟨_, h⟩ ↦ hwB (h (not_not.2 (preimage_mono Set.subset_union_left hwa))).2⟩

/-- A flat `exh` under the negation filters the free-choice presupposition, (47c). -/
theorem exh_filters (hA : a ⊆ A) (hB : b ⊆ B) (hF : FreeChoiceWitnesses R a b) (w : W) :
    ((ofProp (· ∈ exhIEII (fcAlts R a b) (R.preimage (a ∪ b)))).neg.orFilter
      ⟨fun w ↦ w ∈ R.preimage A ∧ w ∈ R.preimage B, C⟩).presup w := by
  have := @preimage_mono _ _ R _ _ hA
  have := @preimage_mono _ _ R _ _ hB
  simp only [orFilter, neg, ofProp, freeChoice hF]
  grind

/-- A flat `exh` under the negation loses double prohibition, since the negated exhaustified
disjunction is compatible with permitting `a`, (47b). -/
theorem exh_loses_double_prohibition (hF : FreeChoiceWitnesses R a b) :
    ∃ w, w ∉ exhIEII (fcAlts R a b) (R.preimage (a ∪ b)) ∧ w ∈ R.preimage a := by
  obtain ⟨w₁, hw₁a, hw₁b⟩ := hF.only_left
  exact ⟨w₁, by grind [freeChoice hF], hw₁a⟩

/-- In `pex[□(A ∧ B)] ∨ C`, with `C` presupposing `¬□a ∧ ¬□b`, the negation of the first
disjunct is negative free choice for `A` and `B`, which entails that presupposition, so it is
filtered and only the homogeneity `□A ↔ □B` projects, (57c). -/
theorem negative_free_choice_filtered (hA : a ⊆ A) (hB : b ⊆ B)
    (h₁ : ∃ w ∈ R.core A, w ∉ R.core B) (h₂ : ∃ w ∈ R.core B, w ∉ R.core A)
    (h : (R.core (A ∩ B)).Nonempty) :
    ((pexNecAnd R A B).orFilter ⟨fun w ↦ w ∉ R.core a ∧ w ∉ R.core b, C⟩).presup =
      (pexNecAnd R A B).presup := by
  funext w
  have := @negative_free_choice_under_negation _ R A B h₁ h₂ h w
  have := @core_mono _ _ R _ _ hA
  have := @core_mono _ _ R _ _ hB
  simp only [orFilter, eq_iff_iff]
  grind [holds, neg]

/-- Since `exh^{IE+II}` is vacuous on `□(A ∧ B)`, the negation of the first disjunct is only
`¬□(A ∧ B)`, and a world requiring `a` but not `B` refutes the filtering, (56c). -/
theorem no_negative_filtering_with_exh (h : (R.core (A ∩ B)).Nonempty)
    (hw : ∃ w ∈ R.core a, w ∉ R.core B) :
    ∃ w, ¬ ((ofProp (· ∈ exhIEII (necAlts R A B) (R.core (A ∩ B)))).orFilter
      ⟨fun w ↦ w ∉ R.core a ∧ w ∉ R.core b, C⟩).presup w := by
  obtain ⟨w, hwa, hwB⟩ := hw
  refine ⟨w, fun ⟨_, hf⟩ ↦ (hf ?_).1 hwa⟩
  rw [exhIEII_necAlts h]
  exact fun hAB ↦ hwB (core_mono Set.inter_subset_right hAB)

/-- Local accommodation over `¬pex[◇(a ∨ b)]`, which is Bochvar's `truthOp`
(`acc(p_q) = q ∧ p`), keeps double prohibition and stops homogeneity from projecting, (59c). -/
theorem double_prohibition_accommodated {w : W} :
    (pexPossOr R a b).neg.truthOp.holds w ↔ w ∉ R.preimage a ∧ w ∉ R.preimage b :=
  (and_iff_right trivial).trans double_prohibition

/-- After local accommodation the negation of the first disjunct is only `◇a ∨ ◇b`, and a world
permitting `a` but not `B` refutes the filtering, (59b). -/
theorem no_filtering_with_accommodation (hw : ∃ w ∈ R.preimage a, w ∉ R.preimage B) :
    ∃ w, ¬ ((pexPossOr R a b).neg.truthOp.orFilter
      ⟨fun w ↦ w ∈ R.preimage A ∧ w ∈ R.preimage B, C⟩).presup w := by
  obtain ⟨w, hwa, hwB⟩ := hw
  refine ⟨w, fun ⟨_, hf⟩ ↦ hwB (hf fun ⟨_, hn⟩ ↦ hn ?_).2⟩
  exact preimage_mono Set.subset_union_left hwa

end Filtering

/-! ### Free choice under quantifiers, §5 -/

section Quantified

variable {R : SetRel W W} {D : Type*} {S : D → Prop} {p q : D → Set W} {w : W}

/-- With universal projection, `¬∃x ∈ S[pex[◇(px ∨ qx)]]` holds exactly where universal double
prohibition does, (70b) and (71), the reading the elided second sentence of (69) needs. -/
theorem universal_double_prohibition :
    (negExistsPartial S fun x ↦ pexPossOr R (p x) (q x)).holds w ↔
      (¬ ∃ x, S x ∧ w ∈ R.preimage (p x)) ∧ ¬ ∃ x, S x ∧ w ∈ R.preimage (q x) := by
  simp only [not_exists, not_and, ← forall₂_and]
  refine Iff.trans ?_ (forall₂_congr fun x _ ↦ double_prohibition)
  simp only [holds, negExistsPartial, neg, not_exists, not_and, ← forall₂_and]

variable (hF : ∀ x, S x → FreeChoiceWitnesses R (p x) (q x))
include hF

/-- With universal projection, `∀x ∈ S[pex[◇(px ∨ qx)]]` holds exactly where universal free
choice does, (66a) and (67). -/
theorem universal_free_choice :
    (forallPartial S fun x ↦ pexPossOr R (p x) (q x)).holds w ↔
      (∀ x, S x → w ∈ R.preimage (p x)) ∧ ∀ x, S x → w ∈ R.preimage (q x) := by
  rw [forallPartial_holds, ← forall₂_and, ← forall₂_and]
  exact forall₂_congr fun x hx ↦ free_choice (hF x hx)

/-- With universal projection, `∃x ∈ S[pex[◇(px ∨ qx)]]` gives existential free choice, (73)
and (74). -/
theorem existential_free_choice
    (hw : (existsPartialUniv S fun x ↦ pexPossOr R (p x) (q x)).holds w) :
    ∃ x, S x ∧ w ∈ R.preimage (p x) ∧ w ∈ R.preimage (q x) :=
  let ⟨x, hx, ha⟩ := hw.2
  ⟨x, hx, (free_choice (hF x hx)).1 ⟨hw.1 x hx, ha⟩⟩

/-- With the presupposition bound by the existential, as in the strong Kleene existential
`existsPartialStrong`, `∃x ∈ S[pex[◇(px ∨ qx)]]` holds exactly where existential free choice
does, (75). -/
theorem existential_free_choice_bound :
    (existsPartialStrong S fun x ↦ pexPossOr R (p x) (q x)).holds w ↔
      ∃ x, S x ∧ w ∈ R.preimage (p x) ∧ w ∈ R.preimage (q x) := by
  rw [existsPartialStrong_holds_iff]
  exact exists_congr fun x ↦ and_congr_right fun hx ↦ free_choice (hF x hx)

/-- *Exactly one student can take Logic or Calculus* says that one student has free choice and
every other has double prohibition, (81), (83) and (76a). -/
theorem exactly_one_free_choice
    (hw : (existsUniquePartial S fun x ↦ pexPossOr R (p x) (q x)).holds w) :
    ∃ x, S x ∧ (w ∈ R.preimage (p x) ∧ w ∈ R.preimage (q x)) ∧
      ∀ y, S y → y ≠ x → w ∉ R.preimage (p y) ∧ w ∉ R.preimage (q y) := by
  obtain ⟨hpre, x, ⟨hx, ha⟩, huniq⟩ := hw
  refine ⟨x, hx, (free_choice (hF x hx)).1 ⟨hpre x hx, ha⟩, fun y hy hyx ↦ ?_⟩
  exact double_prohibition.1 ⟨hpre y hy, fun ha' ↦ hyx (huniq y ⟨hy, ha'⟩)⟩

/-- *Exactly one student can't take Logic or Calculus* says that one student has double
prohibition and every other has free choice, (82), (84) and (77a). -/
theorem exactly_one_double_prohibition
    (hw : (existsUniquePartial S fun x ↦ (pexPossOr R (p x) (q x)).neg).holds w) :
    ∃ x, S x ∧ (w ∉ R.preimage (p x) ∧ w ∉ R.preimage (q x)) ∧
      ∀ y, S y → y ≠ x → w ∈ R.preimage (p y) ∧ w ∈ R.preimage (q y) := by
  obtain ⟨hpre, x, ⟨hx, ha⟩, huniq⟩ := hw
  refine ⟨x, hx, double_prohibition.1 ⟨hpre x hx, ha⟩, fun y hy hyx ↦ ?_⟩
  exact (free_choice (hF y hy)).1 ⟨hpre y hy, not_not.1 fun ha' ↦ hyx (huniq y ⟨hy, ha'⟩)⟩

end Quantified

/-- With universal projection, `¬∃x ∈ S[pex[□(px ∧ qx)]]` holds exactly where universal
negative free choice does, (66b) and (68). -/
theorem universal_negative_free_choice {R : SetRel W W} {D : Type*} {S : D → Prop}
    {p q : D → Set W} {w : W} (h₁ : ∀ x, S x → ∃ w ∈ R.core (p x), w ∉ R.core (q x))
    (h₂ : ∀ x, S x → ∃ w ∈ R.core (q x), w ∉ R.core (p x))
    (h : ∀ x, S x → (R.core (p x ∩ q x)).Nonempty) :
    (negExistsPartial S fun x ↦ pexNecAnd R (p x) (q x)).holds w ↔
      (¬ ∃ x, S x ∧ w ∈ R.core (p x)) ∧ ¬ ∃ x, S x ∧ w ∈ R.core (q x) := by
  simp only [not_exists, not_and, ← forall₂_and]
  refine Iff.trans ?_ (forall₂_congr fun x hx ↦
    negative_free_choice_under_negation (h₁ x hx) (h₂ x hx) (h x hx))
  simp only [holds, negExistsPartial, neg, not_exists, not_and, ← forall₂_and]

end DelPinalBassiSauerland2024
