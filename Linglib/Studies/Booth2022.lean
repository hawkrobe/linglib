module

public import Linglib.Core.Order.Bilattice.Product
public import Linglib.Semantics.Questions.Basic
public import Mathlib.Order.Comparable
public import Mathlib.Tactic.FinCases

/-!
# Booth (2022): Necessity modals, disjunctions, and collectivity

[booth-2022] resolves Ross's Puzzle by requiring the alternatives of a necessity modal's
prejacent to form a minimal cover of the relevant worlds, not merely a cover: each alternative
must be needed, so `□(p ∨ q)` licenses the Independence inferences `◇(p ∧ ¬q)` and `◇(q ∧ ¬p)`,
and the Ross inference from `□p` to `□(p ∨ q)` is strongly invalid. The semantics is bilateral,
its falsity conditions not a function of its truth conditions, so necessity and possibility stay
dual and negated modals distribute over disjunction. The closing reading of `□` as a collective
predicate of the plurality of propositions a disjunction denotes (§4) is not formalized.

## Main definitions

* `IsMinCover`, `IsSuperCover`: the minimal and super covers of §2.1.
* `BilatInqProp`: Def 10, the pairs of the product `Question W ⊙ Question W` with disjoint
  coordinates; `atom`, `negate`, `disj`, `conj`, `necessity`, `possibility`: the clauses of
  Def 14.
* `BilatInqProp.truth`, `BilatInqProp.falsity`: the worlds at which a proposition is true and
  false (Def 17).
* `updateAccess`: the accessibility update of Def 15.
* `Formula`, `Formula.eval`: the language of Def 8 and its interpretation, the restrictor
  conditional evaluating its consequent in the updated model (Def 16).
* `NonHurford`: Def 22.

## Main results

Entailment over a model (Def 18) is inclusion of truth sets, and strong invalidity (Def 21) is
disjointness of the premises' truth set from the conclusion's.

* `isSuperCover_pair_iff`, `isMinCover_pair_iff_inter_sdiff`: the Diversity (Def 2) and
  Independence (Def 6) inferences are super and minimal covering; `IsMinCover.isSuperCover`:
  Independence entails Diversity. `BoothExample.diversity_without_independence`: Figure 1, where
  it does not go the other way.
* `kratzer_monotone`: Fact 1; `BoothExample.not_monotone_necessity`: Booth's necessity is not
  upward monotonic.

* `Formula.eval_neg_neg`: Fact 3, double negation.
* `Formula.fg_eval`: Fact 5, both interpretations of every sentence finitely generated
  (`Question.FG`), by induction over the language.
* `ross_strongly_invalid_of_alt`, `inter_diff_truth_nonempty_of_alt` and their sentence forms
  `Formula.ross_strongly_invalid`, `Formula.independence`: the meta-language Facts 7 and 6.
* `not_forall_disjoint_of_nonHurford`, `not_forall_independence_of_nonHurford`: Facts 7 and 6
  as printed, for every non-Hurford disjunction of Def 22, are false.
* `ross_strongly_invalid`, `extended_ross_strongly_invalid`: Facts 7 and 8 for atoms.
* `independence_left`, `independence_right`: Fact 9. `free_choice_left`, `free_choice_right`:
  Fact 10. `Formula.independence_conditional_left`, `Formula.independence_conditional_right`:
  Fact 11. `unnecessity_distribution_left`, `impossibility_distribution_left` and their mirror
  images: Facts 12 and 13.
* `truth_necessity_subset`: every Booth necessity is a Kratzerian one (Def 1); the model
  `BoothExample` separates them.

## Implementation notes

* `Question W` supplies Def 10's subset-closed families: `Question.ofSet` is `↓{·}` (Def 11),
  `Question.info` is `info` (Def 12) and `Question.alt` is `alt` (Def 13). Def 10's third bullet,
  `P⁺ ∩ P⁻ = {∅}`, is disjointness in `Question W`, whose bottom is `{∅}`, so Booth's
  propositions are the pairs of the product bilattice with disjoint coordinates and the ¬-, ∨-
  and ∧-clauses are the product's negation `ᶜ`, truth join and truth meet.
* Def 17 writes `w ∈ ⟦φ⟧⁺` for a world `w` and a set of states; it is read as
  `w ∈ info ⟦φ⟧⁺`, equivalently `{w} ∈ ⟦φ⟧⁺` (`BilatInqProp.mem_truth_iff`).
* Def 22 is mathlib's `IncompRel` for the positive interpretations. The meta-language Facts 6
  and 7 are stated for every such disjunction, but their proofs assume that no alternative of
  either disjunct is a state of the other, `Disjoint (alt ⟦φ⟧⁺) ⟦ψ⟧⁺`, which is strictly
  stronger. Under Def 22 both facts fail; under the alternative-wise condition the proofs go
  through, and for atoms the two conditions coincide, so the object-language Facts 7–13 stand.
  The correction is this file's, not the paper's.
* Facts 12 and 13 need no non-Hurford hypothesis.

## References

* [booth-2022]
* [simons-2005], the super covers of the Diversity analysis.
* [aloni-2022], Aloni's bilateral state-based modal logic; Booth cites her 2018 manuscript
  "FC disjunction in state-based semantics" (fn. 9).
* [ciardelli-groenendijk-roelofsen-2018], standard inquisitive semantics, in which `¬¬φ` and `φ`
  differ (§3.1).
-/

@[expose] public section

namespace Booth2022

open Bilattice

variable {W : Type*}

/-! ### Super covers and minimal covers (§§1.1, 2.1)

Booth's `□φ` requires the alternatives of `⟦φ⟧⁺` not only to cover the relevant worlds, as the
Kratzerian semantics does, but to form a minimal cover, with no proper subfamily still covering
them. For a disjunction `p ∨ q` the covering relations match the two families of inferences §1
compares: `{⟦p⟧, ⟦q⟧}` super covers the relevant worlds exactly when the Diversity inferences hold
(Def 2), and minimally covers them exactly when the Independence inferences hold (Def 6). A
minimal cover is a super cover, so Independence entails Diversity; the converse fails
(`BoothExample.diversity_without_independence`). -/

/-- `C` is a minimal cover (m-cover) of `S` (§2.1): it covers `S`, `S ⊆ ⋃₀ C`, and no proper
subfamily does. -/
def IsMinCover (C : Set (Set W)) (S : Set W) : Prop :=
  Minimal (fun X ↦ S ⊆ ⋃₀ X) C

theorem IsMinCover.subset_sUnion {C : Set (Set W)} {S : Set W} (h : IsMinCover C S) :
    S ⊆ ⋃₀ C :=
  h.prop

/-- A single set minimally covers a nonempty `S` exactly when it contains it. -/
theorem isMinCover_singleton_iff {X S : Set W} (hS : S.Nonempty) :
    IsMinCover {X} S ↔ S ⊆ X := by
  refine ⟨fun h ↦ by simpa using h.subset_sUnion, fun h ↦ ⟨by simpa using h, fun Y hY hYX ↦ ?_⟩⟩
  obtain ⟨v, hv⟩ := hS
  obtain ⟨Z, hZY, -⟩ := hY hv
  exact Set.singleton_subset_iff.2 (Set.mem_singleton_iff.1 (hYX hZY) ▸ hZY)

/-- A pair minimally covers `S` exactly when it covers `S` and neither member covers it alone,
so that each member contains a world of `S` outside the other (§2.1). -/
theorem isMinCover_pair_iff {A B S : Set W} (hAB : A ≠ B) :
    IsMinCover {A, B} S ↔ S ⊆ A ∪ B ∧ ¬ S ⊆ A ∧ ¬ S ⊆ B := by
  refine ⟨fun h ↦ ⟨by simpa using h.subset_sUnion, fun hA ↦ ?_, fun hB ↦ ?_⟩, ?_⟩
  · have h' := h.le_of_le (y := {A}) (by simpa using hA)
      (Set.singleton_subset_iff.2 (Set.mem_insert A _))
    exact hAB (h' (Set.mem_insert_of_mem A (Set.mem_singleton B))).symm
  · have h' := h.le_of_le (y := {B}) (by simpa using hB)
      (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem A (Set.mem_singleton B)))
    exact hAB (h' (Set.mem_insert A _))
  rintro ⟨hcov, hA, hB⟩
  refine ⟨by simpa using hcov, fun Y hY hYAB ↦ Set.insert_subset_iff.2 ⟨?_, ?_⟩⟩
  · obtain ⟨u, huS, huB⟩ := Set.not_subset.1 hB
    obtain ⟨Z, hZY, huZ⟩ := hY huS
    rcases hYAB hZY with rfl | rfl
    · exact hZY
    · exact absurd huZ huB
  · obtain ⟨v, hvS, hvA⟩ := Set.not_subset.1 hA
    obtain ⟨Z, hZY, hvZ⟩ := hY hvS
    rcases hYAB hZY with rfl | rfl
    · exact absurd hvZ hvA
    · exact Set.singleton_subset_iff.2 hZY

/-- `{A, B}` minimally covers `S` exactly when it covers `S` and `S` meets both relative
complements: the Independence inferences of Def 6, `R ∩ (⟦φ⟧ ∖ ⟦ψ⟧) ≠ ∅` and
`R ∩ (⟦ψ⟧ ∖ ⟦φ⟧) ≠ ∅`. -/
theorem isMinCover_pair_iff_inter_sdiff {A B S : Set W} (hAB : A ≠ B) :
    IsMinCover {A, B} S ↔ S ⊆ A ∪ B ∧ (S ∩ (A \ B)).Nonempty ∧ (S ∩ (B \ A)).Nonempty := by
  rw [isMinCover_pair_iff hAB]
  refine and_congr_right fun hcov ↦ ?_
  have key : ∀ {X Y : Set W}, S ⊆ X ∪ Y → (¬ S ⊆ Y ↔ (S ∩ (X \ Y)).Nonempty) := fun hXY ↦
    ⟨fun h ↦ (Set.not_subset.1 h).imp fun _ ⟨hv, hvY⟩ ↦ ⟨hv, (hXY hv).resolve_right hvY, hvY⟩,
      fun ⟨_, hv, _, hvY⟩ h ↦ hvY (h hv)⟩
  rw [key hcov, key (hcov.trans (Set.union_comm A B).subset)]
  exact and_comm

/-- `C` is a super cover of `S` ([simons-2005], as Booth gives it in §2.1): it covers `S` and each
of its members meets `S`. -/
def IsSuperCover (C : Set (Set W)) (S : Set W) : Prop :=
  S ⊆ ⋃₀ C ∧ ∀ c ∈ C, (c ∩ S).Nonempty

/-- `{A, B}` super covers `S` exactly when it covers `S` and `S` meets both `A` and `B`: the
Diversity inferences of Def 2, `R ∩ ⟦φ⟧ ≠ ∅` and `R ∩ ⟦ψ⟧ ≠ ∅`. -/
theorem isSuperCover_pair_iff {A B S : Set W} :
    IsSuperCover {A, B} S ↔ S ⊆ A ∪ B ∧ (A ∩ S).Nonempty ∧ (B ∩ S).Nonempty := by
  simp [IsSuperCover]

/-- A minimal cover is a super cover, since a member missing `S` could be dropped: Independence
entails Diversity. -/
theorem IsMinCover.isSuperCover {C : Set (Set W)} {S : Set W} (h : IsMinCover C S) :
    IsSuperCover C S := by
  refine ⟨h.subset_sUnion, fun c hc ↦ Set.nonempty_iff_ne_empty.2 fun hcS ↦ ?_⟩
  have hsub : S ⊆ ⋃₀ (C \ {c}) := fun v hv ↦ by
    obtain ⟨d, hd, hvd⟩ := h.subset_sUnion hv
    refine ⟨d, ⟨hd, fun hdc ↦ ?_⟩, hvd⟩
    rw [Set.mem_singleton_iff.1 hdc] at hvd
    exact Set.eq_empty_iff_forall_notMem.1 hcS v ⟨hvd, hv⟩
  exact (h.le_of_le hsub Set.sdiff_subset hc).2 rfl

/-! ### Bilateral inquisitive propositions (Defs 10, 14 and 17) -/

/-- **Booth Def 10**: a bilateral inquisitive proposition is a pair of `Question`s, the states
verifying and the states falsifying it, with no substantive overlap: only the inconsistent state
`∅` both verifies and falsifies it (`Question.disjoint_iff`). The pairs live in the diagonal
product `Question W ⊙ Question W`. -/
abbrev BilatInqProp (W : Type*) := {x : Question W ⊙ Question W // Disjoint x.pro x.con}

namespace BilatInqProp

/-- The positive interpretation `⟦φ⟧⁺`: the states verifying `φ`. -/
abbrev pos (φ : BilatInqProp W) : Question W := φ.1.pro

/-- The negative interpretation `⟦φ⟧⁻`: the states falsifying `φ`. -/
abbrev neg (φ : BilatInqProp W) : Question W := φ.1.con

/-- A bilateral inquisitive proposition from its two interpretations. -/
def mk (pos neg : Question W) (h : ∀ s, s ∈ pos → s ∈ neg → s = ∅) : BilatInqProp W :=
  ⟨Product.mk pos neg, Question.disjoint_iff.2 h⟩

/-- No substantive overlap: only `∅` both verifies and falsifies. -/
theorem no_overlap (φ : BilatInqProp W) (s : Set W) (hpos : s ∈ φ.pos) (hneg : s ∈ φ.neg) :
    s = ∅ :=
  Question.disjoint_iff.1 φ.2 s hpos hneg

/-- **Booth Def 17**: the worlds at which `φ` is true, the informative content of `⟦φ⟧⁺`. -/
def truth (φ : BilatInqProp W) : Set W := φ.pos.info

/-- **Booth Def 17**: the worlds at which `φ` is false, the informative content of `⟦φ⟧⁻`. -/
def falsity (φ : BilatInqProp W) : Set W := φ.neg.info

theorem mem_truth_iff {φ : BilatInqProp W} {w : W} : w ∈ φ.truth ↔ {w} ∈ φ.pos :=
  Question.mem_info_iff_singleton_mem _ _

theorem mem_falsity_iff {φ : BilatInqProp W} {w : W} : w ∈ φ.falsity ↔ {w} ∈ φ.neg :=
  Question.mem_info_iff_singleton_mem _ _

/-- No world makes a proposition both true and false. -/
theorem disjoint_truth_falsity (φ : BilatInqProp W) : Disjoint φ.truth φ.falsity :=
  Set.disjoint_left.2 fun w ht hf ↦
    Set.singleton_ne_empty w (φ.no_overlap {w} (mem_truth_iff.1 ht) (mem_falsity_iff.1 hf))

/-- **Booth Def 14, ¬-clause**: negation swaps the two interpretations, the product's negation
`ᶜ`. -/
def negate (φ : BilatInqProp W) : BilatInqProp W := ⟨φ.1ᶜ, φ.2.symm⟩

@[simp] theorem negate_pos (φ : BilatInqProp W) : φ.negate.pos = φ.neg := rfl
@[simp] theorem negate_neg (φ : BilatInqProp W) : φ.negate.neg = φ.pos := rfl
@[simp] theorem truth_negate (φ : BilatInqProp W) : φ.negate.truth = φ.falsity := rfl
@[simp] theorem falsity_negate (φ : BilatInqProp W) : φ.negate.falsity = φ.truth := rfl

/-- Fact 3, double negation. -/
@[simp] theorem negate_negate (φ : BilatInqProp W) : φ.negate.negate = φ := rfl

/-- **Booth Def 14, atomic clause**: `⟦p⟧⁺ = ↓{V(p)}` and `⟦p⟧⁻ = ↓{W ∖ V(p)}`. -/
def atom (V : Set W) : BilatInqProp W :=
  mk (Question.ofSet V) (Question.ofSet Vᶜ) fun _ hpos hneg ↦
    Set.subset_empty_iff.mp (Set.inter_compl_self V ▸ Set.subset_inter hpos hneg)

@[simp] theorem atom_pos (V : Set W) : (atom V).pos = Question.ofSet V := rfl
@[simp] theorem atom_neg (V : Set W) : (atom V).neg = Question.ofSet Vᶜ := rfl
@[simp] theorem truth_atom (V : Set W) : (atom V).truth = V := Question.info_ofSet V
@[simp] theorem falsity_atom (V : Set W) : (atom V).falsity = Vᶜ := Question.info_ofSet Vᶜ

/-- **Booth Def 14, ∨-clause**: `⟦φ ∨ ψ⟧⁺ = ⟦φ⟧⁺ ∪ ⟦ψ⟧⁺` (inquisitive disjunction, `⊔` of
`Question`s) and `⟦φ ∨ ψ⟧⁻ = ⟦φ⟧⁻ ∩ ⟦ψ⟧⁻` (`⊓`): the truth join of the product. -/
def disj (φ ψ : BilatInqProp W) : BilatInqProp W :=
  ⟨φ.1 ⊔ ψ.1, Product.disjoint_pro_con_sup φ.2 ψ.2⟩

/-- **Booth Def 14, ∧-clause**: `⟦φ ∧ ψ⟧⁺ = ⟦φ⟧⁺ ∩ ⟦ψ⟧⁺` and `⟦φ ∧ ψ⟧⁻ = ⟦φ⟧⁻ ∪ ⟦ψ⟧⁻`: the
truth meet of the product. -/
def conj (φ ψ : BilatInqProp W) : BilatInqProp W :=
  ⟨φ.1 ⊓ ψ.1, Product.disjoint_pro_con_inf φ.2 ψ.2⟩

@[simp] theorem disj_pos (φ ψ : BilatInqProp W) : (disj φ ψ).pos = φ.pos ⊔ ψ.pos := rfl
@[simp] theorem disj_neg (φ ψ : BilatInqProp W) : (disj φ ψ).neg = φ.neg ⊓ ψ.neg := rfl
@[simp] theorem conj_pos (φ ψ : BilatInqProp W) : (conj φ ψ).pos = φ.pos ⊓ ψ.pos := rfl
@[simp] theorem conj_neg (φ ψ : BilatInqProp W) : (conj φ ψ).neg = φ.neg ⊔ ψ.neg := rfl

@[simp] theorem truth_disj (φ ψ : BilatInqProp W) : (disj φ ψ).truth = φ.truth ∪ ψ.truth :=
  Question.info_sup _ _

@[simp] theorem falsity_disj (φ ψ : BilatInqProp W) :
    (disj φ ψ).falsity = φ.falsity ∩ ψ.falsity :=
  Question.info_inf _ _

theorem disj_comm (φ ψ : BilatInqProp W) : disj φ ψ = disj ψ φ :=
  Subtype.ext (sup_comm _ _)

/-- Booth lets `⟦φ ∧ ψ⟧ = ⟦¬(¬φ ∨ ¬ψ)⟧` (Def 14): a De Morgan law of the product. -/
theorem conj_eq_negate_disj (φ ψ : BilatInqProp W) :
    conj φ ψ = negate (disj (negate φ) (negate ψ)) :=
  rfl

/-- **Booth Def 14, □-clause**, over the relevant worlds `R : W → Set W` of Def 9:
`⟦□φ⟧⁺ = ↓{{w | R(w) ≠ ∅ and alt⁺(⟦φ⟧) m-covers R(w)}}` and
`⟦□φ⟧⁻ = ↓{{w | ∃ R' ⊆ R(w), R' ≠ ∅ and alt⁻(⟦φ⟧) m-covers R'}}`. -/
def necessity (R : W → Set W) (φ : BilatInqProp W) : BilatInqProp W :=
  mk (Question.ofSet {w | (R w).Nonempty ∧ IsMinCover (Question.alt φ.pos) (R w)})
    (Question.ofSet {w | ∃ R' ⊆ R w, R'.Nonempty ∧ IsMinCover (Question.alt φ.neg) R'})
    fun _ hpos hneg ↦ Set.eq_empty_of_forall_notMem fun w hw ↦ by
      obtain ⟨R', hR', ⟨v, hv⟩, hmc⟩ := hneg hw
      refine Set.singleton_ne_empty v (φ.no_overlap {v} ?_ ?_)
      · exact (Question.mem_info_iff_singleton_mem _ _).1
          (φ.pos.sUnion_alt_subset_info ((hpos hw).2.subset_sUnion (hR' hv)))
      · exact (Question.mem_info_iff_singleton_mem _ _).1
          (φ.neg.sUnion_alt_subset_info (hmc.subset_sUnion hv))

/-- **Booth Def 14, ◇-clause**: `⟦◇φ⟧ = ⟦¬□¬φ⟧`. -/
def possibility (R : W → Set W) (φ : BilatInqProp W) : BilatInqProp W :=
  negate (necessity R (negate φ))

theorem truth_necessity (R : W → Set W) (φ : BilatInqProp W) :
    (necessity R φ).truth = {w | (R w).Nonempty ∧ IsMinCover (Question.alt φ.pos) (R w)} :=
  Question.info_ofSet _

theorem falsity_necessity (R : W → Set W) (φ : BilatInqProp W) :
    (necessity R φ).falsity =
      {w | ∃ R' ⊆ R w, R'.Nonempty ∧ IsMinCover (Question.alt φ.neg) R'} :=
  Question.info_ofSet _

theorem truth_possibility (R : W → Set W) (φ : BilatInqProp W) :
    (possibility R φ).truth =
      {w | ∃ R' ⊆ R w, R'.Nonempty ∧ IsMinCover (Question.alt φ.pos) R'} :=
  Question.info_ofSet _

theorem falsity_possibility (R : W → Set W) (φ : BilatInqProp W) :
    (possibility R φ).falsity = {w | (R w).Nonempty ∧ IsMinCover (Question.alt φ.neg) (R w)} :=
  Question.info_ofSet _

/-- A Booth necessity is a Kratzerian one (Def 1): the relevant worlds lie in the truth set of
the prejacent. -/
theorem truth_necessity_subset (R : W → Set W) (φ : BilatInqProp W) :
    (necessity R φ).truth ⊆ {w | R w ⊆ φ.truth} := by
  rw [truth_necessity]
  exact fun _ h ↦ h.2.subset_sUnion.trans φ.pos.sUnion_alt_subset_info

end BilatInqProp

/-- **Booth Fact 1**: Kratzer's necessity, true at `w` when `R w ⊆ ⟦φ⟧` (Def 1), is upward
monotonic, so it validates the Ross inference. Booth's is not
(`BoothExample.not_monotone_necessity`). -/
theorem kratzer_monotone (R : W → Set W) : Monotone fun A : Set W ↦ {w | R w ⊆ A} :=
  fun _ _ hAB _ hw ↦ hw.trans hAB

open BilatInqProp

/-- **Booth Def 15**, the accessibility update: `R^φ(w) = R(w) ∩ info ⟦φ⟧⁺`. -/
def updateAccess (R : W → Set W) (φ : BilatInqProp W) (w : W) : Set W :=
  R w ∩ φ.truth

/-! ### Alternatives and non-Hurford disjunctions (Defs 13 and 22) -/

theorem alt_atom_pos (V : Set W) : Question.alt (atom V).pos = {V} :=
  Question.alt_ofSet V

theorem alt_atom_neg (V : Set W) : Question.alt (atom V).neg = {Vᶜ} :=
  Question.alt_ofSet Vᶜ

/-- When no alternative of either disjunct is a state of the other, the alternatives of the
disjunction are those of the disjuncts. -/
theorem alt_disj_pos_eq_union {φ ψ : BilatInqProp W}
    (hφψ : Disjoint (Question.alt φ.pos) ψ.pos) (hψφ : Disjoint (Question.alt ψ.pos) φ.pos) :
    Question.alt (disj φ ψ).pos = Question.alt φ.pos ∪ Question.alt ψ.pos := by
  refine (Question.alt_sup_subset_union φ.pos ψ.pos).antisymm ?_
  rintro q (hq | hq)
  · exact Question.mem_alt_sup_of_alt_left hq fun r hr hqr ↦
      (Set.disjoint_left.1 hφψ hq (ψ.pos.downward_closed r hr q hqr)).elim
  · exact Question.mem_alt_sup_of_alt_right hq fun r hr hqr ↦
      (Set.disjoint_left.1 hψφ hq (φ.pos.downward_closed r hr q hqr)).elim

/-- **Booth Def 22**: `φ ∨ ψ` is non-Hurford when the positive interpretations of the disjuncts
are incomparable. -/
def NonHurford (φ ψ : BilatInqProp W) : Prop :=
  IncompRel (· ≤ ·) φ.pos ψ.pos

theorem NonHurford.symm {φ ψ : BilatInqProp W} (h : NonHurford φ ψ) : NonHurford ψ φ :=
  IncompRel.symm h

theorem nonHurford_atom_iff {Vp Vq : Set W} :
    NonHurford (atom Vp) (atom Vq) ↔ IncompRel (· ≤ ·) Vp Vq :=
  and_congr (not_congr Question.ofSet_le_ofSet_iff) (not_congr Question.ofSet_le_ofSet_iff)

theorem NonHurford.ne {Vp Vq : Set W} (h : NonHurford (atom Vp) (atom Vq)) : Vp ≠ Vq :=
  fun e ↦ (nonHurford_atom_iff.1 h).1 e.le

/-- For non-Hurford atoms, `alt⁺(⟦p ∨ q⟧) = {V(p), V(q)}` (§3.2). -/
theorem alt_disj_atom {Vp Vq : Set W} (h : NonHurford (atom Vp) (atom Vq)) :
    Question.alt (disj (atom Vp) (atom Vq)).pos = {Vp, Vq} :=
  Question.alt_ofSet_sup_ofSet (nonHurford_atom_iff.1 h).1 (nonHurford_atom_iff.1 h).2

/-- `alt⁻(⟦p ∨ q⟧) = {W ∖ (V(p) ∪ V(q))}` (§3.2). -/
theorem alt_disj_atom_neg (Vp Vq : Set W) :
    Question.alt (disj (atom Vp) (atom Vq)).neg = {Vpᶜ ∩ Vqᶜ} := by
  rw [disj_neg, atom_neg, atom_neg, Question.ofSet_inf, Question.alt_ofSet]

/-- `alt⁺(⟦p ∧ ¬q⟧) = {V(p) ∖ V(q)}`. -/
theorem alt_conj_atom_negate (Vp Vq : Set W) :
    Question.alt (conj (atom Vp) (negate (atom Vq))).pos = {Vp ∩ Vqᶜ} := by
  rw [conj_pos, negate_pos, atom_pos, atom_neg, Question.ofSet_inf, Question.alt_ofSet]

/-! ### The language (Def 8) and compactness (Fact 5) -/

/-- The language of Def 8 over atomic sentences `At`. -/
inductive Formula (At : Type*) where
  | atom (p : At)
  | neg (φ : Formula At)
  | conj (φ ψ : Formula At)
  | disj (φ ψ : Formula At)
  | cond (φ ψ : Formula At)
  | box (φ : Formula At)
  | diamond (φ : Formula At)

namespace Formula

variable {At : Type*}

/-- **Booth Def 14** in the model `⟨W, R, V⟩` of Def 9. The restrictor conditional evaluates its
consequent under the updated accessibility, `⟦φ → ψ⟧_M = ⟦ψ⟧_{M^φ}` (Def 16). Every sentence
denotes a bilateral inquisitive proposition by construction, which is Fact 4. -/
def eval (V : At → Set W) : (W → Set W) → Formula At → BilatInqProp W
  | _, atom p => BilatInqProp.atom (V p)
  | R, neg φ => (eval V R φ).negate
  | R, conj φ ψ => (eval V R φ).conj (eval V R ψ)
  | R, disj φ ψ => (eval V R φ).disj (eval V R ψ)
  | R, cond φ ψ => eval V (updateAccess R (eval V R φ)) ψ
  | R, box φ => necessity R (eval V R φ)
  | R, diamond φ => possibility R (eval V R φ)

/-- **Booth Fact 3**, double negation. -/
theorem eval_neg_neg (V : At → Set W) (R : W → Set W) (φ : Formula At) :
    eval V R (neg (neg φ)) = eval V R φ :=
  rfl

/-- **Booth Fact 5**, compactness of alternatives: both interpretations of a sentence are
finitely generated, so each has finitely many alternatives and is generated by them,
`⟦φ⟧° = ↓alt°(⟦φ⟧)` (`Question.fg_iff_finite_alt_and_isNormal`). -/
theorem fg_eval (V : At → Set W) (R : W → Set W) (φ : Formula At) :
    (eval V R φ).pos.FG ∧ (eval V R φ).neg.FG := by
  induction φ generalizing R with
  | atom p => exact ⟨Question.fg_ofSet _, Question.fg_ofSet _⟩
  | neg φ ih => exact (ih R).symm
  | conj φ ψ ihφ ihψ => exact ⟨(ihφ R).1.inf (ihψ R).1, (ihφ R).2.sup (ihψ R).2⟩
  | disj φ ψ ihφ ihψ => exact ⟨(ihφ R).1.sup (ihψ R).1, (ihφ R).2.inf (ihψ R).2⟩
  | cond φ ψ _ ihψ => exact ihψ _
  | box φ _ => exact ⟨Question.fg_ofSet _, Question.fg_ofSet _⟩
  | diamond φ _ => exact ⟨Question.fg_ofSet _, Question.fg_ofSet _⟩

end Formula

/-! ### The meta-language Facts 6 and 7

Booth states both facts for every non-Hurford disjunction (Def 22). Their proofs use that no
alternative of either disjunct is a state of the other, which is strictly stronger; the facts hold
under that condition and fail under Def 22. -/

/-- **Booth Fact 7** (the Ross inference is strongly invalid) under the alternative-wise
non-Hurford condition, once `ψ` has an alternative: `alt⁺(⟦φ⟧)` is then a proper subfamily of
`alt⁺(⟦φ ∨ ψ⟧)` that still covers the relevant worlds. -/
theorem ross_strongly_invalid_of_alt {φ ψ : BilatInqProp W}
    (hφψ : Disjoint (Question.alt φ.pos) ψ.pos) (hψφ : Disjoint (Question.alt ψ.pos) φ.pos)
    (hψ : (Question.alt ψ.pos).Nonempty) (R : W → Set W) :
    Disjoint (necessity R φ).truth (necessity R (disj φ ψ)).truth := by
  refine Set.disjoint_left.2 fun w h₁ h₂ ↦ ?_
  rw [truth_necessity, Set.mem_ofPred_eq] at h₁ h₂
  rw [alt_disj_pos_eq_union hφψ hψφ] at h₂
  obtain ⟨b, hb⟩ := hψ
  exact Set.disjoint_left.1 hψφ hb (Question.mem_of_mem_alt
    (h₂.2.le_of_le h₁.2.subset_sUnion Set.subset_union_left (Set.mem_union_right _ hb)))

/-- **Booth Fact 6** (Independence, meta-language) under the alternative-wise non-Hurford
condition: if `□(φ ∨ ψ)` is true, some relevant world is in the truth set of `φ` but not of `ψ`.
The alternatives other than a chosen alternative of `φ` fail to cover the relevant worlds, and the
world they miss lies in no state of `ψ`. -/
theorem inter_diff_truth_nonempty_of_alt {φ ψ : BilatInqProp W}
    (hφψ : Disjoint (Question.alt φ.pos) ψ.pos) (hψφ : Disjoint (Question.alt ψ.pos) φ.pos)
    (hφ : (Question.alt φ.pos).Nonempty) (hψ : ψ.pos.IsNormal) {R : W → Set W} {w : W}
    (h : w ∈ (necessity R (disj φ ψ)).truth) : (R w ∩ (φ.truth \ ψ.truth)).Nonempty := by
  rw [truth_necessity, Set.mem_ofPred_eq, alt_disj_pos_eq_union hφψ hψφ] at h
  obtain ⟨a, ha⟩ := hφ
  obtain ⟨v, hvR, hv⟩ := Set.not_subset.1 fun hcov ↦
    (h.2.le_of_le hcov Set.sdiff_subset (Set.mem_union_left _ ha)).2 rfl
  obtain ⟨c, hc, hvc⟩ := h.2.subset_sUnion hvR
  have hva : v ∈ a := by
    by_contra hva
    exact hv ⟨c, ⟨hc, fun hca ↦ hva (hca ▸ hvc)⟩, hvc⟩
  refine ⟨v, hvR, Question.subset_info_of_mem (Question.mem_of_mem_alt ha) hva, ?_⟩
  rintro ⟨s, hs, hvs⟩
  obtain ⟨b, hb, hsb⟩ := hψ s hs
  exact hv ⟨b, ⟨.inr hb, fun hba ↦
    Set.disjoint_left.1 hφψ ha (hba ▸ Question.mem_of_mem_alt hb)⟩, hsb hvs⟩

namespace Formula

variable {At : Type*} {V : At → Set W} {R : W → Set W} {φ ψ : Formula At}

/-- **Booth Fact 7** for sentences under the alternative-wise non-Hurford condition; Fact 5
supplies the alternative of `ψ`. -/
theorem ross_strongly_invalid (hφψ : Disjoint (Question.alt (eval V R φ).pos) (eval V R ψ).pos)
    (hψφ : Disjoint (Question.alt (eval V R ψ).pos) (eval V R φ).pos) :
    Disjoint (eval V R (box φ)).truth (eval V R (box (disj φ ψ))).truth :=
  ross_strongly_invalid_of_alt hφψ hψφ (fg_eval V R ψ).1.isNormal.alt_nonempty R

/-- **Booth Fact 6** for sentences under the alternative-wise non-Hurford condition; Fact 5
supplies the alternatives and the normality of the disjuncts. -/
theorem independence (hφψ : Disjoint (Question.alt (eval V R φ).pos) (eval V R ψ).pos)
    (hψφ : Disjoint (Question.alt (eval V R ψ).pos) (eval V R φ).pos) {w : W}
    (h : w ∈ (eval V R (box (disj φ ψ))).truth) :
    (R w ∩ ((eval V R φ).truth \ (eval V R ψ).truth)).Nonempty ∧
      (R w ∩ ((eval V R ψ).truth \ (eval V R φ).truth)).Nonempty := by
  have hφ := (fg_eval V R φ).1.isNormal
  have hψ := (fg_eval V R ψ).1.isNormal
  refine ⟨inter_diff_truth_nonempty_of_alt hφψ hψφ hφ.alt_nonempty hψ h,
    inter_diff_truth_nonempty_of_alt hψφ hφψ hψ.alt_nonempty hφ ?_⟩
  rw [BilatInqProp.disj_comm]
  exact h

end Formula

/-- **Booth Fact 7** as printed, for every non-Hurford disjunction of Def 22, is false: with
worlds `0, 1, 2`, `φ = r₁ ∨ r₂` for `V(r₁) = {0}`, `V(r₂) = {1}`, `ψ = q` for `V(q) = {0, 2}` and
`R(0) = {0, 1}`, both `□φ` and `□(φ ∨ ψ)` are true at `0`. The alternative `{0}` of `φ` is a state
of `ψ`, which the paper's proof overlooks. -/
theorem not_forall_disjoint_of_nonHurford :
    ¬ ∀ (W : Type) (R : W → Set W) (φ ψ : BilatInqProp W), NonHurford φ ψ →
      Disjoint (necessity R φ).truth (necessity R (disj φ ψ)).truth := by
  intro hall
  have h01 : NonHurford (atom ({0} : Set (Fin 3))) (atom {1}) := nonHurford_atom_iff.2
    ⟨fun h ↦ by simpa using h (Set.mem_singleton 0), fun h ↦ by simpa using h (Set.mem_singleton 1)⟩
  have hNH : NonHurford (disj (atom ({0} : Set (Fin 3))) (atom {1})) (atom {0, 2}) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have : ({1} : Set (Fin 3)) ∈ (atom ({0, 2} : Set (Fin 3))).pos := h (by simp)
      simp at this
    · have : ({0, 2} : Set (Fin 3)) ∈ (disj (atom {0}) (atom ({1} : Set (Fin 3)))).pos :=
        h (by simp)
      simp at this
  have hpos : (disj (disj (atom {0}) (atom {1})) (atom ({0, 2} : Set (Fin 3)))).pos =
      Question.ofSet {0, 2} ⊔ Question.ofSet {1} := by
    simp only [disj_pos, atom_pos]
    rw [sup_right_comm, sup_eq_right.2 (Question.ofSet_le_ofSet_iff.2 (by simp))]
  have hne : ({0, 2} : Set (Fin 3)) ≠ {1} := fun h ↦
    absurd (h ▸ (show (0 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) by simp)) (by simp)
  refine Set.disjoint_left.1 (hall (Fin 3) (fun _ ↦ {0, 1}) _ _ hNH)
    (show (0 : Fin 3) ∈ _ from ?_) ?_
  · rw [truth_necessity, Set.mem_ofPred_eq, alt_disj_atom h01, isMinCover_pair_iff h01.ne]
    refine ⟨⟨0, by simp⟩, ?_, ?_, ?_⟩ <;> simp [Set.insert_subset_iff]
  · rw [truth_necessity, Set.mem_ofPred_eq, hpos, Question.alt_ofSet_sup_ofSet (by simp) (by simp),
      isMinCover_pair_iff hne]
    refine ⟨⟨0, by simp⟩, ?_, ?_, ?_⟩ <;> simp [Set.insert_subset_iff]

/-- **Booth Fact 6** as printed, for every non-Hurford disjunction of Def 22, is false: with
worlds `0, 1, 2`, `φ = r` for `V(r) = {0, 1}`, `ψ = p ∨ q` for `V(p) = {0}`, `V(q) = {1, 2}` and
`R(0) = W`, `□(φ ∨ ψ)` is true at `0` but every world in the truth set of `φ` is in that of `ψ`. -/
theorem not_forall_independence_of_nonHurford :
    ¬ ∀ (W : Type) (R : W → Set W) (φ ψ : BilatInqProp W), NonHurford φ ψ →
      ∀ w ∈ (necessity R (disj φ ψ)).truth,
        (R w ∩ (φ.truth \ ψ.truth)).Nonempty ∧ (R w ∩ (ψ.truth \ φ.truth)).Nonempty := by
  intro hall
  have hNH : NonHurford (atom ({0, 1} : Set (Fin 3))) (disj (atom {0}) (atom {1, 2})) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have : ({0, 1} : Set (Fin 3)) ∈ (disj (atom {0}) (atom ({1, 2} : Set (Fin 3)))).pos :=
        h (by simp)
      simp [Set.insert_subset_iff] at this
    · have : ({1, 2} : Set (Fin 3)) ∈ (atom ({0, 1} : Set (Fin 3))).pos := h (by simp)
      simp [Set.insert_subset_iff] at this
  have hpos : (disj (atom ({0, 1} : Set (Fin 3))) (disj (atom {0}) (atom {1, 2}))).pos =
      Question.ofSet {0, 1} ⊔ Question.ofSet {1, 2} := by
    simp only [disj_pos, atom_pos]
    rw [← sup_assoc, sup_eq_left.2 (Question.ofSet_le_ofSet_iff.2 (by simp))]
  have hne : ({0, 1} : Set (Fin 3)) ≠ {1, 2} := fun h ↦
    absurd (h ▸ (show (0 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) by simp)) (by simp)
  have hbox : (0 : Fin 3) ∈ (necessity (fun _ ↦ Set.univ)
      (disj (atom ({0, 1} : Set (Fin 3))) (disj (atom {0}) (atom {1, 2})))).truth := by
    rw [truth_necessity, Set.mem_ofPred_eq, hpos, Question.alt_ofSet_sup_ofSet
      (by simp [Set.insert_subset_iff]) (by simp [Set.insert_subset_iff]), isMinCover_pair_iff hne]
    refine ⟨⟨0, trivial⟩, fun x _ ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
    · fin_cases x <;> simp
    · simpa using h (Set.mem_univ 2)
    · simpa using h (Set.mem_univ 0)
  obtain ⟨x, hx⟩ := (hall (Fin 3) (fun _ ↦ Set.univ) _ _ hNH 0 hbox).1
  fin_cases x <;> simp at hx

/-! ### The object-language Facts 7–13 -/

section Atomic

variable (R : W → Set W) {Vp Vq : Set W}

/-- **Booth Fact 7** for atoms: the Ross inference `□p ∴ □(p ∨ q)` is strongly invalid. -/
theorem ross_strongly_invalid (h : NonHurford (atom Vp) (atom Vq)) :
    Disjoint (necessity R (atom Vp)).truth (necessity R (disj (atom Vp) (atom Vq))).truth := by
  obtain ⟨hpq, hqp⟩ := nonHurford_atom_iff.1 h
  refine ross_strongly_invalid_of_alt ?_ ?_ ?_ R
  · simpa [alt_atom_pos] using hpq
  · simpa [alt_atom_pos] using hqp
  · simp

/-- **Booth Fact 8**: the Extended Ross inference `□p, ◇q ∴ □(p ∨ q)` is strongly invalid. -/
theorem extended_ross_strongly_invalid (h : NonHurford (atom Vp) (atom Vq)) :
    Disjoint ((necessity R (atom Vp)).truth ∩ (possibility R (atom Vq)).truth)
      (necessity R (disj (atom Vp) (atom Vq))).truth :=
  (ross_strongly_invalid R h).mono_left Set.inter_subset_left

/-- **Booth Fact 9**, first Independence inference: `□(p ∨ q)` entails `◇(p ∧ ¬q)`. -/
theorem independence_left (h : NonHurford (atom Vp) (atom Vq)) :
    (necessity R (disj (atom Vp) (atom Vq))).truth ⊆
      (possibility R (conj (atom Vp) (negate (atom Vq)))).truth := by
  intro w hw
  rw [truth_necessity, Set.mem_ofPred_eq, alt_disj_atom h, isMinCover_pair_iff h.ne] at hw
  obtain ⟨v, hvR, hvq⟩ := Set.not_subset.1 hw.2.2.2
  rw [truth_possibility, Set.mem_ofPred_eq, alt_conj_atom_negate]
  exact ⟨{v}, Set.singleton_subset_iff.2 hvR, Set.singleton_nonempty v,
    (isMinCover_singleton_iff (Set.singleton_nonempty v)).2
      (Set.singleton_subset_iff.2 ⟨(hw.2.1 hvR).resolve_right hvq, hvq⟩)⟩

/-- **Booth Fact 9**, second Independence inference: `□(p ∨ q)` entails `◇(q ∧ ¬p)`. -/
theorem independence_right (h : NonHurford (atom Vp) (atom Vq)) :
    (necessity R (disj (atom Vp) (atom Vq))).truth ⊆
      (possibility R (conj (atom Vq) (negate (atom Vp)))).truth := by
  rw [disj_comm]
  exact independence_left R h.symm

/-- **Booth Fact 10**, Free Choice: `◇(p ∨ q)` entails `◇p`. -/
theorem free_choice_left (h : NonHurford (atom Vp) (atom Vq)) :
    (possibility R (disj (atom Vp) (atom Vq))).truth ⊆ (possibility R (atom Vp)).truth := by
  simp only [truth_possibility, Set.ofPred_subset_ofPred]
  rintro w ⟨R', hR', -, hmc⟩
  rw [alt_disj_atom h, isMinCover_pair_iff h.ne] at hmc
  obtain ⟨v, hv, hvq⟩ := Set.not_subset.1 hmc.2.2
  rw [alt_atom_pos]
  exact ⟨{v}, Set.singleton_subset_iff.2 (hR' hv), Set.singleton_nonempty v,
    (isMinCover_singleton_iff (Set.singleton_nonempty v)).2
      (Set.singleton_subset_iff.2 ((hmc.1 hv).resolve_right hvq))⟩

/-- **Booth Fact 10**, Free Choice: `◇(p ∨ q)` entails `◇q`. -/
theorem free_choice_right (h : NonHurford (atom Vp) (atom Vq)) :
    (possibility R (disj (atom Vp) (atom Vq))).truth ⊆ (possibility R (atom Vq)).truth := by
  rw [disj_comm]
  exact free_choice_left R h.symm

/-- **Booth Fact 12**, Unnecessity Distribution: `¬□(p ∨ q)` entails `¬□p`. -/
theorem unnecessity_distribution_left (Vp Vq : Set W) :
    (necessity R (disj (atom Vp) (atom Vq))).falsity ⊆ (necessity R (atom Vp)).falsity := by
  simp only [falsity_necessity, Set.ofPred_subset_ofPred]
  rintro w ⟨R', hR', hne, hmc⟩
  rw [alt_disj_atom_neg, isMinCover_singleton_iff hne] at hmc
  rw [alt_atom_neg]
  exact ⟨R', hR', hne, (isMinCover_singleton_iff hne).2 (hmc.trans Set.inter_subset_left)⟩

/-- **Booth Fact 12**, Unnecessity Distribution: `¬□(p ∨ q)` entails `¬□q`. -/
theorem unnecessity_distribution_right (Vp Vq : Set W) :
    (necessity R (disj (atom Vp) (atom Vq))).falsity ⊆ (necessity R (atom Vq)).falsity := by
  rw [disj_comm]
  exact unnecessity_distribution_left R Vq Vp

/-- **Booth Fact 13**, Impossibility Distribution: `¬◇(p ∨ q)` entails `¬◇p`. -/
theorem impossibility_distribution_left (Vp Vq : Set W) :
    (possibility R (disj (atom Vp) (atom Vq))).falsity ⊆ (possibility R (atom Vp)).falsity := by
  simp only [falsity_possibility, Set.ofPred_subset_ofPred]
  rintro w ⟨hne, hmc⟩
  rw [alt_disj_atom_neg, isMinCover_singleton_iff hne] at hmc
  rw [alt_atom_neg]
  exact ⟨hne, (isMinCover_singleton_iff hne).2 (hmc.trans Set.inter_subset_left)⟩

/-- **Booth Fact 13**, Impossibility Distribution: `¬◇(p ∨ q)` entails `¬◇q`. -/
theorem impossibility_distribution_right (Vp Vq : Set W) :
    (possibility R (disj (atom Vp) (atom Vq))).falsity ⊆ (possibility R (atom Vq)).falsity := by
  rw [disj_comm]
  exact impossibility_distribution_left R Vq Vp

end Atomic

namespace Formula

variable {At : Type*} (V : At → Set W) (R : W → Set W) {p q : At}

/-- **Booth Fact 11**, Independence Conditionals: `□(p ∨ q)` entails `¬p → □q`, whose truth is
that of `□q` under the accessibility updated with `¬p`. -/
theorem independence_conditional_left (h : NonHurford (.atom (V p)) (.atom (V q))) :
    (eval V R (box (disj (atom p) (atom q)))).truth ⊆
      (eval V R (cond (neg (atom p)) (box (atom q)))).truth := by
  intro w hw
  simp only [eval, truth_necessity, Set.mem_ofPred_eq] at hw ⊢
  rw [alt_disj_atom h, isMinCover_pair_iff h.ne] at hw
  have hR : updateAccess R (BilatInqProp.atom (V p)).negate w = R w \ V p := by
    simp [updateAccess, Set.sdiff_eq]
  have hne : (R w \ V p).Nonempty := Set.sdiff_nonempty.2 hw.2.2.1
  rw [hR, alt_atom_pos, isMinCover_singleton_iff hne]
  exact ⟨hne, fun v hv ↦ (hw.2.1 hv.1).resolve_left hv.2⟩

/-- **Booth Fact 11**, Independence Conditionals: `□(p ∨ q)` entails `¬q → □p`. -/
theorem independence_conditional_right (h : NonHurford (.atom (V p)) (.atom (V q))) :
    (eval V R (box (disj (atom p) (atom q)))).truth ⊆
      (eval V R (cond (neg (atom q)) (box (atom p)))).truth := by
  change (necessity R (.disj (.atom (V p)) (.atom (V q)))).truth ⊆ _
  rw [BilatInqProp.disj_comm]
  exact independence_conditional_left V R h.symm

end Formula

/-! ### Booth's Figures 1 and 2

Four worlds, the valuations of `p` and `q` over `Bool × Bool`. Where the relevant worlds are the
three `p ∨ q`-worlds, `{V(p), V(q)}` minimally covers them, as in Figure 2 (Independence), so
`□(p ∨ q)` and, by Fact 9, `◇(p ∧ ¬q)` are true. Where they are the two `p`-worlds, the pair is a
super cover but not a minimal one, as in Figure 1 (Diversity without Independence): the
Kratzerian `□(p ∨ q)` and the Diversity inferences hold, but Booth's `□(p ∨ q)` does not, while
the premises `□p` and `◇q` of the Extended Ross argument are true. -/

namespace BoothExample

/-- Worlds: the truth values of `p` and `q`. -/
abbrev W4 := Bool × Bool

/-- `p` is true at the worlds whose first coordinate is `true`. -/
def vp : Set W4 := {w | w.1 = true}

/-- `q` is true at the worlds whose second coordinate is `true`. -/
def vq : Set W4 := {w | w.2 = true}

/-- The relevant worlds are the three where `p ∨ q` is true. -/
def r₃ : W4 → Set W4 := fun _ ↦ vp ∪ vq

/-- The relevant worlds are the two where `p` is true. -/
def rP : W4 → Set W4 := fun _ ↦ vp

theorem nonHurford : NonHurford (atom vp) (atom vq) :=
  nonHurford_atom_iff.2 ⟨fun h ↦ absurd (h (show (true, false) ∈ vp from rfl)) (by simp [vq]),
    fun h ↦ absurd (h (show (false, true) ∈ vq from rfl)) (by simp [vp])⟩

/-- Figure 2: `{V(p), V(q)}` minimally covers the three `p ∨ q`-worlds. -/
theorem isMinCover_r₃ : IsMinCover {vp, vq} (r₃ (true, true)) := by
  rw [isMinCover_pair_iff nonHurford.ne]
  refine ⟨subset_rfl, fun h ↦ ?_, fun h ↦ ?_⟩
  · exact absurd (h (show (false, true) ∈ r₃ (true, true) from .inr rfl)) (by simp [vp])
  · exact absurd (h (show (true, false) ∈ r₃ (true, true) from .inl rfl)) (by simp [vq])

theorem box_pOrQ : (true, true) ∈ (necessity r₃ (disj (atom vp) (atom vq))).truth := by
  rw [truth_necessity, Set.mem_ofPred_eq, alt_disj_atom nonHurford]
  exact ⟨⟨(true, true), .inl rfl⟩, isMinCover_r₃⟩

theorem diamond_pAndNotQ :
    (true, true) ∈ (possibility r₃ (conj (atom vp) (negate (atom vq)))).truth :=
  independence_left r₃ nonHurford box_pOrQ

/-- Figure 1: on the two `p`-worlds `{V(p), V(q)}` is a super cover but not a minimal one, so
the Diversity inferences hold and the Independence inferences fail. -/
theorem diversity_without_independence :
    IsSuperCover {vp, vq} (rP (true, true)) ∧ ¬ IsMinCover {vp, vq} (rP (true, true)) :=
  ⟨isSuperCover_pair_iff.2 ⟨Set.subset_union_left, ⟨(true, true), rfl, rfl⟩,
    ⟨(true, true), rfl, rfl⟩⟩, fun h ↦ ((isMinCover_pair_iff nonHurford.ne).1 h).2.1 subset_rfl⟩

/-- On the two `p`-worlds `□p` is true. -/
theorem box_p : (true, true) ∈ (necessity rP (atom vp)).truth := by
  rw [truth_necessity, Set.mem_ofPred_eq, alt_atom_pos,
    isMinCover_singleton_iff ⟨(true, true), show (true, true) ∈ rP (true, true) from rfl⟩]
  exact ⟨⟨(true, true), rfl⟩, subset_rfl⟩

/-- On the two `p`-worlds `◇q` is true. -/
theorem diamond_q : (true, true) ∈ (possibility rP (atom vq)).truth := by
  rw [truth_possibility, Set.mem_ofPred_eq, alt_atom_pos]
  exact ⟨{(true, true)}, Set.singleton_subset_iff.2 rfl, Set.singleton_nonempty _,
    (isMinCover_singleton_iff (Set.singleton_nonempty _)).2 (Set.singleton_subset_iff.2 rfl)⟩

/-- On the two `p`-worlds Booth's `□(p ∨ q)` is false, by Fact 7, since `□p` is true there. -/
theorem not_box_pOrQ : (true, true) ∉ (necessity rP (disj (atom vp) (atom vq))).truth :=
  Set.disjoint_left.1 (ross_strongly_invalid rP nonHurford) box_p

/-- On the two `p`-worlds the Kratzerian `□(p ∨ q)` of Def 1 is true: they lie in the truth set
of `p ∨ q`. -/
theorem kratzer_box_pOrQ : rP (true, true) ⊆ (disj (atom vp) (atom vq)).truth := by
  simp [rP]

/-- Booth's necessity is not upward monotonic, unlike Kratzer's (Fact 1, `kratzer_monotone`):
`⟦p⟧ ⊆ ⟦p ∨ q⟧`, yet on the two `p`-worlds `□p` is true and `□(p ∨ q)` false. -/
theorem not_monotone_necessity :
    ¬ ∀ φ ψ : BilatInqProp W4, φ.truth ⊆ ψ.truth →
      (necessity rP φ).truth ⊆ (necessity rP ψ).truth :=
  fun h ↦ not_box_pOrQ (h _ _ (by simp) box_p)

end BoothExample

end Booth2022
