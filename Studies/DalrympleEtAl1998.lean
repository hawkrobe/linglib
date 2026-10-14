module

public import Linglib.Semantics.Plurality.Reciprocal
public import Linglib.Data.Examples.DalrympleEtAl1998
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Bounds.Defs

/-!
# Dalrymple, Kanazawa, Kim, Mchombo and Peters (1998): Reciprocal Expressions and the Concept of Reciprocity

The reciprocal has one meaning that varies with context. It ranges over six quantifiers, the
settings of two parameters (`Reciprocal.Recip`). By the Strongest Meaning Hypothesis a reciprocal
sentence is felicitous in a context when, among its interpretations consistent with the
non-linguistic information, one entails all the others, and the sentence then expresses that
one. Since the quantifiers are ordered by entailment as the product of the parameters, the
hypothesis selects the strongest setting consistent with the context (`isLeast_of_isGreatest`),
Strong Reciprocity whenever that is consistent (`isLeast_strong`). For *gave each other
measles*, asymmetry, acyclicity and catching measles once leave Intermediate Alternative
Reciprocity (`measles_isLeast`). The paper's two admitted failures follow as well. With two
members and an asymmetric relation the hypothesis makes the sentence felicitous whether the
paper marks it acceptable or not (`smh_mispredicts_taller`). For the staring pirates it predicts
Intermediate Reciprocity (`pirates_isLeast`), which a single-valued relation satisfies only
without eye contact, while the sentence allows eye contact (`pirates_eyeContact`).

## Implementation notes

A situation is an extension of the scope relation over a fixed antecedent set, so an
interpretation is the set of relations satisfying a quantifier, the non-linguistic information is
a set of relations, and entailment is inclusion. Each context is stated by the properties of the
relation the paper appeals to. The quantified antecedents of §7 are not formalized.

## References

* [dalrymple-et-al-1998]
-/

@[expose] public section

namespace DalrympleEtAl1998

open Reciprocal Relation

variable {A : Type*} {R : A → A → Prop} {X : Finset A} {I : Set (A → A → Prop)}

/-! ### The six quantifiers (§5) -/

/-- For a symmetric scope relation the direction parameter makes no difference, so the six
quantifiers reduce to three (§5.4). -/
theorem recip_alternative_iff [Std.Symm R] (c : Coverage) :
    Recip (c, .alternative) R X ↔ Recip (c, .plain) R X := by
  have : SymmGen R = R := funext₂ fun x y ↦ propext ⟨fun h ↦ h.elim id (symm_of R), .inl⟩
  cases c <;> simp only [Recip, Direction.rel, this]

/-! ### The Strongest Meaning Hypothesis (§6.2) -/

/-- The interpretation of *the Xs R each other* with the reciprocal read at setting `q` is the
set of extensions of the scope relation that make the sentence true. -/
def interpretation (X : Finset A) (q : Coverage × Direction) : Set (A → A → Prop) :=
  {R | Recip q R X}

/-- The interpretations consistent with the non-linguistic information `I`. By the Strongest
Meaning Hypothesis the sentence is felicitous in `I` when this set has a least element, and it
then expresses that one. -/
def candidates (X : Finset A) (I : Set (A → A → Prop)) : Set (Set (A → A → Prop)) :=
  {p | ∃ q, interpretation X q = p ∧ (p ∩ I).Nonempty}

theorem interpretation_antitone : Antitone (interpretation X) :=
  fun _ _ hq _ hR ↦ recip_antitone hq hR

theorem nonempty_inter_of_le {q q' : Coverage × Direction} (hq : q ≤ q')
    (h : (interpretation X q' ∩ I).Nonempty) : (interpretation X q ∩ I).Nonempty :=
  h.mono (Set.inter_subset_inter_left _ (interpretation_antitone hq))

/-- The hypothesis expresses the interpretation at the strongest setting consistent with the
context. -/
theorem isLeast_of_isGreatest {q : Coverage × Direction}
    (h : IsGreatest {q | (interpretation X q ∩ I).Nonempty} q) :
    IsLeast (candidates X I) (interpretation X q) :=
  ⟨⟨q, rfl, h.1⟩, by
    rintro _ ⟨q', rfl, hq'⟩
    exact interpretation_antitone (h.2 hq')⟩

/-- Whenever Strong Reciprocity is consistent with the context, the sentence expresses it, as
the legislators' sentence (95) does. -/
theorem isLeast_strong (h : ∃ R ∈ I, StrongReciprocity R X) :
    IsLeast (candidates X I) (interpretation X (.ful, .plain)) :=
  isLeast_of_isGreatest ⟨let ⟨R, hRI, hR⟩ := h; ⟨R, hR, hRI⟩, fun ⟨c, d⟩ _ ↦
    Prod.mk_le_mk.2 ⟨by cases c <;> decide, by cases d <;> decide⟩⟩

/-! ### Measles (§6.1) -/

/-- One-way Weak Reciprocity over finitely many members needs a cycle. If each third grader gave
another one measles, some of them passed it around in a circle (99). -/
theorem exists_transGen_of_oneWayWeak (h : OneWayWeakReciprocity R X) : ∃ x, TransGen R x x := by
  obtain ⟨hX, h⟩ := oneWayWeakReciprocity_iff.1 h
  by_contra! hcyc
  let r : X → X → Prop := fun a b ↦ TransGen R b.1 a.1
  have : IsTrans X r := ⟨fun _ _ _ hab hbc ↦ hbc.trans hab⟩
  have : Std.Irrefl r := ⟨fun a ↦ hcyc a.1⟩
  obtain ⟨m, -, hm⟩ := (Finite.wellFounded_of_trans_of_irrefl r).has_min Set.univ
    ⟨⟨_, hX.nonempty.choose_spec⟩, trivial⟩
  obtain ⟨y, hy, -, hR⟩ := h m.1 m.2
  exact hm ⟨y, hy⟩ trivial (.single hR)

/-- In the non-linguistic information for *gave each other measles*, a person catches measles
from at most one person, and measles is not passed around in a circle. -/
def measles : Set (A → A → Prop) :=
  {R | (∀ x x' y, R x y → R x' y → x = x') ∧ ∀ x, ¬ TransGen R x x}

theorem not_oneWayWeak_of_measles (hR : R ∈ measles) : ¬ OneWayWeakReciprocity R X := fun h ↦
  let ⟨x, hx⟩ := exists_transGen_of_oneWayWeak h
  hR.2 x hx

/-- With three or more students, Strong Alternative Reciprocity is false of measles, since the
last to catch it would have caught it from each of the others. -/
theorem not_strongAlternative_of_measles (hR : R ∈ measles) (hX : 3 ≤ X.card) :
    ¬ Recip (.ful, .alternative) R X := by
  classical
  intro h
  obtain ⟨z, hz, hlast⟩ : ∃ z ∈ X, ∀ y ∈ X, R z y → z = y := by
    by_contra! hall
    exact not_oneWayWeak_of_measles hR <| oneWayWeakReciprocity_iff.2
      ⟨Finset.one_lt_card_iff_nontrivial.1 (by omega), fun x hx ↦
        let ⟨y, hy, hxy, hne⟩ := hall x hx
        ⟨y, hy, hne, hxy⟩⟩
  have h' : StrongReciprocity (SymmGen R) X := h
  have hin {y} (hy : y ∈ X) (hyz : y ≠ z) : R y z :=
    Or.elim ((strongReciprocity_iff.1 h').2 hy hz hyz) id fun hzy ↦
      absurd (hlast y hy hzy).symm hyz
  obtain ⟨y, hy, hyz⟩ := X.exists_mem_ne (by omega) z
  obtain ⟨y', hy', hy'y⟩ := (X.erase z).exists_mem_ne
    (by have := Finset.pred_card_le_card_erase (s := X) (a := z); omega) y
  obtain ⟨hy'z, hy'X⟩ := Finset.mem_erase.1 hy'
  exact hy'y (hR.1 _ _ _ (hin hy'X hy'z) (hin hy hyz))

/-- One student giving measles to all the others is a measles situation in which Intermediate
Alternative Reciprocity holds. -/
theorem exists_intermediateAlternative_measles (hX : X.Nontrivial) {s : A} (hs : s ∈ X) :
    ∃ R ∈ measles, Recip (.lin, .alternative) R X := by
  refine ⟨fun x y ↦ x = s ∧ y ≠ s, ⟨fun x x' y hx hx' ↦ hx.1.trans hx'.1.symm, fun x hx ↦ ?_⟩, ?_⟩
  · obtain ⟨b, ⟨rfl, -⟩, -⟩ := TransGen.head'_iff.1 hx
    obtain ⟨c, -, -, hne⟩ := TransGen.tail'_iff.1 hx
    exact hne rfl
  · show IntermediateReciprocity (SymmGen fun x y ↦ x = s ∧ y ≠ s) X
    refine intermediateReciprocity_iff.2 ⟨hX, fun x hx y hy hxy ↦ ?_⟩
    by_cases hxs : x = s
    · exact .single ⟨hx, hy, .of_rel ⟨hxs, hxs ▸ hxy.symm⟩⟩
    by_cases hys : y = s
    · exact .single ⟨hx, hy, .of_rel_symm ⟨hys, hys ▸ hxy⟩⟩
    exact .tail (.single ⟨hx, hs, .of_rel_symm ⟨rfl, hxs⟩⟩) ⟨hs, hy, .of_rel ⟨rfl, hys⟩⟩

/-- With three or more students, *gave each other measles* expresses Intermediate Alternative
Reciprocity (98), since every stronger quantifier is inconsistent with the measles facts. -/
theorem measles_isLeast (hX : 3 ≤ X.card) :
    IsLeast (candidates X measles) (interpretation X (.lin, .alternative)) := by
  obtain ⟨s, hs⟩ := Finset.card_pos.1 (by omega : 0 < X.card)
  obtain ⟨R₀, hR₀, h₀⟩ :=
    exists_intermediateAlternative_measles (Finset.one_lt_card_iff_nontrivial.1 (by omega)) hs
  refine isLeast_of_isGreatest ⟨⟨R₀, h₀, hR₀⟩, ?_⟩
  have howr : ¬ (interpretation X (.tot, .plain) ∩ measles).Nonempty := fun ⟨R, h, hR⟩ ↦
    not_oneWayWeak_of_measles hR h
  rintro ⟨c, d⟩ h
  cases c <;> cases d
  all_goals first
    | decide
    | exact absurd (nonempty_inter_of_le (by decide) h) howr
    | exact absurd h fun ⟨R, h, hR⟩ ↦ not_strongAlternative_of_measles hR hX h

/-! ### Two members and an asymmetric relation (§6.3) -/

section Pair

variable [DecidableEq A]

/-- The non-linguistic information that the relation is asymmetric, as *on top of* and *taller
than* are. -/
def asymmetric : Set (A → A → Prop) :=
  {R | ∀ x y, R x y → ¬ R y x}

private theorem mem_pair (a b : A) {y : A} : y ∈ ({a, b} : Finset A) ↔ y = a ∨ y = b := by
  simp

/-- On two members the three alternative quantifiers agree, each saying that one member bears the
relation to the other. -/
theorem interpretation_pair_alternative {a b : A} (hab : a ≠ b) :
    interpretation {a, b} (.tot, .alternative) = interpretation {a, b} (.ful, .alternative) := by
  ext R
  show OneWayWeakReciprocity (SymmGen R) {a, b} ↔ StrongReciprocity (SymmGen R) {a, b}
  rw [oneWayWeakReciprocity_iff, strongReciprocity_iff, Finset.coe_pair, Set.pairwise_pair,
    imp_iff_right hab]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun ⟨hab', hba'⟩ x hx ↦ ?_⟩
  · obtain ⟨y, hy, hne, hay⟩ := h a (by simp)
    obtain rfl := ((mem_pair _ _).1 hy).resolve_left (Ne.symm hne)
    exact ⟨hay, hay.symm⟩
  · obtain rfl | rfl := (mem_pair _ _).1 hx
    · exact ⟨b, by simp, hab, hab'⟩
    · exact ⟨a, by simp, Ne.symm hab, hba'⟩

/-- With two members and an asymmetric relation, the sentence expresses that one member bears
the relation to the other, Inclusive Alternative Ordering, as for the bunk beds of (108). -/
theorem pair_isLeast {a b : A} (hab : a ≠ b) :
    IsLeast (candidates {a, b} asymmetric) (interpretation {a, b} (.tot, .alternative)) := by
  rw [interpretation_pair_alternative hab]
  refine isLeast_of_isGreatest ⟨⟨fun x y ↦ x = a ∧ y = b, ?_, ?_⟩, ?_⟩
  · show StrongReciprocity (SymmGen fun x y ↦ x = a ∧ y = b) {a, b}
    rw [strongReciprocity_iff, Finset.coe_pair, Set.pairwise_pair]
    exact ⟨Finset.one_lt_card_iff_nontrivial.1 (by rw [Finset.card_pair hab]; omega),
      fun _ ↦ ⟨.of_rel ⟨rfl, rfl⟩, .of_rel_symm ⟨rfl, rfl⟩⟩⟩
  · rintro x y ⟨rfl, rfl⟩ ⟨rfl, -⟩
    exact hab rfl
  have howr : ¬ (interpretation {a, b} (.tot, .plain) ∩ asymmetric).Nonempty := by
    rintro ⟨R, h, hR⟩
    have h' := (oneWayWeakReciprocity_iff (R := R) (X := {a, b})).1 h
    obtain ⟨y, hy, hne, hay⟩ := h'.2 a (by simp)
    obtain ⟨y', hy', hne', hby'⟩ := h'.2 b (by simp)
    obtain rfl := ((mem_pair _ _).1 hy).resolve_left (Ne.symm hne)
    obtain rfl := ((mem_pair _ _).1 hy').resolve_right (Ne.symm hne')
    exact hR _ _ hay hby'
  rintro ⟨c, d⟩ h
  cases c <;> cases d
  all_goals first
    | decide
    | exact absurd (nonempty_inter_of_le (by decide) h) howr

/-- The hypothesis cannot tell (108) from (109). With two members and an asymmetric relation it
makes both felicitous, but the paper marks (109) infelicitous. -/
theorem smh_mispredicts_taller {a b : A} (hab : a ≠ b) :
    (∃ p, IsLeast (candidates {a, b} asymmetric) p) ∧
      Examples.ex108.judgment = .acceptable ∧ Examples.ex109.judgment = .unacceptable :=
  ⟨⟨_, pair_isLeast hab⟩, rfl, rfl⟩

end Pair

/-! ### The staring pirates (§6.3) -/

/-- In the non-linguistic information for *staring at each other*, each stares at only one
other. -/
def singleValued : Set (A → A → Prop) :=
  {R | ∀ x y y', R x y → R x y' → y = y'}

/-- A single-valued relation is strongly alternative-reciprocal on at most three members, since
each pair of members needs an arrow of its own. -/
theorem card_le_three_of_singleValued (hR : R ∈ singleValued)
    (h : Recip (.ful, .alternative) R X) : X.card ≤ 3 := by
  classical
  let E := X.offDiag.filter fun p ↦ R p.1 p.2
  have hcover : X.offDiag ⊆ E ∪ E.image Prod.swap := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.1 hxy
    rcases (strongReciprocity_iff.1 (show StrongReciprocity (SymmGen R) X from h)).2 hx hy hne
      with hR' | hR'
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hxy, hR'⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2
        ⟨(y, x), Finset.mem_filter.2 ⟨Finset.mem_offDiag.2 ⟨hy, hx, hne.symm⟩, hR'⟩, rfl⟩)
  have hE : E.card ≤ X.card := Finset.card_le_card_of_injOn Prod.fst
    (fun p hp ↦ (Finset.mem_offDiag.1 (Finset.mem_filter.1 hp).1).1)
    fun p hp q hq hpq ↦ Prod.ext hpq
      (hR _ _ _ (Finset.mem_filter.1 hp).2 (hpq ▸ (Finset.mem_filter.1 hq).2))
  have := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  rw [Finset.offDiag_card] at this
  have := Finset.card_image_le (s := E) (f := Prod.swap)
  by_contra! hX
  have := Nat.mul_le_mul_right X.card (show 4 ≤ X.card by omega)
  generalize X.card * X.card = m at *
  omega

/-- With a single-valued relation, Intermediate Reciprocity over three or more members leaves no
two members bearing the relation to each other. A pirate who stares back at one staring at him
leaves some pirate out of the loop. -/
theorem not_mutual_of_intermediate (hR : R ∈ singleValued) (h : IntermediateReciprocity R X)
    (hX : 3 ≤ X.card) {a b : A} (ha : a ∈ X) (hab : R a b) (hba : R b a) : False := by
  classical
  have hreach (y) (hy : TransGen (fun u v ↦ u ∈ X ∧ v ∈ X ∧ R u v) a y) : y = a ∨ y = b := by
    induction hy with
    | single h => exact .inr (hR _ _ _ h.2.2 hab)
    | tail _ hcy ih =>
      rcases ih with rfl | rfl
      · exact .inr (hR _ _ _ hcy.2.2 hab)
      · exact .inl (hR _ _ _ hcy.2.2 hba)
  obtain ⟨c, hc⟩ : ((X.erase a).erase b).Nonempty := Finset.card_pos.1 (by
    have := Finset.pred_card_le_card_erase (s := X) (a := a)
    have := Finset.pred_card_le_card_erase (s := X.erase a) (a := b)
    omega)
  obtain ⟨hcb, hca, hcX⟩ : c ≠ b ∧ c ≠ a ∧ c ∈ X := by simpa using hc
  rcases hreach c ((intermediateReciprocity_iff.1 h).2 ha hcX hca.symm) with rfl | rfl
  · exact hca rfl
  · exact hcb rfl

/-- Four pirates, each staring at the next around a circle. -/
def stareRound (x y : Fin 4) : Prop := y = x + 1

/-- Four pirates in two pairs, each staring at the other of the pair. -/
def stareBack (x y : Fin 4) : Prop := x ≠ y ∧ x.val / 2 = y.val / 2

instance : DecidableRel stareBack := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem stareRound_intermediate : IntermediateReciprocity stareRound Finset.univ := by
  have step (x : Fin 4) :
      TransGen (fun a b ↦ a ∈ Finset.univ ∧ b ∈ Finset.univ ∧ stareRound a b) x (x + 1) :=
    .single ⟨Finset.mem_univ _, Finset.mem_univ _, rfl⟩
  refine intermediateReciprocity_iff.2 ⟨by decide, fun x _ y _ hxy ↦ ?_⟩
  obtain rfl | rfl | rfl : y = x + 1 ∨ y = x + 1 + 1 ∨ y = x + 1 + 1 + 1 := by
    revert x y; decide
  · exact step x
  · exact (step x).trans (step _)
  · exact ((step x).trans (step _)).trans (step _)

/-- With four pirates, the fewest for which the paper's argument excludes both quantifiers built
on `FUL`, *staring at each other* expresses Intermediate Reciprocity (110). -/
theorem pirates_isLeast :
    IsLeast (candidates (Finset.univ : Finset (Fin 4)) singleValued)
      (interpretation Finset.univ (.lin, .plain)) := by
  refine isLeast_of_isGreatest ⟨⟨stareRound, stareRound_intermediate, ?_⟩, ?_⟩
  · intro x y y' h h'
    exact h.trans h'.symm
  have hsar : ¬ (interpretation (Finset.univ : Finset (Fin 4)) (.ful, .alternative) ∩
      singleValued).Nonempty :=
    fun ⟨_, h, hR⟩ ↦ absurd (card_le_three_of_singleValued hR h) (by decide)
  rintro ⟨c, d⟩ h
  cases c <;> cases d
  all_goals first
    | decide
    | exact absurd (nonempty_inter_of_le (by decide) h) hsar

/-- The predicted meaning is too strong. When the four pirates stare at each other in two pairs,
every pirate is in eye contact and One-way Weak Reciprocity holds, the meaning the paper gives
(110), but Intermediate Reciprocity fails. -/
theorem pirates_eyeContact :
    stareBack ∈ singleValued ∧ OneWayWeakReciprocity stareBack Finset.univ ∧
      stareBack ∉ interpretation Finset.univ (.lin, .plain) := by
  have hR : stareBack ∈ singleValued := by
    show ∀ x y y' : Fin 4, stareBack x y → stareBack x y' → y = y'
    decide
  exact ⟨hR, by decide, fun h ↦ not_mutual_of_intermediate hR h (by decide)
    (Finset.mem_univ 0) (b := 1) (by decide) (by decide)⟩

end DalrympleEtAl1998
