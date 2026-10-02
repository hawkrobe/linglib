module

public import Linglib.Semantics.Exhaustification.Disjunctive
public import Linglib.Semantics.Exhaustification.PreExhaustified
public import Linglib.Studies.Haspelmath1997

/-!
# Chierchia (2006): Broaden your views

Chierchia treats every polarity-sensitive item as an existential that activates domain
alternatives, Kadmon and Landman's domain widening. An enrichment operation factors the
alternatives into meaning, and an implicature-freezing operator σ locks the result in place.
The items differ in two respects, (94): the size of their alternatives, large subdomains (MAX)
enriched by the even-like `evenEnrich` or every subdomain that stands a chance (MIN) enriched by
the antiexhaustive `oMinus`, and whether σ presupposes proper strengthening. Pure
negative-polarity items (*mai*, *ever*) are MAX; *any* is MIN with the plain σ; Italian
*qualsiasi* is MIN with the presuppositional σ; the existential free-choice items (*irgendein*,
*uno N qualsiasi*) add the uniqueness implicature of their indefinite morphology, after Kratzer
and Shimoyama.

## Main definitions

* `evenEnrich`: the even-like enrichment `E`, (108b).
* `oMinus`: the antiexhaustive enrichment `O⁻` of a domain-dependent proposition, (108c).
* `exactlyOne`, `atLeastTwo`: the exhaustified indefinite, (81b), and its scalar alternative.

## Main results

* `evenEnrich_eq_or_eq_empty`, `evenEnrich_disj_eq_empty`, `evenEnrich_image_antitone_eq`: `E` is
  vacuous or contradictory; it is contradictory at the existential and vacuous under negation,
  (47)–(53).
* `oMinus_subDisj`, `oMinus_subDisj_eq_inter_sInter`: `O⁻` gives an existential universal force
  over its domain, (63), and there agrees with the simpler (62).
* `oMinus_antitone_eq`, `not_properlyStrengthens_oMinus_antitone`: under negation the
  free-choice implicature vanishes, so *qualunque* has no negative-polarity construal, (65)–(72).
* `oMinus_preimage_subDisj`: under a possibility modal every member of the domain is an option.
* `exh_atLeastTwo_eq_exactlyOne`, `oMinus_exactlyOne_eq_empty`: `O` against the scalar
  alternative yields uniqueness, (81), and an existential free-choice item is then contradictory
  in an episodic sentence, (82).
* `oMinus_core_exactlyOne_subset`, `card_le_one_of_forall_mem_core_exactlyOne`: under a
  necessity modal `O⁻` yields free choice, (117), while letting the whole domain be an
  antecedent would leave room for a single doctor only, (118).

## Implementation notes

Propositions are sets of worlds, and "stronger relative to the common ground" in (50a) is
entailment. σ and the recursive computation of appendix A3 are not represented, so the two scopes
of σ and an embedding operator are the two compositions of an enrichment with the operator. A
domain is a finite set of possible witnesses, the widened domain of (57b), so (61b)'s alternatives
are those over its nonempty subdomains. Of the scalar alternatives of (79c) only the second row
is used, since it entails every higher row. As in (95), a formula is a function from domains to
propositions. `oMinus` follows (108c) rather than (62): relating only alternatives over disjoint
subdomains keeps the whole domain from being an antecedent, which the appendix requires to avoid
(118).

## TODO

* The intervention effect (86)–(87), a DP between σ and the item, is a syntactic stipulation in
  the paper and is not formalized.
* The profiles of (94) are not yet connected to the judgments of
  `Data/Examples/Chierchia2006.json`.

## References

* [chierchia-2006]
* [kadmon-landman-1993]
* [kratzer-shimoyama-2002]
* [haspelmath-1997]
-/

@[expose] public section

namespace Chierchia2006

open Exhaustification Indefinite

/-! ### The lexicon of polarity-sensitive items, (94) -/

/-- An item activates as alternatives either the large subdomains, (46), or every subdomain that
stands a chance, (56) and (61b). -/
inductive DomainAlternatives where
  | max
  | min
  deriving DecidableEq, Repr

/-- A polarity-sensitive item in (94) is fixed by the size of its domain alternatives, whether
indefinite morphology adds the uniqueness implicature, and whether the freezing operator σ it
selects presupposes proper strengthening, (72). -/
structure PSIProfile where
  alternatives : DomainAlternatives
  scalar : Bool
  presuppositional : Bool
  deriving DecidableEq, Repr

/-- The pure negative-polarity items *mai*, *ever* and *alcuno* are σ[D-MAX]. -/
def pureNPI : PSIProfile := ⟨.max, false, false⟩

/-- *Any* is σ[D-MIN], a negative-polarity item under negation and a universal free-choice item
elsewhere. -/
def npiFci : PSIProfile := ⟨.min, false, false⟩

/-- The pure universal free-choice items *qualsiasi* and *qualunque* select the presuppositional σ
over MIN alternatives. -/
def pureFci : PSIProfile := ⟨.min, false, true⟩

/-- German *irgendein* is σ[MIN, SCAL], an existential free-choice item with negative-polarity
uses. -/
def existentialNpiFci : PSIProfile := ⟨.min, true, false⟩

/-- Italian *uno N qualsiasi* selects the presuppositional σ over MIN alternatives and carries the
uniqueness implicature. -/
def existentialPureFci : PSIProfile := ⟨.min, true, true⟩

variable {W E : Type*}

/-! ### Even-like enrichment of large alternatives, §4 -/

section Even

/-- Even-like enrichment `E`, (50a) and (108b), keeps the prejacent where it is at least as strong
as every alternative. -/
def evenEnrich (C : Set (Set W)) (p : Set W) : Set W := {w | w ∈ p ∧ ∀ q ∈ C, p ⊆ q}

theorem evenEnrich_subset (C : Set (Set W)) (p : Set W) : evenEnrich C p ⊆ p := fun _ h ↦ h.1

/-- The even-like implicature is a condition on the alternatives, not on the world: enrichment
is vacuous or a contradiction. -/
theorem evenEnrich_eq_or_eq_empty (C : Set (Set W)) (p : Set W) :
    evenEnrich C p = p ∨ evenEnrich C p = ∅ := by
  by_cases h : ∀ q ∈ C, p ⊆ q
  · exact .inl (Set.ext fun w ↦ ⟨fun hw ↦ hw.1, fun hw ↦ ⟨hw, h⟩⟩)
  · exact .inr (Set.eq_empty_of_forall_notMem fun _ hw ↦ h hw.2)

/-- An alternative the prejacent does not entail makes even-like enrichment a contradiction. -/
theorem evenEnrich_eq_empty_of_not_subset {C : Set (Set W)} {p q : Set W} (hq : q ∈ C)
    (h : ¬ p ⊆ q) : evenEnrich C p = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hw ↦ h (hw.2 q hq)

/-- A pure negative-polarity item at its existential is deviant, (47)–(48): a world where some
member of the domain is a witness but no member of the subdomain `S` is shows that the statement
does not entail the alternative over `S`, so even-like enrichment is a contradiction. -/
theorem evenEnrich_disj_eq_empty {D S : Finset E} {P : E → Set W} {C : Set (Set W)}
    (hS : subDisj P S ∈ C) {a : E} {w : W} (ha : a ∈ D) (hPa : w ∈ P a)
    (hSw : ∀ x ∈ S, w ∉ P x) : evenEnrich C (disj D P) = ∅ :=
  evenEnrich_eq_empty_of_not_subset hS fun h ↦
    let ⟨x, hx, hPx⟩ := mem_subDisj.1 (h (mem_subDisj.2 ⟨a, ha, hPa⟩))
    hSw x hx hPx

/-- Under an antitone embedding, alternatives that each entail the prejacent are entailed by the
embedded prejacent, so even-like enrichment is vacuous: domain widening comes to fruition in a
downward-entailing context, (49) and (53). -/
theorem evenEnrich_image_antitone_eq {C : Set W → Set W} (hC : Antitone C) {A : Set (Set W)}
    {p : Set W} (hA : ∀ q ∈ A, q ⊆ p) : evenEnrich (C '' A) (C p) = C p :=
  Set.Subset.antisymm (evenEnrich_subset _ _)
    fun _ hw ↦ ⟨hw, by rintro _ ⟨q, hq, rfl⟩; exact hC (hA q hq)⟩

/-- An item triggering the even-like implicature can meet the presupposition of the strong σ only
by a contradiction, so pure negative-polarity items select the plain σ, footnote 33. -/
theorem eq_empty_of_properlyStrengthens_evenEnrich {C : Set (Set W)} {p : Set W}
    (h : ProperlyStrengthens (· ∈ evenEnrich C p) (· ∈ p)) : evenEnrich C p = ∅ :=
  (evenEnrich_eq_or_eq_empty C p).resolve_left fun heq ↦
    not_properlyStrengthens_of_iff (fun w ↦ by rw [heq]) h

end Even

/-! ### Antiexhaustive enrichment of small alternatives, §5 -/

section Antiexhaustive

variable {D : Finset E} {F : Finset E → Set W}

/-- The antiexhaustive enrichment `O⁻` of the domain-dependent proposition `F` over the domain
`D`, (108c), holds where `F D` holds and `F` holds of no nonempty subdomain without holding of
every nonempty subdomain disjoint from it. -/
def oMinus (F : Finset E → Set W) (D : Finset E) : Set W :=
  F D ∩ {w | ∀ S ⊆ D, ∀ T ⊆ D, S.Nonempty → T.Nonempty → Disjoint S T → w ∈ F S → w ∈ F T}

theorem oMinus_subset : oMinus F D ⊆ F D := Set.inter_subset_left

/-- A statement that entails each of its variants carries a vacuous antiexhaustive implicature,
(66). -/
theorem oMinus_eq_self (h : ∀ T ⊆ D, T.Nonempty → F D ⊆ F T) : oMinus F D = F D :=
  Set.inter_eq_left.2 fun _ hw _ _ T hT _ hT' _ _ ↦ h T hT hT' hw

variable (P : E → Set W)

/-- Antiexhaustive enrichment gives an existential universal force over its domain, (63c)–(63d):
*I saw any student* says that every possible student was seen. Negation over σ denies this
universal, the rhetorical reading (64). -/
theorem oMinus_subDisj (hD : D.Nonempty) : oMinus (subDisj P) D = ⋂ a ∈ D, P a := by
  classical
  refine Set.Subset.antisymm (fun w ⟨hw, h⟩ ↦ Set.mem_iInter₂.2 fun a ha ↦ ?_) fun w hw ↦ ?_
  · obtain ⟨x, hx, hPx⟩ := mem_subDisj.1 hw
    by_cases hxa : x = a
    · exact hxa ▸ hPx
    · simpa using h {x} (by simpa) {a} (by simpa) (by simp) (by simp)
        (Finset.disjoint_singleton.2 hxa) (by simpa)
  · obtain ⟨a, ha⟩ := hD
    have h := Set.mem_iInter₂.1 hw
    exact ⟨mem_subDisj.2 ⟨a, ha, h a ha⟩, fun _ _ T hT _ ⟨b, hb⟩ _ _ ↦
      mem_subDisj.2 ⟨b, hb, h b (hT hb)⟩⟩

/-- On an existential the simpler (62) agrees with (108c): the enrichment asserts the statement
and every alternative over a nonempty subdomain, as in (63c). -/
theorem oMinus_subDisj_eq_inter_sInter (hD : D.Nonempty) :
    oMinus (subDisj P) D = disj D P ∩ ⋂₀ subDisjs D P := by
  rw [oMinus_subDisj P hD, sInter_subDisjs, Set.inter_eq_right.2 (biInter_subset_disj hD)]

/-- With σ over negation, (65)–(66), the statement entails every variant, so the free-choice
implicature vanishes and *any* acts as a negative-polarity item. -/
theorem oMinus_antitone_eq {C : Set W → Set W} (hC : Antitone C) :
    oMinus (fun S ↦ C (subDisj P S)) D = C (disj D P) :=
  oMinus_eq_self fun _ hT _ ↦ hC (subDisj_mono hT)

/-- The presupposition of the strong σ, (72), fails under an antitone context, since the
enrichment coincides with the plain statement: *qualunque* has no negative-polarity construal,
(70). -/
theorem not_properlyStrengthens_oMinus_antitone {C : Set W → Set W} (hC : Antitone C) :
    ¬ ProperlyStrengthens (· ∈ oMinus (fun S ↦ C (subDisj P S)) D) (· ∈ C (disj D P)) :=
  not_properlyStrengthens_of_iff fun w ↦ by rw [oMinus_antitone_eq P hC]

/-- In a positive context the antiexhaustive enrichment properly strengthens the statement,
(71): a world where one member of the domain is a witness and another is not satisfies the
statement but not its enrichment. -/
theorem properlyStrengthens_oMinus {a b : E} {w : W} (ha : a ∈ D) (hb : b ∈ D) (hPa : w ∈ P a)
    (hPb : w ∉ P b) : ProperlyStrengthens (· ∈ oMinus (subDisj P) D) (· ∈ disj D P) :=
  ⟨fun _ h ↦ h.1, w, mem_subDisj.2 ⟨a, ha, hPa⟩, fun h ↦
    hPb (Set.mem_iInter₂.1 (oMinus_subDisj P ⟨a, ha⟩ ▸ h) b hb)⟩

/-- Under a possibility modal the antiexhaustive enrichment is the universal over the options:
every member of the domain is a witness in some accessible world, the distribution of (83)–(85)
without the uniqueness implicature. -/
theorem oMinus_preimage_subDisj (R : SetRel W W) (hD : D.Nonempty) :
    oMinus (fun S ↦ R.preimage (subDisj P S)) D = ⋂ a ∈ D, R.preimage (P a) := by
  simp only [subDisj, SetRel.preimage_iUnion]
  exact oMinus_subDisj _ hD

end Antiexhaustive

/-! ### Existential free-choice items, §6 and appendix A4 -/

section Existential

variable (P : E → Set W) {D S : Finset E}

/-- The exhaustified indefinite `exactlyOne P S` of (81b) holds where exactly one member of `S` is
a witness. -/
def exactlyOne (S : Finset E) : Set W := {w | ∃! x, x ∈ S ∧ w ∈ P x}

/-- `atLeastTwo P S` holds where two members of `S` are witnesses, the next row of the scale
in (79c). -/
def atLeastTwo (S : Finset E) : Set W := {w | ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ w ∈ P x ∧ w ∈ P y}

/-- Exhaustifying the existential against its scalar alternative yields the exhaustified
indefinite, (81a)–(81b), provided some world has a witness but not two. -/
theorem exh_atLeastTwo_eq_exactlyOne (h : ¬ subDisj P S ⊆ atLeastTwo P S) :
    exh {atLeastTwo P S} (subDisj P S) = exactlyOne P S := by
  ext w
  simp only [mem_exh, Set.mem_singleton_iff, forall_eq, imp_iff_not h]
  simp only [mem_subDisj, exactlyOne, atLeastTwo, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, hx, hPx⟩, h2⟩
    exact ⟨x, ⟨hx, hPx⟩, fun y ⟨hy, hPy⟩ ↦ by_contra fun hyx ↦ h2 ⟨y, hy, x, hx, hyx, hPy, hPx⟩⟩
  · rintro ⟨x, ⟨hx, hPx⟩, hu⟩
    exact ⟨⟨x, hx, hPx⟩, fun ⟨y, hy, z, hz, hyz, hPy, hPz⟩ ↦
      hyz ((hu y ⟨hy, hPy⟩).trans (hu z ⟨hz, hPz⟩).symm)⟩

/-- With two possible witnesses the uniqueness and free-choice implicatures clash, (82). The
unique witness of the domain is the unique witness of its singleton, which forces every other
singleton to have a witness too, so an existential free-choice item in an episodic sentence is
contradictory. -/
theorem oMinus_exactlyOne_eq_empty (hD : 1 < D.card) : oMinus (exactlyOne P) D = ∅ := by
  classical
  refine Set.eq_empty_of_forall_notMem fun w ⟨⟨x, ⟨_, hPx⟩, hu⟩, h⟩ ↦ ?_
  obtain ⟨b, hb, hbx⟩ := Finset.exists_mem_ne hD x
  obtain ⟨y, ⟨hy, hPy⟩, -⟩ := h {x} (by simpa) {b} (by simpa) (by simp) (by simp)
    (Finset.disjoint_singleton.2 hbx.symm) ⟨x, ⟨by simp, hPx⟩, fun z hz ↦ by simpa using hz.1⟩
  rw [Finset.mem_singleton] at hy
  exact hbx (hy ▸ hu y ⟨hy ▸ hb, hPy⟩)

section Necessity

variable {R : SetRel W W} {w : W}

/-- Under a necessity modal the uniqueness and free-choice implicatures together rule out any
proper subdomain being necessary, (117c): a necessary subdomain would make its complement
necessary too, and an accessible world would have two witnesses. -/
theorem notMem_core_exactlyOne (hw : w ∈ R.dom)
    (h : w ∈ oMinus (fun S ↦ R.core (exactlyOne P S)) D) (hS : S ⊂ D) (hS' : S.Nonempty) :
    w ∉ R.core (exactlyOne P S) := by
  classical
  intro hcore
  have hT := h.2 S hS.subset (D \ S) Finset.sdiff_subset hS'
    (Finset.sdiff_nonempty.2 hS.not_subset) Finset.disjoint_sdiff hcore
  obtain ⟨v, hv⟩ := hw
  obtain ⟨x, ⟨hx, hPx⟩, -⟩ := hcore hv
  obtain ⟨y, ⟨hy, hPy⟩, -⟩ := hT hv
  obtain ⟨_, -, hz⟩ := h.1 hv
  obtain ⟨hyD, hyS⟩ := Finset.mem_sdiff.1 hy
  exact hyS ((hz x ⟨hS.subset hx, hPx⟩).trans (hz y ⟨hyD, hPy⟩).symm ▸ hx)

/-- Under a necessity modal every member of a domain with two members is a witness in some
accessible world, the free choice of (117d) and (93d). -/
theorem oMinus_core_exactlyOne_subset (hD : 1 < D.card) :
    oMinus (fun S ↦ R.core (exactlyOne P S)) D ∩ R.dom ⊆ ⋂ a ∈ D, R.preimage (P a) := by
  classical
  refine fun w ⟨h, hw⟩ ↦ Set.mem_iInter₂.2 fun a ha ↦ ?_
  have hne : (D.erase a).Nonempty :=
    Finset.card_pos.1 (by rw [Finset.card_erase_of_mem ha]; omega)
  have hnot := notMem_core_exactlyOne P hw h (Finset.erase_ssubset ha) hne
  simp only [SetRel.mem_core, not_forall] at hnot
  obtain ⟨v, hv, hnot⟩ := hnot
  obtain ⟨z, ⟨hz, hPz⟩, hu⟩ := h.1 hv
  by_cases hza : z = a
  · exact ⟨v, hza ▸ hPz, hv⟩
  · exact absurd ⟨z, ⟨Finset.mem_erase.2 ⟨hza, hz⟩, hPz⟩,
      fun y hy ↦ hu y ⟨Finset.mem_of_mem_erase hy.1, hy.2⟩⟩ hnot

/-- If every nonempty subdomain is necessarily witnessed by exactly one member, the domain has at
most one member, which is why the whole domain must not be an antecedent, (118). -/
theorem card_le_one_of_forall_mem_core_exactlyOne (hw : w ∈ R.dom)
    (h : ∀ T ⊆ D, T.Nonempty → w ∈ R.core (exactlyOne P T)) : D.card ≤ 1 := by
  refine Finset.card_le_one.2 fun a ha b hb ↦ ?_
  obtain ⟨v, hv⟩ := hw
  obtain ⟨x, ⟨hx, hPa⟩, -⟩ := h {a} (by simpa) (by simp) hv
  obtain ⟨y, ⟨hy, hPb⟩, -⟩ := h {b} (by simpa) (by simp) hv
  obtain ⟨_, -, hz⟩ := h D le_rfl ⟨a, ha⟩ hv
  rw [Finset.mem_singleton] at hx hy
  subst hx hy
  exact (hz x ⟨ha, hPa⟩).trans (hz y ⟨hb, hPb⟩).symm

end Necessity

/-- In the model of (85) the evaluation world `0` accesses the two other worlds. -/
def accessible : SetRel (Fin 3) (Fin 3) := {p | p.1 = 0 ∧ p.2 ≠ 0}

/-- Doctor `d` is married exactly in world `d + 1`, the distribution of (85). -/
def married (d : Fin 2) : Set (Fin 3) := {d.succ}

/-- Two doctors, each married in one accessible world, satisfy the enriched statement under a
possibility modal, the rescue of (84)–(85). -/
theorem zero_mem_oMinus_preimage_exactlyOne_married :
    0 ∈ oMinus (fun S ↦ accessible.preimage (exactlyOne married S)) .univ := by
  have key (T : Finset (Fin 2)) (hT : T.Nonempty) :
      0 ∈ accessible.preimage (exactlyOne married T) :=
    let ⟨d, hd⟩ := hT
    ⟨d.succ, ⟨d, ⟨hd, rfl⟩, fun _ hy ↦ (Fin.succ_injective _ hy.2).symm⟩, rfl, d.succ_ne_zero⟩
  exact ⟨key _ Finset.univ_nonempty, fun _ _ T _ _ hT _ _ ↦ key T hT⟩

/-- The same distribution satisfies the enriched statement under a necessity modal, (115)–(117):
no single doctor is necessary, so the free-choice implicature holds vacuously. -/
theorem zero_mem_oMinus_core_exactlyOne_married :
    0 ∈ oMinus (fun S ↦ accessible.core (exactlyOne married S)) .univ := by
  refine ⟨fun v hv ↦ ?_, fun S _ T _ _ ⟨d, hd⟩ hST h ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := Fin.exists_succ_eq.2 hv.2
    exact ⟨x, ⟨Finset.mem_univ x, rfl⟩, fun _ hy ↦ (Fin.succ_injective _ hy.2).symm⟩
  · obtain ⟨x, ⟨hx, hdx⟩, -⟩ := h (b := d.succ) ⟨rfl, d.succ_ne_zero⟩
    obtain rfl := Fin.succ_injective _ hdx
    exact absurd hd (Finset.disjoint_left.1 hST hx)

/-- On the same model, asserting every alternative under the necessity modal fails, (118). -/
theorem not_forall_zero_mem_core_exactlyOne_married :
    ¬ ∀ T ⊆ .univ, T.Nonempty → 0 ∈ accessible.core (exactlyOne married T) := fun h ↦
  absurd (card_le_one_of_forall_mem_core_exactlyOne married
    (show 0 ∈ accessible.dom from ⟨1, rfl, by decide⟩) h) (by decide)

end Existential

/-! ### Double duty on the implicational map -/

/-- Roughly half of the languages in [haspelmath-1997]'s survey use one series for negative
polarity and free choice, English among them: the *any*-series covers direct negation and free
choice. -/
theorem any_double_duty :
    ∃ e ∈ Haspelmath1997.english,
      .directNeg ∈ e.functions ∧ .freeChoice ∈ e.functions := by
  decide

/-- The other half separate the two, as Romance does: no Italian series covering direct
negation covers free choice, and the free-choice series *-unque* covers no negation function. -/
theorem italian_separates_uses :
    ∀ e ∈ Haspelmath1997.italian,
      (.directNeg ∈ e.functions → .freeChoice ∉ e.functions) ∧
        (.freeChoice ∈ e.functions →
          .directNeg ∉ e.functions ∧ .indirectNeg ∉ e.functions) := by
  decide

end Chierchia2006
