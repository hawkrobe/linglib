module

public import Linglib.Studies.Fox2007
public import Linglib.Semantics.Modality.Kratzer.Operators
public import Linglib.Logic.Team.Inquisitive
public import Mathlib.Probability.ConditionalProbability
public import Linglib.Data.Examples.BadeEtAl2022
public import Linglib.Data.Experiments.BadeEtAl2022

/-!
# Bade, Picat, Chung and Mascarenhas (2022): Alternatives and attention in language and reasoning

This file formalizes the illusory-inference apparatus of Bade, Picat, Chung and Mascarenhas's
reply to Mascarenhas and Picat, its two routes to the disjunctive fallacy, and the derivations
the paper runs for the epistemic and deontic possibility modals.

From *(a and b) or else c* and *a*, reasoners conclude *b* about 85% of the time though it does
not follow (`illusory_inference_invalid`): the disjunction raises the Hamblin alternatives
*a and b* and *c*, the hint overlaps the first, and selecting it yields the conclusion by
conjunction elimination (`Problem.Illusory`, the §3.2 hallmark). Mascarenhas and Picat found the
same illusion with *might*, whose attentive content is the alternative set `{φ, ⊤}` of
[ciardelli-groenendijk-roelofsen-2009], so *might (a and b)* is the schema's first premise with
`c` the tautology (`mightProblem_eq_disjunction`, by `rfl`); indefinites instantiate it with one
alternative per witness. The second route is exhaustification ((4), after [spector-2007]):
innocent exclusion against the substitution alternatives strengthens the disjunction to its
exclusive reading `exh_route`, from which the conclusion follows classically
(`exh_route_valid`); posterior-based accounts, by contrast, cannot separate the conclusions *b*
and *c* without a prior asymmetry (`posterior_eq_iff`). Footnote 6's excludability asymmetry is
derived (`might_not_excludable`, `allowed_excludable`), as is the fact that the revised flat
premise disarms it for both modals (`revised_flat_not_excludable`).

The experiment's printed contrasts live in `Data.Experiments.BadeEtAl2022`, and §3.2's anatomy
of the illusion is read off the paper's verdict rows: *might* satisfies criteria A–C
(`might_anatomy`) while *allowed to* fails the order and dynamics criteria
(`allowed_not_anatomy`), the paper's ground for classifying the deontic fallacies — about 50%,
and structure-insensitive — as the work of another mechanism, with the package deal of
[merin-1992] and [van-rooy-2000] as the candidate ((16), a datum). The relational route (14)
rests on realism of the modal base: a base is realistic exactly when what is actual is possible
(`Modality.isRealistic_iff_id_le_simplePossibility`), the assumption that is standard for
epistemics and absurd for deontics; with an ordering source, reflexivity alone does not make
best-worlds possibility veridical (`exists_not_possibility`).

## Implementation notes

* Alternatives are Hamblin sets `Set (Set W)`: the repo's InqB supports are lower sets, so the
  attentive `φ ∨ ⊤` collapses to `⊤` there (`support_inqDisj_top`), exactly what the attentive
  proposal avoids.
* `Problem.Illusory` leaves the selected alternative existential with partial overlap as a side
  condition: the paper gives no selection criterion beyond "related to".
* (4b) is innocent exclusion against the connective- and subconstituent-substitution
  alternatives of `(a ∧ b) ∨ c`; the four-member Sauerland set provably does not yield it.
* Criteria A–C of the anatomy are derived from the paper's own contrast verdicts, with the
  marginal order contrast counting as a difference, as the paper's classification requires; D
  and the full classification are the paper's marks in the `anatomy` rows.

## References

* [N. Bade, L. Picat, W. Chung and S. Mascarenhas, *Alternatives and attention in language and
  reasoning: A reply to Mascarenhas & Picat 2019* (2022)][bade-picat-chung-mascarenhas-2022]
* [S. Mascarenhas and L. Picat, *'Might' as a generator of alternatives: The view from
  reasoning* (2019)][mascarenhas-picat-2019]
* [I. Ciardelli, J. Groenendijk and F. Roelofsen, *Attention! 'Might' in Inquisitive Semantics*
  (2009)][ciardelli-groenendijk-roelofsen-2009]
* [P. Koralus and S. Mascarenhas, *The erotetic theory of reasoning* (2013)
  ][koralus-mascarenhas-2013]
* [S. Mascarenhas and P. Koralus, *Illusory inferences with quantifiers*
  (2017)][mascarenhas-koralus-2017]
* [P. Koralus and S. Mascarenhas, *Illusory Inferences in a Question-Based Theory of Reasoning*
  (2018)][koralus-mascarenhas-2018]
* [C. Walsh and P. N. Johnson-Laird, *Co-reference and reasoning*
  (2004)][walsh-johnson-laird-2004]
* [D. Fox, *Free choice and the theory of scalar implicatures* (2007)][fox-2007]
* [B. Spector, *Scalar implicatures: exhaustivity and Gricean reasoning* (2007)][spector-2007]
* [A. Kratzer, *Modality* (1991)][kratzer-1991]
* [A. Merin, *Permission Sentences Stand in the Way of Boolean and Other Lattice-Theoretic
  Semantices* (1992)][merin-1992]
* [R. van Rooy, *Permission to Change* (2000)][van-rooy-2000]
-/

@[expose] public section

namespace BadeEtAl2022

open Set Exhaustification Modality ModalLogic

variable {W : Type*}

/-! ### The illusory-inference schema (§1.1–§1.3) -/

/-- A reasoning problem whose first premise raises alternatives and whose second premise is a
hint (§1.2). -/
structure Problem (W : Type*) where
  /-- The Hamblin alternatives raised by the first premise. -/
  alts : Set (Set W)
  /-- The second premise. -/
  hint : Set W

namespace Problem

variable (P : Problem W)

/-- The classical content of the two premises together. -/
def premises : Set W := ⋃₀ P.alts ∩ P.hint

/-- A conclusion follows classically from the premises. -/
def Entails (q : Set W) : Prop := P.premises ⊆ q

/-- The erotetic selection of the alternative `p` as the answer: the alternative with the
hint. -/
def selected (p : Set W) : Set W := p ∩ P.hint

/-- A conclusion is illusory when some alternative the hint partially overlaps yields it by
conjunction elimination, though it does not follow classically: the hallmark of illusory
inferences from alternatives (§3.2 A), after the question-based theory of
[koralus-mascarenhas-2013] and [koralus-mascarenhas-2018]. -/
def Illusory (q : Set W) : Prop :=
  (∃ p ∈ P.alts, (P.selected p).Nonempty ∧ P.selected p ⊆ q) ∧ ¬ P.Entails q

end Problem

/-- Schema (2): the disjunctive premise `(a ∧ b) ∨ c` with hint `a`. -/
def disjunction (a b c : Set W) : Problem W := ⟨{a ∩ b, c}, a⟩

/-- *might φ* raises the alternatives `{φ, ⊤}`, its attentive content (7b). -/
def might (p : Set W) : Set (Set W) := {p, univ}

/-- Schema (9): `might (a ∧ b)` with hint `a`. -/
def mightProblem (a b : Set W) : Problem W := ⟨might (a ∩ b), a⟩

/-- Schema (3): an indefinite raises one alternative per member of its domain. -/
def indefinite {E : Type*} (P : E → Set W) (D : Set E) (hint : Set W) : Problem W :=
  ⟨P '' D, hint⟩

variable {a b c : Set W}

/-- The schema (1)/(2) is classically invalid: the paper's countermodel has Bill speaking
German, John English, and Mary not French (§1.1). -/
theorem illusory_inference_invalid (h : ((c ∩ a) \ b).Nonempty) :
    ¬ (disjunction a b c).Entails b := by
  obtain ⟨w, ⟨hwc, hwa⟩, hwb⟩ := h
  exact fun hent ↦ hwb (hent ⟨⟨c, by simp [disjunction], hwc⟩, hwa⟩)

/-- Whenever both disjuncts are live, the disjunctive conclusion is illusory (2). -/
theorem disjunction_illusory (hab : (a ∩ b).Nonempty) (h : ((c ∩ a) \ b).Nonempty) :
    (disjunction a b c).Illusory b :=
  ⟨⟨a ∩ b, by simp [disjunction], by
      obtain ⟨w, hwa, hwb⟩ := hab
      exact ⟨w, ⟨hwa, hwb⟩, hwa⟩, fun _ hw ↦ hw.1.2⟩, illusory_inference_invalid h⟩

/-- (8b) is the special case `c := ⊤` of the disjunctive premise of (2). -/
theorem mightProblem_eq_disjunction : mightProblem a b = disjunction a b univ := rfl

/-- The *might* premise is informationally idle (§2.1). -/
@[simp] theorem sUnion_might (p : Set W) : ⋃₀ might p = univ := by simp [might]

/-- It is nevertheless not the alternative set of the tautology (§2.1). -/
theorem might_ne_of_ne_univ {p : Set W} (hp : p ≠ univ) : might p ≠ might univ := by
  simp [might, hp]

/-- The *might* conclusion is illusory (9)/(10). -/
theorem might_illusory (hab : (a ∩ b).Nonempty) (h : (a \ b).Nonempty) :
    (mightProblem a b).Illusory b :=
  disjunction_illusory hab (by simpa using h)

/-- The indefinite conclusion about John is illusory whenever another witness could verify the
indefinite (3). -/
theorem indefinite_illusory {E : Type*} {P : E → Set W} {D : Set E} {hint : Set W} {john : E}
    (hj : john ∈ D) (hw : (P john ∩ hint).Nonempty)
    (hcm : ∃ x ∈ D, ((P x ∩ hint) \ P john).Nonempty) :
    (indefinite P D hint).Illusory (P john) := by
  refine ⟨⟨P john, ⟨john, hj, rfl⟩, hw, fun _ hw ↦ hw.1⟩, ?_⟩
  obtain ⟨x, hx, w, ⟨hwx, hwh⟩, hwj⟩ := hcm
  exact fun hent ↦ hwj (hent ⟨⟨P x, ⟨x, hx, rfl⟩, hwx⟩, hwh⟩)

/-! ### The scalar-implicature route (§1.4) -/

/-- The alternatives of `(a ∧ b) ∨ c` by substitution of connectives and of subconstituents.
The paper names no alternative set; against the four-member Sauerland set, innocent exclusion
denies only the conjunction of the disjuncts, which does not give (4b). -/
def scalarAlternatives (a b c : Set W) : Set (Set W) :=
  {(a ∩ b) ∪ c, (a ∩ b) ∩ c, a ∪ c, b ∪ c, a ∩ c, b ∩ c, a ∩ b, a, b, c}

/-- (4b): exhaustifying (4a) against its alternatives yields the exclusive reading
`(a ∧ b ∧ ¬c) ∨ (c ∧ ¬a ∧ ¬b)`, given a world of each disjunct without the other. -/
theorem exh_route (hab : ((a ∩ b) \ c).Nonempty) (hc : (c \ (a ∪ b)).Nonempty) :
    exhIE (scalarAlternatives a b c) ((a ∩ b) ∪ c) = ((a ∩ b) \ c) ∪ (c \ (a ∪ b)) := by
  obtain ⟨x, ⟨hxa, hxb⟩, hxc⟩ := hab
  obtain ⟨y, hyc, hyab⟩ := hc
  have hya : y ∉ a := fun h ↦ hyab (Or.inl h)
  have hyb : y ∉ b := fun h ↦ hyab (Or.inr h)
  have hM : IsMinimalCover (scalarAlternatives a b c) ((a ∩ b) ∪ c) {x, y} := by
    refine ⟨?_, fun w hw ↦ ?_, ?_⟩
    · rintro v (rfl | rfl)
      exacts [Or.inl ⟨hxa, hxb⟩, Or.inr hyc]
    · rcases hw with ⟨hwa, hwb⟩ | hwc
      · refine ⟨x, Or.inl rfl, fun q hq hxq ↦ ?_⟩
        simp only [scalarAlternatives, mem_insert_iff, mem_singleton_iff] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [Or.inl ⟨hwa, hwb⟩, (hxc hxq.2).elim, Or.inl hwa, Or.inl hwb, (hxc hxq.2).elim,
          (hxc hxq.2).elim, ⟨hwa, hwb⟩, hwa, hwb, (hxc hxq).elim]
      · refine ⟨y, Or.inr rfl, fun q hq hyq ↦ ?_⟩
        simp only [scalarAlternatives, mem_insert_iff, mem_singleton_iff] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [Or.inr hwc, (hya hyq.1.1).elim, Or.inr hwc, Or.inr hwc, (hya hyq.1).elim,
          (hyb hyq.1).elim, (hya hyq.1).elim, (hya hyq).elim, (hyb hyq).elim, hwc]
    · rintro v (rfl | rfl) u (rfl | rfl) huv
      · exact leALT_refl _ _
      · exact (hxc (huv c (by simp [scalarAlternatives]) hyc)).elim
      · exact (hya (huv a (by simp [scalarAlternatives]) hxa)).elim
      · exact leALT_refl _ _
  rw [hM.exhIE_eq]
  ext u
  simp only [scalarAlternatives, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq,
    mem_ofPred_eq, mem_union, mem_inter_iff, mem_sdiff]
  constructor
  · rintro ⟨hu, h⟩
    rcases hu with ⟨hua, hub⟩ | huc
    · refine Or.inl ⟨⟨hua, hub⟩, fun huc ↦ ?_⟩
      exact h.2.2.2.2.1 (by simp_all) ⟨hua, huc⟩
    · by_cases hua : u ∈ a
      · exact (h.2.2.2.2.1 (by simp_all) ⟨hua, huc⟩).elim
      · by_cases hub : u ∈ b
        · exact (h.2.2.2.2.2.1 (by simp_all) ⟨hub, huc⟩).elim
        · exact Or.inr ⟨huc, fun h' ↦ h'.elim hua hub⟩
  · rintro (⟨⟨hua, hub⟩, huc⟩ | ⟨huc, huab⟩)
    · refine ⟨Or.inl ⟨hua, hub⟩, ?_⟩
      simp_all
    · refine ⟨Or.inr huc, ?_⟩
      simp_all

/-- With the exclusive reading (4b), the conclusion follows classically (§1.4). -/
theorem exh_route_valid : (((a ∩ b) \ c) ∪ (c \ (a ∪ b))) ∩ a ⊆ b := by
  rintro u ⟨⟨⟨-, hub⟩, -⟩ | ⟨-, huab⟩, hua⟩
  · exact hub
  · exact (huab (Or.inl hua)).elim

/-! ### Footnote 6: the excludability asymmetry -/

section Flat

variable {R : SetRel W W} {ALT : Set (Set W)}

/-- Under a reflexive frame, `a` entails `◇a`, so `◇a` is never innocently excludable from
`a ∧ ◇b`: *not might a* contradicts *a* (fn 6). -/
theorem might_not_excludable (hR : R.IsRefl) (hfin : ALT.Finite)
    (hsat : (a ∩ R.preimage b).Nonempty) :
    ¬ IsInnocentlyExcludable ALT (a ∩ R.preimage b) (R.preimage a) :=
  not_isInnocentlyExcludable_of_phi_subset hfin hsat fun w hw ↦ ⟨w, hw.1, hR.refl w⟩

/-- Over a frame with a world where `a` holds, `◇b` holds and `◇a` fails, `◇a` is innocently
excludable from `a ∧ ◇b`: the implicature *not allowed to a* is available (fn 6). -/
theorem allowed_excludable (hw : ∃ w ∈ a ∩ R.preimage b, w ∉ R.preimage a) :
    IsInnocentlyExcludable {a ∩ R.preimage b, R.preimage a} (a ∩ R.preimage b)
      (R.preimage a) := by
  obtain ⟨w, hw, hwa⟩ := hw
  refine .of_forall_subset_or_notMem (by simp) hw hwa ?_
  rintro q (rfl | rfl)
  exacts [Or.inl subset_rfl, Or.inr hwa]

/-- The revised flat premise `a ∧ ◇(a ∧ b)` entails `◇a` under every frame. -/
theorem revised_flat_subset : a ∩ R.preimage (a ∩ b) ⊆ R.preimage a :=
  fun _ hw ↦ SetRel.preimage_mono inter_subset_left hw.2

/-- So in the experiment's revised flat condition the implicature is unavailable for both
modals, which fn 6's design change implies but does not state. -/
theorem revised_flat_not_excludable (hfin : ALT.Finite)
    (hsat : (a ∩ R.preimage (a ∩ b)).Nonempty) :
    ¬ IsInnocentlyExcludable ALT (a ∩ R.preimage (a ∩ b)) (R.preimage a) :=
  not_isInnocentlyExcludable_of_phi_subset hfin hsat revised_flat_subset

end Flat

/-! ### §1.5: posteriors cannot separate the conclusions -/

section Posterior

open MeasureTheory ProbabilityTheory

variable {A B C : Set W}

/-- (5): the premises `((a ∧ b) ∨ c) ∧ a` are classically `(a ∧ b) ∨ (a ∧ c)`. -/
theorem premises_eq_distrib (A B C : Set W) : ((A ∩ B) ∪ C) ∩ A = (A ∩ B) ∪ (A ∩ C) := by
  ext; simp; tauto

theorem premises_inter_left (A B C : Set W) : ((A ∩ B) ∪ C) ∩ A ∩ B = A ∩ B := by
  ext; simp; tauto

theorem premises_inter_right (A B C : Set W) : ((A ∩ B) ∪ C) ∩ A ∩ C = A ∩ C := by
  ext; simp; tauto

/-- Conditioning any finite measure on the premises, the posteriors of `b` and of `c` agree iff
the priors of `a ∧ b` and `a ∧ c` do: a posterior-based account of the task distinguishes the
observed conclusion from the unobserved one only through the priors (§1.5). -/
theorem posterior_eq_iff [MeasurableSpace W] (μ : Measure W) [IsFiniteMeasure μ]
    (hE : MeasurableSet (((A ∩ B) ∪ C) ∩ A)) (h0 : μ (((A ∩ B) ∪ C) ∩ A) ≠ 0) :
    μ[B | ((A ∩ B) ∪ C) ∩ A] = μ[C | ((A ∩ B) ∪ C) ∩ A] ↔ μ (A ∩ B) = μ (A ∩ C) := by
  rw [cond_apply hE, cond_apply hE, premises_inter_left, premises_inter_right]
  exact ENNReal.mul_right_inj (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
    (ENNReal.inv_ne_top.2 h0)

end Posterior

/-! ### The relational route (14) and its deontic absurdity -/

section Relational

/-- With an ordering source, actuality entails best-worlds possibility when the actual world
also verifies the ordering source at itself. -/
theorem possibility_of_isRealistic {f : ModalBase W} {g : OrderingSource W} {p : W → Prop}
    {w : W} (hf : f.IsRealistic) (hw : ∀ q ∈ g w, q w) (hp : p w) : possibility f g p w :=
  ⟨w, ⟨hf.mem_accessibleWorlds w, fun _ _ _ q hq _ ↦ hw q hq⟩, hp⟩

/-- Realism of the base alone does not make best-worlds possibility veridical, so (14) needs
more than (14b): the actual world must be among the best-ranked. -/
theorem exists_not_possibility :
    ∃ (f : ModalBase Bool) (g : OrderingSource Bool) (p : Bool → Prop) (w : Bool),
      f.IsRealistic ∧ p w ∧ ¬ possibility f g p w :=
  ⟨emptyBackground, fun _ ↦ [(· = true)], (· = false), false,
    fun _ _ h ↦ (List.not_mem_nil h).elim, rfl,
    fun ⟨v, hvb, hv⟩ ↦ by
      obtain ⟨_, hbest⟩ := mem_bestWorlds.1 (mem_bestAccessible.1 hvb)
      have h := hbest true (accessible_emptyBackground _ _)
      simp_all [atLeastAsGoodAs_iff]⟩

end Relational

/-! ### Why not InqB (§2.1) -/

section InqB

open Inquisitive

variable {Atom : Type*} [DecidableEq W] (M : Model W Atom) (φ : Formula Atom)

/-- In the repo's InqB, support is a lower set, so inquisitive disjunction with the tautology
is the tautology: the attentive content of (7a), where the alternatives properly include one
another, is not expressible there, which is why the study keeps Hamblin sets. -/
theorem support_inqDisj_top :
    support M (.inqDisj φ Formula.bot.neg) = support M Formula.bot.neg := by
  simp only [support, himp_self, sup_top_eq]

end InqB

/-! ### The experiment and the anatomy of the illusion (§2.3, §3.2) -/

/-- The design crosses modal, structure and conjunct order into twelve conditions (§2.3.1). -/
theorem conditions_card : Fintype.card (Modal × Structure × Order) = 12 := rfl

/-- Criteria A–C of §3.2, read off the paper's verdicts on its own contrasts: more fallacies
than baseline, an order-of-premises effect, and no fallacy once the question–answer dynamic is
flattened. The marginal epistemic order contrast counts as a difference, as the paper's
classification of *might* requires; criterion D and the paper's full classification are the
`anatomy` rows. -/
structure Anatomy (m : Modal) : Prop where
  fallacy : (contrasts m .canonicalVsBaseline).verdict ≠ .noDifference
  orderOfPremises : (contrasts m .canonicalVsReversed).verdict ≠ .noDifference
  dynamics : (contrasts m .flatVsBaseline).verdict = .noDifference

instance (m : Modal) : Decidable (Anatomy m) :=
  decidable_of_iff (_ ∧ _ ∧ _) ⟨fun ⟨a, b, c⟩ ↦ ⟨a, b, c⟩, fun ⟨a, b, c⟩ ↦ ⟨a, b, c⟩⟩

/-- *might* shows the full signature of illusory inferences from alternatives (§3.2). -/
theorem might_anatomy : Anatomy .epistemic := by decide

/-- *allowed to* does not (§3.2). -/
theorem allowed_not_anatomy : ¬ Anatomy .deontic := by decide

/-- Specifically, the deontic fallacies fail the order and the dynamics criteria: canonical and
reversed do not differ, and the flat structure still produces the fallacy (§2.4). -/
theorem allowed_fails_order_and_dynamics :
    (contrasts .deontic .canonicalVsReversed).verdict = .noDifference ∧
      (contrasts .deontic .flatVsBaseline).verdict ≠ .noDifference := by decide

/-- Deontic targets drew more fallacious endorsements than epistemic ones in every structure
(Table 5). -/
theorem deontic_more_fallacies : ∀ s, (modalContrasts s).verdict = .lower := by decide

/-- The epistemic order contrast is the marginal one (Table 2), the caveat on criterion B. -/
theorem might_order_marginal :
    (contrasts .epistemic .canonicalVsReversed).verdict = .marginallyHigher := rfl

end BadeEtAl2022
