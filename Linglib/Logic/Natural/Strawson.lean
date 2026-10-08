module

public import Linglib.Logic.Natural.Additivity
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Conditionals.Horizon
public import Linglib.Semantics.Degree.Superlative
public import Linglib.Semantics.Modality.Kratzer.Ordering
public import Linglib.Semantics.Focus.Particles
public import Linglib.Semantics.Attitudes.Preference.BestWorlds

/-!
# Strawson entailment

An operator into partial propositions is Strawson downward entailing when shrinking its argument
gives a conclusion that the original Strawson-entails, the inference being checked only where the
presuppositions involved hold. Von Fintel introduces the notion to keep the Fauconnier–Ladusaw
theory of negative polarity licensing for focus *only*, the adversative attitudes, superlatives,
temporal *since* and conditional antecedents, none of which is downward entailing in the classical
sense. Gajewski defines Strawson anti-additivity, which the same operators also satisfy.

Strawson entailment adds presuppositions only as premises, so each Strawson property holds as soon
as the assertion has its classical counterpart, whatever the presupposition; it is the
presupposition that defeats the classical property.

## Main definitions

* `IsStrawsonDE`, `IsStrawsonUE`: antitonicity and monotonicity under Strawson entailment.
* `IsStrawsonAntiAdditive`: `f (p ⊔ q)` is Strawson equivalent to `f p` conjoined with `f q`.
* `only`: von Fintel's *only* over a name.

## Main results

* `IsStrawsonDE.of_antitone`, `IsStrawsonUE.of_monotone`,
  `IsStrawsonAntiAdditive.of_isAntiAdditive`: the classical property of the assertion suffices.
* `isStrawsonAntiAdditive_iff`: Strawson anti-additivity is Strawson downward entailingness
  together with the Strawson form of Atlas's pseudo-anti-additivity.
* `isStrawsonDE_ofProp_iff`, `isStrawsonAntiAdditive_ofProp_iff`: without presuppositions the
  Strawson notions are the classical ones.
* `isStrawsonAntiAdditive_only`, `not_antitone_truthSet_only`: *only* over a name is Strawson
  anti-additive and not classically downward entailing.
* `Degree.isStrawsonAntiAdditive_superlative`,
  `Conditional.isStrawsonAntiAdditive_horizonCounterfactual`: the superlative in its class and the
  modal-horizon counterfactual in its antecedent are Strawson anti-additive, and neither is
  classically downward entailing.
* `Desire.BestWorlds.isStrawsonUE_want`, `Desire.BestWorlds.isStrawsonUE_glad`,
  `Desire.BestWorlds.not_isStrawsonDE_glad`, `Desire.BestWorlds.isStrawsonAntiAdditive_regret`:
  *want* and *glad* are Strawson upward entailing and *glad* is not Strawson downward entailing,
  while *sorry* is Strawson anti-additive.
* `Focus.Particles.isStrawsonDE_only`, `Focus.Particles.isStrawsonAntiAdditive_only_subset`,
  `Focus.Particles.isStrawsonDE_only_apply`: the propositional exclusive is Strawson downward
  entailing in its prejacent and, applied to an individual, in its predicate, on scales refining
  entailment; `Focus.Particles.not_isStrawsonDE_only_superset` fails it on the reversed scale.
* `only_eq_only_range`, `only_ne_only_range`: the name-based *only* is the exclusive over the
  alternatives the name generates exactly when no predication entails another's.

## Implementation notes

* Strawson entailment takes the presuppositions of premise and conclusion alike as premises, as
  in von Fintel's Strawson validity and Gajewski's own proofs, rather than the literal clause of
  Gajewski's cross-categorial definition at type `t`.
* `only` is von Fintel's name-based *only*, which excludes individuals; the propositional
  exclusive of Coppock and Beaver, which excludes alternative propositions, is
  `Focus.Particles.only`, and its Strawson facts hold with the alternatives held fixed, as von
  Fintel requires. `only` presupposes that `x` is `P`; Horn's presupposition that something is
  `P` gives the same Strawson facts, as von Fintel notes.
* *Want*, *glad* and *sorry* are the best-worlds entries of `Desire.BestWorlds`; following Heim,
  the factivity of *glad* and *sorry* is doxastic, and with suitable ordering sources *sorry* also
  covers *regret*, *amazed* and *surprised*. Von Fintel calls *glad* upward entailing; its
  presupposition that the domain contains non-`p` worlds can fail at a larger argument, so
  `Desire.BestWorlds.isStrawsonUE_glad` is the Strawson form he states for *want*.
* The other operators live with their owners, the superlative in `Degree.superlative` and the
  conditional in `Conditional.horizonCounterfactual`, and their Strawson facts are proved here,
  as are those of Iatridou's temporal *since*, defined here.

## References

* [strawson-1952]
* [von-fintel-1999]
* [gajewski-2005]
* [gajewski-2011]
* [coppock-beaver-2014]
* [atlas-1996]
* [horn-1996]
* [heim-1992]
* [heim-1999]
-/

@[expose] public section

namespace Presupposition.PartialProp

variable {W : Type*} {p q : PartialProp W}

theorem strawsonEntails_of_assertion_le (h : p.assertion ≤ q.assertion) : p.strawsonEntails q :=
  fun w _ _ hp ↦ h w hp

theorem strawsonEquiv_of_assertion_eq (h : p.assertion = q.assertion) : p.strawsonEquiv q :=
  ⟨strawsonEntails_of_assertion_le h.le, strawsonEntails_of_assertion_le h.ge⟩

theorem strawsonEntails_ofProp_iff {a b : W → Prop} :
    (ofProp a).strawsonEntails (ofProp b) ↔ a ≤ b :=
  ⟨fun h w ha ↦ h w trivial trivial ha, fun h w _ _ ha ↦ h w ha⟩

end Presupposition.PartialProp

namespace NaturalLogic

open Presupposition PartialProp

variable {α ι W D : Type*}

/-! ### Strawson monotonicity -/

section Preorder

variable [Preorder α] {f : α → PartialProp W}

/-- An operator into partial propositions is Strawson downward entailing if `p ≤ q` makes `f q`
Strawson-entail `f p` ([von-fintel-1999]'s (14)). -/
def IsStrawsonDE (f : α → PartialProp W) : Prop :=
  ∀ ⦃p q⦄, p ≤ q → (f q).strawsonEntails (f p)

/-- An operator into partial propositions is Strawson upward entailing if `p ≤ q` makes `f p`
Strawson-entail `f q`. -/
def IsStrawsonUE (f : α → PartialProp W) : Prop :=
  ∀ ⦃p q⦄, p ≤ q → (f p).strawsonEntails (f q)

/-- Von Fintel's own statement of Strawson downward entailingness asks that `f p` be true wherever
it is defined and `f q` is true. -/
theorem isStrawsonDE_iff :
    IsStrawsonDE f ↔ ∀ ⦃p q⦄, p ≤ q → ∀ w, (f p).presup w → (f q).holds w → (f p).holds w :=
  ⟨fun h _ _ hpq w hp hq ↦ ⟨hp, h hpq w hq.1 hp hq.2⟩,
    fun h _ _ hpq w hq hp hq' ↦ (h hpq w hp ⟨hq, hq'⟩).2⟩

/-- An antitone assertion is Strawson downward entailing, whatever the presupposition. -/
theorem IsStrawsonDE.of_antitone (h : Antitone fun p ↦ (f p).assertion) : IsStrawsonDE f :=
  fun _ _ hpq ↦ strawsonEntails_of_assertion_le (h hpq)

/-- A monotone assertion is Strawson upward entailing, whatever the presupposition. -/
theorem IsStrawsonUE.of_monotone (h : Monotone fun p ↦ (f p).assertion) : IsStrawsonUE f :=
  fun _ _ hpq ↦ strawsonEntails_of_assertion_le (h hpq)

/-- Classical downward entailingness of the truth set implies the Strawson form. -/
theorem IsStrawsonDE.of_antitone_truthSet (h : Antitone fun p ↦ (f p).truthSet) :
    IsStrawsonDE f :=
  fun _ _ hpq _ hq _ hq' ↦ (h hpq ⟨hq, hq'⟩).2

/-- Without presuppositions, Strawson downward entailingness is antitonicity. -/
theorem isStrawsonDE_ofProp_iff {g : α → W → Prop} :
    IsStrawsonDE (fun p ↦ ofProp (g p)) ↔ Antitone g :=
  forall₂_congr fun _ _ ↦ imp_congr_right fun _ ↦ strawsonEntails_ofProp_iff

/-- Without presuppositions, Strawson upward entailingness is monotonicity. -/
theorem isStrawsonUE_ofProp_iff {g : α → W → Prop} :
    IsStrawsonUE (fun p ↦ ofProp (g p)) ↔ Monotone g :=
  forall₂_congr fun _ _ ↦ imp_congr_right fun _ ↦ strawsonEntails_ofProp_iff

/-- A presupposition failing at a smaller argument defeats classical downward entailingness. -/
theorem not_antitone_truthSet {p q : α} {w : W} (hpq : p ≤ q) (hq : (f q).holds w)
    (hp : ¬ (f p).presup w) : ¬ Antitone fun p ↦ (f p).truthSet :=
  fun h ↦ hp (h hpq hq).1

end Preorder

/-! ### Strawson anti-additivity -/

section SemilatticeSup

variable [SemilatticeSup α] {f : α → PartialProp W}

/-- An operator into partial propositions is Strawson anti-additive if `f (p ⊔ q)` is Strawson
equivalent to `f p` conjoined with `f q` ([gajewski-2011]'s (36)). -/
def IsStrawsonAntiAdditive (f : α → PartialProp W) : Prop :=
  ∀ p q, (f (p ⊔ q)).strawsonEquiv ((f p).and (f q))

/-- An anti-additive assertion is Strawson anti-additive, whatever the presupposition. -/
theorem IsStrawsonAntiAdditive.of_isAntiAdditive (h : IsAntiAdditive fun p ↦ (f p).assertion) :
    IsStrawsonAntiAdditive f :=
  fun p q ↦ strawsonEquiv_of_assertion_eq (h p q)

theorem IsStrawsonAntiAdditive.isStrawsonDE (h : IsStrawsonAntiAdditive f) : IsStrawsonDE f :=
  fun p q hpq w hq hp ha ↦ by
    rw [← sup_eq_right.2 hpq] at hq ha
    exact ((h p q).1 w hq ⟨hp, sup_eq_right.2 hpq ▸ hq⟩ ha).1

/-- Strawson anti-additivity adds to Strawson downward entailingness the Strawson form of
[atlas-1996]'s pseudo-anti-additivity, that `f p` and `f q` together entail `f (p ⊔ q)`
([von-fintel-1999]'s (25); [gajewski-2011], Appendix 1). -/
theorem isStrawsonAntiAdditive_iff :
    IsStrawsonAntiAdditive f ↔
      IsStrawsonDE f ∧ ∀ p q, ((f p).and (f q)).strawsonEntails (f (p ⊔ q)) :=
  ⟨fun h ↦ ⟨h.isStrawsonDE, fun p q ↦ (h p q).2⟩, fun ⟨h, h'⟩ p q ↦
    ⟨fun w hs hpq ha ↦ ⟨h le_sup_left w hs hpq.1 ha, h le_sup_right w hs hpq.2 ha⟩, h' p q⟩⟩

/-- Without presuppositions, Strawson anti-additivity is anti-additivity. -/
theorem isStrawsonAntiAdditive_ofProp_iff {g : α → W → Prop} :
    IsStrawsonAntiAdditive (fun p ↦ ofProp (g p)) ↔ IsAntiAdditive g := by
  refine forall₂_congr fun p q ↦ ?_
  simp only [strawsonEquiv, AntisymmRel, strawsonEntails, ofProp, PartialProp.and, true_and,
    forall_const, funext_iff, Pi.inf_apply, inf_Prop_eq]
  exact ⟨fun h w ↦ propext ⟨h.1 w, h.2 w⟩, fun h ↦ ⟨fun w ↦ (h w).mp, fun w ↦ (h w).mpr⟩⟩

end SemilatticeSup

/-! ### *Only* -/

section Only

variable (x : ι) (P : ι → Set W)

/-- *Only x is P* presupposes that `x` is `P` and asserts that nothing else is
([von-fintel-1999]'s (15)). -/
def only : PartialProp W where
  presup w := w ∈ P x
  assertion w := ∀ y, y ≠ x → w ∉ P y

theorem isStrawsonAntiAdditive_only : IsStrawsonAntiAdditive (only (W := W) x) :=
  .of_isAntiAdditive fun _ _ ↦ funext fun _ ↦ propext <| by
    simp only [only, Pi.sup_apply, Pi.inf_apply, inf_Prop_eq, Set.sup_eq_union, Set.mem_union,
      not_or, imp_and, forall_and]

theorem isStrawsonDE_only : IsStrawsonDE (only (W := W) x) :=
  (isStrawsonAntiAdditive_only x).isStrawsonDE

/-- *Only John ate vegetables* does not classically entail *only John ate kale*, whose
presupposition may fail ([von-fintel-1999]'s (11)). -/
theorem not_antitone_truthSet_only :
    ¬ Antitone fun P : Bool → Set Unit ↦ (only true P).truthSet :=
  not_antitone_truthSet (p := ⊥) (q := fun y ↦ {_u | y = true}) (w := ()) bot_le
    ⟨rfl, fun _ hy h ↦ hy h⟩ id

/-- When distinct individuals yield alternatives none of which the prejacent entails, the
name-based *only* is the propositional exclusive `Focus.Particles.only` applied to the
predication of `x`, over the alternatives the name generates ([coppock-beaver-2014]'s (93)). -/
theorem only_eq_only_range (hP : ∀ y, P x ⊆ P y → y = x) :
    only x P = Focus.Particles.only (· ⊆ ·) (Set.range P) (P x) := by
  refine PartialProp.ext ?_ (funext fun w ↦ propext ?_)
  · rw [Focus.Particles.only_presup, Focus.Particles.atLeast_subset_eq (Set.mem_range_self x)]
    rfl
  · simp only [only, Focus.Particles.only_assertion, Focus.Particles.mem_atMost,
      Set.forall_mem_range]
    refine ⟨fun h y hw ↦ ?_, fun h y hyx hw ↦ hyx (hP y (h y hw))⟩
    by_cases hyx : y = x
    · exact hyx ▸ subset_rfl
    · exact absurd hw (h y hyx)

/-- Without that condition the two come apart, since two individuals with the same predication
are one alternative, entailed by the prejacent, for the exclusive but two individuals for the
name-based *only*. -/
theorem only_ne_only_range :
    only true (fun _ : Bool ↦ (.univ : Set Unit)) ≠
      Focus.Particles.only (· ⊆ ·) (Set.range fun _ : Bool ↦ (.univ : Set Unit)) .univ := by
  intro h
  have h0 : (Focus.Particles.only (· ⊆ ·) (Set.range fun _ : Bool ↦ (.univ : Set Unit))
      .univ).assertion () := fun q ⟨_, hq⟩ _ ↦ hq ▸ subset_rfl
  rw [← h] at h0
  exact h0 false Bool.false_ne_true (Set.mem_univ ())

end Only

/-! ### Temporal *since* -/

section Since

variable {T : Type*} [LinearOrder T] (ago : T → T)

/-- *It has been five years since p* presupposes that `p` held at the time `ago t` five years
before the evaluation time `t` and asserts that it has not held since ([von-fintel-1999], after
Iatridou). -/
def since (p : Set T) : PartialProp T where
  presup t := ago t ∈ p
  assertion t := Disjoint (Set.Ioc (ago t) t) p

/-- *Since* is Strawson anti-additive in its clause, as [gajewski-2011] finds von Fintel's
Strawson downward entailing operators to be. -/
theorem isStrawsonAntiAdditive_since : IsStrawsonAntiAdditive (since ago) :=
  .of_isAntiAdditive fun _ _ ↦ funext fun _ ↦ propext Set.disjoint_union_right

/-- *Since* is Strawson downward entailing. -/
theorem isStrawsonDE_since : IsStrawsonDE (since ago) :=
  (isStrawsonAntiAdditive_since ago).isStrawsonDE

/-- *It's been five years since I saw a bird of prey* does not classically entail *it's been five
years since I saw an eagle*, whose presupposition may fail. -/
theorem not_antitone_truthSet_since :
    ¬ Antitone fun p : Set ℤ ↦ (since (· - 5) p).truthSet :=
  not_antitone_truthSet (p := ∅) (q := {-5}) (w := 0) (Set.empty_subset _)
    ⟨show (0 : ℤ) - 5 ∈ ({-5} : Set ℤ) from Set.mem_singleton_iff.2 (by decide),
      show Disjoint (Set.Ioc ((0 : ℤ) - 5) 0) {-5} by simp⟩ fun h ↦ h

end Since

end NaturalLogic

/-! ### The propositional exclusive -/

namespace Focus.Particles

open NaturalLogic

variable {W ι : Type*} {S : Set W → Set W → Prop} (C : Set (Set W))

/-- On a scale refining entailment, *only* is Strawson downward entailing in its prejacent with
the alternatives held fixed ([von-fintel-1999], §3.4; [coppock-beaver-2014], fn. 22). -/
theorem isStrawsonDE_only (hS : ∀ ⦃p q r⦄, p ⊆ q → S q r → S p r) : IsStrawsonDE (only S C) :=
  .of_antitone fun _ _ hpq ↦ antitone_atMost hS hpq

/-- On the entailment scale *only* is Strawson anti-additive in its prejacent. -/
theorem isStrawsonAntiAdditive_only_subset : IsStrawsonAntiAdditive (only (· ⊆ ·) C) :=
  .of_isAntiAdditive fun p q ↦ funext fun w ↦ propext <| by
    show w ∈ Exhaustification.excludes C (p ∪ q) ↔
      w ∈ Exhaustification.excludes C p ∧ w ∈ Exhaustification.excludes C q
    rw [Exhaustification.excludes_union]
    exact Iff.rfl

theorem isStrawsonDE_only_subset : IsStrawsonDE (only (· ⊆ ·) C) :=
  (isStrawsonAntiAdditive_only_subset C).isStrawsonDE

/-- Applied to the predication of an individual, *only* is Strawson downward entailing in the
predicate with the alternatives held fixed, so NP-modifying *only* licenses negative polarity
items in the verb phrase ([coppock-beaver-2014]'s (93)). -/
theorem isStrawsonDE_only_apply (hS : ∀ ⦃p q r⦄, p ⊆ q → S q r → S p r) (x : ι) :
    IsStrawsonDE fun P : ι → Set W ↦ only S C (P x) :=
  .of_antitone fun _ _ hPQ ↦ antitone_atMost hS (hPQ x)

/-- *There only was precipitation in Medford* does not classically entail *there only was rain in
Medford*, whose presupposition, the premise [von-fintel-1999]'s (67) adds, may fail. -/
theorem not_antitone_truthSet_only_subset :
    ¬ Antitone fun p : Set Bool ↦ (only (· ⊆ ·) {{true}, .univ} p).truthSet :=
  not_antitone_truthSet (p := {true}) (q := .univ) (w := false) (Set.subset_univ _)
    ⟨⟨.univ, by simp, trivial, subset_rfl⟩, fun q hq hw ↦ by
      rcases hq with rfl | rfl
      exacts [absurd hw (by simp), subset_rfl]⟩
    fun ⟨_, _, hw, hsub⟩ ↦ by simpa using hsub hw

/-- On a scale on which a weaker alternative outranks a stronger one, here reverse entailment,
*only* is not Strawson downward entailing in its prejacent ([coppock-beaver-2014], fn. 22). The
two-world model is ours; the footnote states the claim without one. -/
theorem not_isStrawsonDE_only_superset :
    ¬ IsStrawsonDE (only (· ⊇ ·) ({{true}, .univ} : Set (Set Bool))) := fun h ↦ by
  have := h (p := {true}) (q := .univ) (Set.subset_univ _) true
    ⟨.univ, by simp, trivial, subset_rfl⟩ ⟨{true}, by simp, rfl, subset_rfl⟩
    (fun _ _ _ ↦ Set.subset_univ _) .univ (by simp) trivial
  exact absurd (this (Set.mem_univ false)) (by simp)

end Focus.Particles

/-! ### *Want*, *glad* and *sorry* -/

namespace Desire.BestWorlds

open Modality NaturalLogic

variable {W : Type*} (dox base : W → Set W) (g : W → List (W → Prop))

/-- *Want* is Strawson upward entailing in its complement ([von-fintel-1999], §3.2). -/
theorem isStrawsonUE_want : IsStrawsonUE (want base g) :=
  .of_monotone fun _ _ h _ hw ↦ hw.trans h

theorem isStrawsonUE_glad : IsStrawsonUE (glad dox base g) :=
  .of_monotone fun _ _ h _ hw ↦ hw.trans h

/-- *Glad* is not Strawson downward entailing, so it licenses no negative polarity item
([von-fintel-1999], §3.3). The subject believes world `0` and prefers world `1`, so is glad that
`0` or `1` holds but not that `0` does. -/
theorem not_isStrawsonDE_glad :
    ¬ IsStrawsonDE (glad (fun _ : Fin 3 ↦ {0}) (fun _ ↦ .univ) (fun _ ↦ [(· = 1)])) := by
  have hb : bestAmong (Set.univ : Set (Fin 3)) [(· = 1)] = {1} := by
    rw [bestAmong_eq_of_exists ⟨1, Set.mem_univ _, by simp⟩]
    ext
    simp
  intro h
  have h1 : ({1} : Set (Fin 3)) ⊆ {0} := by
    have := h (p := {0}) (q := {0, 1}) (by simp) 0
    simp only [glad, want, Want, hb] at this
    exact this ⟨by simp, Set.subset_univ _, ⟨0, by simp⟩, ⟨2, by simp⟩⟩
      ⟨subset_rfl, Set.subset_univ _, ⟨0, by simp⟩, ⟨1, by simp⟩⟩ (by simp)
  simpa using h1 (Set.mem_singleton 1)

/-- *Sorry* is Strawson anti-additive in its complement, since wanting a disjunction false is
wanting each disjunct false. -/
theorem isStrawsonAntiAdditive_regret : IsStrawsonAntiAdditive (regret dox base g) :=
  .of_isAntiAdditive fun p q ↦ funext fun w ↦ propext <| by
    show Want (g w) (base w) (p ∪ q)ᶜ ↔ Want (g w) (base w) pᶜ ∧ Want (g w) (base w) qᶜ
    rw [Set.compl_union]
    exact want_inter_iff

theorem isStrawsonDE_regret : IsStrawsonDE (regret dox base g) :=
  (isStrawsonAntiAdditive_regret dox base g).isStrawsonDE

/-- *Sorry that Robin bought a car* does not classically entail *sorry that Robin bought a Honda
Civic*, whose factive presupposition may fail ([von-fintel-1999]'s (30)). The subject believes
world `true` and prefers world `false`. -/
theorem not_antitone_truthSet_regret :
    ¬ Antitone fun p : Set Bool ↦
      (regret (fun _ ↦ {true}) (fun _ ↦ .univ) (fun _ ↦ [(· = false)]) p).truthSet := by
  refine not_antitone_truthSet (p := ∅) (q := {true}) (w := true) (Set.empty_subset _)
    ⟨⟨subset_rfl, Set.subset_univ _, ⟨true, trivial, rfl⟩, ⟨false, trivial, by simp⟩⟩, ?_⟩
    fun h ↦ h.1 rfl
  show bestAmong .univ [(· = false)] ⊆ {true}ᶜ
  rw [bestAmong_eq_of_exists ⟨false, Set.mem_univ _, by simp⟩]
  intro x hx
  simp_all

end Desire.BestWorlds

/-! ### Superlatives -/

namespace Degree

open NaturalLogic

variable {α D W : Type*} [Preorder D] (μ : α → D) (x : α)

/-- The superlative is Strawson anti-additive in its comparison class. -/
theorem isStrawsonAntiAdditive_superlative :
    IsStrawsonAntiAdditive (superlative (W := W) μ · x) :=
  .of_isAntiAdditive (isAntiAdditive_superlative_assertion μ x)

theorem isStrawsonDE_superlative : IsStrawsonDE (superlative (W := W) μ · x) :=
  (isStrawsonAntiAdditive_superlative μ x).isStrawsonDE

/-- *Emma is the tallest girl in her class* does not classically entail *Emma is the tallest girl
in her class to have learned the alphabet*, whose presupposition may fail ([von-fintel-1999]'s
(76)). -/
theorem not_antitone_truthSet_superlative :
    ¬ Antitone fun C : Unit → Set Unit ↦ (superlative (fun _ : Unit ↦ (0 : ℕ)) C ()).truthSet :=
  not_antitone_truthSet (p := ⊥) (q := fun _ ↦ .univ) (w := ()) bot_le
    ⟨trivial, fun _ _ h ↦ absurd rfl h⟩ id

end Degree

/-! ### Conditional antecedents -/

namespace Conditional

open NaturalLogic

variable {I W : Type*} (horizon : I → Set W) (q : Set W)

/-- The modal-horizon counterfactual is Strawson anti-additive in its antecedent, since a strict
conditional with a disjunctive antecedent is the conjunction of the conditionals of the disjuncts
([gajewski-2011], Appendix 1). -/
theorem isStrawsonAntiAdditive_horizonCounterfactual :
    IsStrawsonAntiAdditive (horizonCounterfactual horizon · q) :=
  .of_isAntiAdditive fun p p' ↦ funext fun i ↦ propext <| by
    show i ∈ strictImp horizon (p ∪ p') q ↔ i ∈ strictImp horizon p q ∧ i ∈ strictImp horizon p' q
    rw [strictImp_union_left]
    exact Iff.rfl

theorem isStrawsonDE_horizonCounterfactual :
    IsStrawsonDE (horizonCounterfactual horizon · q) :=
  (isStrawsonAntiAdditive_horizonCounterfactual horizon q).isStrawsonDE

/-- Strengthening the antecedent is not classically valid, since a strengthened antecedent can
fall outside the horizon ([von-fintel-1999], §4.3). -/
theorem not_antitone_truthSet_horizonCounterfactual :
    ¬ Antitone fun p : Set Unit ↦
      (horizonCounterfactual (fun _ : Unit ↦ (.univ : Set Unit)) p .univ).truthSet :=
  not_antitone_truthSet (p := ∅) (q := .univ) (w := ()) (Set.empty_subset _)
    ⟨⟨(), trivial, trivial⟩, Set.subset_univ _⟩ fun h ↦ h.ne_empty (Set.inter_empty _)

end Conditional
