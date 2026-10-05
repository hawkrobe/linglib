module

public import Linglib.Logic.Natural.Additivity
public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Modality.Kratzer.Ordering

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
* `only`, `glad`, `regret`, `superlative`, `since`, `would`: von Fintel's operators.

## Main results

* `IsStrawsonDE.of_antitone`, `IsStrawsonUE.of_monotone`,
  `IsStrawsonAntiAdditive.of_isAntiAdditive`: the classical property of the assertion suffices.
* `isStrawsonAntiAdditive_iff`: Strawson anti-additivity is Strawson downward entailingness
  together with the Strawson form of Atlas's pseudo-anti-additivity.
* `isStrawsonDE_ofProp_iff`, `isStrawsonAntiAdditive_ofProp_iff`: without presuppositions the
  Strawson notions are the classical ones.
* `isStrawsonAntiAdditive_only`, `isStrawsonAntiAdditive_regret`,
  `isStrawsonAntiAdditive_superlative`, `isStrawsonAntiAdditive_since`,
  `isStrawsonAntiAdditive_would`, `isStrawsonUE_glad`, `not_isStrawsonDE_glad`, and the
  `not_antitone_truthSet_` counterexamples.

## Implementation notes

* Strawson entailment takes the presuppositions of premise and conclusion alike as premises, as
  in von Fintel's Strawson validity and Gajewski's own proofs, rather than the literal clause of
  Gajewski's cross-categorial definition at type `t`.
* *Only* presupposes that `x` is `P`; Horn's presupposition that something is `P` gives the same
  Strawson facts, as von Fintel notes.
* *Glad* and *regret* take the belief worlds and the modal base as world-indexed sets and the
  ordering source as a world-indexed list, so their best worlds are `Modality.bestAmong`;
  following Heim, their factivity is doxastic. With suitable ordering sources *regret* also covers
  *sorry*, *amazed* and *surprised*.
* Von Fintel calls *glad* upward entailing; its presupposition that the modal base contains
  non-`p` worlds can fail at a larger argument, so `isStrawsonUE_glad` is the Strawson form he
  states for *want*.
* The superlative's degree measure does not vary with the world, and *since* reads von Fintel's
  prose meaning off world-indexed `past` and `window` sets.
* `would` is the modal-horizon conditional; the admissibility of the horizon, a condition on the
  context that does not mention the antecedent, is left to the caller.

## References

* [strawson-1952]
* [von-fintel-1999]
* [gajewski-2005]
* [gajewski-2011]
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

end Only

/-! ### *Glad* and *regret* -/

section Attitudes

open Modality

variable (dox base : W → Set W) (g : W → List (W → Prop))

/-- *a is glad that p* presupposes that `a` believes `p` and that the modal base contains the
belief worlds and both `p`-worlds and non-`p`-worlds, and asserts that the best worlds of the base
under the ordering source `g` are `p`-worlds ([von-fintel-1999]'s (50)). -/
def glad (p : Set W) : PartialProp W where
  presup w := dox w ⊆ p ∧ dox w ⊆ base w ∧ (base w ∩ p).Nonempty ∧ (base w \ p).Nonempty
  assertion w := bestAmong (base w) (g w) ⊆ p

/-- *a regrets that p* has the presupposition of *glad* and asserts that no best world of the
modal base is a `p`-world ([von-fintel-1999]'s (53)). -/
def regret (p : Set W) : PartialProp W where
  presup := (glad dox base g p).presup
  assertion w := Disjoint (bestAmong (base w) (g w)) p

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
    simp only [glad, hb] at this
    exact this ⟨by simp, Set.subset_univ _, ⟨0, by simp⟩, ⟨2, by simp⟩⟩
      ⟨subset_rfl, Set.subset_univ _, ⟨0, by simp⟩, ⟨1, by simp⟩⟩ (by simp)
  simpa using h1 (Set.mem_singleton 1)

theorem isStrawsonAntiAdditive_regret : IsStrawsonAntiAdditive (regret dox base g) :=
  .of_isAntiAdditive fun _ _ ↦ funext fun _ ↦ propext Set.disjoint_union_right

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
  show Disjoint (bestAmong .univ [(· = false)]) {true}
  rw [bestAmong_eq_of_exists ⟨false, Set.mem_univ _, by simp⟩]
  simp

end Attitudes

/-! ### Superlatives -/

section Superlative

variable [Preorder D] (μ : ι → D) (Q : ι → Set W) (a : ι)

/-- *a is the μ-est Q* presupposes that `a` is a `Q` and asserts that every other `Q` has a
smaller degree ([von-fintel-1999]'s (79)). -/
def superlative : PartialProp W where
  presup w := w ∈ Q a
  assertion w := ∀ x, w ∈ Q x → x ≠ a → μ x < μ a

theorem isStrawsonAntiAdditive_superlative :
    IsStrawsonAntiAdditive (superlative (W := W) μ · a) :=
  .of_isAntiAdditive fun _ _ ↦ funext fun _ ↦ propext <| by
    simp only [superlative, Pi.sup_apply, Pi.inf_apply, inf_Prop_eq, Set.sup_eq_union,
      Set.mem_union, or_imp, forall_and]

theorem isStrawsonDE_superlative : IsStrawsonDE (superlative (W := W) μ · a) :=
  (isStrawsonAntiAdditive_superlative μ a).isStrawsonDE

/-- At a world, the superlative holds exactly when `a` is the absolute superlative of the
`Q`-individuals there ([heim-1999]). -/
theorem holds_superlative_iff {D : Type*} [LinearOrder D] (μ : ι → D) (w : W) :
    (superlative μ Q a).holds w ↔ Degree.absoluteSuperlative μ {x | w ∈ Q x} a :=
  Iff.rfl

/-- *Emma is the tallest girl in her class* does not classically entail *Emma is the tallest girl
in her class to have learned the alphabet*, whose presupposition may fail ([von-fintel-1999]'s
(76)). -/
theorem not_antitone_truthSet_superlative :
    ¬ Antitone fun Q : Unit → Set Unit ↦ (superlative (fun _ : Unit ↦ (0 : ℕ)) Q ()).truthSet :=
  not_antitone_truthSet (p := ⊥) (q := fun _ ↦ .univ) (w := ()) bot_le
    ⟨trivial, fun _ _ h ↦ absurd rfl h⟩ id

end Superlative

/-! ### Temporal *since* -/

section Since

variable (past window : W → Set W)

/-- *It has been five years since p* presupposes a `p`-time five years ago, in `past`, and asserts
none since, in `window` ([von-fintel-1999]'s (20)–(22)). -/
def since (p : Set W) : PartialProp W where
  presup w := (past w ∩ p).Nonempty
  assertion w := Disjoint (window w) p

theorem isStrawsonAntiAdditive_since : IsStrawsonAntiAdditive (since past window) :=
  .of_isAntiAdditive fun _ _ ↦ funext fun _ ↦ propext Set.disjoint_union_right

theorem isStrawsonDE_since : IsStrawsonDE (since past window) :=
  (isStrawsonAntiAdditive_since past window).isStrawsonDE

/-- *Since I saw a bird of prey* does not classically entail *since I saw an eagle*
([von-fintel-1999]'s (20)). -/
theorem not_antitone_truthSet_since :
    ¬ Antitone fun p : Set Unit ↦ (since (fun _ ↦ .univ) (fun _ ↦ ∅) p).truthSet :=
  not_antitone_truthSet (p := ∅) (q := .univ) (w := ()) (Set.empty_subset _)
    ⟨⟨(), trivial, trivial⟩, Set.empty_disjoint _⟩ fun h ↦ h.ne_empty (Set.inter_empty _)

end Since

/-! ### Conditional antecedents -/

section Would

variable (horizon : W → Set W)

/-- *If p, would q* presupposes that the modal horizon admits `p` and asserts that every
`p`-world of the horizon is a `q`-world ([von-fintel-1999]'s (82) and (83)). -/
def would (p q : Set W) : PartialProp W where
  presup w := (horizon w ∩ p).Nonempty
  assertion w := w ∈ Conditional.strictImp horizon p q

theorem isStrawsonAntiAdditive_would (q : Set W) :
    IsStrawsonAntiAdditive (would horizon · q) :=
  .of_isAntiAdditive fun _ _ ↦ funext fun _ ↦ propext <| by
    simp only [would, Pi.inf_apply, inf_Prop_eq, Set.sup_eq_union, Conditional.mem_strictImp,
      Set.inter_union_distrib_left, Set.union_subset_iff]

theorem isStrawsonDE_would (q : Set W) : IsStrawsonDE (would horizon · q) :=
  (isStrawsonAntiAdditive_would horizon q).isStrawsonDE

/-- Strengthening the antecedent is not classically valid, since a strengthened antecedent can
fall outside the horizon ([von-fintel-1999], §4.3). -/
theorem not_antitone_truthSet_would :
    ¬ Antitone fun p : Set Unit ↦ (would (fun _ ↦ .univ) p .univ).truthSet :=
  not_antitone_truthSet (p := ∅) (q := .univ) (w := ()) (Set.empty_subset _)
    ⟨⟨(), trivial, trivial⟩, Set.subset_univ _⟩ fun h ↦ h.ne_empty (Set.inter_empty _)

end Would

end NaturalLogic
