import Mathlib.Data.Set.Insert
import Linglib.Data.Examples.Yalcin2007

/-!
# Yalcin (2007): Epistemic Modals

This file formalizes [yalcin-2007]'s domain semantics for epistemic modals and the puzzle of
epistemic contradictions, sentences of the form *it is raining and it might not be raining*
or *it is not raining and it might be raining*. Unlike Moore-paradoxical sentences, which are
unassertable but embed happily under *suppose* and in conditional antecedents, epistemic
contradictions are unsupposable, and a relational semantics cannot explain this, since it
makes them true at some world (`exists_relational_contra`). Domain semantics evaluates a
sentence at an index of an information parameter, a set of worlds, and a world, with the
epistemic possibility modal quantifying existentially over the parameter (`Sentence.might`).
Attitude verbs shift the parameter to the attitude state and quantify over it (`supposes`),
so the universal quantifier of *suppose* is trumped by an embedded modal
(`supposes_might_iff`), an attitude with an embedded possibility modal is the attitude's dual
(`supposes_might_iff_not_supposes_neg`), and no state of supposition accepts an epistemic
contradiction (`not_supposes_contra`). An indicative conditional shifts the parameter to the
largest nonempty substate accepting its antecedent and quantifies over it (`ifThen`), so
conditionals with an epistemic contradiction as antecedent are never true
(`ifThen_contra_false`), and the conditional with an epistemic necessity in its consequent is
equivalent to the plain one (`ifThen_must_iff`). Three notions of consequence are compared.
Standard and diagonal consequence preserve truth at points, the latter at points whose world
lies in the information state; informational consequence preserves acceptance, truth
throughout a state evaluated at that state (`InfoConsequence`). Informational consequence
validates Łukasiewicz's principle, epistemic contradiction, and the nonfactivity of epistemic
possibility together (`lukasiewicz`, `epistemic_contradiction`, `nonfactivity`), which no
classical consequence relation can, while diagonal consequence rejects epistemic contradiction
(`not_diagonal_epistemic_contradiction`); on factual sentences informational consequence is
classical (`factual_classical`). The dual necessity modal yields the same results
(`not_accepted_neg_must`).

## Implementation notes

The context coordinate is fixed throughout, so a sentence is a function of the index alone.
The largest nonempty substate accepting the antecedent is characterized rather than
constructed, and a conditional is true only if it exists. The probabilistic extension of the
information parameter in the paper's seventh section is not modelled.

## References

* [yalcin-2007]
* [kaplan-1989]
* [veltman-1996]
* [stephenson-2007]
-/

namespace Yalcin2007

variable {W : Type*}

/-- A sentence relative to a fixed context: truth at an index consisting of an information
parameter, a set of worlds, and a world. -/
abbrev Sentence (W : Type*) := Set W → W → Prop

namespace Sentence

variable (φ ψ : Sentence W)

/-- A nonepistemic sentence places a condition on the world alone. -/
def ofProp (p : Set W) : Sentence W := λ _ w => w ∈ p

def neg : Sentence W := λ s w => ¬ φ s w

def conj : Sentence W := λ s w => φ s w ∧ ψ s w

/-- Epistemic possibility: existential quantification over the information parameter. -/
def might : Sentence W := λ s _ => ∃ w' ∈ s, φ s w'

/-- Epistemic necessity: universal quantification over the information parameter. -/
def must : Sentence W := λ s _ => ∀ w' ∈ s, φ s w'

/-- A sentence is accepted in a state when it is true at every world of the state, relative
to that state. -/
def AcceptedIn (s : Set W) : Prop := ∀ w ∈ s, φ s w

/-- Iterating epistemic possibility adds nothing. -/
theorem might_might : φ.might.might = φ.might := by
  ext s w
  constructor
  · rintro ⟨_, _, h⟩; exact h
  · rintro ⟨w', hw', h⟩; exact ⟨w', hw', w', hw', h⟩

/-- Necessity is the dual of possibility. -/
theorem must_eq_neg_might_neg : φ.must = φ.neg.might.neg := by
  ext s w; simp [must, might, neg]

end Sentence

open Sentence

/-- The epistemic contradiction *not p and it might be that p*. -/
def contra (p : Set W) : Sentence W := (ofProp p).neg.conj (ofProp p).might

/-- The epistemic contradiction *p and it might be that not p*. -/
def contra' (p : Set W) : Sentence W := (ofProp p).conj (ofProp p).neg.might

/-- No nonempty state accepts an epistemic contradiction. -/
theorem not_accepted_contra {p s : Set W} (hs : s.Nonempty) : ¬ (contra p).AcceptedIn s := by
  intro h
  obtain ⟨w, hw⟩ := hs
  obtain ⟨-, w', hw', hp⟩ := h w hw
  exact (h w' hw').1 hp

theorem not_accepted_contra' {p s : Set W} (hs : s.Nonempty) : ¬ (contra' p).AcceptedIn s := by
  intro h
  obtain ⟨w, hw⟩ := hs
  obtain ⟨-, w', hw', hp⟩ := h w hw
  exact hp (h w' hw').1

/-! ### Relational semantics -/

/-- Epistemic possibility under an accessibility relation. -/
def relMight (R : W → W → Prop) (p : Set W) : Set W := {w | ∃ w', R w w' ∧ w' ∈ p}

/-- A relational semantics makes an epistemic contradiction true at a world, so it cannot
explain why the contradiction cannot be supposed. -/
theorem exists_relational_contra :
    ∃ (R : Bool → Bool → Prop) (p : Set Bool) (w : Bool), w ∉ p ∧ w ∈ relMight R p :=
  ⟨λ _ _ => True, {true}, false, by simp, ⟨true, trivial, rfl⟩⟩

/-! ### Attitudes -/

variable {φ ψ : Sentence W} {s : Set W} {w : W}

/-- *x supposes φ*: φ holds at every world compatible with the supposition, relative to the
state of supposition, which the verb makes the information parameter. -/
def supposes (S : W → Set W) (φ : Sentence W) : Sentence W :=
  λ _ w => ∀ w' ∈ S w, φ (S w) w'

theorem supposes_iff_accepted {S : W → Set W} : supposes S φ s w ↔ φ.AcceptedIn (S w) :=
  Iff.rfl

/-- The universal quantifier of the attitude is trumped by an embedded possibility modal. -/
theorem supposes_might_iff {S : W → Set W} (hne : (S w).Nonempty) :
    supposes S φ.might s w ↔ ∃ w' ∈ S w, φ (S w) w' := by
  constructor
  · intro h; obtain ⟨v, hv⟩ := hne; exact h v hv
  · intro h _ _; exact h

/-- Attitude plus epistemic possibility is the attitude's dual. -/
theorem supposes_might_iff_not_supposes_neg {S : W → Set W} (hne : (S w).Nonempty) :
    supposes S φ.might s w ↔ ¬ supposes S φ.neg s w := by
  rw [supposes_might_iff hne]
  simp [supposes, neg]

/-- No state of supposition satisfies an epistemic contradiction. -/
theorem not_supposes_contra {S : W → Set W} {p : Set W} (hne : (S w).Nonempty) :
    ¬ supposes S (contra p) s w :=
  not_accepted_contra hne

/-! ### Indicative conditionals -/

/-- `s'` is the largest nonempty substate of `s` accepting `α`. -/
def IsMaxAccepting (s : Set W) (α : Sentence W) (s' : Set W) : Prop :=
  s' ⊆ s ∧ s'.Nonempty ∧ α.AcceptedIn s' ∧
    ∀ t ⊆ s, t.Nonempty → α.AcceptedIn t → t ⊆ s'

/-- The indicative conditional: the consequent holds throughout the largest nonempty substate
accepting the antecedent, relative to that substate. -/
def ifThen (α ψ : Sentence W) : Sentence W :=
  λ s _ => ∃ s', IsMaxAccepting s α s' ∧ ψ.AcceptedIn s'

/-- For a factual antecedent the shifted state is the intersection, when nonempty. -/
theorem isMaxAccepting_ofProp (p : Set W) (hne : (s ∩ p).Nonempty) :
    IsMaxAccepting s (ofProp p) (s ∩ p) :=
  ⟨Set.inter_subset_left, hne, λ _ hw => hw.2, λ t ht _ hacc w hw => ⟨ht hw, hacc w hw⟩⟩

/-- A conditional whose antecedent is an epistemic contradiction is never true. -/
theorem ifThen_contra_false {p : Set W} : ¬ ifThen (contra p) ψ s w := by
  rintro ⟨s', ⟨-, hne, hacc, -⟩, -⟩
  exact not_accepted_contra hne hacc

/-- The conditional with an epistemic necessity in its consequent is equivalent to the plain
conditional: the necessity's quantification is trumped by the conditional's. -/
theorem ifThen_must_iff {α : Sentence W} : ifThen α ψ.must s w ↔ ifThen α ψ s w := by
  constructor
  · rintro ⟨s', hmax, h⟩
    obtain ⟨v, hv⟩ := hmax.2.1
    exact ⟨s', hmax, h v hv⟩
  · rintro ⟨s', hmax, h⟩
    exact ⟨s', hmax, λ _ _ => h⟩

/-! ### Consequence -/

/-- Standard consequence preserves truth at every point. -/
def StandardConsequence (Γ : List (Sentence W)) (φ : Sentence W) : Prop :=
  ∀ s w, (∀ γ ∈ Γ, γ s w) → φ s w

/-- Diagonal consequence preserves truth at the diagonal points, those whose world lies in
the information state. -/
def DiagonalConsequence (Γ : List (Sentence W)) (φ : Sentence W) : Prop :=
  ∀ s w, w ∈ s → (∀ γ ∈ Γ, γ s w) → φ s w

/-- Informational consequence preserves acceptance. -/
def InfoConsequence (Γ : List (Sentence W)) (φ : Sentence W) : Prop :=
  ∀ s, (∀ γ ∈ Γ, γ.AcceptedIn s) → φ.AcceptedIn s

/-- The absurd sentence. -/
def bot : Sentence W := ofProp ∅

theorem DiagonalConsequence.of_standard {Γ : List (Sentence W)}
    (h : StandardConsequence Γ φ) : DiagonalConsequence Γ φ :=
  λ s w _ hΓ => h s w hΓ

/-- Łukasiewicz's principle: from *not p*, *it is not possible that p*. -/
theorem lukasiewicz (p : Set W) : InfoConsequence [(ofProp p).neg] (ofProp p).might.neg := by
  intro s h w hw ⟨w', hw', hp⟩
  exact h _ List.mem_cons_self w' hw' hp

/-- Epistemic contradiction: *not p and it might be that p* is absurd. -/
theorem epistemic_contradiction (p : Set W) : InfoConsequence [contra p] bot := by
  intro s h w hw
  exact absurd (h _ List.mem_cons_self) (not_accepted_contra ⟨w, hw⟩)

/-- Nonfactivity: *it might be that p* does not yield *p*. -/
theorem nonfactivity :
    ¬ InfoConsequence [(ofProp {true}).might] (ofProp ({true} : Set Bool)) := by
  intro h
  have := h Set.univ (by
    simp only [List.mem_singleton, forall_eq]
    intro _ _; exact ⟨true, trivial, rfl⟩) false trivial
  simp [ofProp] at this

/-- Diagonal consequence rejects epistemic contradiction: with more than one world
epistemically possible at a context, a contradiction is true at its diagonal point. -/
theorem not_diagonal_epistemic_contradiction :
    ¬ DiagonalConsequence [contra ({true} : Set Bool)] bot := by
  intro h
  have := h Set.univ false trivial (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨by simp [ofProp, neg], true, trivial, rfl⟩)
  simp [bot, ofProp] at this

/-- Diagonal consequence is nonfactive as well. -/
theorem not_diagonal_factivity :
    ¬ DiagonalConsequence [(ofProp {true}).might] (ofProp ({true} : Set Bool)) := by
  intro h
  have := h Set.univ false trivial (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨true, trivial, rfl⟩)
  simp [ofProp] at this

/-- On factual sentences informational consequence is classical: a conjunction with a negated
sentence is absurd exactly when the other conjunct entails that sentence. -/
theorem factual_classical (p q : Set W) :
    InfoConsequence [(ofProp p).neg.conj (ofProp q)] bot ↔
      InfoConsequence [ofProp q] (ofProp p) := by
  constructor
  · intro h s hq w hw
    by_contra hp
    have := h {w} (by
      simp only [List.mem_singleton, forall_eq]
      intro v hv
      rw [Set.mem_singleton_iff.mp hv]
      exact ⟨hp, hq _ List.mem_cons_self w hw⟩) w rfl
    simp [bot, ofProp] at this
  · intro h s hs w hw
    have hc := hs _ List.mem_cons_self
    refine absurd (h s ?_ w hw) (hc w hw).1
    simp only [List.mem_singleton, forall_eq]
    exact λ v hv => (hc v hv).2

/-- Informational consequence is nonclassical: epistemic contradiction and nonfactivity, which
no classical consequence relation admits together. -/
theorem not_classical :
    InfoConsequence [contra ({true} : Set Bool)] bot ∧
      ¬ InfoConsequence [(ofProp {true}).might] (ofProp ({true} : Set Bool)) :=
  ⟨epistemic_contradiction _, nonfactivity⟩

/-! ### Epistemic necessity -/

/-- *Not p and it must be that p* is accepted by no nonempty state. -/
theorem not_accepted_neg_must {p : Set W} (hs : s.Nonempty) :
    ¬ ((ofProp p).neg.conj (ofProp p).must).AcceptedIn s := by
  intro h
  obtain ⟨w, hw⟩ := hs
  exact (h w hw).1 ((h w hw).2 w hw)

end Yalcin2007
