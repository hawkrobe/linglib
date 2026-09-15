import Linglib.Semantics.Conditionals.Stalnaker

/-!
# Stalnaker (1975): Indicative Conditionals

This file formalizes [stalnaker-1975]'s account of the direct argument, *either the butler or
the gardener did it, so if the butler didn't, the gardener did*. The indicative conditional
has the selection-function truth condition of [stalnaker-1968], and entails the material
conditional without being entailed by it (`selectionConditional_imp_material`,
`not_entails_direct`). What makes the argument compelling is pragmatic: in a context, an
indicative conditional's selection function keeps to the context set whenever the antecedent
is compatible with it, and a disjunction is appropriately asserted only where each disjunct
can hold without the other. Under the constraint, a proposition accepted in the context is
accepted under any compatible antecedent (`selectionConditional_of_accepted`), the indicative
and the material conditional are accepted in the same contexts (`accepted_iff_material`), and
so the direct argument, contraposition and the hypothetical syllogism are reasonable for
indicatives though invalid (`direct_argument`, `contraposition`, `hypothetical_syllogism`).

The appendix's calculus makes reasonable inference a logical notion: a pragmatic
interpretation assigns each sentence a proposition in a context, an appropriateness relation
and a change function obeying two postulates, and an inference is reasonable when every
context in which its premisses are appropriately asserted in sequence comes to entail its
conclusion (`PragmaticInterpretation.Reasonable`). An entailment whose conclusion expresses
the same proposition in every context is reasonable (`Reasonable.of_entails`). On the
language of the direct argument, whose contexts carry a
selection function obeying the constraint, the direct argument is reasonable in the language
(`direct_argument_reasonable`) though not an entailment in it. The fatalist's argument
(`fatalism`) draws each of its conditional conclusions reasonably within the context that
supposes a disjunct, and fails only by detaching them: constructive dilemma, valid for
entailment (`Entails.or`), does not hold for reasonable inference.

## Implementation notes

A context of the conditional language is a context set together with a selection function
obeying the pragmatic constraint for it, and assertion restricts the selection function to
the updated set, so that indicatives conform to the constraint after every assertion. The
appropriateness relation encodes the paper's two generalizations, that a disjunction requires
each disjunct to be open without the other and that an indicative conditional requires a
compatible antecedent, together with the first postulate. Subjunctive conditionals, which
suspend the constraint, are outside the language; the substrate's `Mood.admissibleSelection`
carries the paper's account of the mood distinction.

## References

* [stalnaker-1975]
* [stalnaker-1968]
* [grice-1975]
* [anderson-1951]
-/

namespace Stalnaker1975

open Conditional

/-! ### The indicative conditional in a context -/

section Context

variable {W : Type*} (s : SelectionFunction W) {C : Set W} {p q r : W → Prop}

/-- The conditional entails the material conditional: at a world where the antecedent holds
the selected world is the world itself. -/
theorem selectionConditional_imp_material {w : W} (h : selectionConditional s p q w) (hp : p w) :
    q w := by
  unfold selectionConditional at h
  rwa [s.centering w {w' | p w'} hp] at h

/-- Weakening the consequent preserves the conditional. -/
theorem selectionConditional_mono (hqr : ∀ w, q w → r w) {w : W}
    (h : selectionConditional s p q w) : selectionConditional s p r w :=
  hqr _ h

/-- A proposition accepted in a context is accepted under any antecedent compatible with the
context, once the selection function obeys the pragmatic constraint. -/
theorem selectionConditional_of_accepted (hC : pragmaticConstraint s C) (hp : ∃ w ∈ C, p w)
    (hq : ∀ w ∈ C, q w) : ∀ w ∈ C, selectionConditional s p q w := λ w hw =>
  selectionConditional_eq_material_within_context s C p q w hw
    (hp.imp λ _ hv => ⟨hv.2, hv.1⟩) hC λ w' hw' _ => hq w' hw'

/-- The direct argument is reasonable: in a context accepting the disjunction where the
negated first disjunct is open, the indicative conditional is accepted. -/
theorem direct_argument (hC : pragmaticConstraint s C) (hopen : ∃ w ∈ C, ¬ p w)
    (hdisj : ∀ w ∈ C, p w ∨ q w) : ∀ w ∈ C, selectionConditional s (λ w => ¬ p w) q w :=
  λ w hw => selectionConditional_eq_material_within_context s C _ q w hw
    (hopen.imp λ _ hv => ⟨hv.2, hv.1⟩) hC λ w' hw' hnp => (hdisj w' hw').resolve_left hnp

/-- In a context compatible with the antecedent, the indicative and the material conditional
are accepted together. -/
theorem accepted_iff_material (hC : pragmaticConstraint s C) (hp : ∃ w ∈ C, p w) :
    (∀ w ∈ C, selectionConditional s p q w) ↔ ∀ w ∈ C, p w → q w :=
  ⟨λ h w hw hpw => selectionConditional_imp_material s (h w hw) hpw,
    λ h w hw => selectionConditional_eq_material_within_context s C p q w hw
      (hp.imp λ _ hv => ⟨hv.2, hv.1⟩) hC h⟩

/-- Contraposition is reasonable for indicatives: when the conditional is accepted and the
negated consequent is open, the contrapositive is accepted. -/
theorem contraposition (hC : pragmaticConstraint s C) (hq : ∃ w ∈ C, ¬ q w)
    (h : ∀ w ∈ C, selectionConditional s p q w) :
    ∀ w ∈ C, selectionConditional s (λ w => ¬ q w) (λ w => ¬ p w) w := by
  intro w hw
  have hsel : s.sel w {w' | ¬ q w'} ∈ C := hC w _ hw (hq.imp λ _ hv => ⟨hv.2, hv.1⟩)
  have hnq : ¬ q (s.sel w {w' | ¬ q w'}) := s.inclusion w _ (hq.imp λ _ hv => hv.2)
  exact λ hp => hnq (selectionConditional_imp_material s (h _ hsel) hp)

/-- The hypothetical syllogism is reasonable for indicatives: when both conditionals are
accepted and the first antecedent is open, the chained conditional is accepted. -/
theorem hypothetical_syllogism (hC : pragmaticConstraint s C) (hp : ∃ w ∈ C, p w)
    (h₁ : ∀ w ∈ C, selectionConditional s p q w) (h₂ : ∀ w ∈ C, selectionConditional s q r w) :
    ∀ w ∈ C, selectionConditional s p r w := by
  intro w hw
  have hsel : s.sel w {w' | p w'} ∈ C := hC w _ hw (hp.imp λ _ hv => ⟨hv.2, hv.1⟩)
  have hpsel : p (s.sel w {w' | p w'}) := s.inclusion w _ (hp.imp λ _ hv => hv.2)
  show r (s.sel w {w' | p w'})
  exact selectionConditional_imp_material s (p := q) (q := r) (h₂ _ hsel)
    (selectionConditional_imp_material s (p := p) (q := q) (h₁ _ hsel) hpsel)

/-- A counterfactual antecedent, one incompatible with the context, selects outside the
context set: the conditional must be subjunctive. -/
theorem sel_notMem_of_incompatible (hp : ∀ w ∈ C, ¬ p w) (hne : ∃ w, p w) (w : W) :
    s.sel w {w' | p w'} ∉ C :=
  λ hmem => hp _ hmem (s.inclusion w _ hne)

end Context

/-! ### Reasonable inference -/

/-- A pragmatic interpretation of a language (the paper's appendix): the proposition each
sentence expresses in a context, an appropriateness relation, and a change function, obeying
the two postulates that an appropriate assertion is compatible with the context and that an
assertion adds its proposition to the context set. -/
structure PragmaticInterpretation (L W K : Type*) where
  /-- The context set of a context. -/
  contextSet : K → Set W
  /-- The proposition a sentence expresses in a context. -/
  prop : L → K → Set W
  /-- Appropriateness of asserting a sentence in a context. -/
  appropriate : L → K → Prop
  /-- The context resulting from asserting a sentence. -/
  change : L → K → K
  /-- The first postulate: an appropriate assertion is compatible with the context. -/
  appropriate_compatible : ∀ P k, appropriate P k → (contextSet k ∩ prop P k).Nonempty
  /-- The second postulate: an assertion narrows the context set to its proposition. -/
  contextSet_change : ∀ P k, contextSet (change P k) = contextSet k ∩ prop P k

namespace PragmaticInterpretation

variable {L W K : Type*} (I : PragmaticInterpretation L W K)

/-- The context after asserting a sequence of sentences. -/
def changeSeq (σ : List L) (k : K) : K := σ.foldl (λ k P => I.change P k) k

/-- Sequential appropriateness: each sentence is appropriate in the context the preceding
ones produce. -/
def AppropriateSeq : List L → K → Prop
  | [], _ => True
  | P :: σ, k => I.appropriate P k ∧ AppropriateSeq σ (I.change P k)

/-- Reasonable inference: every context in which the premisses are appropriately asserted in
sequence comes to entail the conclusion. -/
def Reasonable (σ : List L) (P : L) : Prop :=
  ∀ k, I.AppropriateSeq σ k → I.contextSet (I.changeSeq σ k) ⊆ I.prop P (I.changeSeq σ k)

/-- Entailment in the language: the premiss's proposition is included in the conclusion's in
every context. -/
def Entails (P Q : L) : Prop := ∀ k, I.prop P k ⊆ I.prop Q k

/-- A sentence is rigid when it expresses the same proposition in every context. -/
def Rigid (P : L) : Prop := ∀ k k', I.prop P k = I.prop P k'

theorem changeSeq_singleton (P : L) (k : K) : I.changeSeq [P] k = I.change P k := rfl

/-- An entailment of a rigid conclusion is a reasonable inference. -/
theorem Reasonable.of_entails {P Q : L} (hQ : I.Rigid Q) (h : I.Entails P Q) :
    I.Reasonable [P] Q := λ k _ => by
  rw [changeSeq_singleton, I.contextSet_change, hQ (I.change P k) k]
  exact λ _ hw => h _ hw.2

/-- Constructive dilemma for entailment: with disjunction interpreted as union, entailments
from the disjuncts yield an entailment from the disjunction. -/
theorem Entails.or {P₁ P₂ Q₁ Q₂ P Q : L} (hP : ∀ k, I.prop P k = I.prop P₁ k ∪ I.prop P₂ k)
    (hQ : ∀ k, I.prop Q k = I.prop Q₁ k ∪ I.prop Q₂ k) (h₁ : I.Entails P₁ Q₁)
    (h₂ : I.Entails P₂ Q₂) : I.Entails P Q := λ k => by
  rw [hP, hQ]
  exact Set.union_subset_union (h₁ k) (h₂ k)

end PragmaticInterpretation

/-! ### The language of the direct argument -/

/-- The sentences: atoms, negation, disjunction, and the indicative conditional. -/
inductive Sentence (Atom : Type*)
  | atom (a : Atom)
  | not (P : Sentence Atom)
  | or (P Q : Sentence Atom)
  | ifThen (P Q : Sentence Atom)

/-- A context: a context set and a selection function obeying the pragmatic constraint for
it. -/
structure Context (W : Type*) where
  /-- The context set. -/
  set : Set W
  /-- The selection function of the context. -/
  sel : SelectionFunction W
  /-- Indicative conditionals conform to the constraint. -/
  constraint : pragmaticConstraint sel set

variable {Atom W : Type*}

/-- The proposition a sentence expresses in a context under a valuation of the atoms. -/
def Sentence.prop (V : Atom → Set W) : Sentence Atom → Context W → Set W
  | .atom a, _ => V a
  | .not P, k => (P.prop V k)ᶜ
  | .or P Q, k => P.prop V k ∪ Q.prop V k
  | .ifThen P Q, k => selectionConditional k.sel (P.prop V k) (Q.prop V k)

/-- Appropriateness: a disjunction requires each disjunct to be open without the other, an
indicative conditional requires a compatible antecedent, and every assertion is compatible
with the context. -/
def Sentence.Appropriate (V : Atom → Set W) : Sentence Atom → Context W → Prop
  | .or P Q, k =>
    (k.set ∩ (P.prop V k ∩ (Q.prop V k)ᶜ)).Nonempty ∧
      (k.set ∩ (Q.prop V k ∩ (P.prop V k)ᶜ)).Nonempty
  | .ifThen P Q, k =>
    (k.set ∩ P.prop V k).Nonempty ∧ (k.set ∩ (Sentence.ifThen P Q).prop V k).Nonempty
  | P, k => (k.set ∩ P.prop V k).Nonempty

/-- The context after accepting a proposition: the narrowed context set with the selection
function restricted to it. -/
noncomputable def Context.update (k : Context W) (P : Set W) : Context W :=
  ⟨k.set ∩ P, k.sel.restrict (k.set ∩ P), pragmaticConstraint_restrict _ _⟩

/-- The pragmatic interpretation of the language under a valuation. -/
noncomputable def interp (V : Atom → Set W) : PragmaticInterpretation (Sentence Atom) W (Context W)
    where
  contextSet := Context.set
  prop := Sentence.prop V
  appropriate := Sentence.Appropriate V
  change P k := k.update (P.prop V k)
  appropriate_compatible P k h := by
    cases P with
    | or P Q =>
      obtain ⟨w, hw, hP, -⟩ := h.1
      exact ⟨w, hw, Or.inl hP⟩
    | ifThen P Q => exact h.2
    | atom a => exact h
    | not P => exact h
  contextSet_change _ _ := rfl

/-- Reasonable inference in the language: reasonable under every valuation. -/
def ReasonableInL (W : Type*) (σ : List (Sentence Atom)) (P : Sentence Atom) : Prop :=
  ∀ V : Atom → Set W, (interp V).Reasonable σ P

/-- Entailment in the language: entailment under every valuation. -/
def EntailsInL (W : Type*) (P Q : Sentence Atom) : Prop :=
  ∀ V : Atom → Set W, (interp V).Entails P Q

/-- The indicative conditional entails the material conditional in the language. -/
theorem ifThen_entails_material (P Q : Sentence Atom) :
    EntailsInL W (.ifThen P Q) (.or (.not P) Q) := λ V k w h => by
  by_cases hp : w ∈ P.prop V k
  · exact Or.inr (selectionConditional_imp_material k.sel h hp)
  · exact Or.inl hp

/-- The direct argument is reasonable in the language: wherever a disjunction of atoms is
appropriately asserted, the context comes to accept the conditional from the negated first
disjunct to the second. -/
theorem direct_argument_reasonable (a b : Atom) :
    ReasonableInL W [.or (.atom a) (.atom b)] (.ifThen (.not (.atom a)) (.atom b)) := by
  rintro V k ⟨⟨-, hopen⟩, -⟩
  refine direct_argument (Context.sel _) (Context.constraint _) ?_ ?_
  · obtain ⟨w, hw, hb, ha⟩ := hopen
    exact ⟨w, ⟨hw, Or.inr hb⟩, ha⟩
  · exact λ w hw => hw.2

/-! ### The direct argument is not an entailment -/

/-- The suspects. -/
inductive Suspect
  | butler | gardener | someoneElse
  deriving DecidableEq, Repr

/-- The atoms of the butler-or-gardener argument. -/
inductive Culprit
  | butler | gardener
  deriving DecidableEq, Repr

/-- The valuation: each atom names its suspect. -/
def culpritOf : Culprit → Set Suspect
  | .butler => {.butler}
  | .gardener => {.gardener}

open Classical in
/-- A selection function that, off the antecedent, reaches for someone else first. -/
noncomputable def someoneElseFirst : SelectionFunction Suspect where
  sel w A :=
    if w ∈ A then w
    else if Suspect.someoneElse ∈ A then .someoneElse
    else if Suspect.gardener ∈ A then .gardener
    else .butler
  inclusion w A hA := by
    split_ifs with hw hs hg
    · exact hw
    · exact hs
    · exact hg
    · obtain ⟨v, hv⟩ := hA
      cases v with
      | butler => exact hv
      | gardener => exact absurd hv hg
      | someoneElse => exact absurd hv hs
  centering w A hw := by simp [hw]

/-- At a world where the butler did it, *the butler or the gardener did it* holds while *if the
butler didn't, the gardener did* fails: the direct argument is no entailment. -/
theorem not_entails_direct :
    ¬ EntailsInL Suspect (.or (.atom Culprit.butler) (.atom .gardener))
      (.ifThen (.not (.atom .butler)) (.atom .gardener)) := by
  intro h
  have := h culpritOf ⟨Set.univ, someoneElseFirst, λ _ _ _ _ => trivial⟩
    (show Suspect.butler ∈ (interp culpritOf).prop (.or (.atom .butler) (.atom .gardener)) _ from
      Or.inl rfl)
  change ({Suspect.gardener} : Set Suspect)
    (someoneElseFirst.sel .butler {w' | ({Suspect.butler} : Set Suspect)ᶜ w'}) at this
  have h1 : Suspect.butler ∉ ({w' | ({Suspect.butler} : Set Suspect)ᶜ w'} : Set Suspect) :=
    λ h => h rfl
  have h2 : Suspect.someoneElse ∈ ({w' | ({Suspect.butler} : Set Suspect)ᶜ w'} : Set Suspect) :=
    λ h => Suspect.noConfusion h
  simp only [someoneElseFirst, ite_eq_right h1, ite_eq_left h2] at this
  exact (by decide : Suspect.someoneElse ≠ .gardener) this

/-! ### Fatalism -/

/-- The atoms of the fatalist's argument: being killed, and taking precautions. -/
inductive Fate
  | killed | precautions
  deriving DecidableEq, Repr

/-- A world: whether one is killed, and whether one takes precautions. -/
abbrev Outcome := Bool × Bool

/-- The valuation of the fatalist's atoms. -/
def fateOf : Fate → Set Outcome
  | .killed => {w | w.1 = true}
  | .precautions => {w | w.2 = true}

open Classical in
/-- A selection function that, off the antecedent, reaches first for survival. -/
noncomputable def survivalFirst : SelectionFunction Outcome where
  sel w A :=
    if w ∈ A then w
    else if (false, true) ∈ A then (false, true)
    else if (false, false) ∈ A then (false, false)
    else if (true, true) ∈ A then (true, true)
    else (true, false)
  inclusion w A hA := by
    split_ifs with hw h1 h2 h3
    · exact hw
    · exact h1
    · exact h2
    · exact h3
    · obtain ⟨v, hv⟩ := hA
      rcases v with ⟨_ | _, _ | _⟩
      · exact absurd hv h2
      · exact absurd hv h1
      · exact hv
      · exact absurd hv h3
  centering w A hw := by simp [hw]

/-- The null context of the fatalist, with a selection function reaching first for survival. -/
noncomputable def fateCtx : Context Outcome := ⟨Set.univ, survivalFirst, λ _ _ _ _ => trivial⟩

/-- *I will be killed.* -/
def killed : Sentence Fate := .atom .killed

/-- *I take precautions.* -/
def precautions : Sentence Fate := .atom .precautions

/-- The fatalist's argument: *I will be killed or not; if I will, then even with precautions I
will be killed; if I will not, then even without precautions I will not be; so precautions are
ineffective or unnecessary*. In the null context the disjunction is appropriate, and each
conditional is accepted in the context supposing its disjunct; but the disjunction of the
conditionals is not accepted in the context of the disjunctive premiss, since at a world
where one is killed without precautions neither conditional holds. Constructive dilemma
fails for reasonable inference. -/
theorem fatalism :
    (Sentence.or killed (.not killed)).Appropriate fateOf fateCtx ∧
    (fateCtx.update (killed.prop fateOf fateCtx)).set ⊆
      (Sentence.ifThen precautions killed).prop fateOf
        (fateCtx.update (killed.prop fateOf fateCtx)) ∧
    (fateCtx.update ((Sentence.not killed).prop fateOf fateCtx)).set ⊆
      (Sentence.ifThen (.not precautions) (.not killed)).prop fateOf
        (fateCtx.update ((Sentence.not killed).prop fateOf fateCtx)) ∧
    ¬ (fateCtx.update ((Sentence.or killed (.not killed)).prop fateOf fateCtx)).set ⊆
      (Sentence.or (.ifThen precautions killed) (.ifThen (.not precautions) (.not killed))).prop
        fateOf (fateCtx.update ((Sentence.or killed (.not killed)).prop fateOf fateCtx)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (Set.univ ∩ (fateOf .killed ∩ ((fateOf .killed)ᶜ)ᶜ)).Nonempty ∧
      (Set.univ ∩ ((fateOf .killed)ᶜ ∩ (fateOf .killed)ᶜ)).Nonempty
    exact ⟨⟨(true, true), trivial, rfl, λ h => h rfl⟩,
      ⟨(false, true), trivial, Bool.false_ne_true, Bool.false_ne_true⟩⟩
  · have h1 := selectionConditional_of_accepted (survivalFirst.restrict (Set.univ ∩ fateOf .killed))
      (pragmaticConstraint_restrict _ _) (p := fateOf .precautions) (q := fateOf .killed)
      ⟨(true, true), ⟨trivial, rfl⟩, rfl⟩ λ _ hw => hw.2
    exact λ w hw => h1 w hw
  · have h2 := selectionConditional_of_accepted
      (survivalFirst.restrict (Set.univ ∩ (fateOf .killed)ᶜ)) (pragmaticConstraint_restrict _ _)
      (p := (fateOf .precautions)ᶜ) (q := (fateOf .killed)ᶜ)
      ⟨(false, false), ⟨trivial, Bool.false_ne_true⟩, Bool.false_ne_true⟩ λ _ hw => hw.2
    exact λ w hw => h2 w hw
  · intro h
    have hw := h (show (true, false) ∈ (fateCtx.update
      ((Sentence.or killed (.not killed)).prop fateOf fateCtx)).set from ⟨trivial, Or.inl rfl⟩)
    rcases hw with hw | hw
    · change fateOf .killed ((survivalFirst.restrict _).sel (true, false) _) at hw
      rw [SelectionFunction.restrict_sel_of_mem] at hw
      · simp [survivalFirst, fateOf, Sentence.prop, fateCtx, Context.update, precautions,
          killed] at hw
        have n1 : ¬ ({w : Outcome | w.2 = true} (true, false)) := Bool.false_ne_true
        have p2 : {w : Outcome | w.2 = true} (false, true) := rfl
        simp only [ite_eq_right n1, ite_eq_left p2] at hw
        exact Bool.false_ne_true hw
      · exact ⟨trivial, Or.inl rfl⟩
      · exact ⟨(false, true), rfl, trivial, Or.inr Bool.false_ne_true⟩
    · change (fateOf .killed)ᶜ ((survivalFirst.restrict _).sel (true, false) _) at hw
      rw [SelectionFunction.centering] at hw
      · exact hw rfl
      · exact Bool.false_ne_true

end Stalnaker1975
