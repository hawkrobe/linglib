/-
# PLA Semantics
@cite{dekker-2012}

Satisfaction and truth for Predicate Logic with Anaphora.

## Key Concepts

### Witness Sequences
Pronouns are interpreted via witness sequences ê = (e₁,..., eₙ).
Unlike variables (interpreted by assignments), pronouns get their values
from outside the formula through the witness sequence.

### Satisfaction
M, g, ê ⊨ φ means formula φ is satisfied in model M relative to:
- Assignment g (for variables)
- Witness sequence ê (for pronouns)

### Truth
M ⊨ φ means φ is true in M: for all assignments g, there exists a witness
sequence ê such that M, g, ê ⊨ φ.

-/

import Linglib.Theories.Semantics.Dynamic.PLA.Basic
import Linglib.Theories.Semantics.Dynamic.Core.DynamicTy2
import Linglib.Theories.Semantics.Dynamic.Core.Translation

namespace Semantics.Dynamic.PLA

open Classical
open Semantics.Dynamic.Core


/-- An assignment maps variable indices to entities -/
abbrev Assignment (E : Type*) := VarIdx → E

/-- A witness sequence maps pronoun indices to entities -/
abbrev WitnessSeq (E : Type*) := PronIdx → E

/-- Update an assignment at a single variable: g[i ↦ e] -/
def Assignment.update {E : Type*} (g : Assignment E) (i : VarIdx) (e : E) : Assignment E :=
  λ j => if j = i then e else g j

notation g "[" i " ↦ " e "]" => Assignment.update g i e

@[simp]
theorem Assignment.update_same {E : Type*} (g : Assignment E) (i : VarIdx) (e : E) :
    (g[i ↦ e]) i = e := by simp [Assignment.update]

@[simp]
theorem Assignment.update_other {E : Type*} (g : Assignment E) (i j : VarIdx) (e : E) (h : j ≠ i) :
    (g[i ↦ e]) j = g j := by simp [Assignment.update, h]

/-- A model provides predicate interpretations -/
structure Model (E : Type*) where
  /-- Interpretation: predicate name → argument tuple → truth value -/
  interp : String → List E → Bool


/--
Evaluate a term given assignment g and witness sequence ê.

⟦x_i⟧^{g,ê} = g(i) (variables from assignment)
⟦p_i⟧^{g,ê} = ê(i) (pronouns from witness sequence)

Variables and pronouns have different interpretation sources.
-/
def Term.eval {E : Type*} (g : Assignment E) (ê : WitnessSeq E) : Term → E
  | .var i => g i
  | .pron i => ê i

@[simp]
theorem Term.eval_var {E : Type*} (g : Assignment E) (ê : WitnessSeq E) (i : VarIdx) :
    (Term.var i).eval g ê = g i := rfl

@[simp]
theorem Term.eval_pron {E : Type*} (g : Assignment E) (ê : WitnessSeq E) (i : PronIdx) :
    (Term.pron i).eval g ê = ê i := rfl


/--
PLA Satisfaction: M, g, ê ⊨ φ

@cite{dekker-2012} Definition 4, Ch. 2 (PLA Satisfaction and Truth, p.22; adapted to type-theoretic setting).

- Atomic: check predicate interpretation on evaluated terms
- Negation: classical negation
- Conjunction: both conjuncts satisfied
- Existential: witness exists in domain
-/
def Formula.sat {E : Type*} [Nonempty E] (M : Model E) (g : Assignment E) (ê : WitnessSeq E) :
    Formula → Prop
  | .atom name ts => M.interp name (ts.map (Term.eval g ê))
  | .neg φ => ¬φ.sat M g ê
  | .conj φ ψ => φ.sat M g ê ∧ ψ.sat M g ê
  | .exists_ i φ => ∃ e : E, φ.sat M (g[i ↦ e]) ê

/-- Truth in a model: M ⊨ φ iff for all g, ∃ê such that M, g, ê ⊨ φ -/
def Formula.trueIn {E : Type*} [Nonempty E] (M : Model E) (φ : Formula) : Prop :=
  ∀ g : Assignment E, ∃ ê : WitnessSeq E, φ.sat M g ê


/-- Double negation elimination -/
theorem Formula.sat_neg_neg {E : Type*} [Nonempty E] (M : Model E) (g : Assignment E)
    (ê : WitnessSeq E) (φ : Formula) :
    (∼(∼φ)).sat M g ê ↔ φ.sat M g ê := by
  simp only [Formula.sat]
  exact Classical.not_not

/-- Conjunction elimination (left) -/
theorem Formula.sat_conj_left {E : Type*} [Nonempty E] (M : Model E) (g : Assignment E)
    (ê : WitnessSeq E) (φ ψ : Formula) :
    (φ ⋀ ψ).sat M g ê → φ.sat M g ê := And.left

/-- Conjunction elimination (right) -/
theorem Formula.sat_conj_right {E : Type*} [Nonempty E] (M : Model E) (g : Assignment E)
    (ê : WitnessSeq E) (φ ψ : Formula) :
    (φ ⋀ ψ).sat M g ê → ψ.sat M g ê := And.right

/-- Conjunction introduction -/
theorem Formula.sat_conj_intro {E : Type*} [Nonempty E] (M : Model E) (g : Assignment E)
    (ê : WitnessSeq E) (φ ψ : Formula) :
    φ.sat M g ê → ψ.sat M g ê → (φ ⋀ ψ).sat M g ê := And.intro

/-- Existential introduction -/
theorem Formula.sat_exists_intro {E : Type*} [Nonempty E] (M : Model E) (g : Assignment E)
    (ê : WitnessSeq E) (i : VarIdx) (φ : Formula) (e : E) :
    φ.sat M (g[i ↦ e]) ê → (Formula.exists_ i φ).sat M g ê :=
  λ h => ⟨e, h⟩


/--
Term evaluation under resolution: when ê(i) = g(ρ(i)), evaluation is preserved.
-/
theorem Term.eval_resolve {E : Type*} (g : Assignment E) (ê : WitnessSeq E) (ρ : Resolution)
    (t : Term) (h : ∀ i, t = .pron i → ê i = g (ρ i)) :
    t.eval g ê = (t.resolve ρ).eval g ê := by
  cases t with
  | var i => rfl
  | pron i =>
    simp only [eval, resolve]
    exact h i rfl

/--
Resolution Correctness (@cite{dekker-2012} Observation 7, §2.2, p.30).

If the witness sequence agrees with the assignment via resolution (ê = g ∘ ρ on pronouns),
and no pronoun resolves to a bound variable, then satisfaction is preserved:

  M, g, ê ⊨ φ ↔ M, g, ê ⊨ φ^ρ
-/
theorem Formula.sat_resolve {E : Type*} [Nonempty E]
    (M : Model E) (g : Assignment E) (ê : WitnessSeq E) (ρ : Resolution)
    (φ : Formula)
    (hcompat : ∀ i ∈ φ.range, ê i = g (ρ i))
    (hnoCapture : ∀ i ∈ φ.range, ρ i ∉ φ.domain) :
    φ.sat M g ê ↔ (φ.resolve ρ).sat M g ê := by
  induction φ generalizing g ê with
  | atom name ts =>
    simp only [sat, resolve]
    have heq : (ts.map (Term.resolve ρ)).map (Term.eval g ê) = ts.map (Term.eval g ê) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro t ht
      simp only [Function.comp_apply]
      cases t with
      | var i => rfl
      | pron i =>
        simp only [Term.resolve, Term.eval]
        symm
        apply hcompat
        rw [range_atom, mem_termsPronouns]
        exact ⟨.pron i, ht, by simp [Term.pronouns]⟩
    simp only [heq]
  | neg φ ih =>
    simp only [sat, resolve]
    rw [ih g ê (λ i hi => hcompat i hi) (λ i hi => hnoCapture i hi)]
  | conj φ ψ ih1 ih2 =>
    simp only [sat, resolve]
    have h1 := ih1 g ê
      (λ i hi => hcompat i (range_conj_left φ ψ hi))
      (λ i hi => by
        have := hnoCapture i (range_conj_left φ ψ hi)
        simp only [domain] at this ⊢
        exact λ hc => this (Finset.mem_union_left _ hc))
    have h2 := ih2 g ê
      (λ i hi => hcompat i (range_conj_right φ ψ hi))
      (λ i hi => by
        have := hnoCapture i (range_conj_right φ ψ hi)
        simp only [domain] at this ⊢
        exact λ hc => this (Finset.mem_union_right _ hc))
    rw [h1, h2]
  | exists_ j φ ih =>
    simp only [sat, resolve]
    have hcompat' : ∀ e, ∀ i ∈ φ.range, ê i = (g[j ↦ e]) (ρ i) := by
      intro e i hi
      have hne : ρ i ≠ j := by
        have := hnoCapture i hi
        simp only [domain] at this
        exact λ heq => this (by rw [heq]; exact Finset.mem_insert_self j _)
      simp only [Assignment.update, if_neg hne]
      exact hcompat i hi
    have hnoCapture' : ∀ i ∈ φ.range, ρ i ∉ φ.domain := by
      intro i hi
      have := hnoCapture i hi
      simp only [domain] at this ⊢
      exact λ hc => this (Finset.mem_insert_of_mem hc)
    exact exists_congr (λ e => ih (g[j ↦ e]) ê (hcompat' e) hnoCapture')


section Examples

/-- "A man walked. He sat down." -/
def exManWalkedIn : Formula :=
  (Formula.exists_ 0 (Formula.atom "Man" [.var 0] ⋀ Formula.atom "WalkedIn" [.var 0]))
  ⋀ Formula.atom "SatDown" [.pron 0]

/-- Resolution: p₀ → x₀ -/
def exResolution : Resolution := λ _ => 0

/-- The resolved formula has no pronouns -/
example : (exManWalkedIn.resolve exResolution).range = ∅ :=
  Formula.resolve_no_pronouns exManWalkedIn exResolution

end Examples


/-- For pronoun-free terms, evaluation doesn't depend on the witness sequence. -/
theorem Term.eval_witness_irrelevant {E : Type*} (t : Term) (ht : t.pronouns = ∅)
    (g : Assignment E) (ê₁ ê₂ : WitnessSeq E) :
    t.eval g ê₁ = t.eval g ê₂ := by
  cases t with
  | var _ => rfl
  | pron i => simp [Term.pronouns] at ht


/-- Observation 4 (@cite{dekker-2012} §2.2, p.25): PLA and PL equivalence.

For pronoun-free formulas, satisfaction is independent of the witness sequence.
This shows PLA conservatively extends PL: standard predicate logic formulas have
the same truth conditions in PLA as in PL. -/
theorem obs4_pla_pl_equivalence {E : Type*} [Nonempty E] (M : Model E)
    (φ : Formula) (hfree : φ.range = ∅)
    (g : Assignment E) (ê₁ ê₂ : WitnessSeq E) :
    φ.sat M g ê₁ ↔ φ.sat M g ê₂ := by
  induction φ generalizing g with
  | atom name ts =>
    simp only [Formula.sat]
    have h : ts.map (Term.eval g ê₁) = ts.map (Term.eval g ê₂) := by
      apply List.map_congr_left
      intro t ht
      cases t with
      | var _ => rfl
      | pron i =>
        exfalso
        have : i ∈ (Formula.atom name ts).range := by
          rw [Formula.range_atom, mem_termsPronouns]
          exact ⟨.pron i, ht, Finset.mem_singleton_self i⟩
        simp [hfree] at this
    rw [h]
  | neg φ ih =>
    simp only [Formula.sat]
    exact not_congr (ih hfree g)
  | conj φ ψ ih₁ ih₂ =>
    simp only [Formula.sat]
    have hφ : φ.range = ∅ := by
      apply Finset.subset_empty.mp
      calc φ.range ⊆ (φ ⋀ ψ).range := Formula.range_conj_left φ ψ
        _ = ∅ := hfree
    have hψ : ψ.range = ∅ := by
      apply Finset.subset_empty.mp
      calc ψ.range ⊆ (φ ⋀ ψ).range := Formula.range_conj_right φ ψ
        _ = ∅ := hfree
    exact and_congr (ih₁ hφ g) (ih₂ hψ g)
  | exists_ j φ ih =>
    simp only [Formula.sat]
    exact exists_congr (λ e => ih hfree (g[j ↦ e]))


/--
Observation 5 (@cite{dekker-2012} §2.2): Relevance.

Satisfaction depends only on the values of free variables and pronouns
that actually occur in the formula. Assignments that agree on freeVars
and witness sequences that agree on range yield the same satisfaction.
-/
theorem obs5_relevance {E : Type*} [Nonempty E] (M : Model E)
    (φ : Formula) (g₁ g₂ : Assignment E) (ê₁ ê₂ : WitnessSeq E)
    (hg : ∀ x ∈ φ.freeVars, g₁ x = g₂ x)
    (hê : ∀ i ∈ φ.range, ê₁ i = ê₂ i) :
    φ.sat M g₁ ê₁ ↔ φ.sat M g₂ ê₂ := by
  induction φ generalizing g₁ g₂ ê₁ ê₂ with
  | atom name ts =>
    simp only [Formula.sat]
    have h : ts.map (Term.eval g₁ ê₁) = ts.map (Term.eval g₂ ê₂) := by
      apply List.map_congr_left
      intro t ht
      cases t with
      | var i =>
        simp only [Term.eval]
        apply hg
        simp only [Formula.freeVars, Finset.mem_biUnion, List.mem_toFinset]
        exact ⟨.var i, ht, Finset.mem_singleton_self i⟩
      | pron i =>
        simp only [Term.eval]
        apply hê
        rw [Formula.range_atom, mem_termsPronouns]
        exact ⟨.pron i, ht, Finset.mem_singleton_self i⟩
    rw [h]
  | neg φ ih =>
    simp only [Formula.sat]
    exact not_congr (ih g₁ g₂ ê₁ ê₂ hg hê)
  | conj φ ψ ih₁ ih₂ =>
    simp only [Formula.sat]
    have hgφ : ∀ x ∈ φ.freeVars, g₁ x = g₂ x :=
      λ x hx => hg x (Finset.mem_union_left _ hx)
    have hgψ : ∀ x ∈ ψ.freeVars, g₁ x = g₂ x :=
      λ x hx => hg x (Finset.mem_union_right _ hx)
    have hêφ : ∀ i ∈ φ.range, ê₁ i = ê₂ i :=
      λ i hi => hê i (Finset.mem_union_left _ hi)
    have hêψ : ∀ i ∈ ψ.range, ê₁ i = ê₂ i :=
      λ i hi => hê i (Finset.mem_union_right _ hi)
    exact and_congr (ih₁ g₁ g₂ ê₁ ê₂ hgφ hêφ) (ih₂ g₁ g₂ ê₁ ê₂ hgψ hêψ)
  | exists_ j φ ih =>
    simp only [Formula.sat]
    apply exists_congr
    intro e
    apply ih
    · intro x hx
      simp only [Assignment.update]
      split
      · rfl
      · rename_i hne
        apply hg
        exact Finset.mem_erase.mpr ⟨hne, hx⟩
    · intro i hi
      exact hê i hi


-- ════════════════════════════════════════════════════════════════
-- § Embedding into Dynamic Ty2 @cite{muskens-1996}
-- ════════════════════════════════════════════════════════════════

/-! PLA distinguishes variables (`VarIdx`) from pronouns (`PronIdx`);
Dynamic Ty2 has a single dref type `S → E`. The embedding uses the
sum type `(VarIdx ⊕ PronIdx) → E` as the `S` parameter, providing
type-safe separation without magic numbers. Because PLA updates are
eliminative (filter, never extend), every PLA formula translates to
a `test` in Dynamic Ty2. -/

/-- PLA assignment merging variable and pronoun assignments via sum type:
`.inl i` accesses variable `i`, `.inr i` accesses pronoun `i`. -/
abbrev MergedAssignment (E : Type*) := (VarIdx ⊕ PronIdx) → E

/-- Variable dref: projection at `.inl i`. -/
def varDref {E : Type*} (i : VarIdx) : Dref (MergedAssignment E) E :=
  λ g => g (.inl i)

/-- Pronoun dref: projection at `.inr i`. -/
def pronDref {E : Type*} (i : PronIdx) : Dref (MergedAssignment E) E :=
  λ g => g (.inr i)

/-- Interpret a PLA term as a Dynamic Ty2 dref. -/
def termToDref {E : Type*} : Term → Dref (MergedAssignment E) E
  | .var i => varDref i
  | .pron i => pronDref i

/-- Convert `PLAPoss` to merged assignment. -/
def plaPossToMerged {E : Type*} (p : PLAPoss E) : MergedAssignment E
  | .inl i => p.assignment i
  | .inr i => p.witnesses i

/-- Convert merged assignment to `PLAPoss`. -/
def mergedToPLAPoss {E : Type*} (g : MergedAssignment E) : PLAPoss E :=
  { assignment := λ i => g (.inl i)
  , witnesses := λ i => g (.inr i) }

theorem plaPoss_roundtrip {E : Type*} (p : PLAPoss E) :
    mergedToPLAPoss (plaPossToMerged p) = p := by
  simp only [mergedToPLAPoss, plaPossToMerged]

theorem merged_roundtrip {E : Type*} (g : MergedAssignment E) :
    plaPossToMerged (mergedToPLAPoss g) = g := by
  funext x
  cases x <;> rfl


section Embedding

variable {E : Type*} [Nonempty E]

/-- Functional update for merged assignments (only affects variables). -/
def extend (g : MergedAssignment E) (i : VarIdx) (e : E) : MergedAssignment E :=
  λ x => match x with
    | .inl j => if j = i then e else g (.inl j)
    | .inr j => g (.inr j)

/-- Evaluate a term given a merged assignment. -/
def evalTerm (g : MergedAssignment E) : Term → E
  | .var i => g (.inl i)
  | .pron i => g (.inr i)

/-- Translate a PLA formula to a Dynamic Ty2 condition.

PLA existentials check for *existence* of a witness but don't extend the
assignment (eliminative semantics). -/
def formulaToCondition (M : Model E) : Formula → Condition (MergedAssignment E)
  | .atom name ts => λ g => M.interp name (ts.map (evalTerm g))
  | .neg φ => λ g => ¬(formulaToCondition M φ g)
  | .conj φ ψ => λ g => formulaToCondition M φ g ∧ formulaToCondition M ψ g
  | .exists_ x φ => λ g => ∃ e : E, formulaToCondition M φ (extend g x e)

/-- Translate a PLA formula to a Dynamic Ty2 DRS. PLA's eliminative
updates mean every formula translates to a `test`. -/
def formulaToDRS (M : Model E) (φ : Formula) : DRS (MergedAssignment E) :=
  test (formulaToCondition M φ)

theorem formulaToDRS_atom (M : Model E) (name : String) (ts : List Term) :
    formulaToDRS M (.atom name ts) =
      test (λ g => M.interp name (ts.map (evalTerm g))) := rfl

theorem formulaToDRS_neg (M : Model E) (φ : Formula) :
    formulaToDRS M (∼φ) = test (λ g => ¬formulaToCondition M φ g) := rfl

theorem formulaToDRS_conj (M : Model E) (φ ψ : Formula) :
    formulaToDRS M (φ ⋀ ψ) =
      test (λ g => formulaToCondition M φ g ∧ formulaToCondition M ψ g) := rfl

theorem formulaToDRS_exists (M : Model E) (x : VarIdx) (φ : Formula) :
    formulaToDRS M (.exists_ x φ) =
      test (λ g => ∃ e : E, formulaToCondition M φ (extend g x e)) := rfl

/-- Split a merged assignment into variable and witness components. -/
def splitAssignment (g : MergedAssignment E) : Assignment E × WitnessSeq E :=
  (λ i => g (.inl i), λ i => g (.inr i))

theorem evalTerm_eq_Term_eval (g : MergedAssignment E) (t : Term) :
    evalTerm g t = t.eval (splitAssignment g).1 (splitAssignment g).2 := by
  cases t with
  | var i => rfl
  | pron i => rfl

theorem extend_fst_eq_update (g : MergedAssignment E) (x : VarIdx) (e : E) :
    (splitAssignment (extend g x e)).1 = (splitAssignment g).1[x ↦ e] := by
  ext n
  simp only [splitAssignment, extend, Assignment.update]

theorem extend_snd_eq (g : MergedAssignment E) (x : VarIdx) (e : E) :
    (splitAssignment (extend g x e)).2 = (splitAssignment g).2 := by
  ext n
  simp only [splitAssignment, extend]

theorem formulaToCondition_eq_sat (M : Model E) (φ : Formula) (g : MergedAssignment E) :
    formulaToCondition M φ g ↔ φ.sat M (splitAssignment g).1 (splitAssignment g).2 := by
  induction φ generalizing g with
  | atom name ts =>
    simp only [formulaToCondition, Formula.sat, splitAssignment]
    have h : ts.map (evalTerm g) = ts.map (Term.eval (λ i => g (.inl i)) λ i => g (.inr i)) := by
      apply List.map_congr_left
      intro t _
      exact evalTerm_eq_Term_eval g t
    rw [h]
  | neg φ ih =>
    simp only [formulaToCondition, Formula.sat]
    exact not_congr (ih g)
  | conj φ ψ ih1 ih2 =>
    simp only [formulaToCondition, Formula.sat]
    exact and_congr (ih1 g) (ih2 g)
  | exists_ x φ ih =>
    simp only [formulaToCondition, Formula.sat]
    constructor
    · intro ⟨e, he⟩
      use e
      rw [ih (extend g x e)] at he
      rw [extend_fst_eq_update, extend_snd_eq] at he
      exact he
    · intro ⟨e, he⟩
      use e
      rw [ih (extend g x e)]
      rw [extend_fst_eq_update, extend_snd_eq]
      exact he

/-- A merged assignment satisfies the embedded DRS iff the split
assignment satisfies the original PLA formula. -/
theorem formulaToDRS_correct (M : Model E) (φ : Formula) (g h : MergedAssignment E) :
    formulaToDRS M φ g h ↔ (g = h ∧ φ.sat M (splitAssignment g).1 (splitAssignment g).2) := by
  simp only [formulaToDRS, test]
  constructor
  · intro ⟨heq, hcond⟩
    subst heq
    exact ⟨rfl, (formulaToCondition_eq_sat M φ g).mp hcond⟩
  · intro ⟨heq, hsat⟩
    subst heq
    exact ⟨rfl, (formulaToCondition_eq_sat M φ g).mpr hsat⟩

end Embedding

end Semantics.Dynamic.PLA
