import Linglib.Fragments.Akan.Determiners
import Linglib.Semantics.Quantification.ChoiceFunction

/-!
# Owusu (2022): Cross-Categorial Definiteness/Familiarity

This file formalizes the third chapter of [owusu-2022], on the Akan indefinite *bí* as an
unambiguous choice function after [kratzer-1998-pseudoscope] whose situation pronoun ties the
function and the noun phrase to one index, the dissertation's entry (67): *bí* applies a
skolemized choice function to its restrictor at the situation of its argument
(`skolemDenot`). The ∃ > ¬ reading of *bí* under negation is specific, its witness being the
function's choice, and the tying of the two indices is contentful in both coordinates
(`bi_wide_scope_specific`, `tying_contentful`); a two-person model of the dissertation's
example (21), *Onipa bí a-n-to dwom* 'a certain person didn't sing', makes the wide-scope
reading true and the narrow-scope reading false (`bi_wide_scope_witnessed`, `someone_sang`).

## Implementation notes

The substrate type is the skolemized choice function of
`Semantics/Quantification/ChoiceFunction`, and the bare noun phrase is not analysed here, bare
nouns receiving kind and indefinite readings outside the choice-function analysis. Wide scope
under negation follows because the choice-function variable is contextually given and
negation binds no situation variable, so the function's referent is fixed before negation
applies and ¬ > ∃ is underivable; the general lemma states what the ∃ > ¬ reading entails, and
the model witnesses it where the two readings come apart. The narrow-scope readings in
conditional antecedents, the opaque readings under intensional verbs by a skolem world index
after [mirrazi-2024], and the functional readings bound by individual quantifiers need binding
machinery beyond the fixed-situation fragment formalized here.

## TODO

* The *nó* analysis of the second chapter, familiarity with a non-uniqueness presupposition,
  alongside [bombi-2018], [schwarz-2013], and [arkoh-matthewson-2013].
* The clausal determiner *nó* of the fourth chapter.
* Narrow-scope *bí* in conditional antecedents and opaque *bí* under intensional verbs.
* The individual skolem index and the subject/object asymmetry with *biara* 'every'.
* The over-generation argument against free existential closure.
* The *bí nó* against *nó bí* order contrast.

## References

* [owusu-2022]
* [kratzer-1998-pseudoscope]
* [mirrazi-2024]
* [bombi-2018]
* [schwarz-2013]
* [arkoh-matthewson-2013]
-/

open Quantification.ChoiceFunction

namespace Owusu2022

open Akan.Determiners

/-- [owusu-2022]'s denotation table for the Akan indefinite contrast:
*bí* applies a skolemized choice function to an intensional restrictor
at the situation of its argument (entry (67); the same index feeds the
CF and the restrictor — `SkolemCF.applyIntension`). The `.bare` cell is
`none` — *not CF-analyzed here*, not undefined: bare NPs receive
kind/indefinite readings (App. A) outside the CF analysis. -/
def skolemDenot {S E : Type*} (f : SkolemCF S E) (s₀ : S) :
    Indefinite → Option ((S → E → Prop) → E)
  | .bi => some (f.applyIntension s₀)
  | .bare => none

@[simp] theorem skolemDenot_bi {S E : Type*} (f : SkolemCF S E) (s₀ : S) :
    skolemDenot f s₀ .bi = some (f.applyIntension s₀) := rfl

@[simp] theorem skolemDenot_bare {S E : Type*} (f : SkolemCF S E) (s₀ : S) :
    skolemDenot f s₀ .bare = none := rfl

/-- [owusu-2022]'s wide-scope-under-negation prediction (§3.2.5, §3.3)
for the `.bi` denotation: the ∃ > ¬ reading is *specific* — if the
CF-selected member of the (at `s₀`) non-empty restrictor fails `VP`,
some restrictor member fails `VP`, witnessed by the CF's choice. It does
not entail the narrow-scope ¬ > ∃ (see the model below). -/
theorem bi_wide_scope_specific {S E : Type*}
    {f : SkolemCF S E} {s₀ : S} (hf : (f s₀).isCorrect)
    {P : S → E → Prop} {VP : E → Prop} (hN : ∃ x, P s₀ x) :
    ∀ d ∈ skolemDenot f s₀ .bi, ¬ VP (d P) → ∃ x, P s₀ x ∧ ¬ VP x := by
  simp only [skolemDenot_bi, Option.mem_some_iff, forall_eq']
  exact cf_wide_scope_specific (f s₀) hf hN

/-- Entry (67)'s same-index tying is contentful in both coordinates:
a single CF/restrictor pair where the tied denotation `f_s(P(s))`
differs from the restrictor-shifted variant `f_s(P(s'))` and from the
CF-index-shifted variant `f_s'(P(s))`. -/
theorem tying_contentful :
    ∃ (S E : Type) (f : SkolemCF S E) (P : S → E → Prop)
      (s s' : S), f.applyIntension s P ≠ f s (P s') ∧
        f.applyIntension s P ≠ f s' (P s) := by
  classical
  refine ⟨Bool, Bool × Bool,
    λ s N => (s, if N (s, true) then true else false),
    λ s x => x.2 = s, true, false, ?_, ?_⟩
  · simp only [SkolemCF.applyIntension]
    rw [if_pos trivial, if_neg (λ h => Bool.noConfusion h)]
    decide
  · simp only [SkolemCF.applyIntension]
    rw [if_pos trivial]
    decide

/-! ### A two-person model of ex. (21)

*Onipa bí a-n-to dwom* 'person INDEF PERF-NEG-sing song' = 'A certain
person didn't sing' ([owusu-2022] §3.2.5 ex. (21), judged
Indefinite ≫ Neg only). Two people — *Kofi* and *Ama*, common Twi
day-names — exhaust the domain *onipa* 'person'; Kofi sang, Ama did
not. -/

/-- *onipa* 'person' (Akan/Twi). The atomic restrictor type. -/
inductive Onipa where | kofi | ama

/-- *to dwom* 'sing (a) song': Kofi sang, Ama did not. -/
def ToDwom : Onipa → Prop
  | .kofi => True
  | .ama => False

open Classical in
/-- A correct `SkolemCF` over the trivial situation `Unit` that selects
*Ama* whenever the restrictor allows it, else *Kofi*. -/
noncomputable def preferAma : SkolemCF Unit Onipa :=
  λ _ P => if P .ama then .ama else .kofi

theorem preferAma_correct : preferAma.isCorrect := by
  intro _ P ⟨x, hPx⟩
  unfold preferAma
  split_ifs with h
  · exact h
  · cases x
    · exact hPx
    · exact absurd hPx h

/-- The wide-scope (∃ > ¬) reading of ex. (21) is witnessed: the `.bi`
denotation picks *Ama* from the (rigid, on this one-situation model)
*onipa* domain, and she did not sing. -/
theorem bi_wide_scope_witnessed :
    ∀ d ∈ skolemDenot preferAma () .bi,
      ¬ ToDwom (d (λ _ _ => True)) := by
  simp only [skolemDenot_bi, Option.mem_some_iff, forall_eq']
  simp only [SkolemCF.applyIntension, preferAma, if_true]
  exact id

/-- The narrow-scope (¬ > ∃) reading of ex. (21) — 'no person sang' —
is false on this model: Kofi sang. -/
theorem someone_sang : ∃ x : Onipa, ToDwom x := ⟨.kofi, trivial⟩

end Owusu2022
