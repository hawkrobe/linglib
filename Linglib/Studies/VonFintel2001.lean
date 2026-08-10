import Mathlib.Data.Set.Basic
import Linglib.Semantics.Conditionals.Basic
import Linglib.Semantics.Exhaustification.Operators.Basic

/-!
# von Fintel (2001): Conditional Strengthening

[von-fintel-2001] derives conditional perfection ([geis-zwicky-1971]) from
answer-level exhaustivity, reconstructing [cornulier-1983]'s "presumption of
exhaustivity" via [groenendijk-stokhof-1984]'s exhaustive answers: a
conditional asserted as the answer to "under which conditions does C hold?"
is exhaustified against the answers naming alternative triggers.
Exhaustification excludes the alternative triggers; when the salient triggers
cover every route to C, the strengthened answer yields
`conditionalPerfection`. When they cover only a narrower set, the coverage
premise fails and only relativized perfection arises (the paper's
after-midnight example).

The paper runs the exclusion step as a Gamut-style quantity implicature; here
it is the project-canonical innocent-exclusion operator `exhIE`
([spector-2016]).

## Main results

* `exhaustifiedAnswer`: `exhIE` at the answer level — the answer "trigger `t`
  causes C" with the alternative triggers' answers excluded.
* `exhaustification_yields_perfection`: if the alternative answers are
  innocently excludable and the salient triggers cover C, the exhaustified
  answer entails `conditionalPerfection`.
-/

namespace VonFintel2001

open Semantics.Conditionals Exhaustification

variable {ι W : Type*}

/-- The answers competing with "trigger `t` causes C": `causes t'` for the
other salient triggers `t'`. -/
def answerAlternatives (causes : ι → Set W) (triggers : Set ι) (t : ι) :
    Set (Set W) :=
  causes '' (triggers \ {t})

/-- The exhaustified answer: assert "trigger `t` causes C" and innocently
exclude the alternative triggers' answers. -/
def exhaustifiedAnswer (causes : ι → Set W) (triggers : Set ι) (t : ι) :
    Set W :=
  exhIE (answerAlternatives causes triggers t) (causes t)

variable {causes : ι → Set W} {triggers : Set ι} {t t' : ι} {p C : Set W}
  {w : W}

@[simp] theorem mem_answerAlternatives {q : Set W} :
    q ∈ answerAlternatives causes triggers t ↔
      ∃ t' ∈ triggers, t' ≠ t ∧ causes t' = q := by
  simp [answerAlternatives, and_assoc]

/-- Exclusion and coverage entail perfection: if trigger `t` requires `p`, no
alternative salient trigger causes C at `w`, and every C-world has a salient
trigger, then `w ∈ conditionalPerfection p C`. -/
theorem perfection_from_exclusion_and_coverage
    (h_req : w ∈ causes t → w ∈ p)
    (h_excl : ∀ t' ∈ triggers, t' ≠ t → w ∉ causes t')
    (h_cov : w ∈ C → ∃ t' ∈ triggers, w ∈ causes t') :
    w ∈ conditionalPerfection p C := by
  intro hnp hC
  obtain ⟨t', ht', hct'⟩ := h_cov hC
  rcases eq_or_ne t' t with rfl | hne
  · exact hnp (h_req hct')
  · exact h_excl t' ht' hne hct'

/-- The exhaustified answer excludes each innocently excludable alternative
trigger at the world of evaluation. -/
theorem exhaustifiedAnswer_excludes
    (h_exh : w ∈ exhaustifiedAnswer causes triggers t)
    (h_ie : IsInnocentlyExcludable
      (answerAlternatives causes triggers t) (causes t) (causes t')) :
    w ∉ causes t' :=
  h_exh _ h_ie.2

/-- Answer-level exhaustification yields perfection: if trigger `t` requires
`p`, every alternative salient trigger's answer is innocently excludable, and
the salient triggers cover C, then the exhaustified answer entails
`conditionalPerfection p C`. -/
theorem exhaustification_yields_perfection
    (h_req : causes t ⊆ p)
    (h_ie : ∀ t' ∈ triggers, t' ≠ t →
      IsInnocentlyExcludable
        (answerAlternatives causes triggers t) (causes t) (causes t'))
    (h_cov : w ∈ C → ∃ t' ∈ triggers, w ∈ causes t')
    (h_exh : w ∈ exhaustifiedAnswer causes triggers t) :
    w ∈ conditionalPerfection p C :=
  perfection_from_exclusion_and_coverage (fun h => h_req h)
    (fun t' ht' hne => exhaustifiedAnswer_excludes h_exh (h_ie t' ht' hne))
    h_cov

/-- Exclusion is essential: requirement and coverage alone do not yield
perfection. Witness: a second salient trigger fires at a world outside `p`,
so the paper's counterexample typology (a QUD that does not elicit an
exhaustive list of sufficient conditions) predicts no perfection. -/
theorem coverage_without_exclusion_insufficient :
    ∃ (W ι : Type) (causes : ι → Set W) (triggers : Set ι) (t : ι)
      (p C : Set W) (w : W),
      t ∈ triggers ∧ causes t ⊆ p ∧
      (∀ w ∈ C, ∃ t' ∈ triggers, w ∈ causes t') ∧
      w ∉ conditionalPerfection p C :=
  ⟨Bool, Bool, fun t => {w | w = t}, Set.univ, true, {w | w = true},
    Set.univ, false, Set.mem_univ _, fun _ hw => hw,
    fun w _ => ⟨w, Set.mem_univ w, rfl⟩,
    fun h => h Bool.false_ne_true (Set.mem_univ false)⟩

end VonFintel2001
