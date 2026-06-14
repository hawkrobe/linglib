import Linglib.Fragments.Akan.Determiners
import Linglib.Semantics.Quantification.ChoiceFunction

/-!
# [owusu-2022]: Cross-Categorial Definiteness/Familiarity

[owusu-2022] Ch 3 analyses the Akan (Kwa, Niger-Congo) indefinite *bí* as
an unambiguous choice function (after [kratzer-1998-pseudoscope]) whose
situation pronoun ties the CF and the NP to a single index — entry (67):
⟦bí⟧ = λs.λP : CH(f_s). f_s(P(s)). The substrate type is
`SkolemCF S E := S → CF E` (`ChoiceFunction.lean`). The *nó* chapters and
the rival analyses in [bombi-2018], [schwarz-2013],
[arkoh-matthewson-2013] are left for future Studies files.

## Main declarations

* `Owusu2022.skolemDenot` — denotation table for the Fragment's
  `Akan.Determiners.Indefinite` contrast: `.bi` is a skolemized CF
  applied at the situation of its argument; `.bare` is not CF-analyzed
  here.
* `Owusu2022.bi_wide_scope_specific` — the ∃ > ¬ reading of the `.bi`
  denotation is specific (its witness is the CF's choice), derived from
  the substrate's `cf_wide_scope_specific`.
* `Owusu2022.tying_contentful` — entry (67)'s same-index tying of CF
  and restrictor is contentful in both coordinates.
* `Owusu2022.Onipa`, `Owusu2022.preferAma` — a two-person model of
  §3.2.5 ex. (21) *Onipa bí a-n-to dwom* 'a certain person didn't sing'.
* `Owusu2022.bi_wide_scope_witnessed`, `Owusu2022.someone_sang` — on
  that model the ∃ > ¬ reading is true while the ¬ > ∃ reading is false,
  the configuration where the two readings diverge.

## Implementation notes

Wide scope under negation (data §3.2.5 exx. (21)–(22); analysis §3.3):
the CF variable is contextually given (speaker-anchored), and negation
binds no situation variable, so the CF's referent is fixed before
negation applies and ¬ > ∃ is underivable. The general lemma states what
the ∃ > ¬ reading entails; the two-person model witnesses it on a model
falsifying ¬ > ∃ — the case where the readings come apart. The
operator-side derivation — extensional operators provably neutralize the
situation pronoun's free/bound distinction, situation quantifiers
provably separate it — lives in the substrate
(`Semantics/Quantification/ChoiceFunction`: `bound_free_collapse`,
`bound_free_diverge_box`). The narrow-scope readings in conditional
antecedents (situation pronoun bound locally) and the opaque readings
under intensional verbs (a skolem *world* index, §3.3.3, following
Mirrazi's world-skolemized CFs — a 2019 ms., published as
[mirrazi-2024]) need binding machinery beyond the fixed-situation
fragment formalized here, as do the functional readings bound by
individual quantifiers (the *biara* subject/object asymmetry via weak
crossover on the individual skolem index).

## Todo

* The *nó* analysis (familiarity + non-uniqueness presuppositions,
  Ch 2), alongside [bombi-2018], [schwarz-2013],
  [arkoh-matthewson-2013].
* The clausal determiner *nó* (Ch 4): definite propositions, NegP
  attachment, CPS/CG dual update.
* Narrow-scope *bí* in conditional antecedents (situation pronoun bound
  locally) and opaque *bí* under intensional verbs (skolem world index,
  §3.3.3).
* The individual skolem index: functional readings under *biara*
  'every' and the subject/object asymmetry via weak crossover (§3.3).
* The over-generation argument against free ∃-closure: the unavailable
  ∃-below-negation reading (the analysis' (50)) and the
  downward-entailing weak-truth-conditions scenario.
* The *bí nó* (anaphoric definite) vs *nó bí* (partitive) order
  contrast (§3.4).
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
    Indefinite → Option (Core.Intension S (E → Prop) → E)
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
    {P : Core.Intension S (E → Prop)} {VP : E → Prop} (hN : ∃ x, P s₀ x) :
    ∀ d ∈ skolemDenot f s₀ .bi, ¬ VP (d P) → ∃ x, P s₀ x ∧ ¬ VP x := by
  simp only [skolemDenot_bi, Option.mem_some_iff, forall_eq']
  exact cf_wide_scope_specific (f s₀) hf hN

/-- Entry (67)'s same-index tying is contentful in both coordinates:
a single CF/restrictor pair where the tied denotation `f_s(P(s))`
differs from the restrictor-shifted variant `f_s(P(s'))` and from the
CF-index-shifted variant `f_s'(P(s))`. -/
theorem tying_contentful :
    ∃ (S E : Type) (f : SkolemCF S E) (P : Core.Intension S (E → Prop))
      (s s' : S), f.applyIntension s P ≠ f s (P s') ∧
        f.applyIntension s P ≠ f s' (P s) := by
  classical
  refine ⟨Bool, Bool × Bool,
    fun s N => (s, if N (s, true) then true else false),
    fun s x => x.2 = s, true, false, ?_, ?_⟩
  · simp only [SkolemCF.applyIntension]
    rw [if_pos trivial, if_neg (fun h => Bool.noConfusion h)]
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
  fun _ P => if P .ama then .ama else .kofi

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
      ¬ ToDwom (d (Core.Intension.rigid (fun _ => True))) := by
  simp only [skolemDenot_bi, Option.mem_some_iff, forall_eq']
  simp only [SkolemCF.applyIntension, Core.Intension.rigid, preferAma,
    if_true]
  exact id

/-- The narrow-scope (¬ > ∃) reading of ex. (21) — 'no person sang' —
is false on this model: Kofi sang. -/
theorem someone_sang : ∃ x : Onipa, ToDwom x := ⟨.kofi, trivial⟩

end Owusu2022
