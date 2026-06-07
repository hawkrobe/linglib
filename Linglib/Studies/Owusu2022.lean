import Linglib.Fragments.Akan.Determiners
import Linglib.Semantics.Quantification.ChoiceFunction

/-!
# [owusu-2022]: Cross-Categorial Definiteness/Familiarity

[owusu-2022] Ch 3 analyses the Akan (Kwa, Niger-Congo) indefinite *bí* as
an unambiguous choice function (after [kratzer-1998]) whose situation
pronoun ties the CF and the NP to a single index — entry (67):
⟦bí⟧ = λs.λP : CH(f_s). f_s(P(s)). The substrate type is
`SkolemCF S E := S → CF E` (`ChoiceFunction.lean`). The *nó* chapters and
the rival analyses in [bombi-2018], [schwarz-2013],
[arkoh-matthewson-2013] are left for future Studies files.

## Main declarations

* `Owusu2022.skolemDenot` — denotation table for the Fragment's
  `Akan.Determiners.Indefinite` contrast: `.bi` is a skolemized CF
  applied at the situation of its argument; `.bare` is outside the CF
  analysis.
* `Owusu2022.bi_wide_scope_under_negation` — wide scope under negation
  (∃ > ¬) for the `.bi` denotation at a fixed situation, derived from
  the substrate's `cf_wide_scope_under_negation`.
* `Owusu2022.Onipa`, `Owusu2022.preferAma` — a two-person model of
  §3.2.5 ex. (21) *Onipa bí a-n-to dwom* 'a certain person didn't sing'.
* `Owusu2022.bi_wide_scope_witnessed`, `Owusu2022.someone_sang` — on
  that model the ∃ > ¬ reading is true and the ¬ > ∃ reading false.

## Implementation notes

Wide scope under negation (data §3.2.5 exx. (21)–(22); analysis §3.3):
the CF variable is contextually given (speaker-anchored), and negation
binds no situation variable, so the CF's referent is fixed before
negation applies and ¬ > ∃ is underivable. The narrow-scope readings in
conditional antecedents (situation pronoun bound locally) and the opaque
readings under intensional verbs (a skolem *world* index, §3.3.3 after
[mirrazi-2024]) need binding machinery beyond the fixed-situation
fragment formalized here.

## Todo

* The *nó* analysis (familiarity + non-uniqueness presuppositions,
  Ch 2), alongside [bombi-2018], [schwarz-2013],
  [arkoh-matthewson-2013].
* The clausal determiner *nó* (Ch 4): definite propositions, NegP
  attachment, CPS/CG dual update.
* Narrow-scope *bí* in conditional antecedents (situation pronoun bound
  locally) and opaque *bí* under intensional verbs (skolem world index,
  §3.3.3).
* The *bí nó* (anaphoric definite) vs *nó bí* (partitive) order
  contrast (§3.4).
-/

open Semantics.Quantification.ChoiceFunction

namespace Owusu2022

open Akan.Determiners

/-- [owusu-2022]'s denotation table for the Akan indefinite contrast:
*bí* applies a skolemized choice function at the situation of its
argument (entry (67)); bare NPs (kind/indefinite readings, App. A) are
outside the CF analysis. -/
def skolemDenot {S E : Type*} (f : SkolemCF S E) (s₀ : S) :
    Indefinite → Option ((E → Prop) → E)
  | .bi => some (f.apply s₀)
  | .bare => none

/-- [owusu-2022]'s wide-scope-under-negation prediction (§3.2.5, §3.3)
for the `skolemDenot` denotation of `Indefinite.bi`: at a fixed
situation `s₀` the CF's output satisfies `VP` whenever the non-empty
restrictor entails `VP` — the ∃ > ¬ reading. -/
theorem bi_wide_scope_under_negation {S E : Type*}
    {f : SkolemCF S E} {s₀ : S} (hf : (f s₀).isCorrect)
    {N VP : E → Prop} (hN : ∃ x, N x) (hAll : ∀ x, N x → VP x) :
    ∀ d ∈ skolemDenot f s₀ .bi, VP (d N) := by
  rintro d hd
  obtain rfl : f.apply s₀ = d := Option.some.inj hd
  exact cf_wide_scope_under_negation (f s₀) hf N VP hN hAll

/-! ### A two-person model of ex. (21)

*Onipa bí a-n-to dwom* 'person INDEF PERF-NEG-sing song' = 'A certain
person didn't sing' ([owusu-2022] §3.2.5 ex. (21), judged
Indefinite ≫ Neg only). Two people — *Kofi* and *Ama*, common Twi
day-names — exhaust the domain *onipa* 'person'; Kofi sang, Ama did
not. -/

/-- *onipa* 'person' (Akan/Twi). The atomic restrictor type. -/
inductive Onipa where | kofi | ama
  deriving DecidableEq

/-- *to dwom* 'sing (a) song': Kofi sang, Ama did not. -/
def ToDwom : Onipa → Prop
  | .kofi => True
  | .ama => False

instance : DecidablePred ToDwom := fun x => match x with
  | .kofi => isTrue trivial
  | .ama => isFalse id

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
denotation picks *Ama* from the *onipa* domain, and she did not sing. -/
theorem bi_wide_scope_witnessed :
    ∀ d ∈ skolemDenot preferAma () .bi, ¬ ToDwom (d (fun _ => True)) := by
  rintro d hd
  obtain rfl : preferAma.apply () = d := Option.some.inj hd
  simp only [SkolemCF.apply, preferAma, if_true]
  exact id

/-- The narrow-scope (¬ > ∃) reading of ex. (21) — 'no person sang' —
is false on this model: Kofi sang. -/
theorem someone_sang : ∃ x : Onipa, ToDwom x := ⟨.kofi, trivial⟩

end Owusu2022
