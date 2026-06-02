import Linglib.Fragments.Akan.Determiners
import Linglib.Semantics.Quantification.ChoiceFunction

/-!
# [owusu-2022]: Cross-Categorial Definiteness/Familiarity

Selected formalization from Augustina Owusu's doctoral dissertation
(Rutgers, 2022), focused here on the indefinite *bí* in Akan (Kwa,
Niger-Congo). The dissertation's analysis of the definite *nó* and
the clausal/cross-categorial uses is left for future Studies files,
where it will sit alongside the rival analyses in [bombi-2018],
[schwarz-2013], and [arkoh-matthewson-2013].

## Main declarations

* `Akan.Determiners.Indefinite.bi_wide_scope_under_negation`
  — Owusu's prediction that *bí* under negation takes wide scope,
  derived from the substrate's `cf_wide_scope_under_negation` applied
  at a fixed situation of a `SkolemCF`.
* `Owusu2022.Nipa` — a 2-person Akan-flavored domain (Kofi, Ama).
* `Owusu2022.preferAma` — a `SkolemCF` witness that selects Ama
  whenever the restrictor allows it.
* `Owusu2022.bi_wide_scope_witnessed` — the wide-scope reading of
  *Nipa bí an-ba* 'a certain person didn't come' is true in a model
  where Ama is the non-comer.

## Implementation notes

Per [owusu-2022] Ch 3, *bí* is "an unambiguous choice function
with an implicit skolemworld/situation variable" (Abstract p. iii),
"always skolemized to the situation of its argument". The substrate
type is `SkolemCF S E := S → CF E` (`ChoiceFunction.lean`); a
*bí*-DP's denotation at evaluation situation s₀ is `f.apply s₀ N`
for some correct skolem CF `f` and NP-property `N`. The wide-scope-
under-negation prediction (Owusu §3.2.2; cf. [zimmermann-2026]
§3.3 ex. 15) follows because negation is non-intensional and so
cannot shift the situation argument; the skolem CF's output is fixed
before negation applies. The narrow-scope readings within islands
and opaque readings within intensional verbs that [owusu-2022]
also documents (Abstract p. iii) require local situation-binding
machinery beyond the present scope.

## References

* [owusu-2022] Ch 3 — the *bí* choice-function analysis.
* [zimmermann-2026] §3.3 — the Hausa *wani* / Akan *bí* contrast.

## Todo

* Owusu's *nó* analysis (familiarity + non-uniqueness presuppositions,
  Ch 2) — alongside [bombi-2018], [schwarz-2013],
  [arkoh-matthewson-2013].
* The clausal-determiner *nó* (Ch 4): definite propositions, NegP
  attachment, CPS/CG dual update.
* Narrow-scope readings of *bí* within islands and opaque readings
  within intensional verbs (Abstract p. iii) — requires local
  situation binding.
* The *bí nó* / *nó bí* word-order contrast (Ch 3.4): specific
  definite vs. partitive.
-/

open Semantics.Quantification.ChoiceFunction

namespace Akan.Determiners.Indefinite

/-- [owusu-2022]'s wide-scope-under-negation prediction for the
*bí* entry. Given a `SkolemCF` evaluated at situation `s₀` and a
non-empty restrictor whose members all satisfy `VP`, the CF's output
at `s₀` also satisfies `VP` — yielding the ∃ > ¬ reading. The
situation argument `s₀` is shared between the CF and the NP-property
(Owusu's "always skolemized to the situation of its argument",
Abstract p. iii); since negation is non-intensional it cannot shift
this situation, so the CF's output is fixed before negation applies. -/
theorem bi_wide_scope_under_negation {S E : Type*}
    (f : SkolemCF S E) (s₀ : S) (hf : (f s₀).isCorrect)
    {N VP : E → Prop} (hN : ∃ x, N x) (hAll : ∀ x, N x → VP x) :
    VP (f.apply s₀ N) :=
  cf_wide_scope_under_negation (f s₀) hf N VP hN hAll

end Akan.Determiners.Indefinite

namespace Owusu2022

open Akan.Determiners

/-! ### A 2-person Akan-flavored domain

Two people — *Kofi* and *Ama*, common Twi day-names — exhaust the
domain *nipa* 'person'. *Ama* did not come (*an-ba*); *Kofi* did.
This is the minimal domain on which Owusu's wide-scope-under-negation
prediction for *bí* (Ch 3.2.2) is observable. -/

/-- *nipa* 'person' (Akan/Twi). The atomic restrictor type. -/
inductive Nipa where | kofi | ama
  deriving DecidableEq, Repr

/-- *ba-e* 'came-PERF': Kofi came, Ama did not. -/
def Baa : Nipa → Prop
  | .kofi => True
  | .ama => False

instance : DecidablePred Baa := fun x => match x with
  | .kofi => isTrue trivial
  | .ama => isFalse id

/-! ### A `SkolemCF` witness for *Nipa bí an-ba*

The CF *preferAma* selects Ama whenever the restrictor admits her;
otherwise it falls back to Kofi. The situation parameter is `Unit`
(one situation suffices for this finite domain); the CF is constant
across situations. -/

section
open Classical

/-- A correct `SkolemCF` skolemized to the trivial situation `Unit`,
which selects *Ama* whenever the restrictor allows it. -/
noncomputable def preferAma : SkolemCF Unit Nipa :=
  fun _ P => if P .ama then .ama else .kofi

theorem preferAma_correct : preferAma.isCorrect := by
  intro _ P ⟨x, hPx⟩
  show P (preferAma () P)
  unfold preferAma
  split_ifs with h
  · exact h
  · cases x
    · exact hPx
    · exact absurd hPx h

end

/-! ### Wide-scope reading of *Nipa bí an-ba*

*Nipa bí an-ba* 'a certain person didn't come' under Owusu's
wide-scope CF analysis: the skolem CF returns *Ama* (who did not
come), so the ∃¬ reading holds. The narrow-scope (¬∃) reading would
assert no one came, which is false on this model (Kofi came). -/

/-- The wide-scope reading of *Nipa bí an-ba* is witnessed: there is
a particular *nipa* — namely *Ama* — who did not come, and
*preferAma* picks her out. -/
theorem bi_wide_scope_witnessed :
    ¬ Baa (preferAma.apply () (fun x => ¬ Baa x)) := by
  show ¬ Baa (preferAma () (fun x => ¬ Baa x))
  unfold preferAma
  rw [if_pos (show ¬ Baa Nipa.ama from id)]
  exact id

/-- The narrow-scope (¬∃) reading of *Nipa bí an-ba* would say that
no *nipa* came. False on this model: Kofi came. -/
theorem bi_narrow_scope_false :
    ¬ ¬ ∃ x : Nipa, Baa x :=
  fun h => h ⟨.kofi, trivial⟩

end Owusu2022
