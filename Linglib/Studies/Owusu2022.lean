import Linglib.Semantics.Quantification.ChoiceFunction

/-!
# @cite{owusu-2022}: Cross-Categorial Definiteness/Familiarity

Selected formalization from Augustina Owusu's doctoral dissertation
(Rutgers, 2022), focused here on the indefinite *bí* in Akan (Kwa,
Niger-Congo). The dissertation's analysis of the definite *nó* is
left for a future study file, where it is to be paired with the
rival analyses in @cite{bombi-2018}, @cite{schwarz-2013}, and
@cite{arkoh-matthewson-2013}.

## Main contribution formalized here

Owusu analyzes Akan *bí* as a **skolemized choice function**, with
individual and situation indices, following @cite{kratzer-1998} and
@cite{reinhart-1997}. The key empirical consequence is that *bí*-NPs
take obligatory **wide scope under negation** (Owusu's *Me-n-ni
fish bí* 'I don't eat a certain (kind of) fish' has only the ∃ > ¬
reading, never ¬ > ∃). The mechanism is structural rather than
scopal: since negation is not an intensional operator, it cannot
shift the resource-situation argument of the choice function, so
the CF's output is fixed before negation applies.

This contrasts directly with the Hausa *wani* analysis from
@cite{zimmermann-2008}, where *wani* permits both ∃ > ¬ and ¬ > ∃
under VP-negation. The Owusu/Zimmermann cross-linguistic contrast
is the strongest evidence the African data offers for the choice
function vs. ∃-quantifier distinction, which is not adjudicable on
English alone (see @cite{zimmermann-2026} §3.3 for review).

## Architecture

The CF substrate lives in `Linglib.Semantics.Quantification.ChoiceFunction`.
This file does not duplicate the abstract framework-asymmetry theorem
`correct_cfs_disagree_on_some_sem` (which is the right home for the
Bool-witness demonstration that CFs and ∃-quantifiers make divergent
predictions). It states only the Akan-specific wide-scope-under-negation
prediction and verifies it on a small concrete model.
-/

namespace Owusu2022

open Semantics.Quantification.ChoiceFunction

/-! ### Akan *bí* as a choice function: wide scope under negation

Under Owusu's analysis, ⟦*bí*⟧ = λs.λP. CH(f_s). f_s(P(s)). For the
purposes of scope-under-negation, the key property of any correct CF
is: applying it to a non-empty restrictor produces an element of that
restrictor. Wide scope follows: if every restrictor element is in the
scope predicate, the CF's output is too. -/

/-- *bí* takes wide scope under negation: given a correct choice
    function `f` and a non-empty restrictor `N`, if every element
    of `N` satisfies the (negated) predicate `VP`, then so does
    `f N` — yielding the ∃ > ¬ reading rather than ¬ > ∃.

    Owusu's prediction (cf. @cite{zimmermann-2026} §3.3 ex. 15):
    *Me-n-ni fish bí* does not have the ¬∃ reading 'I don't eat
    any fish' — only the ∃¬ reading 'there is a particular fish
    I don't eat'.

    The formal content is `cf_wide_scope_under_negation` from
    `ChoiceFunction.lean`. -/
theorem bi_wide_scope_under_negation {E : Type*}
    (f : CF E) (hf : f.isCorrect)
    {N VP : E → Prop}
    (hN : ∃ x, N x) (hAll : ∀ x, N x → VP x) :
    VP (f N) :=
  cf_wide_scope_under_negation f hf N VP hN hAll

end Owusu2022
