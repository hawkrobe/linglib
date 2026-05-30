import Linglib.Semantics.Quantification.UnifiedUniversal
import Linglib.Semantics.Quantification.ONEModifiers
import Linglib.Semantics.Quantification.ChoiceFunction

/-!
# @cite{zimmermann-2008}: Quantification in Hausa

Formalization of the Hausa quantifier system from Zimmermann's handbook
chapter in @cite{matthewson-2008}, *Quantification: A Cross-Linguistic
Perspective*. Hausa is a Chadic (Afro-Asiatic) language with three
syntactic classes of adnominal quantifiers (Z. §3): class-A modifiers
(numerals, quantity expressions), class-B prenominal functional heads
(*wani*-existentials and *koo*+*wh*-universals), and class-C nominal
heads (proportional quantifiers).

This study file formalizes the class-B contrasts that ground later work
on African quantification, including @cite{haslinger-etal-2025-nllt}
(which adopts Q_∀ + ONE as the cross-linguistic substrate) and
@cite{owusu-2022} (which contrasts the Hausa *wani* analysis with the
Akan *bí* choice function).

## Main contributions formalized here

* **The *koo*+*wh* construction is productive, not a flat lexeme.**
  Hausa universals are built from the disjunction-marker *koo* plus a
  *wh*-word (Z. §3.2.1): *koo-waa* 'everyone' (*wh* = *waa* 'who'),
  *koo-mee* 'everything' (*wh* = *mee* 'what'), *koo-`ìnaa* 'everywhere'
  (*wh* = *`ìnaa* 'where'), *koo-wànè/koo-wàcè/koo-wàdànnè*
  'each m./f./pl.' (*wh* = *wànè/wàcè/wàdànnè* 'which.m/f/pl').

* **The *koo*+*wh* / *duk(à)* contrast instantiates the Q_∀ + ONE
  decomposition** later articulated by @cite{haslinger-etal-2025-nllt}.
  *koo*+*wh* is a prenominal D-head with phi-agreement that selects
  bare SG count NPs and yields distributive readings (Z. §4.1, §4.2.1).
  *duk(à)* is an unagreeing modifier that combines with DEF PL / mass
  NPs and yields collective readings.

* **Scope contrast between *wani* and *koo*+*wh* under negation.**
  *wani*-NPs allow both narrow (¬∃) and wide (∃¬) scope under VP
  negation (Z. §3.2.4 ex. 69). *koo*+*wh* allows only narrow scope
  under VP negation (Z. §3.2.4 ex. 73); the *not-every* reading
  requires focus and sentence negation (ex. 74). Bare indefinite NPs
  always take narrow scope (Z. §2.1.3 ex. 14).

## Architecture

Following the project's Layered Grounding discipline, this file does
not introduce paper-specific wrappers around substrate operators.
*koo*+*wh* is `everyPresup` (Q_∀ + ONE_∅) applied with Hausa-flavored
docstring rationale; *duk(à)* is `QForall` (bare Q_∀) on a CUM
lattice. The theorems below name the Hausa predictions and reduce
them to substrate identities.

## What is left for future work

* Other sources of universal force (Z. §4.4): verbal grade-4 *totality*
  morphology, adverbial *duk* 'completely', reduplicated numerals
  yielding distance-distributivity.
* Class-C proportional quantifiers (*yawancin* 'most of', Z. §3.3).
* The free-choice reading of *koo*+*wh* in modal/intensional contexts
  (Z. §3.2.3 ex. 68), which depends on alternative-sensitivity
  machinery formalized for Akan *bi-ara* in @cite{philipp-2022}.
-/

namespace Zimmermann2008

open Semantics.Quantification.UnifiedUniversal
open Semantics.Quantification.ONEModifiers
open Semantics.Quantification.ChoiceFunction
open Core.Quantification (some_sem)

/-! ### *koo*+*wh*: distributive universal via Q_∀ + ONE_∅

In Hausa, the universal *koo*+*wh* selects bare SG count NPs. On the
project's mereological substrate, this means the restrictor is atomic
and pairwise non-overlapping — precisely the `ONE_empty` presupposition
of @cite{haslinger-etal-2025-nllt}. Under this presupposition,
`QForall` (the unified mereological universal) collapses to pointwise
universal quantification — the distributive prediction of Z. §4.2.1. -/

/-- *koo*+*wh* distributes over the atoms of its restrictor.

The Hausa prediction (Z. §4.2.1 ex. 89a): *koo-wànè daalìbii yáa
tàaru à gàba-n makàrantaa* is ungrammatical — *koo*+*wh* cannot
co-occur with the collective predicate *tàaru* 'gather' precisely
because it forces a distributive construal.

The formal content is `every_distributes`: under `ONE_empty P`, the
mereological `QForall P Q` reduces to `∀ x, P x → Q x`. -/
theorem koo_distributes {α : Type*} [PartialOrder α]
    {P Q : α → Prop} (hONE : ONE_empty P) :
    QForall P Q ↔ ∀ x, P x → Q x :=
  every_distributes hONE

/-! ### *duk(à)*: collective universal via bare Q_∀

In Hausa, *duk(à)* is a modifier (not a D-head): it follows or precedes
the NP without agreement and selects DEF PL count NPs or mass NPs
(Z. §4.1). The restrictor is therefore CUM (closed under sum) with a
unique maximal element — the plural-DEF sum. On the substrate,
`QForall` on such a restrictor reduces to predication of the maximal
sum — the collective prediction of Z. §4.2.1 ex. 90. -/

/-- *duk(à)* applies its scope to the maximal element of a CUM restrictor.

The Hausa prediction (Z. §4.2.1 ex. 90a): *duk daalìbâ-n sun tàaru à
gàba-n makàrantaa* 'all the students gathered at the front of the
school' is grammatical — *duk* freely co-occurs with collective
predicates because it predicates the scope of the maximal plural sum
rather than distributing over atoms.

The formal content is `dng_cum'` from `UnifiedUniversal.lean`. -/
theorem duk_collective {α : Type*} [SemilatticeSup α]
    {P Q : α → Prop} (hCum : Mereology.CUM P)
    {m : α} (hMax : Mereology.isMaximal P m) :
    QForall P Q ↔ Q m :=
  dng_cum' hCum hMax

/-! ### *wani/wata/wa(`dan)su*: existential quantifier with flexible scope

Z. §3.2.4 ex. (69) shows that *wani* under VP-negation is ambiguous
between ¬∃ ('I didn't see anyone', preferred) and ∃¬ ('there is
someone I didn't see'). The narrow-scope (¬∃) reading is the one
that justifies an existential analysis: a *wani*-NP in the scope of
negation can simply assert the non-existence of a satisfier. -/

/-- *wani* can take narrow scope under negation: ¬∃x[N(x) ∧ VP(x)]
is satisfiable when no N is VP'd.

The formal content is `exists_narrow_scope_under_negation` from
`ChoiceFunction.lean` (which lives there as a control case for the
choice-function/∃-quantifier contrast in @cite{owusu-2022}). -/
theorem wani_narrow_scope {E : Type*}
    {N VP : E → Prop} (hNone : ∀ x, N x → ¬ VP x) :
    ¬ ∃ x, N x ∧ VP x :=
  exists_narrow_scope_under_negation N VP hNone

end Zimmermann2008
