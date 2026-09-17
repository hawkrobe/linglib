import Linglib.Fragments.Hausa.Determiners
import Linglib.Semantics.Quantification.Basic
import Mathlib.Data.Finset.Card

/-!
# Zimmermann (2008): Quantification in Hausa

This file formalizes the scopal and quantificational observations of [zimmermann-2008]'s
chapter on the Hausa quantifier system in [matthewson-2008], whose inventory the fragment
`Hausa.Determiners` types after [newman-2000] and [jaggar-2001]. Bare indefinite noun phrases
always scope under negation, whether they follow or precede the negation marker, (11)–(14); the
chapter's preferred account makes them predicates whose existential force comes from the verb,
after van Geenhoven, so that negation over the verb yields a negative existential in either
position (`bareVerb`, `neg_bareVerb_iff`, `bare_no_wide_scope`). The marked indefinite *wani* is
an existential that is ambiguous under verb-phrase negation between the negative existential
and the some-not reading, (69), which come apart on a three-passenger model
(`wani_wide_scope`, `wani_narrow_scope_false`). The distributive universal *koo*+*wh* reads
as a negative existential under verb-phrase negation, (73), and as a negative universal under
sentence negation, (74): the first is the universal scoping over the negation
(`every_neg_iff_not_some`), and the two readings differ on the model
(`kowWh_negation_readings_diverge`). The collective universal *duk* takes a plural or mass
argument, (85)–(86), combines with collective predicates that the distributive *koo*+*wh*
rejects, (89)–(90) (`duk_collective`, `not_every_collective`), and yields the negative
universal under either negation, (91) (`neg_duk_iff`).

## Implementation notes

* The chapter leaves the choice among generalized-quantifier, indeterminate-pronoun and
  choice-function analyses of the class-B quantifiers open (§3.2.5); *wani* and *koo*+*wh* are
  read here as the generalized quantifiers `some_sem` and `every_sem`, the first of the three.
* A collective predicate is one that holds only of pluralities of at least two members; the
  distributive universal applies it member by member and so fails.
* The binding differences of §4.2.3 and the adverbial quantifiers of §6 are not represented.

## References

* [zimmermann-2008]
* [matthewson-2008]
* [newman-2000]
* [jaggar-2001]
-/

namespace Zimmermann2008

open Hausa.Determiners Quantifier Quantifier.GQ

variable {α E : Type*}

/-! ### Bare indefinites under negation, §2.1.3 -/

/-- A verb that forms a complex predicate with a bare indefinite argument: the existential
force comes from the verb, `λP λe. ∃x, P x ∧ V x e`. -/
def bareVerb (V : α → E → Prop) (P : α → Prop) (e : E) : Prop := ∃ x, P x ∧ V x e

/-- Negation over the verb yields the negative existential, (14): no bare-indefinite reading
scopes over negation, wherever the noun phrase sits. -/
theorem neg_bareVerb_iff (V : α → E → Prop) (P : α → Prop) (e : E) :
    ¬ bareVerb V P e ↔ ∀ x, P x → ¬ V x e := by
  simp [bareVerb]

/-! ### A three-passenger domain -/

/-- Three passengers, *faasinjojî*: Audù, Bàlki and Càdi. -/
inductive Faasinjee
  | audu | balki | cadi
  deriving DecidableEq, Repr, Fintype

/-- *yā daurà wàndà* 'buckled their seatbelt': Audù and Bàlki did, Càdi did not. -/
def Daura : Faasinjee → Prop
  | .audu => True
  | .balki => True
  | .cadi => False

instance : DecidablePred Daura := λ x => match x with
  | .audu => isTrue trivial
  | .balki => isTrue trivial
  | .cadi => isFalse id

/-- The bare-indefinite reading of *passengers didn't buckle* is false on the model, while the
some-not reading a wide-scope indefinite would give is true: the readings the chapter
separates in (13) are distinct. -/
theorem bare_no_wide_scope :
    ¬ ¬ bareVerb (λ x (_ : Unit) => Daura x) (λ _ => True) () ∧
      ∃ x : Faasinjee, ¬ Daura x :=
  ⟨λ h => h ⟨.audu, trivial, trivial⟩, ⟨.cadi, id⟩⟩

/-! ### The class-B quantifiers, §3.2 -/

/-- The wide-scope reading of *wani faasinjèe bài daurà wàndà ba*, some passenger did not
buckle their seatbelt, (69ii): Càdi is the witness. -/
theorem wani_wide_scope : some_sem (λ _ : Faasinjee => True) (¬ Daura ·) :=
  ⟨.cadi, trivial, id⟩

/-- The negative existential reading, no passenger buckled their seatbelt, (69i), fails: Audù
did. -/
theorem wani_narrow_scope_false : ¬ ¬ ∃ x : Faasinjee, Daura x :=
  λ h => h ⟨.audu, trivial⟩

/-- The two readings of *wani* under verb-phrase negation come apart on the model, (69). -/
theorem wani_ambiguity_witness :
    some_sem (λ _ : Faasinjee => True) (¬ Daura ·) ∧ ¬ ¬ ∃ x : Faasinjee, Daura x :=
  ⟨wani_wide_scope, wani_narrow_scope_false⟩

/-- The universal over the negation is the negative existential: *koo*+*wh* under verb-phrase
negation, (73), *I saw no one*. -/
theorem every_neg_iff_not_some (R S : α → Prop) :
    every_sem R (¬ S ·) ↔ ¬ some_sem R S := by
  simp [every_sem, some_sem]

/-- The negative existential of (73) and the negative universal of (74) differ on the model:
not every passenger buckled, yet it is false that none did. -/
theorem kowWh_negation_readings_diverge :
    ¬ every_sem (λ _ : Faasinjee => True) Daura ∧
      ¬ every_sem (λ _ : Faasinjee => True) (¬ Daura ·) :=
  ⟨λ h => h .cadi trivial, λ h => h .audu trivial trivial⟩

/-! ### The two universals, §4 -/

/-- The distributive universal *koo*+*wh*: the generalized quantifier `every_sem` over a
predicate of individuals. -/
def kowWhSem (R S : α → Prop) : Prop := every_sem R S

/-- The collective universal *duk*: its plural or mass argument, (85)–(86), is a plurality, and
the predicate applies to the plurality as a whole. -/
def dukSem (R : Finset α) (S : Finset α → Prop) : Prop := S R

/-- A collective predicate such as *tàaru* 'gather' or *keewàyee* 'surround' holds only of
pluralities with at least two members. -/
def Collective (S : Finset α → Prop) : Prop := ∀ s, S s → 2 ≤ s.card

/-- *Duk* combines with a collective predicate, (90): the students gathered as a group. -/
theorem duk_collective {R : Finset α} {S : Finset α → Prop} (h : S R) : dukSem R S := h

/-- *Koo*+*wh* cannot combine with a collective predicate, (89): applying it member by member
asks each singleton to gather, which no collective predicate allows. -/
theorem not_every_collective {R : Finset α} {S : Finset α → Prop} (hS : Collective S)
    (hR : R.Nonempty) : ¬ kowWhSem (· ∈ R) (λ x => S {x}) := by
  obtain ⟨x, hx⟩ := hR
  intro h
  have := hS {x} (h x hx)
  simp at this

/-- *Duk* under negation is the negative universal *not all*, (91), under verb-phrase and
sentence negation alike: for a distributive predicate, not every member satisfies it. -/
theorem neg_duk_iff (R : Finset α) (P : α → Prop) :
    ¬ dukSem R (λ s => ∀ x ∈ s, P x) ↔ ¬ every_sem (· ∈ R) P := by
  simp [dukSem, every_sem]

/-- *Kōwānè faasinjèe yā daurà wàndà* 'every passenger buckled their seatbelt' is false on the
model: Càdi did not. -/
theorem kowWh_daura_false : ¬ kowWhSem (λ _ : Faasinjee => True) Daura :=
  λ h => h .cadi trivial

end Zimmermann2008
