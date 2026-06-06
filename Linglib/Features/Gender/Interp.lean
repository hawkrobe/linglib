import Linglib.Features.Gender.Basic

/-!
# Gender — dimensions of interpretation
[sudo-spathas-2020] [hammerly-2019] [merchant-2014] [sauerland-2003]

Which dimension of meaning a gender inference lives in, classified **per
lexical item** — not per language or per category ([sudo-spathas-2020]).
Their Greek noun classes, diagnosed by focus constructions (more stable
than [merchant-2014]'s ellipsis judgments, which they could not replicate):

* **Class I** (adherfos/adherfi 'brother/sister'): the gender inference is
  in *both* the asserted and presupposed dimensions — focus alternatives
  carry it (`GenderInferences.dual`).
* **Class III marked members** (dhaskala 'teacher.F'): *presupposed only* —
  the feminine restricts focus comparison, the masculine is neutral
  (`GenderInferences.presupposedOnly`).
* **Class II epicenes** (jatros 'doctor'): *no* semantic gender inference;
  inferences arise pragmatically via competition with the opposite GENDER
  (`GenderInferences.bare`; the Maximize-Presupposition-style derivation is
  study content, cf. [sauerland-2003]).

The fourth cell — asserted but not presupposed — is unattested in their
Greek classes (`InferenceLocus.greek_asserted_imp_presupposed`) but is not
excluded by the type: it is precisely [hammerly-2019]'s analysis of French
*lexical* gender (feminine asserts `λ x, x is female`; masculine contributes
nothing), argued *against* presuppositional accounts on the epicene test
(#la singe for a known-female monkey). The presuppositional tradition
([sauerland-2003]) remains correct for *pronominal* gender — pronominal and
lexical gender are partially distinct facets ([hammerly-2019]; also
[kramer-2015] on pronominal-gender-only languages).

## Implementation notes

* `GenderInferences` carries `Option`-al restrictors per dimension: absence
  of an inference is distinct from a trivial one — that distinction *is*
  [sudo-spathas-2020]'s typology. `InferenceLocus` is its Boolean shadow,
  derived by `GenderInferences.locus`, never stipulated separately.
* `GenderInfo` is the discourse-knowledge layer (what participants know
  about a referent's gender), distinct from both dimensions of lexical
  content; its eventual re-grounding target is this typology.
-/

set_option autoImplicit false

namespace Gender

/-! ### Inference loci -/

/-- Which dimensions of meaning carry a gender inference for a given
    lexical item ([sudo-spathas-2020]). -/
structure InferenceLocus where
  /-- The inference is part of asserted content. -/
  asserted : Bool
  /-- The inference is part of presupposed content. -/
  presupposed : Bool
  deriving DecidableEq, Repr, Fintype

namespace InferenceLocus

/-- Class I: inference in both dimensions (Greek adherfos). -/
def dual : InferenceLocus := ⟨true, true⟩

/-- Class III marked members: presupposed only (Greek dhaskala). -/
def presupposedOnly : InferenceLocus := ⟨false, true⟩

/-- Class II epicenes: no semantic inference; gender competition does the
    pragmatic work (Greek jatros). -/
def competition : InferenceLocus := ⟨false, false⟩

/-- [hammerly-2019]'s French lexical gender: asserted, not presupposed —
    the cell unattested in [sudo-spathas-2020]'s Greek classes. -/
def assertedOnly : InferenceLocus := ⟨true, false⟩

/-- [sudo-spathas-2020]'s Greek classes satisfy a containment: asserted
    gender is also presupposed. An observation about their inventory, not a
    well-formedness filter — [hammerly-2019]'s `assertedOnly` violates it
    by design. -/
theorem greek_asserted_imp_presupposed :
    ∀ l ∈ [dual, presupposedOnly, competition],
      l.asserted = true → l.presupposed = true := by decide

end InferenceLocus

/-! ### Gender inferences -/

section Inferences

variable {E : Type*}

/-- The gender inferences a gendered noun form carries over a domain `E` of
    referents: an optional restrictor per dimension of meaning
    ([sudo-spathas-2020]). `none` = no inference in that dimension. -/
structure GenderInferences (E : Type*) where
  /-- Restrictor contributed to asserted content, if any. -/
  asserted : Option (E → Prop)
  /-- Restrictor contributed to presupposed content, if any. -/
  presupposed : Option (E → Prop)

namespace GenderInferences

/-- The Boolean shadow: which dimensions carry an inference. -/
def locus (g : GenderInferences E) : InferenceLocus :=
  ⟨g.asserted.isSome, g.presupposed.isSome⟩

/-- Class I construction: one restrictor in both dimensions
    (adherfos = male sibling, asserted and presupposed). -/
def dual (P : E → Prop) : GenderInferences E := ⟨some P, some P⟩

/-- Class III construction: restrictor presupposed only (dhaskala). -/
def presupposedOnly (P : E → Prop) : GenderInferences E := ⟨none, some P⟩

/-- [hammerly-2019] construction: restrictor asserted only (French lionne
    = female ∧ lion by Predicate Modification). -/
def assertedOnly (P : E → Prop) : GenderInferences E := ⟨some P, none⟩

/-- Class II construction: no semantic gender inference (jatros). -/
def bare : GenderInferences E := ⟨none, none⟩

@[simp] theorem locus_dual (P : E → Prop) :
    (dual P).locus = InferenceLocus.dual := rfl

@[simp] theorem locus_presupposedOnly (P : E → Prop) :
    (presupposedOnly P).locus = InferenceLocus.presupposedOnly := rfl

@[simp] theorem locus_assertedOnly (P : E → Prop) :
    (assertedOnly P).locus = InferenceLocus.assertedOnly := rfl

@[simp] theorem locus_bare :
    (bare : GenderInferences E).locus = InferenceLocus.competition := rfl

end GenderInferences

end Inferences

end Gender

/-! ### Discourse-level gender knowledge -/

/-- Gender knowledge state for a discourse referent.

    Distinct from the comparative `Gender` label a noun's agreement class
    carries: `GenderInfo` describes what the discourse participants know or
    assume about a referent's gender. Motivated by [arnold-2026]'s
    observation that singular *they* is licensed by two inversely correlated
    pragmatic conditions: one requiring an underspecified discourse
    representation, the other requiring knowledge that the referent's
    pronouns are *they/them*. See also [newman-1992], [newman-1998], and
    [camilliere-etal-2021]. -/
inductive GenderInfo where
  /-- Gender is known to discourse participants and matches a
      morphosyntactic agreement class.
      Example: "my sister" → `.known .feminine` -/
  | known : Gender → GenderInfo
  /-- Gender is unknown, irrelevant, or not elaborated in the discourse.
      Example: "every student", "someone", "the clerk" (in passing). -/
  | unspecified : GenderInfo
  deriving DecidableEq, Repr, BEq

/-- Lift a comparative gender label to discourse-level knowledge. -/
def Gender.toGenderInfo (g : Gender) : GenderInfo := .known g

/-- Extract the gender label, if known. -/
def GenderInfo.toGender : GenderInfo → Option Gender
  | .known g => some g
  | .unspecified => none

/-- Round-trip: known gender survives the coarsening. -/
theorem GenderInfo.roundtrip_known (g : Gender) :
    g.toGenderInfo.toGender = some g := rfl
