import Linglib.Semantics.Reference.Basic
import Linglib.Semantics.Reference.Kripke
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Studies.Longobardi2001

/-!
# Longobardi (2005): Toward a Unified Grammar of Reference

This file formalizes the topological mapping theory of reference of [longobardi-2005]: a
nominal refers to an individual, an object or a kind, exactly when its D position holds
referential content. Individuals are denoted in D (52) and arguments denote individuals
(53), a referential value being a constant when a lexically referential expression occupies
or chains to D and a variable, ranging over the objects of the kind the noun names, otherwise
(54). Only a kind-naming noun can supply the restriction of a variable, so the two axioms
yield the paper's questions (57): an object-naming noun in argument position must fill D, by
raising or an expletive article, while a kind-naming noun need not (`NominalConfig`,
`Licensed`, `proper_names_must_raise`, `common_nouns_need_not_raise`). The four classes of
nominal heads of the properness hierarchy (25) order access to N-to-D raising
(`NominalHeadClass`, `raising_monotone`), and the definite article of *la Maria* is an
expletive that fills D without contributing an operator, so it induces no kind reading
(`ArticleType`, `kindReading_iff_operator`). Proper names in D are the directly referential
expressions of the semantics substrate (`proper_name_in_d_is_constant`), and the parameters
of [longobardi-2001] fix where D must be filled overtly (`strong_d_bridge`,
`greek_confirms`).

## Implementation notes

N-to-D raising is head-to-head movement on the extended projection of the noun. The Italian
*solo* paradigm, which diagnoses raising by the position of the noun relative to the adverb,
and the scope and rigidity facts distinguishing *la Maria* from *il tavolo* are described in
prose.

## TODO

The paper is not on file; the numbered axioms, theorems, and tables are transcribed from an
earlier version of this file and are UNVERIFIED.

## References

* [longobardi-2005]
* [longobardi-2001]
* [longobardi-1994]
-/

namespace Longobardi2005

open Longobardi2001 (DPParameter ArgumentType
  romance english greek PnRequiresOvertD BnCanBeReferential)

/-! ### The properness hierarchy (25), (28) -/

/-- The four classes of nominal heads, from the most prototypically referential to the
least: pronouns, proper names, the special common nouns *casa* 'home', *mamma* 'mom', and
*lunedì* 'Monday', and ordinary common nouns. -/
inductive NominalHeadClass where
  | pronoun
  | properName
  | specialCommon
  | commonNoun
  deriving DecidableEq, Repr

/-- Object-referential: the head can denote an object by occupying D. -/
def ObjectReferential : NominalHeadClass → Prop
  | .commonNoun => False
  | _ => True

/-- Can function as a predicate, without D. -/
def CanBePredicate : NominalHeadClass → Prop
  | .pronoun => False
  | _ => True

/-- Kind-referential: can denote a kind under the definite article. -/
def KindReferential : NominalHeadClass → Prop
  | .pronoun | .properName => False
  | _ => True

/-- N-to-D raising is obligatory in argument position. -/
def RaisingObligatory : NominalHeadClass → Prop
  | .pronoun | .properName => True
  | _ => False

instance : DecidablePred ObjectReferential := λ c => by
  cases c <;> unfold ObjectReferential <;> infer_instance
instance : DecidablePred CanBePredicate := λ c => by
  cases c <;> unfold CanBePredicate <;> infer_instance
instance : DecidablePred KindReferential := λ c => by
  cases c <;> unfold KindReferential <;> infer_instance
instance : DecidablePred RaisingObligatory := λ c => by
  cases c <;> unfold RaisingObligatory <;> infer_instance

/-- The scale of properness (25): pronouns, then names, then the special common nouns, then
common nouns. -/
def propernessRank : NominalHeadClass → ℕ
  | .pronoun => 0
  | .properName => 1
  | .specialCommon => 2
  | .commonNoun => 3

/-- Access to raising decreases along the scale: a more proper head raises at least as
obligatorily. -/
theorem raising_monotone (c₁ c₂ : NominalHeadClass) (h : propernessRank c₁ ≤ propernessRank c₂)
    (h₂ : RaisingObligatory c₂) : RaisingObligatory c₁ := by
  cases c₁ <;> cases c₂ <;> simp_all [propernessRank, RaisingObligatory]

/-- Kind reference and object reference come apart on the scale: the special common nouns
alone have both. -/
theorem both_references_iff (c : NominalHeadClass) :
    ObjectReferential c ∧ KindReferential c ↔ c = .specialCommon := by
  cases c <;> simp [ObjectReferential, KindReferential]

/-! ### The topological mapping (52) to (56) -/

/-- The lexical naming type of a noun (§4): object-naming, learned by applying it to an
object, or kind-naming, learned by recognizing an open set of objects. -/
inductive LexicalNamingType where
  | objectNaming
  | kindNaming
  deriving DecidableEq, Repr

/-- Only a kind-naming noun supplies the restriction of a variable ranging over the objects
of its kind (54b). -/
def LexicalNamingType.CanRestrictVariable : LexicalNamingType → Prop
  | .kindNaming => True
  | .objectNaming => False

instance : DecidablePred LexicalNamingType.CanRestrictVariable := λ t => by
  cases t <;> unfold LexicalNamingType.CanRestrictVariable <;> infer_instance

/-- A nominal in a syntactic position: the head's naming type, whether D holds lexically
referential content, a raised noun, a determiner, or a pronoun, and whether the nominal is an
argument. -/
structure NominalConfig where
  namingType : LexicalNamingType
  dHasReferentialContent : Bool
  isArgument : Bool
  deriving DecidableEq, Repr

/-- (54a): the nominal is a constant, denoting one individual through the content of D. -/
def NominalConfig.IsConstant (nc : NominalConfig) : Prop := nc.dHasReferentialContent = true

/-- (54b): the nominal is a variable, D being empty and the noun restricting it. -/
def NominalConfig.IsVariable (nc : NominalConfig) : Prop :=
  nc.dHasReferentialContent = false ∧ nc.namingType.CanRestrictVariable

/-- (52) and (53): an argument denotes an individual, as a constant or as a variable. -/
def NominalConfig.Licensed (nc : NominalConfig) : Prop :=
  nc.isArgument = true → nc.IsConstant ∨ nc.IsVariable

instance : DecidablePred NominalConfig.IsConstant := λ _ => inferInstanceAs (Decidable (_ = _))
instance : DecidablePred NominalConfig.IsVariable := λ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred NominalConfig.Licensed := λ _ => inferInstanceAs (Decidable (_ → _))

/-- (55): an argument with an empty D is a variable. -/
theorem isVariable_of_licensed {nc : NominalConfig} (h : nc.Licensed) (ha : nc.isArgument = true)
    (hd : nc.dHasReferentialContent = false) : nc.IsVariable :=
  (h ha).resolve_left λ hc => Bool.noConfusion (hd.symm.trans hc)

/-- Question (57c): an object-naming noun cannot restrict a variable, so as an argument it
must fill D, by raising or by an expletive article. -/
theorem proper_names_must_raise {nc : NominalConfig} (hn : nc.namingType = .objectNaming)
    (ha : nc.isArgument = true) (h : nc.Licensed) : nc.dHasReferentialContent = true :=
  (h ha).elim id λ hv => by
    have := hv.2
    rw [hn] at this
    exact this.elim

/-- Question (57a): a kind-naming noun is licensed as an argument with an empty D, as a
variable, so it need not raise. -/
theorem common_nouns_need_not_raise (isArgument : Bool) :
    NominalConfig.Licensed ⟨.kindNaming, false, isArgument⟩ := by
  cases isArgument <;> decide

/-- The two argument types of [longobardi-2001] are the two referential values: a referential
argument is a constant and a quantificational one a variable. -/
def argumentTypeToConfig : ArgumentType → NominalConfig
  | .referential => ⟨.objectNaming, true, true⟩
  | .quantificational => ⟨.kindNaming, false, true⟩

theorem argumentType_value (t : ArgumentType) :
    (argumentTypeToConfig t).Licensed ∧
      ((argumentTypeToConfig t).IsConstant ↔ t = .referential) := by
  cases t <;> decide

/-! ### Expletive articles (§8) -/

/-- The definite article of *la Maria* is an expletive filling D with no semantic content,
chained to the name; that of *il tavolo* is an operator. -/
inductive ArticleType where
  | expletive
  | operator
  deriving DecidableEq, Repr

/-- A kind reading needs an operator in D: the expletive article of a name induces none, so
*la Maria* is as rigid and scopeless as bare *Maria*. -/
def KindReadingPossible : ArticleType → Prop
  | .expletive => False
  | .operator => True

instance : DecidablePred KindReadingPossible := λ a => by
  cases a <;> unfold KindReadingPossible <;> infer_instance

theorem kindReading_iff_operator (a : ArticleType) : KindReadingPossible a ↔ a = .operator := by
  cases a <;> simp [KindReadingPossible]

/-! ### Bridges -/

open Reference.Basic (properName isDirectlyReferential constantCharacter)

/-- A proper name in D is a constant in the semantic sense too: directly referential, with a
constant character. -/
theorem proper_name_in_d_is_constant {C W E : Type*} (e : E) :
    isDirectlyReferential (properName (C := C) (W := W) e).character ∧
      constantCharacter (properName (C := C) (W := W) e).character :=
  ⟨Reference.Basic.properName_isDirectlyReferential e,
   Reference.Basic.properName_constantCharacter e⟩

/-- The strong-D parameter of [longobardi-2001] is the requirement that D be filled overtly
for a constant: Romance names need D filled and Romance bare nouns cannot be constants,
while English allows both. -/
theorem strong_d_bridge :
    PnRequiresOvertD romance ∧ ¬ PnRequiresOvertD english ∧
      ¬ BnCanBeReferential romance ∧ BnCanBeReferential english := by
  decide

/-- Greek, with strong D and adjectives opaque to raising, must fill D with an overt article
on every name. -/
theorem greek_confirms : PnRequiresOvertD greek ∧ ¬ BnCanBeReferential greek := by
  decide

end Longobardi2005
