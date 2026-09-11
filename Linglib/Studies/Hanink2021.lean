import Linglib.Semantics.Definiteness.Interpret
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
import Linglib.Data.Examples.Hanink2021
import Mathlib.Data.Prod.Lex

/-!
# Hanink (2021): DP Structure and Internally Headed Relatives in Washo

This file formalizes [hanink-2021]'s argument that indices are syntactic objects of their own, a
head idx below D that Washo pronounces as *gi ~ ge*: in third-person pronouns (1), in
demonstratives (2), and at the edge of internally headed relative clauses (3), which are DPs
over a nominalized CP (40). The index has two meanings (80): as a variable it is the property of
being the antecedent, so a familiar DP is D's ι over the restriction modified by the index (15),
which is the substrate's anaphoric description, `interpret_anaphoric_eq_russellIota`, with the
deixis of *hádi* and *wídi* a presupposition on D (34); as a binder it turns the open proposition
of the embedded clause, whose semantic head is a restricted variable (69), into a property
without movement, the substrate's abstraction `lambdaAbsG`, so that the relative denotes what an
externally headed relative denotes by raising and intersection, `russellIota_idxBind`, (72) and
(60). The Prohibition against Vacuous Binding (86) leaves the binder meaning to complements with
a free variable: under a perception verb the nominalization has none, so the index is a
variable and the clause a familiar DP over a property of events (106). Washo relatives are
island-insensitive (50) and restrictive, with existential readings (53) and stacking (54), the
profile of a language with articles (49) and (52), and idx bears no φ-features of the head (91),
so its relation to the head is binding, not Agree (section 4.5). The exponence of idx (119) is
*gi*, *ge* under dependent case, and null before an overt NP, and that of D (130) is null,
*hádi*, or *wídi*; with contextual specificity ranked above the Elsewhere Principle (118), the
Vocabulary derives the whole distribution, `idxExponent`: overt in pronouns, whose NP is elided
(113), in relatives (114), and in demonstratives, whose complement is RP (129), null in
anaphoric bare definites (115) even under dependent case (22). The examples are the rows of
`Data.Examples.Hanink2021`.

## Implementation notes

The index is the substrate's assignment index, so the variable meaning is `idxVar` and the
binder meaning `lambdaAbsG`; D's ι is `russellIota`, whose `∃!` presupposition is (34a)'s.
The R head of demonstratives (35) is the identity relation, so it is not represented. Ellipsis
of a pronoun's NP is recorded as the complement lacking the feature that makes an NP overt
(section 6.3). The quantified heads of section 5.1 and the German relative-clause parallel of
section 4.4 are recorded as data and prose only.

## TODO

* Quantified heads (98) to (103): [matthewson-2001]'s *all* over an index-hosting DP, and the
  relative-internal scope it predicts.

## References

* [hanink-2021]
* [schwarz-2009]
* [elbourne-2005]
* [heim-kratzer-1998]
* [kratzer-2009]
* [arregi-nevins-2012]
* [jacobsen-1964]
* [matthewson-2001]
-/

namespace Hanink2021

open Semantics.Composition Definiteness DistributedMorphology Morphology.Exponence
open scoped Assignment

variable {E W : Type}

/-! ### The two meanings of the index, (80) -/

/-- (80a), (14): the index as a variable, the property of being its value. -/
def idxVar (n : ℕ) : DenotG E W .et := λ g x => x = g n

/-- (80b): the index as a binder, taking the open proposition of its complement to the property
of the values of the variable that verify it: the substrate's abstraction over `n`, achieved
without movement. -/
abbrev idxBind (n : ℕ) (φ : DenotG E W .t) : DenotG E W .et := lambdaAbsG n φ

/-- (15), (35b), (97), and (106): a familiar DP, D's ι over the restriction modified by the index
as a variable, is the substrate's anaphoric description: the antecedent, if it satisfies the
restriction. -/
theorem interpret_anaphoric_eq_russellIota (R : DenotGS E W .et) (d : ℕ) (g : Assignment E)
    (gs : SitAssignment W) :
    interpret (.anaphoric R d) g gs = russellIota (λ x => R g gs x ∧ idxVar d g x) := by
  rw [interpret_anaphoric]
  split_ifs with h
  · exact ((russellIota_eq_some_iff _ _).mpr ⟨⟨h, rfl⟩, λ _ hx => hx.2⟩).symm
  · refine (Option.eq_none_iff_forall_ne_some.mpr λ e he => h ?_).symm
    obtain ⟨⟨hR, rfl⟩, -⟩ := (russellIota_eq_some_iff _ _).mp he
    exact hR

/-- (34b), (34c): the demonstrative D heads *hádi* and *wídi* add a deictic presupposition and
otherwise contribute ι, so a demonstrative refers as the anaphoric DP does. -/
theorem interpret_demonstrative_eq_russellIota (R : DenotGS E W .et)
    (deictic : Features.Deixis.Feature) (sIdx d : ℕ) (g : Assignment E) (gs : SitAssignment W) :
    interpret (.demonstrative R deictic sIdx d) g gs =
      russellIota (λ x => R g gs x ∧ idxVar d g x) :=
  (interpret_demonstrative_eq_anaphoric R deictic sIdx d g gs).trans
    (interpret_anaphoric_eq_russellIota R d g gs)

/-! ### Internally headed relatives, section 4 -/

/-- (69), (70): the embedded clause of an internally headed relative, an open proposition whose
semantic head is the restricted variable `n`: the restriction `P` holds of its value, and the
clause `ψ` says the rest of it. -/
def openClause (n : ℕ) (P : E → Prop) (ψ : DenotG E W .t) : DenotG E W .t :=
  λ g => P (g n) ∧ ψ g

/-- (71) is (59): the index binding the restricted variable in situ yields the property an
externally headed relative builds by abstracting over the trace and intersecting with the
head noun. -/
theorem idxBind_openClause (n : ℕ) (P : E → Prop) (ψ : DenotG E W .t) (g : Assignment E) :
    idxBind n (openClause n P ψ) g = λ x => P x ∧ lambdaAbsG n ψ g x := by
  funext x
  simp only [idxBind, lambdaAbsG, openClause, Function.update_self]

/-- (72) is (60): the silent D over the bound clause refers to what the definite over the
externally headed relative refers to, the same meaning by different steps. -/
theorem russellIota_idxBind (n : ℕ) (P : E → Prop) (ψ : DenotG E W .t) (g : Assignment E) :
    russellIota (idxBind n (openClause n P ψ) g) =
      russellIota (λ x => P x ∧ lambdaAbsG n ψ g x) := by
  rw [idxBind_openClause]

/-- The index has a free occurrence in `φ`: some value of the variable changes its truth. -/
def BindsIn (n : ℕ) (φ : DenotG E W .t) : Prop := ∃ g x, ¬ (φ (g[n ↦ x]) ↔ φ g)

/-- (86), the Prohibition against Vacuous Binding: without a free occurrence of the index the
binder meaning is constant and binds nothing, so only the variable meaning survives, which is
why a perception nominalization (106), a property of events with no open variable, is a
familiar DP. -/
theorem idxBind_eq_const_of_not_bindsIn {n : ℕ} {φ : DenotG E W .t} (h : ¬ BindsIn n φ)
    (g : Assignment E) : idxBind n φ g = λ _ => φ g := by
  funext x
  simp only [BindsIn, not_exists, not_not] at h
  exact propext (h g x)

/-! ### The exponence of idx and D, section 6 -/

/-- The features Vocabulary Insertion reads at idx and D and on their complements: the index
head, dependent (accusative) case, the D head with its deixis, and the complement's category, an
overt NP, a CP, an RP, or a nominal under ellipsis, which lacks the phonological features that
make an NP overt (section 6.3). -/
inductive Feat where
  | idx | dep | np | cp | rp | elided
  | d | deixis (f : Features.Deixis.Feature)
  deriving DecidableEq, Repr

/-- (119), (131): the Vocabulary entries for idx, *gi* elsewhere, *ge* under dependent case, and
null before an overt NP. -/
def idxItems : List (VocabularyItem Feat String) :=
  [[Feat.idx] ⟷ "gi", [Feat.idx, .dep] ⟷ "ge", ⟨⟨[.idx], [], [[.np]]⟩, ""⟩]

/-- (130): the Vocabulary entries for D, null elsewhere, *hádi* distal, *wídi* proximal. -/
def dItems : List (VocabularyItem Feat String) :=
  [[Feat.d] ⟷ "", [Feat.d, .deixis .distal] ⟷ "hádi", [Feat.d, .deixis .proximal] ⟷ "wídi"]

/-- (118): contextual specificity takes precedence over the Elsewhere Principle, the ordering of
[arregi-nevins-2012]: an item is ranked first by the features it demands of the context and
then by those it spells out. -/
def contextualSpecificity (i : VocabularyItem Feat String) : ℕ ×ₗ ℕ :=
  toLex ((i.site.leftCtx ++ i.site.rightCtx).flatten.length, i.site.focus.length)

/-- The exponent of idx in a neighborhood. -/
def idxExponent (n : Neighborhood (List Feat)) : Option String :=
  realize contextualSpecificity idxItems n

/-- The exponent of D in a neighborhood. -/
def dExponent (n : Neighborhood (List Feat)) : Option String :=
  realize contextualSpecificity dItems n

/-- The distribution of *gi ~ ge* (108) to (115) and (127) to (129): overt in pronouns, whose NP
is elided (113), at the edge of clausal nominalizations (114), and in demonstratives, whose
complement is RP (129), each alternating for case ((44), (45)); null before the overt NP of an
anaphoric bare definite (115), and still null under dependent case (22), where the contextual
entry outranks the case entry. -/
theorem idxExponent_distribution :
    idxExponent ⟨[.idx], [], [[.elided]]⟩ = some "gi" ∧
      idxExponent ⟨[.idx, .dep], [], [[.elided]]⟩ = some "ge" ∧
      idxExponent ⟨[.idx], [], [[.cp]]⟩ = some "gi" ∧
      idxExponent ⟨[.idx, .dep], [], [[.cp]]⟩ = some "ge" ∧
      idxExponent ⟨[.idx], [[.d, .deixis .distal]], [[.rp]]⟩ = some "gi" ∧
      idxExponent ⟨[.idx], [], [[.np]]⟩ = some "" ∧
      idxExponent ⟨[.idx, .dep], [], [[.np]]⟩ = some "" := by
  decide

/-- Under the Elsewhere score alone the case entry and the contextual entry tie on the accusative
bare definite and vocabulary order decides for *ge*; the paper's ordering (118) is what makes
the null entry win. -/
theorem subsetPrinciple_accusative_bare :
    subsetPrinciple idxItems ⟨[.idx, .dep], [], [[.np]]⟩ = some "ge" := by
  decide

/-- (25), (127): the demonstratives *hádigi* and *wídigi* decompose as the D exponent followed by
the idx exponent. -/
theorem demonstrative_forms :
    (dExponent ⟨[.d, .deixis .distal], [], [[.idx]]⟩).bind
        (λ a => (idxExponent ⟨[.idx], [[.d, .deixis .distal]], [[.rp]]⟩).map (a ++ ·)) =
      some "hádigi" ∧
    (dExponent ⟨[.d, .deixis .proximal], [], [[.idx]]⟩).bind
        (λ a => (idxExponent ⟨[.idx], [[.d, .deixis .proximal]], [[.rp]]⟩).map (a ++ ·)) =
      some "wídigi" := by
  decide

end Hanink2021
