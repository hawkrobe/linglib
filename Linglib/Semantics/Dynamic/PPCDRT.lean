module

public import Linglib.Semantics.Dynamic.PCDRT

/-!
# Partial Plural CDRT

Partial Plural Compositional DRT ([haug-dalrymple-2020]) joins the plural information states of
Plural CDRT ([brasoveanu-2007], [dotlacil-2013]) with the partial assignments of Partial CDRT
([haug-2014]), in which an anaphoric condition is a presupposition rather than a resolution the
grammar makes. This file defines the conditions of a PPDRS on the states of `PCDRT`, reading a
dref's values and dependencies through `PCDRT.value` and `PCDRT.dep`.

A condition takes the output state and the set `Δ` of drefs the DRS distributes over. Three
anaphoric relations are distinguished ([higginbotham-1985], [williams-1991]):

* binding (`u_anaph = u_ant`), pointwise equality of the two drefs, which needs c-command;
* group identity (`∪u_anaph → ∪u_ant`), the anaphor's values summed over each state's class
  under distribution equal to the antecedent's values over the whole state, so that the
  antecedent escapes the distribution;
* reciprocity, group identity with distinctness in every state, the contribution of *each
  other*; without the distinctness it is the underspecified meaning of German *sich* or the
  Cheyenne reflexive/reciprocal affix ([murray-2008], [cable-2014]).

## Main definitions

* `PPCDRT.PPDRSCond`: a condition on a plural state under a distribution context.
* `PPCDRT.eqClass`: the class of a state under distribution.
* `PPCDRT.bindingCond`, `PPCDRT.groupIdentityCond`, `PPCDRT.reciprocityCond`,
  `PPCDRT.underspecifiedCond`: the anaphoric relations.

## Main results

* `PPCDRT.groupIdentityCond_empty`: without distribution, group identity is equality of the two
  drefs' values.
* `PPCDRT.reciprocityCond_empty_iff`: without distribution, reciprocity is a dependency with equal
  domain and codomain and no reflexive pair.
* `PPCDRT.binding_implies_groupIdentity`, `PPCDRT.reciprocity_excludes_binding`: binding and
  reciprocity against group identity.
* `PPCDRT.nontrivial_value_of_reciprocityCond`: a reciprocal's antecedent denotes a plurality.

## References

* [D. T. T. Haug and M. Dalrymple, *Reciprocity: Anaphora, scope, and quantification*
  (2020)][haug-dalrymple-2020]
* [D. T. T. Haug, *Partial dynamic semantics for anaphora: Compositionality without syntactic
  coindexation* (2014)][haug-2014]
* [A. Brasoveanu, *Structured nominal and modal reference* (2007)][brasoveanu-2007]
* [J. Dotlačil, *Reciprocals distribute over information states* (2013)][dotlacil-2013]
* [J. Higginbotham, *On semantics* (1985)][higginbotham-1985]
* [E. Williams, *Reciprocal scope* (1991)][williams-1991]
* [S. E. Murray, *Reflexivity and reciprocity with(out) underspecification* (2008)][murray-2008]
* [S. Cable, *Reflexives, reciprocals and contrast* (2014)][cable-2014]
-/

@[expose] public section

namespace PPCDRT

open PCDRT

variable {E : Type*}

/-- A PPDRS condition ([haug-dalrymple-2020] (27)): a property of the output plural state and of
the set `Δ` of drefs the DRS distributes over ((25)). -/
abbrev PPDRSCond (E : Type*) := PluralAssign ℕ E → Set ℕ → Prop

variable (uAnaph uAnt : ℕ) (S : PluralAssign ℕ E) (Δ : Set ℕ)

/-! ### Distribution -/

/-- The class of `s` under distribution over `Δ` ([haug-dalrymple-2020] (26)): the states of `S`
agreeing with `s` on every dref in `Δ`. -/
def eqClass (s : PartialAssign ℕ E) : PluralAssign ℕ E :=
  {t ∈ S | ∀ u ∈ Δ, t u = s u}

@[simp] theorem eqClass_empty (s : PartialAssign ℕ E) : eqClass S ∅ s = S := by
  ext t; simp [eqClass]

theorem mem_eqClass {s t : PartialAssign ℕ E} :
    t ∈ eqClass S Δ s ↔ t ∈ S ∧ ∀ u ∈ Δ, t u = s u := Iff.rfl

theorem self_mem_eqClass {s : PartialAssign ℕ E} (hs : s ∈ S) : s ∈ eqClass S Δ s :=
  ⟨hs, fun _ _ ↦ rfl⟩

/-! ### Anaphoric relations -/

/-- Binding (`u_anaph = u_ant`, [haug-dalrymple-2020] (30)): the two drefs hold the same value in
every state, both defined and equal or both undefined. This is stronger than the coreference
presupposition of (29), which constrains only the states where both are defined. -/
def bindingCond : PPDRSCond E := fun S _ ↦ ∀ s ∈ S, s uAnaph = s uAnt

/-- Group identity (`∪u_anaph → ∪u_ant`, [haug-dalrymple-2020] (29), (38)): in every state, the
anaphor's values over the state's class under distribution are the antecedent's values over the
whole state. -/
def groupIdentityCond : PPDRSCond E := fun S Δ ↦
  ∀ s ∈ S, value uAnaph (eqClass S Δ s) = value uAnt S

/-- Reciprocity (`∪u_anaph → ∪u_ant`, `∂(u_anaph ≠ u_ant)`, [haug-dalrymple-2020] (41)): group
identity, with the two drefs distinct in every state where both are defined. -/
def reciprocityCond : PPDRSCond E := fun S Δ ↦
  groupIdentityCond uAnaph uAnt S Δ ∧
    ∀ s ∈ S, ∀ a b, s uAnaph = some a → s uAnt = some b → a ≠ b

/-- The underspecified reflexive/reciprocal ([haug-dalrymple-2020] (79b)): group identity
without distinctness, admitting reflexive, reciprocal and mixed construals ([murray-2008],
[cable-2014]). -/
def underspecifiedCond : PPDRSCond E := groupIdentityCond uAnaph uAnt

/-- Without distribution, group identity is equality of the two drefs' values, the cumulative
identity `∪u_anaph = ∪u_ant` of [haug-dalrymple-2020] (39). -/
theorem groupIdentityCond_empty :
    groupIdentityCond uAnaph uAnt S ∅ ↔ value uAnaph S = value uAnt S := by
  simp only [groupIdentityCond, eqClass_empty]
  refine ⟨fun h ↦ ?_, fun h _ _ ↦ h⟩
  obtain rfl | ⟨s, hs⟩ := S.eq_empty_or_nonempty
  · simp [value]
  · exact h s hs

/-- Binding implies group identity without distribution. Under distribution the two come apart
([haug-dalrymple-2020] (24) against (31)). -/
theorem binding_implies_groupIdentity (h : bindingCond uAnaph uAnt S ∅) :
    groupIdentityCond uAnaph uAnt S ∅ := by
  intro s hs
  rw [eqClass_empty]
  exact Set.ext fun _ ↦ exists_congr fun g ↦ and_congr_right fun hg ↦ by
    change g uAnaph = _ ↔ g uAnt = _
    rw [h g hg]

/-- Reciprocity excludes binding once some state defines the anaphor: distinctness there
contradicts pointwise equality. Without such a state both drefs may be undefined throughout, and
binding and reciprocity hold together vacuously. -/
theorem reciprocity_excludes_binding (hdef : ∃ s ∈ S, ∃ d, s uAnaph = some d)
    (h : reciprocityCond uAnaph uAnt S Δ) : ¬ bindingCond uAnaph uAnt S Δ := fun hb ↦
  let ⟨s, hs, d, hd⟩ := hdef
  h.2 s hs d d hd ((hb s hs).symm.trans hd) rfl

theorem reciprocity_strengthens_underspecified (h : reciprocityCond uAnaph uAnt S Δ) :
    underspecifiedCond uAnaph uAnt S Δ := h.1

variable {uAnaph uAnt S Δ}

/-- Without distribution, and where the two drefs are defined in the same states, reciprocity is
a property of the dependency between antecedent and anaphor: its domain and codomain coincide,
and it is irreflexive. This is [haug-dalrymple-2020]'s gloss of (39), cumulative identity across
states combined with distinctness within each. -/
theorem reciprocityCond_empty_iff (hdef : ∀ s ∈ S, (s uAnaph).isSome ↔ (s uAnt).isSome) :
    reciprocityCond uAnaph uAnt S ∅ ↔
      (dep uAnt uAnaph S).dom = (dep uAnt uAnaph S).cod ∧ (dep uAnt uAnaph S).IsIrrefl := by
  rw [reciprocityCond, groupIdentityCond_empty,
    ← dom_dep (u := uAnt) (v := uAnaph) fun s hs ↦ (hdef s hs).2,
    ← cod_dep (u := uAnt) (v := uAnaph) fun s hs ↦ (hdef s hs).1, eq_comm]
  refine and_congr_right' ⟨fun h ↦ ⟨fun a ⟨s, hs, ha, ha'⟩ ↦ h s hs a a ha' ha rfl⟩, ?_⟩
  rintro h s hs a b ha hb rfl
  exact h.irrefl _ ⟨s, hs, hb, ha⟩

/-- A reciprocal's antecedent denotes a plurality: at a state defining both drefs, the
anaphor's value lies among the antecedent's by group identity and differs from the antecedent's
value there. This holds under any distribution. -/
theorem nontrivial_value_of_reciprocityCond (h : reciprocityCond uAnaph uAnt S Δ)
    {s : PartialAssign ℕ E} (hs : s ∈ S) {a b : E} (ha : s uAnaph = some a)
    (hb : s uAnt = some b) : (value uAnt S).Nontrivial :=
  ⟨a, h.1 s hs ▸ ⟨s, self_mem_eqClass S Δ hs, ha⟩, b, ⟨s, hs, hb⟩, h.2 s hs a b ha hb⟩

end PPCDRT
