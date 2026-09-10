import Linglib.Data.Examples.Guerrini2026
import Linglib.Logic.Modal.Defs
import Linglib.Semantics.Genericity.NominalMappingParameter
import Linglib.Semantics.Plurality.Basic
import Linglib.Semantics.Plurality.Cumulativity

/-!
# Guerrini (2026): Distributive Kind Predication

This file formalizes [guerrini-2026]'s account of why generalizations with kind-denoting plurals,
English bare plurals and Italian definite plurals, are distributed unlike singular indefinite
generics: they can also be accidental (Table 1), cumulative (section 4), and near-universal in
episodic sentences (section 5). Such a sentence is structurally ambiguous (28). In the Bona Fide
Generic parse the kind restricts `Gen`, a modalized universal, as a singular indefinite does,
`bonaFideGeneric`; in Distributive Kind Predication the kind is interpreted at the evaluation
world and the predicate distributes over its members, as with a definite plural,
`distributiveKindPred`, so the generalization is extensional and can be accidental. The generic
parse is distribution at every accessible world, so it entails distribution at the actual one and
fails at any accessible exception (53). Cumulative Kind Predication is the cumulative operator
over the kind's sum (74b); the rival with the operator below `Gen` (74c) makes every member relate
to every location, `forall_of_cumulativeBelowGen`, the paper's reason for rejecting it for
*elephants live in Africa and Asia*. Which parses a nominal has follows from what it denotes (10):
`DIST` and the cumulative operator need a sum, so a kind; the existential of Derived Property
Predication (105) needs a property; `Gen` takes either. Under [chierchia-1998]'s Nominal Mapping
Parameter the English bare plural is ambiguous between kind and property, the Italian definite
plural is a kind and the Italian bare plural a property (145), and the singular indefinite, whose
kind formation is undefined (16), has only `Gen` and the existential, `Parse.available_iff`. The
paper's examples are the rows of `Data.Examples.Guerrini2026`.

## Implementation notes

`Gen` is the paper's black box: a universal over the worlds an accessibility relation reaches and
over the members of the kind there, so its law-likeness is a frame condition rather than a
normality ordering. Kinds are represented by their sum at each world, a finite set of atoms, which
is what `DIST` and the cumulative operator see. Homogeneity and its removal by *all* and *always*
(section 3.3, Table 3), the subjunctive diagnostic (section 3.5), and the epistemic-adjective
argument for a separate property parse (section 5.2.2) are recorded in the rows but not
formalized, since they need a trivalent `Gen` and a mood licensing substrate.

## References

* [guerrini-2026]
* [chierchia-1998]
* [beck-sauerland-2000]
-/

namespace Guerrini2026

open ModalLogic Plurality Plurality.Cumulativity Semantics.Kinds

variable {Atom W : Type*} (R : W → W → Prop) (k : W → Finset Atom) (P : Atom → W → Prop) {w : W}

/-! ### The two parses of a generalization, section 3.2 -/

/-- (29): the Bona Fide Generic parse. The kind restricts `Gen`, a universal over the worlds `R`
accesses and the members of the kind there, so the kind's world variable stays bound. -/
def bonaFideGeneric (w : W) : Prop := □[R] (λ v => ∀ a ∈ k v, P a v) w

/-- (30): Distributive Kind Predication. The kind is interpreted at the evaluation world and the
predicate distributes over its members. -/
abbrev distributiveKindPred [∀ a w, Decidable (P a w)] (w : W) : Prop := distMaximal P (k w) w

/-- (28): the generic parse is Distributive Kind Predication at every accessible world. -/
theorem bonaFideGeneric_iff [∀ a w, Decidable (P a w)] :
    bonaFideGeneric R k P w ↔ ∀ v, R w v → distributiveKindPred k P v :=
  Iff.rfl

/-- A law-like generalization holds of the actual members: under a reflexive accessibility the
generic parse entails Distributive Kind Predication. -/
theorem distributiveKindPred_of_bonaFideGeneric [∀ a w, Decidable (P a w)] [Std.Refl R]
    (h : bonaFideGeneric R k P w) : distributiveKindPred k P w :=
  h w (Std.Refl.refl w)

/-- (53): the accidental case. Distribution over the actual members says nothing about other
worlds, so it survives an exception at an accessible world, which falsifies the generic parse. -/
theorem not_bonaFideGeneric_of_exception {v : W} (hv : R w v) {a : Atom} (ha : a ∈ k v)
    (hp : ¬ P a v) : ¬ bonaFideGeneric R k P w :=
  λ h => hp (h v hv a ha)

/-- (19) and (31): the singular indefinite generic, `Gen` over the noun's property. -/
def singularIndefiniteGeneric (N : Atom → W → Prop) (w : W) : Prop :=
  □[R] (λ v => ∀ a, N a v → P a v) w

/-- (28a): the generic parse of a kind-denoting plural is the singular indefinite generic over
membership in the kind, which is why the two have very similar meanings. -/
theorem bonaFideGeneric_iff_singularIndefiniteGeneric :
    bonaFideGeneric R k P w ↔ singularIndefiniteGeneric R P (λ a v => a ∈ k v) w :=
  Iff.rfl

/-! ### Cumulativity, section 4 -/

variable {Loc : Type*} (S : Atom → Loc → Prop) (locs : Finset Loc)

/-- (74b): Cumulative Kind Predication, [beck-sauerland-2000]'s cumulative operator relating
the kind's sum at the evaluation world to the locations. -/
abbrev cumulativeKindPred (w : W) : Prop := Cumulative S (k w) locs

/-- (74c): the cumulative operator below `Gen`, which then ranges over the sub-pluralities of the
kind: every nonempty sample of the kind at every accessible world relates cumulatively to the
locations. -/
def cumulativeBelowGen (w : W) : Prop :=
  □[R] (λ v => ∀ X ⊆ k v, X.Nonempty → Cumulative S X locs) w

/-- (74c) is the strong reading: taken at a singleton sample, it makes every member of the kind
relate to every location, so it is false of elephants and Africa and Asia. -/
theorem forall_of_cumulativeBelowGen [Std.Refl R] (h : cumulativeBelowGen R k S locs w)
    {a : Atom} (ha : a ∈ k w) {l : Loc} (hl : l ∈ locs) : S a l := by
  obtain ⟨b, hb, hab⟩ := (h w (Std.Refl.refl w) {a} (Finset.singleton_subset_iff.2 ha)
    (Finset.singleton_nonempty a)).2 l hl
  rwa [Finset.mem_singleton.1 hb] at hab

/-- The strong reading entails Cumulative Kind Predication, the salient weak one. -/
theorem cumulativeKindPred_of_cumulativeBelowGen [Std.Refl R] (hne : (k w).Nonempty)
    (h : cumulativeBelowGen R k S locs w) : cumulativeKindPred k S locs w :=
  h w (Std.Refl.refl w) (k w) subset_rfl hne

/-! ### Derived Property Predication, section 5.3 -/

/-- (105b): Derived Property Predication, the low-scoped existential over a property. -/
def dpp (N : Atom → W → Prop) (w : W) : Prop := ∃ a, N a w ∧ P a w

/-- (105): the near-universal reading of an episodic bare plural is Distributive Kind
Predication and the existential one Derived Property Predication over the same noun; the first
entails the second once the kind has members. -/
theorem dpp_of_distributiveKindPred [∀ a w, Decidable (P a w)] (hne : (k w).Nonempty)
    (h : distributiveKindPred k P w) : dpp P (λ a v => a ∈ k v) w :=
  let ⟨a, ha⟩ := hne
  ⟨a, ha, h a ha⟩

/-! ### Which parses a nominal has, sections 2 and 5.4 -/

/-- The nominal expressions of (145) and (31). -/
inductive Nominal
  | englishBarePlural
  | italianDefinitePlural
  | italianBarePlural
  | singularIndefinite
  deriving DecidableEq

namespace Nominal

/-- (146): [chierchia-1998]'s Nominal Mapping Parameter. English nouns can be kinds or
properties, Italian nouns are properties. -/
def mapping : Nominal → NMP.NominalMapping
  | .italianDefinitePlural | .italianBarePlural => .predOnly
  | _ => .argAndPred

/-- (13): whether the definite article, Italian's kind-forming operator, is present. -/
def definite : Nominal → Bool
  | .italianDefinitePlural => true
  | _ => false

/-- Whether the noun is plural, so that kind formation is defined for it (16). -/
def plural : Nominal → Bool
  | .singularIndefinite => false
  | _ => true

/-- (10a) and (16): the expression denotes a kind when the parameter or the article makes kind
formation available and the noun is plural. -/
def CanDenoteKind (n : Nominal) : Prop :=
  NMP.CanDenoteKind n.mapping (n.definite = true) ∧ NMP.downDefinedFor .count n.plural = true

/-- (145): the expression denotes a property when the parameter allows it and no article has
formed a kind. -/
def CanDenoteProperty (n : Nominal) : Prop :=
  NMP.CanDenoteProperty n.mapping ∧ n.definite = false

instance : DecidablePred CanDenoteKind := λ n => by unfold CanDenoteKind; infer_instance
instance : DecidablePred CanDenoteProperty := λ n => by unfold CanDenoteProperty; infer_instance

end Nominal

/-- The operator that takes the subject in (28), (74b), and (105). -/
inductive Parse
  | gen
  | dist
  | cumul
  | dpp
  deriving DecidableEq

/-- (10): `DIST` and the cumulative operator apply to a sum, so need a kind; the existential of
Derived Property Predication needs a property; `Gen` takes either. -/
def Parse.Available (n : Nominal) : Parse → Prop
  | .gen => n.CanDenoteKind ∨ n.CanDenoteProperty
  | .dist | .cumul => n.CanDenoteKind
  | .dpp => n.CanDenoteProperty

instance (n : Nominal) : DecidablePred (Parse.Available n) := λ p => by
  cases p <;> unfold Parse.Available <;> infer_instance

/-- (145), Table 1, and Table 2: the English bare plural has all four parses, the Italian
definite plural the three kind parses, and the Italian bare plural and the singular indefinite,
which cannot denote a kind, only `Gen` and the existential, so no accidental or cumulative
generalization. -/
theorem Parse.available_iff (p : Parse) :
    p.Available .englishBarePlural ∧ (p.Available .italianDefinitePlural ↔ p ≠ .dpp) ∧
      (p.Available .italianBarePlural ↔ p = .gen ∨ p = .dpp) ∧
      (p.Available .singularIndefinite ↔ p = .gen ∨ p = .dpp) := by
  cases p <;> decide

end Guerrini2026
