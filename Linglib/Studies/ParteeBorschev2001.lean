import Linglib.Semantics.Possessive.Basic

/-!
# Partee & Borschev 2001: Some puzzles of predicate possessives

Paper-anchored consumer of the possessive substrate for [partee-borschev-2001].
P&B argue against the uniform "argument-only" analysis of possessives
([jensen-vikner-1994]) using **predicate possessives**: a possessive occurs as a
bare predicate (type ⟨e,t⟩) only when its possession relation is a free
contextual variable (a *modifier* genitive), not when it is the inherent
relation of a relational noun or adjective (an *argument* genitive).

The argument/modifier distinction is **study-local**: it is P&B's analysis of a
*construction*, contested by [vikner-jensen-2002] (who deny the split is
grammatical), so it is not a field of the theory-neutral substrate carrier
(`Possessive.Carrier`). The predicate form itself *is* substrate — the bare
⟨e,t⟩ possessive predicate is `Possessive.viaArgument` (the relation applied to
the possessor).

## Main statements

* `canBePredicate_iff_modifier` — predicativity is exactly modifier-provenance.
* `team_predicate_ok` / `brother_predicate_bad` / `favoriteMovie_predicate_bad`
  — P&B (1c)–(3c): *that team is John's* ✓, *#that brother/favorite movie is
  John's* (decide-checked from the relation source).
* `RussianForm.predicativity` — the morphosyntactically overt confirmation
  (§2.2): the Russian genitive NP (argument) cannot predicate, the prenominal
  possessive (modifier) can.
* `predicateForm_eq_viaArgument` — the bare predicate possessive is the substrate
  `Possessive.viaArgument` predicate.

## References

* [partee-borschev-2001]: Some puzzles of predicate possessives.
* [jensen-vikner-1994]: the uniform argument-only analysis P&B argue against.
-/

namespace ParteeBorschev2001

open ArgumentStructure.Relational

/-! ### Relation provenance and predicativity

The argument/modifier distinction is P&B's analytical classification of a
construction, kept study-local (V&J reject it). -/

/-- The provenance of a genitive's possession relation: supplied lexically by a
relational noun/adjective (*argument*) or as a free contextual variable
(*modifier*). -/
inductive RelationProvenance where
  /-- Inherent/lexical relation — the argument genitive. -/
  | argument
  /-- Free contextual relation — the modifier genitive. -/
  | modifier
  deriving DecidableEq, Repr

/-- A possessive occurs as a bare predicate (*that team is John's*) iff its
relation is modifier-provenance. Argument genitives cannot — P&B's central
generalization. -/
def CanBePredicate : RelationProvenance → Prop
  | .modifier => True
  | .argument => False

instance : DecidablePred CanBePredicate := fun p => by
  cases p <;> unfold CanBePredicate <;> infer_instance

/-- Predicativity is exactly modifier-provenance. Inverting the provenance flips
the prediction, so the distinction is not decorative. -/
theorem canBePredicate_iff_modifier (p : RelationProvenance) :
    CanBePredicate p ↔ p = .modifier := by
  cases p <;> simp [CanBePredicate]

/-! ### English predicate possessives (P&B 2001 (1)–(3))

The genitive relation has three sources: the context (a free `R`, with a plain
noun), an inherently relational noun (*brother*), or an inherently relational
adjective (*favorite*). Only the contextual source is a modifier. -/

/-- The three sources of the genitive relation (P&B 2001 §1.1). -/
inductive RelationSource where
  /-- Free contextual relation (plain noun, e.g. *team*). -/
  | context
  /-- Inherent relation of a relational noun (*brother*). -/
  | relationalNoun
  /-- Inherent relation of a relational adjective (*favorite*). -/
  | relationalAdjective
  deriving DecidableEq, Repr

/-- Only the contextual source yields a modifier genitive; the two inherent
sources yield argument genitives. -/
def RelationSource.provenance : RelationSource → RelationProvenance
  | .context => .modifier
  | .relationalNoun => .argument
  | .relationalAdjective => .argument

/-- P&B (1c) *that team is John's* — acceptable: contextual relation (modifier). -/
theorem team_predicate_ok :
    CanBePredicate RelationSource.context.provenance := by decide

/-- P&B (2c) *#that brother is John's* — degraded: relational noun (argument). -/
theorem brother_predicate_bad :
    ¬ CanBePredicate RelationSource.relationalNoun.provenance := by decide

/-- P&B (3c) *#that favorite movie is John's* — degraded: relational adjective
(argument). The whole N-bar *favorite movie* supplies the relation. -/
theorem favoriteMovie_predicate_bad :
    ¬ CanBePredicate RelationSource.relationalAdjective.provenance := by decide

/-! ### Russian: overt morphosyntax (P&B 2001 §2.2)

In Russian the distinction is visible in the form: the genitive NP (*Peti*) is
uniformly argument-like and cannot occur in predicate position, while the
prenominal quasi-adjectival possessive (*Petin*) and possessive pronouns admit
the modifier reading and can. -/

/-- Russian possessive forms and their relation provenance (P&B 2001 §2.2). -/
inductive RussianForm where
  /-- Postnominal genitive NP, *Peti* — uniformly argument. -/
  | genitiveNP
  /-- Prenominal quasi-adjectival possessive, *Petin* — admits modifier. -/
  | prenominalPossessive
  /-- Possessive pronoun, *moj* — admits modifier. -/
  | possessivePronoun
  deriving DecidableEq, Repr

/-- Provenance of each Russian form. -/
def RussianForm.provenance : RussianForm → RelationProvenance
  | .genitiveNP => .argument
  | .prenominalPossessive => .modifier
  | .possessivePronoun => .modifier

/-- The overt confirmation: a Russian form occurs as a predicate iff it is not
the (argument-only) genitive NP. -/
theorem RussianForm.predicativity (f : RussianForm) :
    CanBePredicate f.provenance ↔ f ≠ .genitiveNP := by
  cases f <;> decide

/-! ### The predicate form is substrate

The bare predicate possessive *John's* (`λx. R(John)(x)`) is the substrate
`Possessive.viaArgument` — the relation applied to the possessor, a genuine
⟨e,t⟩ predicate that the uniform argument-only approach cannot produce
standalone. -/

variable {E S : Type*}

theorem predicateForm_eq_viaArgument (possessor : E) (R : Pred2 E S) :
    (fun x s => R possessor x s) = Possessive.viaArgument possessor R :=
  rfl

end ParteeBorschev2001
