/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

/-!
# Perfect-auxiliary selection (be/have)

[burzio-1986] [sorace-2000]

The be/have perfect-auxiliary selection typology: many European languages select
between *be* and *have* as the perfect auxiliary by the transitivity/
unaccusativity class of the lexical verb (the Auxiliary Selection Hierarchy):
unaccusatives → *be* (Italian *è arrivato*, French *est arrivé*),
unergatives/transitives → *have* (Italian *ha mangiato*). English has collapsed
the split (all verbs take *have*). Graduated from the dissolved `Typology/`
drawer; the orthogonal inflectional typology of auxiliary verb
constructions lives in `Syntax/Category/Auxiliary/Constructions.lean`.

## Main definitions

* `PerfectAux` — be vs have.
* `TransitivityClass` — the argument-structure class selection keys on.
* `SelectionRule` — a language's selection regime (split/haveOnly/beOnly/mixed).
* `selection` / `canonicalSelection` / `germanSelection` / `SelectsBe`.

## Implementation note

`selection` flattens [sorace-2000]'s Auxiliary Selection *Hierarchy* (a 7-class
semantic gradient with per-language cutoffs) to a 4-class enum keyed on a single
reflexive parameter. A faithful graded scale, derived from
`Semantics/ArgumentStructure/EntailmentProfile.lean`'s proto-role predicates, is
the documented successor (it would discharge `Studies/Sorace2000`'s standing TODO).
-/

namespace ArgumentStructure.AuxiliarySelection

/-- Perfect auxiliary choice. -/
inductive PerfectAux where
  /-- Italian *essere*, French *être*, German *sein*. -/
  | be
  /-- Italian *avere*, French *avoir*, German *haben*. -/
  | have
  deriving DecidableEq, Repr

/-- Transitivity class relevant to auxiliary selection. -/
inductive TransitivityClass where
  /-- Subject is the theme: *arrive*, *fall*, *die*. -/
  | unaccusative
  /-- Subject is an agent and there is no object: *run*, *laugh*. -/
  | unergative
  /-- Subject is an agent and the object a theme: *eat*, *build*. -/
  | transitive
  /-- A reflexive clitic, which selects *be* in Romance and *have* in
      German. -/
  | reflexive
  deriving DecidableEq, Repr

/-- Language-level auxiliary selection rule. -/
inductive SelectionRule where
  /-- Unaccusatives take *be* and the rest *have*: Italian, French, German,
      Dutch. -/
  | split
  /-- Every verb takes *have*: English, Spanish. -/
  | haveOnly
  /-- Every verb takes *be*; rare, reported for some Sardinian dialects. -/
  | beOnly
  /-- Gradient or variable selection, as in some German dialects. -/
  | mixed
  deriving DecidableEq, Repr

/-- Auxiliary selection driven by a single binary parameter: does the
    language treat reflexives as BE-selecting (Romance pattern) or
    HAVE-selecting (German pattern)? In this coarse 4-class model
    unaccusatives select BE and unergatives/transitives select HAVE, with the
    reflexive row the locus of cross-linguistic variation ([burzio-1986] for
    the Italian generalization; [sorace-2000] for the cross-linguistic split). -/
def selection (reflexIsBe : Bool) : TransitivityClass → PerfectAux
  | .unaccusative => .be
  | .reflexive    => if reflexIsBe then .be else .have
  | .unergative   => .have
  | .transitive   => .have

/-- Canonical (Romance) auxiliary selection: reflexives → *be*. -/
def canonicalSelection : TransitivityClass → PerfectAux := selection true

/-- German auxiliary selection: reflexives → *haben*, not *sein* — the
    Romance-vs-German reflexive contrast of [sorace-2000]. -/
def germanSelection : TransitivityClass → PerfectAux := selection false

/-- The auxiliary a selection rule assigns to each transitivity class:
    `split` follows `selection`, `haveOnly`/`beOnly` are constant
    (English *has arrived*), and `mixed` systems make no categorical
    assignment. -/
def SelectionRule.selects (reflexIsBe : Bool) :
    SelectionRule → TransitivityClass → Option PerfectAux
  | .split, c    => some (selection reflexIsBe c)
  | .haveOnly, _ => some .have
  | .beOnly, _   => some .be
  | .mixed, _    => none

/-- Does this transitivity class canonically select *be*?
    Defined off `canonicalSelection` so the equivalence is true by
    construction. -/
def SelectsBe (c : TransitivityClass) : Prop :=
  canonicalSelection c = .be

instance : DecidablePred SelectsBe := fun c => by
  unfold SelectsBe
  infer_instance

end ArgumentStructure.AuxiliarySelection
