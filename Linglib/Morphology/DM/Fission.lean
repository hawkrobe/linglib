import Mathlib.Logic.Basic

/-!
# Fission (Distributed Morphology)
[halle-marantz-1993] [noyer-1992]

Fission is the postsyntactic DM operation that splits a single terminal
node into two morphological exponents. In the DM derivation, Fission
applies after syntax but before Vocabulary Insertion: a feature bundle
with multiply-realizable content is partitioned into two pieces, each
of which is then independently subject to VI.

The classical motivation is [noyer-1992]'s analysis of Afro-Asiatic
person/number portmanteaux, where a single agreement slot surfaces as
two clitic-like exponents. Subsequent work — notably
[arregi-nevins-2012] on Basque auxiliary doubling — has used the
same operation for clitic doubling more generally.

## Architecture

A Fission rule is parameterized over three types: a `Person` category
(the morphological feature being split), a `Ctx` (the structural
context that licenses Fission), and an `Out` (the two-piece
realization output). Conditions on `Person` and `Ctx` are `Prop`-valued
with carried `DecidablePred` witnesses, matching the
`ImpoverishmentRule` shape in
`Linglib/Morphology/DM/Impoverishment.lean`.

## Main declarations

* `FissionRule Person Ctx Out` — the generic rule structure
* `applyFission` — partial application returning `Option Out`
* `PFMarkingCondition Out` — phonological well-formedness check
* `fissionSatisfiesPF` — composition of Fission with a PF check

## Implementation notes

This file is currently consumed by exactly one paper anchor —
`Studies/MunozPerez2026.lean` (Chilean Spanish
stylistic applicatives). Per linglib's ≥2-consumer graduation rule,
single-paper formalisations normally stay in `Studies/`. The promotion
here is deliberate: the inline Fission framework in MunozPerez2026 is
language-neutral and the second consumer is identified.

## Todo

* Migrate a second consumer to discharge the ≥2-consumer rule.
  The DM literature has several Fission analyses that could be
  formalised against this substrate — [arregi-nevins-2012] on
  Basque clitic doubling is the most direct candidate; Spanish dialect
  clitic doubling and ditropic clitics in Romance are also natural
  fits.
-/

namespace Morphology.DM.Fission

/-! ### Fission rule -/

/-- A Fission rule is parameterized over:
* `Person` — the morphological category fissioned (e.g., φ-features);
* `Ctx`    — the structural context licensing Fission
            (e.g., a verbal-head list in [munoz-perez-2026]);
* `Out`    — the two-piece realization output.

Both `contextOk` and `personOk` are `Prop`-valued with carried
`DecidablePred` witnesses, matching the mathlib idiom and the
`ImpoverishmentRule` template (see `Impoverishment.lean`). -/
structure FissionRule (Person Ctx Out : Type*) where
  /-- The structural condition licensing Fission. -/
  contextOk : Ctx → Prop
  /-- Decidability witness for `contextOk`. -/
  decContext : DecidablePred contextOk
  /-- The person condition triggering Fission (e.g., [+PART, +SING]). -/
  personOk : Person → Prop
  /-- Decidability witness for `personOk`. -/
  decPerson : DecidablePred personOk
  /-- Realization: map each licensed person to a two-piece output. -/
  realize : Person → Out

variable {Person Ctx Out : Type*}

/-- Expose `decContext` as an instance so `if rule.contextOk c then …`
    elaborates at concrete contexts. -/
instance (rule : FissionRule Person Ctx Out) (c : Ctx) :
    Decidable (rule.contextOk c) := rule.decContext c

/-- Expose `decPerson` as an instance so `if rule.personOk p then …`
    elaborates at concrete persons. -/
instance (rule : FissionRule Person Ctx Out) (p : Person) :
    Decidable (rule.personOk p) := rule.decPerson p

/-- Apply Fission: yield the two-piece realization when both the
    structural and person conditions hold; otherwise `none`. -/
def applyFission (rule : FissionRule Person Ctx Out) (p : Person) (c : Ctx) :
    Option Out :=
  if rule.contextOk c ∧ rule.personOk p then
    some (rule.realize p)
  else
    none

/-! ### PF marking condition -/

/-- A PF well-formedness check over the realization output. Each
    language stipulates its own marking requirement (e.g., the
    anticausative-Voice PF requirement in [munoz-perez-2026],
    rule 55). -/
structure PFMarkingCondition (Out : Type*) where
  /-- Does this realization satisfy the PF marking requirement? -/
  satisfied : Out → Prop
  /-- Decidability witness for `satisfied`. -/
  decSatisfied : DecidablePred satisfied

instance (pf : PFMarkingCondition Out) (o : Out) :
    Decidable (pf.satisfied o) := pf.decSatisfied o

/-- When Fission applies and the resulting realization satisfies the
    PF marking requirement, this returns `true`. Otherwise `false`. -/
def fissionSatisfiesPF (rule : FissionRule Person Ctx Out)
    (pf : PFMarkingCondition Out) (p : Person) (c : Ctx) : Bool :=
  match applyFission rule p c with
  | some out => decide (pf.satisfied out)
  | none     => false

end Morphology.DM.Fission
