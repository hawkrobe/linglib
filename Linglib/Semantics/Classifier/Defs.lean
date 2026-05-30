import Mathlib.Data.Set.Card
import Linglib.Core.Logic.Intensional.Rigidity
import Linglib.Core.Scales.Comparison

/-!
# Classifier Denotations à la Sudo (2016)
@cite{sudo-2016}

A classifier denotation in Sudo's framework: at each world `w`, the classifier
takes a numeral `n` and an entity `x`, presupposes a sortal predicate `P_w(x)`,
and asserts that `x` is the join of `n` atomic `P`-parts.

Concretely, Sudo (2016, eq. 4):
  ⟦-rin⟧ = λw. λn. λx : *flower_w(x). |{y ⊑ x : flower_w(y)}| = n

This contrasts with the Chierchia / Little-Moroney-Royer framework in
`Classifier.Basic`, where the classifier is a *noun-side* predicate
transformer `(E → Prop) → (E → Prop)` that atomizes the noun denotation
without reference to a numeral. The two views are different theoretical
commitments and coexist in this directory.

## Key types

- `ClassifierDenot W E` — sortal + counting predicates (intensional)
- `ClassifierDenot.apply` — Sudo's body: `sortal_w(x) ∧ |{y ≤ x : counted_w(y)}| = n`
- `ClassifierDenot.ofSortal` — atomic-sortal constructor (the common case)

## Out of scope

Non-atomic classifiers like `-kumi` (pair) and `-daasu` (dozen) per Sudo
(9a/b) require explicit mereological joins of disjoint pairs and are not
expressible via `ofSortal`. A separate constructor will be added when the
non-atomic case is needed.
-/

namespace Semantics.Classifier

universe u v

/-- A Sudo-style classifier denotation: at each world, a sortal presupposition
    plus a predicate whose ⊑-atomic parts of `x` are counted.

    For atomic-sortal classifiers (the common case: `-rin`, `-hiki`, `-nin`,
    `-mai`, `-hon`, `-ko`, `-tou`), `sortal = counted`. For mensural
    classifiers like `-hai` (cupful), the relationship is more nuanced and
    handled by separate constructors. -/
structure ClassifierDenot (W : Type u) (E : Type v) [PartialOrder E] where
  /-- The sortal presupposition. ⟦-rin⟧ presupposes `flower`; ⟦-nin⟧
      presupposes `human`; ⟦-hiki⟧ presupposes `animal ∧ small`. -/
  sortal : Core.Intension W (E → Prop)
  /-- The countable base whose atomic ⊑-parts of `x` are counted.
      For atomic-sortal classifiers, `counted = sortal` (see `ofSortal`). -/
  counted : Core.Intension W (E → Prop)

namespace ClassifierDenot

variable {W : Type u} {E : Type v} [PartialOrder E]

/-- Construct an atomic-sortal classifier from a single predicate.
    The sortal and the counting base coincide — the standard case in
    Sudo (4) for `-rin`, (8a) for `-nin`, (8b) for `-hiki` (with the
    sortal being a conjunction `small ∧ animal`). -/
def ofSortal (P : Core.Intension W (E → Prop)) : ClassifierDenot W E where
  sortal := P
  counted := P

/-- The body of Sudo's denotation (eq. 4): `apply cl w n x` iff `sortal_w(x)`
    AND the count of `x`'s ⊑-atomic `counted`-parts equals `n`.

    The counting clause is the **exact (`=`) case of the shared
    comparison-over-a-measure primitive** `Core.Scale.Comparison.over`, with the
    measure being the atom-count `λx. |{y ⊑ x : counted_w(y)}|` — classifier
    counting *is* numeral comparison with `μ = atom-count`, the same primitive
    measure phrases and bare cardinals use. (`Set.ncard` returns 0 on infinite
    sets; for natural-language counting the relevant sets are finite.) -/
def apply (cl : ClassifierDenot W E) (w : W) (n : ℕ) (x : E) : Prop :=
  cl.sortal w x ∧
    x ∈ Core.Scale.Comparison.eq.over (fun y => {z : E | z ≤ y ∧ cl.counted w z}.ncard) n

@[simp] lemma ofSortal_sortal (P : Core.Intension W (E → Prop)) :
    (ofSortal P).sortal = P := rfl

@[simp] lemma ofSortal_counted (P : Core.Intension W (E → Prop)) :
    (ofSortal P).counted = P := rfl

/-- For atomic-sortal classifiers, the body reduces to the join of the
    sortal presupposition and the cardinality constraint over `P`. -/
lemma apply_ofSortal (P : Core.Intension W (E → Prop)) (w : W) (n : ℕ) (x : E) :
    apply (ofSortal P) w n x ↔
      P w x ∧ {y : E | y ≤ x ∧ P w y}.ncard = n := Iff.rfl

end ClassifierDenot

end Semantics.Classifier
