import Linglib.Semantics.Plurality.Distributivity
import Linglib.Semantics.Plurality.Trivalent

/-!
# English universal/distributive determiners

[haslinger-etal-2025-nllt]

Fragment entries for the English DP-internal universal quantifiers `each`,
`every`, and `all`, grounded in the theory-layer operators from
`Semantics/Plurality/`. Parallel to `Fragments/German/Distributives.lean`.

## Inventory

| Form    | Semantics       | [±dist] / [±max] | ONE-stack ([haslinger-etal-2025-nllt] eq. 79) |
|---------|-----------------|------------------|-----------------------------------------------|
| *each*  | `distMaximal`   | +dist, +max      | `Q_∀[ONE_∅[ONE_AT]]` (atomicity presupposition) |
| *every* | `distMaximal`   | +dist, +max      | `Q_∀[ONE_∅]` (non-overlap presupposition)       |
| *all*   | `allViaForallH` | −dist, +max      | bare `Q_∀`                                      |

`each` and `every` share their `DistMaxClass` (both +dist, +max) — the
distinction between them is the **atomicity** presupposition (`ONE_AT`), which
`DistMaxClass` does not record but the `atomicityPresup` field does. This is the
contrast that blocks *each ten minutes* while allowing *every ten minutes*
(intervals satisfy non-overlap but not atomicity).
-/

namespace English.Distributives

open Semantics.Plurality
open Semantics.Plurality.Distributivity
open Semantics.Plurality.Trivalent

variable {Atom W : Type*} [DecidableEq Atom]

-- Semantic entries

/-- ⟦each⟧ = `distMaximal`: distribute P to every atom. The atomicity
presupposition (`ONE_AT`) is a felicity condition, not part of the asserted
content. [haslinger-etal-2025-nllt] eq. (79c). -/
def eachSem (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] :
    Finset Atom → W → Prop :=
  distMaximal P

/-- ⟦every⟧ = `distMaximal`: same asserted content as `each`; differs only in
carrying the weaker non-overlap presupposition (`ONE_∅`).
[haslinger-etal-2025-nllt] eq. (79b). -/
def everySem (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] :
    Finset Atom → W → Prop :=
  distMaximal P

/-- ⟦all⟧ = `allViaForallH`: bare universal, maximization without distributive
inferences. [haslinger-etal-2025-nllt] eq. (79a); [kriz-spector-2021] §5.3. -/
def allSem [Fintype Atom] (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (x : Finset Atom) (w : W) : Prop :=
  allViaForallH P x w

-- Lexical properties

/-- An English universal determiner with grounded distributivity classification.
`atomicityPresup` records the `ONE_AT` (atomicity) felicity condition that
distinguishes *each* from *every* — a distinction `DistMaxClass` collapses. -/
structure DistributiveEntry where
  /-- Surface form. -/
  form : String
  /-- English gloss. -/
  gloss : String
  /-- Carries the atomicity presupposition (`ONE_AT`)? `each` does, `every`
      does not. -/
  atomicityPresup : Bool
  /-- Distributivity/maximality classification. -/
  distMaxClass : DistMaxClass
  deriving Repr

/-- *each*: +dist, +max, with the atomicity presupposition. -/
def eachEntry : DistributiveEntry :=
  { form := "each"
  , gloss := "each"
  , atomicityPresup := true
  , distMaxClass := .distMax }

/-- *every*: +dist, +max, with only the non-overlap presupposition. -/
def everyEntry : DistributiveEntry :=
  { form := "every"
  , gloss := "every"
  , atomicityPresup := false
  , distMaxClass := .distMax }

/-- *all*: −dist, +max, bare `Q_∀`. -/
def allEntry : DistributiveEntry :=
  { form := "all"
  , gloss := "all"
  , atomicityPresup := false
  , distMaxClass := .nonDistMax }

-- Grounding theorems

/-- *each*'s semantics IS `distMaximal`. -/
theorem each_eq_distMaximal (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] :
    eachSem P = distMaximal P := rfl

/-- *every*'s semantics IS `distMaximal` (same asserted content as *each*). -/
theorem every_eq_distMaximal (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] :
    everySem P = distMaximal P := rfl

/-- *all* reduces to a simple universal check on atoms. -/
theorem all_iff_allSatisfy [Fintype Atom] (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (x : Finset Atom) (w : W) :
    allSem P x w ↔ allSatisfy P x w :=
  allViaForallH_iff_allSatisfy P x w

/-- *each* and *every* share a `DistMaxClass` (both +dist, +max) but differ in
the atomicity presupposition: this is the every-vs-each contrast that
`DistMaxClass` alone cannot express. [haslinger-etal-2025-nllt] §6.2. -/
theorem each_every_same_class_different_atomicity :
    eachEntry.distMaxClass = everyEntry.distMaxClass ∧
    eachEntry.atomicityPresup = true ∧ everyEntry.atomicityPresup = false := by
  decide

end English.Distributives
