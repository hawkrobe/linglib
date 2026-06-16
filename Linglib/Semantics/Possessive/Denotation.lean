import Linglib.Semantics.Reference.Nominal
import Linglib.Semantics.Definiteness.Maximality
import Linglib.Semantics.Possessive.Basic

/-!
# Possessive-of as a Kleisli arrow

The possessive denotation in the unified referential currency `NominalDenot`
(`Semantics/Reference/Nominal.lean`), which is a monad. *NP's N* is **Kleisli
`bind`** into the definite possessee of the possessor: re-point the possessor
denotation's selector through the possession relation (`russellIota` of the
relation), inheriting the possessor's intrinsic presupposition. So:

* possessive **nesting** (*John's mother's friend*) is `bind` associativity;
* the possessor's φ-features (when it is a pronoun) **ride along** to the whole
  possessive, by `applyTo_presup`;
* the existence/uniqueness presupposition is **selector definedness**
  (`russellIota_isSome_iff_existsUnique`), not a separate intrinsic presup.

## Main declarations

* `Possessive.theOf R` — the Kleisli arrow: the unique `R`-possessee of a
  possessor, as a `NominalDenot`.
* `Possessive.applyTo nd R = nd >>= theOf R` — *NP's N*.
* `Possessive.Definite.toNominalDenot` — a definite carrier as a `NominalDenot`
  (always-defined selector, from `HasIotaWitness`).

## Main statements

* `applyTo_presup` — the possessive's presupposition *is* the possessor's.
* `applyTo_selector` — the selector binds through the iota of the relation.
* `applyTo_applyTo` — nesting, from `bind_assoc`.
-/

namespace Possessive

open Semantics.Reference (NominalDenot)
open Semantics.Definiteness (russellIota russellIota_isSome_iff_existsUnique existsUnique)

variable {Ctx : Type*} {W E : Type}

/-! ### The Kleisli arrow -/

/-- The unique entity the `possessor` stands in relation `R` to, as a
`NominalDenot`: a definite referent (`russellIota`) with vacuous intrinsic
presupposition — definedness is its only presupposition. -/
noncomputable def theOf (R : E → E → Prop) (possessor : E) : NominalDenot Ctx W E where
  presup := fun _ _ => True
  selector := fun _ _ => russellIota (E := E) (fun y => R possessor y)

/-- *NP's N*: re-select the possessor denotation through the possession relation
`R`. -/
noncomputable def applyTo (nd : NominalDenot Ctx W E) (R : E → E → Prop) : NominalDenot Ctx W E :=
  nd >>= theOf R

/-! ### Composition laws -/

/-- The possessive's intrinsic presupposition **is** the possessor's — a
possessor pronoun's φ-features ride along to the whole possessive. -/
@[simp] theorem applyTo_presup (nd : NominalDenot Ctx W E) (R : E → E → Prop)
    (c : Ctx) (w : W) : (applyTo nd R).presup c w = nd.presup c w := by
  simp only [applyTo, theOf, NominalDenot.bind_presup]
  cases nd.selector c w <;> simp

/-- The possessive's selector binds the possessor through the iota of the
relation: defined exactly when the possessor is defined and has a unique
`R`-possessee. -/
@[simp] theorem applyTo_selector (nd : NominalDenot Ctx W E) (R : E → E → Prop)
    (c : Ctx) (w : W) :
    (applyTo nd R).selector c w =
      (nd.selector c w).bind (fun p => russellIota (E := E) (fun y => R p y)) := by
  simp only [applyTo, theOf, NominalDenot.bind_selector]

/-- Nesting (*John's mother's friend*) — from `bind` associativity. -/
theorem applyTo_applyTo (nd : NominalDenot Ctx W E) (R₁ R₂ : E → E → Prop) :
    applyTo (applyTo nd R₁) R₂ = nd >>= fun p => applyTo (theOf R₁ p) R₂ := by
  simp only [applyTo, NominalDenot.bind_assoc]

/-! ### Definite carriers as nominal denotations -/

/-- A definite possessive carrier as a `NominalDenot` over its situations: the
selector is `russellIota` of the possessee predicate, always defined because the
carrier bears the iota-presupposition (`HasIotaWitness`). -/
noncomputable def Definite.toNominalDenot {S : Type} (d : Possessive.Definite E S) :
    NominalDenot Ctx S E where
  presup := fun _ _ => True
  selector := fun _ s => russellIota (E := E) (fun y => d.predicate y s)

end Possessive
