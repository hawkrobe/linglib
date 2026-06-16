import Linglib.Semantics.Possessive.Denotation
import Linglib.Semantics.Reference.PronounDenotation

/-!
# Possessive pronouns: where the possessive and pronoun APIs meet

A possessive pronoun (*his book*, *mine*) is the possessive Kleisli arrow
(`Possessive.applyTo` / `theOf`) applied to a possessor that is a **pronoun**
denotation. Because both APIs trade in `NominalDenot` and possessive-of is
`bind`, they compose with no glue:

* the selector picks the **possessee** (the unique `R`-possessee of the pronoun's
  referent), while
* the intrinsic presupposition is the pronoun's **φ-features on the possessor**
  (`g i`) — *not* on the possessee.

That presup-on-possessor / selector-on-possessee split — what distinguishes a
possessive pronoun from a plain pronoun — is exactly `Possessive.applyTo_presup`,
i.e. *derived*, not stipulated.

## Main statements

* `possessivePronoun_presup` — *his N*'s presupposition is the possessor
  pronoun's φ-presupposition (on `g i`).
* `possessivePronoun_selector` — *his N*'s selector is the unique `R`-possessee
  of the pronoun's referent.
-/

namespace Possessive

open Semantics.Reference (NominalDenot)
open Semantics.Definiteness (russellIota)
open Core (Assignment)
open Core.Logic.Intensional.Variables (interpPronoun)

variable {E : Type} [PartialOrder E]

/-- *his N*'s intrinsic presupposition is the possessor pronoun's φ-feature
presupposition, imposed on the **possessor** `g i` — the φ-features ride along
the possessive by `applyTo_presup`. -/
theorem possessivePronoun_presup (p : PersonalPronoun) (i : ℕ)
    (speaker addressee : E) (isFemale isInanimate : E → Prop) (R : E → E → Prop)
    (g : Assignment E) (w : PUnit) :
    (applyTo (p.denote i speaker addressee isFemale isInanimate) R).presup g w
      = (p.phiPresup speaker addressee isFemale isInanimate).presup (g i) := by
  simp only [applyTo_presup, PersonalPronoun.denote]

/-- *his N*'s selector picks the unique `R`-possessee of the pronoun's
referent — the possessee, not the possessor. -/
theorem possessivePronoun_selector (p : PersonalPronoun) (i : ℕ)
    (speaker addressee : E) (isFemale isInanimate : E → Prop) (R : E → E → Prop)
    (g : Assignment E) (w : PUnit) :
    (applyTo (p.denote i speaker addressee isFemale isInanimate) R).selector g w
      = russellIota (E := E)
          (fun y => R (interpPronoun (E := E) (W := PUnit) i g) y) := by
  rw [applyTo_selector]; rfl

end Possessive
