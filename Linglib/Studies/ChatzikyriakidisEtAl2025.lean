import Linglib.Data.Examples.Schema
import Linglib.Semantics.TypeTheoretic.Basic
import Linglib.Data.Examples.ChatzikyriakidisEtAl2025

/-!
# Chatzikyriakidis–Cooper–Gregoromichelaki–Sutton 2025: TTR intentional identity

[chatzikyriakidis-etal-2025] §2.3.2 treats [geach-1967]'s Hob–Nob puzzle —
"Hob thinks a witch has blighted Bob's mare, and Nob wonders whether she (the
same witch) killed Cob's sow" — following [ranta-1994]'s belief-context
analysis, recast by [cooper-2023] with record types in place of contexts: Hob's
and Nob's belief contexts overlap with respect to a shared witch component,
which need not be witnessed. Types, unlike sets of worlds, are individuated
intensionally (`Semantics.TypeTheoretic.ext_equiv_not_implies_int_eq`), so two
agents' attitudes can concern the same possibly-empty type.

This file formalizes the shared-component core of the account: Hob's and Nob's
contents both have `witchType` as a meet component while that type is empty.
The full analysis additionally aligns *labels* across the agents' belief
contexts ("indexed by the same variable in their respective belief contexts"),
giving sameness of discourse referent rather than merely of type; that
refinement awaits dependent record substrate, and without it component-sharing
alone cannot distinguish "the same witch" from "a witch of the same kind" —
the distinction [edelberg-1986]'s asymmetry data make empirically load-bearing.

## Main declarations

- `Examples.hobNob`: Geach's sentence as a `LinguisticExample`
- `witchType`, `hobContent`, `nobContent`: the Hob–Nob model
- `SharesComponent`: a content has `T` as its left meet component
- `intentional_identity`: the contents share the empty witch type yet
  are intensionally distinct
- `validates_hobNob`: the model validates the empirical datum
-/

namespace ChatzikyriakidisEtAl2025

open Semantics.TypeTheoretic

/-! ### TTR model of the Hob–Nob puzzle -/

/-- The shared witch type: empty carrier (no witch exists), individuated
intensionally by its name. -/
def witchType : IType := ⟨Empty, "witch"⟩

/-- "blighted Bob's mare" as a predicate type. -/
def blightBobsMare : IType := ⟨Unit, "blighted_bobs_mare"⟩

/-- "killed Cob's sow" as a predicate type. -/
def killCobsSow : IType := ⟨Unit, "killed_cobs_sow"⟩

/-- Hob's belief content: a witch who blighted Bob's mare. -/
def hobContent : IType := witchType.meet blightBobsMare

/-- Nob's wonder content: the *same* witch type, met with killing Cob's sow. -/
def nobContent : IType := witchType.meet killCobsSow

/-- `C` has `T` as its left meet component: witnesses of `C` are pairs whose
first coordinate inhabits `T`. Two contents stand in intentional identity
when they share a component in this sense. -/
def SharesComponent (T C : IType) : Prop := ∃ X, C = T.meet X

theorem sharesComponent_hobContent : SharesComponent witchType hobContent :=
  ⟨blightBobsMare, rfl⟩

theorem sharesComponent_nobContent : SharesComponent witchType nobContent :=
  ⟨killCobsSow, rfl⟩

/-- The witch type is empty: no witch exists. -/
theorem isFalse_witchType : IsFalse witchType.carrier :=
  show IsEmpty Empty from inferInstance

/-- The two contents are intensionally distinct (their event components
differ), even though both are empty. -/
theorem hobContent_ne_nobContent : ¬ hobContent.intEq nobContent :=
  λ h => absurd (congrArg IType.name (h : hobContent = nobContent)) (by decide)

/-- The contents are extensionally equivalent (both carriers are empty) yet
intensionally distinct — the model-level instance of
`ext_equiv_not_implies_int_eq`. An extensional semantics (`Set W`-style
contents) identifies the two attitudes; TTR keeps them apart. -/
theorem extEquiv_not_intEq :
    hobContent.extEquiv nobContent ∧ ¬ hobContent.intEq nobContent :=
  ⟨⟨Equiv.refl _⟩, hobContent_ne_nobContent⟩

/-- Intentional identity, TTR-style: Hob's and Nob's contents share the witch
type as a common intensional component, are intensionally distinct contents,
and the shared type is empty — both attitudes are "about the same witch-type"
although no witch exists. -/
theorem intentional_identity :
    SharesComponent witchType hobContent ∧
    SharesComponent witchType nobContent ∧
    ¬ hobContent.intEq nobContent ∧
    IsFalse witchType.carrier :=
  ⟨sharesComponent_hobContent, sharesComponent_nobContent,
   hobContent_ne_nobContent, isFalse_witchType⟩

/-- The model validates `Examples.hobNob`'s key judgment: the discourse is
acceptable although no witch need exist, and the model supplies shared
cross-attitude content built on an empty type. -/
theorem validates_hobNob :
    Examples.hobNob.judgment = .acceptable ∧
    SharesComponent witchType hobContent ∧
    SharesComponent witchType nobContent ∧
    IsFalse witchType.carrier :=
  ⟨rfl, sharesComponent_hobContent, sharesComponent_nobContent, isFalse_witchType⟩

end ChatzikyriakidisEtAl2025
