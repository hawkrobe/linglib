module

public import Mathlib.Order.Atoms
public import Mathlib.Tactic.DeriveFintype

/-!
# Focus marking

Binary focus marking (`Mark`): the marking feature of the focus axis,
one of [krifka-2008]'s four information-structure notions. Use `Mark`
when only the binary focused-vs-not distinction is needed;
`WithAlternatives` carries the Roothian alternative-set
structure. Marks are ordered by prominence, `nonFocused < focused`, the
scale on which one constituent is more focused than another
([abeille-et-al-2020], [winckel-et-al-2025]). `Strategy` is where a focused
constituent is realized, in its base position or fronted to the left
periphery, the in situ vs ex situ cut of the West African focus literature
([hartmann-zimmermann-2007]).

## References

* [abeille-et-al-2020]
* [hartmann-zimmermann-2007]
* [krifka-2008]
* [winckel-et-al-2025]
-/

@[expose] public section

namespace Focus

/-- Binary focus marking — whether a constituent bears focus (pitch
accent / contrast) or not. -/
inductive Mark where
  /-- Constituent is focus-marked (pitch accent / contrast). -/
  | focused
  /-- Constituent is not focus-marked. -/
  | nonFocused
  deriving DecidableEq, Repr, Fintype

namespace Mark

/-- The rank of a mark, higher for focused. -/
def rank : Mark → ℕ
  | .focused => 1
  | .nonFocused => 0

/-- `nonFocused < focused`: a focused constituent is the more prominent. -/
instance : LinearOrder Mark := LinearOrder.lift' rank (by decide)

/-- `⊥ = nonFocused`, `⊤ = focused`. -/
instance : BoundedOrder Mark where
  top := .focused
  le_top := by decide
  bot := .nonFocused
  bot_le := by decide

instance : IsSimpleOrder Mark where
  exists_pair_ne := ⟨.nonFocused, .focused, by decide⟩
  eq_bot_or_eq_top := by decide

end Mark

/-- A focused constituent is realized in its base position or fronted to the left periphery
of its clause. -/
inductive Strategy where
  | inSitu
  | exSitu
  deriving DecidableEq, Repr, Inhabited

end Focus
