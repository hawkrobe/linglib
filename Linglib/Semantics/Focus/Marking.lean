/-!
# Focus marking

Binary focus marking (`Mark`): the marking feature of the focus axis,
one of [krifka-2008]'s four information-structure notions. Use `Mark`
when only the binary focused-vs-not distinction is needed;
`WithAlternatives` carries the Roothian alternative-set
structure. `Strategy` is where a focused constituent is realized, in its
base position or fronted to the left periphery, the in situ vs ex situ
cut of the West African focus literature ([hartmann-zimmermann-2007]).

## References

* [hartmann-zimmermann-2007]
* [krifka-2008]
-/

namespace Focus

/-- Binary focus marking — whether a constituent bears focus (pitch
accent / contrast) or not. -/
inductive Mark where
  /-- Constituent is focus-marked (pitch accent / contrast). -/
  | focused
  /-- Constituent is not focus-marked. -/
  | nonFocused
  deriving DecidableEq, Repr

/-- A focused constituent is realized in its base position or fronted to the left periphery
of its clause. -/
inductive Strategy where
  | inSitu
  | exSitu
  deriving DecidableEq, Repr, Inhabited

end Focus
