/-!
# Focus marking

Binary focus marking (`Mark`): the marking feature of the focus axis,
one of [krifka-2008]'s four information-structure notions. Use `Mark`
when only the binary focused-vs-not distinction is needed;
`Alternatives.AltMeaning` carries the Roothian alternative-set
structure.
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

end Focus
