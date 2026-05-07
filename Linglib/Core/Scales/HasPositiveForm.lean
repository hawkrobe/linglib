import Linglib.Core.Scales.HasComparison

/-!
# Core/Scales/HasPositiveForm.lean — positive-form typeclass (parameterized)

Each gradability framework provides a structurally-different standard-source
for the unmodified positive form ("Kim is tall" — without comparison or
modifier). The `Source` parameter exposes this structural difference at
the type level rather than hiding it inside an opaque `Prop`.

- Kennedy 2007: `Source = δ` (degree threshold)
- Charlow-Sutton-Wechsler 2024: `Source = State` (contrast point on state ordering)
- Klein 1980: `Source = Set α` (comparison class)
- Lassiter-Goodman 2017: `Source = PMF δ` (threshold prior)

This file is part of the Phase A.7 atomic typeclass landing per master plan v4.
-/

namespace Core.Scale

/-- Each framework provides its own standard-source structure.
    The `Source` parameter makes the framework's standard-determination
    apparatus visible at the type level — not hidden inside the `Prop`.

    Kennedy: `Source = δ` (threshold). CSW: `Source = State` (contrast point).
    Klein: `Source = Set α` (comparison class). Lassiter-Goodman: `Source =
    PMF δ` (threshold prior). -/
class HasPositiveForm (α : Type*) (Source : Type*) [HasComparison α] where
  isPositive : Source → α → Prop

end Core.Scale
