import Linglib.Syntax.Category.Verb.Defs
import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Clause complementation: selection

[noonan-2007]

The [noonan-2007]-anchored selection relation between verb frames and
clause-typers.

## Main definitions

- `ComplementType.toCoding`, `Verb.realizes` — the selection relation
- `ComplementType.codings_toFrame` — the enum view and the typed frames
  record the same coding

## Implementation notes

The typed complement-frame object (`Slot`, `Frame`) lives in
`Syntax/Clause/Frame.lean`; [noonan-2007]'s enums (`Complement.Coding`,
`CTPClass`, `RealityStatus`) in `Features/Complementation.lean`; the
generated CTP sample rows in `Data/Complementation/`. [deal-2026]'s
CP-external shell inventory and the language placements of its (79)
table live in `Studies/Deal2026.lean`; consistency checks on the
selection relation live in Studies
(e.g. `Bondarenko2022.hanaxa_frames_realized`).
-/

namespace Clause.Complementation

/-! ### Selection

The [noonan-2007]-anchored relation between a verb's complement frames
and a language's clause-typing morphemes. -/

/-- The [noonan-2007] coding of a complement frame: `none` for
non-clausal frames, for small clauses (outside the coding inventory),
and for embedded questions (interrogativity is a clause-form axis, not
a coding). -/
def _root_.ComplementType.toCoding : ComplementType → Option Complement.Coding
  | .finiteClause => some .indicative
  | .infinitival => some .infinitive
  | .gerund => some .nominalized
  | .smallClause => none
  | .none => none
  | .np => none
  | .np_np => none
  | .np_pp => none
  | .question => none

/-- The enum view and the typed frames record the same coding: a cell's
    frame carries exactly the codings `toCoding` assigns it. -/
theorem _root_.ComplementType.codings_toFrame (ct : ComplementType) :
    ct.toFrame.codings = ct.toCoding.toList := by cases ct <;> rfl

/-- Some frame of `v` is realized by clause-typer `c`: a recorded
    [noonan-2007] coding of `v`'s frames matches the typer's. -/
def _root_.Verb.realizes (v : Verb) (c : Complementizer) : Prop :=
  ∃ t ∈ v.codings, c.coding = some t

instance (v : Verb) (c : Complementizer) : Decidable (v.realizes c) :=
  inferInstanceAs (Decidable (∃ t ∈ v.codings, _))

end Clause.Complementation
