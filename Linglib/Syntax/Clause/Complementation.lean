import Linglib.Semantics.Verb.Defs
import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Clause complementation: selection

[deal-2026] [noonan-2007]

The [noonan-2007]-anchored selection relation between verb frames and
clause-typers.

## Main definitions

- `ComplementType.toNoonan`, `Verb.compTypes`, `Verb.realizes` — the
  selection relation

## Implementation notes

The typed complement-frame object (`Slot`, `Frame`) and [deal-2026]'s CP
external-shell inventory (`Slot.Shell`, `Slot.ShellInventory`, the named
witnesses) live in `Syntax/Clause/Frame.lean`; [noonan-2007]'s enums
(`NoonanCompType`, `CTPClass`, `RealityStatus`) in
`Features/Complementation.lean`; the generated CTP sample rows in
`Data/Complementation/`. Placement of individual languages in Table 79
cells consumes Fragment data and lives in `Studies/Deal2026.lean`;
consistency checks on the selection relation live in Studies
(e.g. `Bondarenko2022.hanaxa_frames_realized`).
-/

namespace Clause.Complementation

/-! ### Selection

The [noonan-2007]-anchored relation between a verb's complement frames
and a language's clause-typing morphemes. -/

/-- The [noonan-2007] category of a complement frame; `none` for
non-clausal frames. -/
def _root_.ComplementType.toNoonan : ComplementType → Option NoonanCompType
  | .finiteClause => some .indicative
  | .infinitival => some .infinitive
  | .gerund => some .nominalized
  | .smallClause => some .paratactic
  | .none => none
  | .np => none
  | .np_np => none
  | .np_pp => none
  | .question => some .indicative

/-- The legacy `ComplementType` cells of a verb's frame inventory
    (frames richer than any cell are dropped). -/
def _root_.Verb.compTypes (v : Verb) : List ComplementType :=
  v.frames.filterMap Frame.toComplementType

/-- Some frame of `v` is realized by clause-typer `c`: a slot's
    [noonan-2007] coding matches the typer's. The `∃ t` guard keeps
    coding-less slots from matching type-less typers (`none`/`none`). -/
def _root_.Verb.realizes (v : Verb) (c : Complementizer) : Prop :=
  ∃ fr ∈ v.frames, ∃ s ∈ fr, ∃ t, s.coding = some t ∧ c.noonanType = some t

end Clause.Complementation
