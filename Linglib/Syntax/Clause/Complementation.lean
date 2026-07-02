import Linglib.Semantics.Verb.Defs
import Linglib.Syntax.Complementizer.Basic

/-!
# Clause complementation: surface typology and selection

[deal-2026] [noonan-2007]

[deal-2026]'s notional-complement surface structures and CP external-shell
inventory, plus the [noonan-2007]-anchored selection relation between verb
frames and clause-typers.

## Main definitions

- `CPShell`, `CPShellInventory`, `isAttestedShell`, `hasNominalShell` —
  CP external shells ([deal-2026] Table 79)
- `ComplementType.toNoonan`, `Verb.frames`, `Verb.realizes` — the
  selection relation

## Implementation notes

[noonan-2007]'s enums (`NoonanCompType`, `CTPClass`, `RealityStatus`) live
in `Features/Complementation.lean`; the generated CTP sample rows in
`Data/Complementation/`. Placement of individual languages in Table 79
cells consumes Fragment data and lives in `Studies/Deal2026.lean`;
consistency checks on the selection relation live in Studies
(e.g. `Bondarenko2022.hanaxa_frames_realized`). Shell implicational
generalisations ("P-shelling co-occurs with D-shelling") are proven on the
named witnesses; the universal claims stay in Table 79 commentary.
-/

namespace Clause.Complementation

/-! ### CP-external wrapping shells

`ComplementSize` and `ClauseSpine` (Syntax/Minimalist/) record *internal*
clause height; `CPShell` records what wraps the CP *externally*.
[deal-2026] Table 79 cross-classifies the two axes. -/

/-- A wrapping head above a CP: [deal-2026] Table 79 attests D, N, and P;
`c` is the base case, so `bareCP = [.c]`. -/
inductive CPShell where
  /-- The CP itself (always present). -/
  | c
  /-- D shell. -/
  | d
  /-- N shell (between D and CP). -/
  | n
  /-- P shell. -/
  | p
  deriving DecidableEq, Repr

/-- An ordered shell list, innermost first: `[.c, .d]` = D wraps CP,
`[.c, .n, .d]` = D wraps N wraps CP. -/
abbrev CPShellInventory := List CPShell

/-- The shell inventory is a [deal-2026] Table 79 cell. -/
def isAttestedShell : CPShellInventory → Bool
  | [.c] => true
  | [.c, .d] => true
  | [.c, .n, .d] => true
  | [.c, .d, .p] => true
  | _ => false

/-- The bare-CP cell (Nez Perce; English *think*). -/
def bareCP : CPShellInventory := [.c]

/-- The V D CP cell (Washo, [bochnak-hanink-2021]). -/
def dCP : CPShellInventory := [.c, .d]

/-- The V D N CP cell (Adyghe, [caponigro-polinsky-2011]). -/
def dnCP : CPShellInventory := [.c, .n, .d]

/-- The V P D CP cell (Bulgarian, [krapova-2010]; Ndebele,
[pietraszko-2019]). -/
def pdCP : CPShellInventory := [.c, .d, .p]

/-- The four named witnesses are all attested. -/
theorem named_shells_attested :
    isAttestedShell bareCP = true ∧
    isAttestedShell dCP = true ∧
    isAttestedShell dnCP = true ∧
    isAttestedShell pdCP = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- P-shelling co-occurs with D-shelling. -/
theorem pdCP_contains_p_and_d : CPShell.p ∈ pdCP ∧ CPShell.d ∈ pdCP := by
  decide

/-- N appears only inside a D shell. -/
theorem dnCP_contains_n_and_d : CPShell.n ∈ dnCP ∧ CPShell.d ∈ dnCP := by
  decide

/-- Every named shell contains C. -/
theorem named_shells_contain_c :
    CPShell.c ∈ bareCP ∧ CPShell.c ∈ dCP ∧
    CPShell.c ∈ dnCP ∧ CPShell.c ∈ pdCP := by
  decide

/-- `V P CP` (P with no D shell) is not a Table 79 cell. -/
theorem pCP_not_attested : isAttestedShell [.c, .p] = false := rfl

/-- `V N CP` (N with no D shell) is not a Table 79 cell. -/
theorem nCP_not_attested : isAttestedShell [.c, .n] = false := rfl

/-- The clause complex is wrapped in a nominal projection: its shell
    contains D (Washo `dCP`, Adyghe `dnCP`, Bulgarian/Ndebele `pdCP`;
    `bareCP` is not). On [deal-2026]'s attested cells this coincides
    with `≠ bareCP` (`pCP`/`nCP` are unattested); D-membership is the
    definitional content, not the complement of a special case. -/
def hasNominalShell (inv : CPShellInventory) : Prop := CPShell.d ∈ inv

instance : DecidablePred hasNominalShell :=
  λ inv => inferInstanceAs (Decidable (CPShell.d ∈ inv))

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

/-- A verb's complement frames: main plus alternate, when present. -/
def _root_.Verb.frames (v : Verb) : List ComplementType :=
  v.complementType :: v.altComplementType.toList

/-- `v`'s frame `f` is realized by clause-typer `c` ([noonan-2007]). -/
def _root_.Verb.realizes (v : Verb) (c : Complementizer) : Prop :=
  ∃ f ∈ v.frames, f.toNoonan = c.noonanType

end Clause.Complementation
