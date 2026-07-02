import Linglib.Features.Complementation
import Linglib.Features.ClauseForm
import Linglib.Features.Case.Basic

/-! # Complement frames — typed slots

A verb's complement frame as a list of typed `Slot`s, factoring the flat
`ComplementType` enum cells into their axes: syntactic category, case
marking, CP-external shell ([deal-2026]), clause form, [noonan-2007]
coding, and embedded-subject requirement (genitive subjects of
nominalized clauses, [bondarenko-2022]). The legacy enum survives as a
round-trip view (`ComplementType.toFrame` / `Frame.toComplementType`).

## Main declarations

* `Slot.Shell`, `Slot.ShellInventory` (+ `isAttested`, `hasNominalShell`,
  the named cells) — CP-external wrapping shells ([deal-2026] Table 79)
* `Slot`, `Slot.WellFormed` — one complement position: category plus
  optional clausal axes
* `Frame` + `Frame.np`, `Frame.finiteClause`, … — a frame is a list of
  slots; the legacy enum cells as smart constructors

## Implementation notes

Frame-conditioned readings (attitude, opacity, control) are not slot
data — they live on `Verb.Reading` (`Semantics/Verb/Defs.lean`), keyed
to the verb's frames. The [noonan-2007] selection relation between verb
frames and clause-typers (`Verb.realizes`) lives in
`Syntax/Clause/Complementation.lean`. This file never imports
`Semantics/`.
-/

namespace Slot

/-! ### CP-external wrapping shells

`ComplementSize` and `ClauseSpine` (Syntax/Minimalist/) record *internal*
clause height; `Slot.Shell` records what wraps the CP *externally*.
[deal-2026] Table 79 cross-classifies the two axes. -/

/-- A wrapping head above a CP: [deal-2026] Table 79 attests D, N, and P;
`c` is the base case, so the bare-CP inventory is `[.c]`. -/
inductive Shell where
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
abbrev ShellInventory := List Shell

namespace ShellInventory

/-- The shell inventory is a [deal-2026] Table 79 cell. -/
def isAttested : ShellInventory → Bool
  | [.c] => true
  | [.c, .d] => true
  | [.c, .n, .d] => true
  | [.c, .d, .p] => true
  | _ => false

/-- The bare-CP cell (Nez Perce; English *think*). -/
def bareCP : ShellInventory := [.c]

/-- The V D CP cell (Washo, [bochnak-hanink-2021]). -/
def dCP : ShellInventory := [.c, .d]

/-- The V D N CP cell (Adyghe, [caponigro-polinsky-2011]). -/
def dnCP : ShellInventory := [.c, .n, .d]

/-- The V P D CP cell (Bulgarian, [krapova-2010]; Ndebele,
[pietraszko-2019]). -/
def pdCP : ShellInventory := [.c, .d, .p]

/-- The four named witnesses are all attested. -/
theorem named_shells_attested :
    isAttested bareCP = true ∧
    isAttested dCP = true ∧
    isAttested dnCP = true ∧
    isAttested pdCP = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- P-shelling co-occurs with D-shelling. -/
theorem pdCP_contains_p_and_d : Shell.p ∈ pdCP ∧ Shell.d ∈ pdCP := by
  decide

/-- N appears only inside a D shell. -/
theorem dnCP_contains_n_and_d : Shell.n ∈ dnCP ∧ Shell.d ∈ dnCP := by
  decide

/-- Every named shell contains C. -/
theorem named_shells_contain_c :
    Shell.c ∈ bareCP ∧ Shell.c ∈ dCP ∧
    Shell.c ∈ dnCP ∧ Shell.c ∈ pdCP := by
  decide

/-- `V P CP` (P with no D shell) is not a Table 79 cell. -/
theorem pCP_not_attested : isAttested [.c, .p] = false := rfl

/-- `V N CP` (N with no D shell) is not a Table 79 cell. -/
theorem nCP_not_attested : isAttested [.c, .n] = false := rfl

/-- The clause complex is wrapped in a nominal projection: its shell
    contains D (Washo `dCP`, Adyghe `dnCP`, Bulgarian/Ndebele `pdCP`;
    `bareCP` is not). On [deal-2026]'s attested cells this coincides
    with `≠ bareCP` (`pCP`/`nCP` are unattested); D-membership is the
    definitional content, not the complement of a special case. -/
def hasNominalShell (inv : ShellInventory) : Prop := Shell.d ∈ inv

instance : DecidablePred hasNominalShell :=
  λ inv => inferInstanceAs (Decidable (Shell.d ∈ inv))

end ShellInventory

/-! ### Complement-frame axes -/

/-- Syntactic category of a complement slot. -/
inductive Cat where
  | nominal
  | adpositional
  | clausal
  deriving DecidableEq, Repr

/-- Embedded-subject requirement of a clausal slot: obligatorily null
    (control/raising infinitives) or overt, optionally with a fixed
    case (genitive subjects of nominalized clauses, [bondarenko-2022]). -/
inductive EmbeddedSubject where
  | obligatorilyNull
  | overt (subjCase : Option Case)
  deriving DecidableEq, Repr

end Slot

/-! ### The frame object -/

/-- One complement position of a verb's frame: its category plus, for
    clausal slots, the recorded clausal axes. On non-clausal slots the
    clausal axes are `none` (`Slot.WellFormed`); on clausal slots `none`
    means unrecorded. Frame-conditioned readings and control are not
    slot data — they live on `Verb.Reading`. -/
structure Slot where
  cat : Slot.Cat
  /-- Case marking on the slot (case-marked nominalized clauses, NPs). -/
  marking : Option Case := none
  /-- CP-external wrapping shell ([deal-2026] Table 79). -/
  shell : Option Slot.ShellInventory := none
  /-- Clause form (declarative vs embedded question). -/
  clauseForm : Option Features.ClauseForm := none
  /-- [noonan-2007] coding of the complement clause. -/
  coding : Option NoonanCompType := none
  /-- Embedded-subject requirement. -/
  embeddedSubject : Option Slot.EmbeddedSubject := none
  deriving DecidableEq, Repr

/-- Clausal axes are reserved for clausal slots. -/
def Slot.WellFormed (s : Slot) : Prop :=
  s.cat = .clausal ∨
    (s.shell = none ∧ s.clauseForm = none ∧ s.coding = none ∧
      s.embeddedSubject = none)

instance : DecidablePred Slot.WellFormed := fun s => by
  unfold Slot.WellFormed; infer_instance

/-- The slot is clausal. -/
def Slot.isClausal (s : Slot) : Prop := s.cat = .clausal

/-- A complement frame: the verb's selected complement positions in
    order. Intransitive = `[]`; double object = two slots. -/
abbrev Frame := List Slot

namespace Frame

/-- The [noonan-2007] codings recorded across the frame's slots. -/
def codings (fr : Frame) : List NoonanCompType := fr.filterMap (·.coding)

/-- Some slot of the frame records clause form `cf`. -/
def hasClauseForm (fr : Frame) (cf : Features.ClauseForm) : Prop :=
  ∃ s ∈ fr, s.clauseForm = some cf

instance (fr : Frame) (cf : Features.ClauseForm) :
    Decidable (fr.hasClauseForm cf) := by
  unfold hasClauseForm; infer_instance

/-- Some slot of the frame records [noonan-2007] coding `t`. -/
def hasCoding (fr : Frame) (t : NoonanCompType) : Prop :=
  ∃ s ∈ fr, s.coding = some t

instance (fr : Frame) (t : NoonanCompType) : Decidable (fr.hasCoding t) := by
  unfold hasCoding; infer_instance

/-! ### Smart constructors — the legacy `ComplementType` cells -/

/-- Transitive: one nominal slot. -/
def np : Frame := [{ cat := .nominal }]

/-- Double object: two nominal slots. -/
def np_np : Frame := [{ cat := .nominal }, { cat := .nominal }]

/-- NP + PP: a nominal plus an adpositional slot. -/
def np_pp : Frame := [{ cat := .nominal }, { cat := .adpositional }]

/-- Finite declarative clause. -/
def finiteClause : Frame :=
  [{ cat := .clausal, coding := some .indicative,
     clauseForm := some .declarative }]

/-- Infinitival clause: obligatorily null embedded subject. -/
def infinitival : Frame :=
  [{ cat := .clausal, coding := some .infinitive,
     embeddedSubject := some .obligatorilyNull }]

/-- Gerund / nominalized clause. -/
def gerund : Frame := [{ cat := .clausal, coding := some .nominalized }]

/-- Small clause (paratactic coding). -/
def smallClause : Frame := [{ cat := .clausal, coding := some .paratactic }]

/-- Embedded question. -/
def question : Frame :=
  [{ cat := .clausal, clauseForm := some .embeddedQuestion }]

end Frame

/-! ### The legacy enum view -/

/-- The `Frame` cell of a legacy `ComplementType` (`.none` ↦ `[]`). -/
def ComplementType.toFrame : ComplementType → Frame
  | .none => []
  | .np => Frame.np
  | .np_np => Frame.np_np
  | .np_pp => Frame.np_pp
  | .finiteClause => Frame.finiteClause
  | .infinitival => Frame.infinitival
  | .gerund => Frame.gerund
  | .smallClause => Frame.smallClause
  | .question => Frame.question

/-- Partial inverse of `ComplementType.toFrame`: the legacy enum cell a
    frame instantiates, `none` on frames richer than any cell. -/
def Frame.toComplementType (fr : Frame) : Option ComplementType :=
  [ComplementType.none, .np, .np_np, .np_pp, .finiteClause, .infinitival,
    .gerund, .smallClause, .question].find? (·.toFrame == fr)

/-- The enum view round-trips over the smart-constructor cells. -/
theorem toComplementType_toFrame (ct : ComplementType) :
    ct.toFrame.toComplementType = some ct := by cases ct <;> rfl
