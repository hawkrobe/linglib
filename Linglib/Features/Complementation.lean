import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

/-!
# Complementation — Noonan typology and control

[noonan-2007]

The cross-linguistic complementation typology: [noonan-2007]'s six
morphological complement codings (`Complement.Coding`, in his summary
table's row order via `rank`) and twelve of his fourteen
complement-taking-predicate classes (`CTPClass`) with their default
reality status (`RealityStatus`, `ctpRealityStatus`), plus the control
enum for infinitival complements (`ControlType`).

These enums stay in `Features/` because `Data/Complementation/Schema.lean`
types its rows with them and the Data layer imports Features only. The
typed complement-frame object and the flat `ComplementType` view live
in `Syntax/Category/Verb/Frame.lean`; the adapter (`ComplementType.toCoding`)
in `Syntax/Category/Verb/Selection.lean`.

## Main declarations

* `Complement.Coding` + `isReduced` + `rank` — [noonan-2007]'s complement
  types, classified by the morphological coding of the complement clause
* `CTPClass`, `RealityStatus`, `ctpRealityStatus` — [noonan-2007]'s CTP
  classification and realis/irrealis defaults
* `ControlType` — subject/object control vs raising for infinitival
  complements
-/

/--
Control type for verbs with infinitival complements.
-/
inductive ControlType where
  | subjectControl  -- "John tried to leave" (John = leaver)
  | objectControl   -- "John persuaded Mary to leave" (Mary = leaver)
  | raising         -- "John seems to be happy" (no theta role for matrix subject)
  | none            -- Not applicable
  deriving DecidableEq, Repr

/-! ### Noonan complement typology -/

namespace Complement

/-- The six major complement types of [noonan-2007]'s survey, classified
    by the morphological coding of the complement clause (part of speech
    of its predicate, subject relation, inflectional range). -/
inductive Coding where
  | indicative     -- Finite clause with indicative mood marking
  | subjunctive    -- Finite clause with subjunctive/irrealis marking
  | paratactic     -- Juxtaposed fully-inflected clause, no subordinator
  | infinitive     -- Non-finite with "to" or equivalent
  | nominalized    -- Gerund / action nominal
  | participle     -- Participial complement
  deriving DecidableEq, Repr, BEq

/-- Is this coding non-finite (infinitive, nominalized, participial)? -/
def Coding.isReduced : Coding → Bool
  | .infinitive  => true
  | .nominalized => true
  | .participle  => true
  | _            => false

/-- Position in [noonan-2007]'s summary-table row order (indicative
    first, participle last). A presentation order, not an inflectional
    finiteness scale: paratactic complements carry the same inflectional
    range as indicatives. -/
def Coding.rank : Coding → Nat
  | .indicative  => 0
  | .subjunctive => 1
  | .paratactic  => 2
  | .infinitive  => 3
  | .nominalized => 4
  | .participle  => 5

/-- The summary-table row order as a linear order. -/
instance : LinearOrder Coding :=
  .lift' Coding.rank fun a b => by
    cases a <;> cases b <;> simp [Coding.rank]

end Complement

/-- Twelve of [noonan-2007]'s fourteen CTP classes (§3.2; predicates of
    fearing §3.2.6 and conjunctive predicates §3.2.14 are omitted), in
    the chapter's presentation order with perception hoisted next to the
    epistemic classes:
    - Utterance/propAttitude/pretence: report/judge propositional content
    - Commentative/knowledge: evaluate/know propositional content
    - Perception: direct experience
    - Desiderative/manipulative/modal: irrealis orientation
    - Achievement/phasal: aspectual
    - Negative: negation as CTP -/
inductive CTPClass where
  | utterance       -- say, tell, report
  | propAttitude    -- believe, think, suppose
  | pretence        -- pretend, act as if
  | commentative    -- regret, be sorry
  | knowledge       -- know, realize, discover
  | perception      -- see, hear, feel
  | desiderative    -- want, wish, hope
  | manipulative    -- make, cause, persuade, order
  | modal           -- can, must, should
  | achievement     -- positive: manage, dare; negative: try, forget to, avoid (§3.2.10)
  | phasal          -- start, stop, continue
  /-- A CTP whose sole semantic content is sentential negation
      ([noonan-2007] §3.2.13). Typologically rare; canonical examples
      are Fijian *sega* and Shuswap negative predicates. English `avoid`,
      `refrain`, `prevent` are NOT in this class — they are *negative
      achievement* predicates (§3.2.10). -/
  | negative
  deriving DecidableEq, Repr, BEq

/-- The fundamental realis/irrealis split that predicts complement type
    selection. Realis CTPs tend toward indicative; irrealis toward
    subjunctive/infinitive ([noonan-2007] §3.1.1). -/
inductive RealityStatus where
  | realis    -- CTP asserts or presupposes complement truth
  | irrealis  -- CTP does not commit to complement truth
  deriving DecidableEq, Repr

/-- Default reality status of each CTP class, extending [noonan-2007]'s
    realis/irrealis mood distinction (§3.1.1) from complement roles to
    CTP classes. The phasal and perception assignments are extensions:
    Noonan assigns their complements determined time reference, not a
    mood value. -/
def ctpRealityStatus : CTPClass → RealityStatus
  | .utterance    => .realis
  | .propAttitude => .realis
  | .pretence     => .irrealis
  | .commentative => .realis
  | .knowledge    => .realis
  | .perception   => .realis
  | .desiderative => .irrealis
  | .manipulative => .irrealis
  | .modal        => .irrealis
  | .achievement  => .irrealis
  | .phasal       => .realis
  | .negative     => .irrealis
