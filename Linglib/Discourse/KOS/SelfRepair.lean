import Linglib.Discourse.KOS.Defs
import Linglib.Discourse.KOS.Basic

/-!
# KOS: Self-Repair via MaxPending (= head of Pending)
[ginzburg-2012] §8.2 (pp. 282–290) "Unifying Self- and Other-Correction"

Per [ginzburg-2012] §6.3 footnote 31 p. 168 and §8.2: **MaxPending is
the maximal element of `dgb.pending`**, not a separate field. Self-repair
operates on the head of Pending directly.

## Operations

- `TIS.maxPending` — accessor: `dgb.pending.head?`
- `TIS.replaceMaxPending` — backwards-looking appropriateness repair
  (Ginzburg §8.2 ex. 31 p. 287 — the canonical repair operation):
  swap the current head of Pending with a corrected LocProp
- `TIS.clearMaxPending` — drop the head of Pending (abandon current
  incomplete utterance)
- `TIS.pushMaxPending` — push a new LocProp onto Pending (start a new
  in-construction utterance; equivalent to `DGB.pushPending`)

## Caveat

`TIS.extendMaxPendingPhon` and the procedural startRepair/completeRepair
sketched in earlier formaliser drafts are not Ginzburg operations per se —
he describes (informally) "incrementalising" Pending word-by-word but
doesn't enumerate operations. We expose only the `replaceMaxPending`
operation (which corresponds to ex. 31 p. 287's Backwards-looking
appropriateness repair) and the LocProp-stack manipulators that any
incremental-construction model needs. The §8.2.3 incremental dynamics is
deferred substrate work.
-/

namespace Discourse.KOS

-- ════════════════════════════════════════════════════
-- § 1. MaxPending Accessor
-- ════════════════════════════════════════════════════

/-- The current MaxPending: the head of `dgb.pending`, if any.
[ginzburg-2012] §6.3 footnote 31 p. 168. -/
def TIS.maxPending {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) : Option (LocProp Cont) :=
  tis.dgb.pending.head?

-- ════════════════════════════════════════════════════
-- § 2. MaxPending Stack Operations
-- ════════════════════════════════════════════════════

/-- Push a fresh LocProp onto Pending (start a new in-construction
utterance, becoming the new MaxPending). Equivalent to `DGB.pushPending`
lifted to TIS. -/
def TIS.pushMaxPending {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (lp : LocProp Cont) :
    TIS P Fact QContent Cont :=
  { tis with dgb := tis.dgb.pushPending lp }

/-- Drop the current MaxPending (abandon the in-construction or ungrounded
LocProp at the head of Pending). -/
def TIS.clearMaxPending {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) : TIS P Fact QContent Cont :=
  { tis with dgb := { tis.dgb with pending := tis.dgb.pending.tail } }

-- ════════════════════════════════════════════════════
-- § 3. Backwards-Looking Appropriateness Repair (§8.2 ex. 31 p. 287)
-- ════════════════════════════════════════════════════

/-- Backwards-looking appropriateness repair: replace the current
MaxPending with a corrected LocProp.

[ginzburg-2012] ex. 31 (p. 287): the speaker recognises that the
current maxpending's content fails appropriateness (wrong word, wrong
referent) and updates it to a candidate replacement.

If Pending is empty, this initializes it with the supplied form
(lenient default — Ginzburg's rule presupposes a MaxPending to repair). -/
def TIS.replaceMaxPending {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (replacement : LocProp Cont) :
    TIS P Fact QContent Cont :=
  { tis with dgb := { tis.dgb with
      pending := match tis.dgb.pending with
                 | [] => [replacement]
                 | _ :: rest => replacement :: rest } }

-- ════════════════════════════════════════════════════
-- § 4. Substrate Theorems
-- ════════════════════════════════════════════════════

/-- `pushMaxPending` makes the pushed LocProp the new MaxPending. -/
@[simp] theorem pushMaxPending_becomes_max {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (lp : LocProp Cont) :
    (tis.pushMaxPending lp).maxPending = some lp := rfl

/-- `clearMaxPending` removes the head of Pending. -/
@[simp] theorem clearMaxPending_drops_head {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) :
    (tis.clearMaxPending).dgb.pending = tis.dgb.pending.tail := rfl

/-- `replaceMaxPending` makes the replacement the new MaxPending. -/
@[simp] theorem replaceMaxPending_becomes_max {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (replacement : LocProp Cont) :
    (tis.replaceMaxPending replacement).maxPending = some replacement := by
  unfold TIS.replaceMaxPending TIS.maxPending
  cases tis.dgb.pending <;> rfl

/-- `replaceMaxPending` preserves the rest of Pending (only the head changes). -/
@[simp] theorem replaceMaxPending_preserves_tail {P Fact QContent : Type*} {Cont : Type}
    (tis : TIS P Fact QContent Cont) (replacement : LocProp Cont) :
    (tis.replaceMaxPending replacement).dgb.pending.tail = tis.dgb.pending.tail := by
  unfold TIS.replaceMaxPending
  cases tis.dgb.pending <;> rfl

end Discourse.KOS
