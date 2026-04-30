import Linglib.Theories.Dialogue.KOS.Defs
import Linglib.Theories.Dialogue.KOS.Basic

/-!
# KOS: Self-Repair via MaxPending
@cite{ginzburg-2012} §8.2 (pp. 282–290) "Unifying Self- and Other-Correction"

The self-repair substrate that previous formaliser stubs (`tucMidRepair`,
`repair_clears_tuc`) gestured at without backing. Operations on the
`MaxPending` field of `TIS.private_`:

- `startRepair` — initialize MaxPending with an empty form
- `extendRepair` — append phonological material
- `completeRepair` — promote MaxPending to Pending as a full LocProp,
  then clear MaxPending
- `clearMaxPending` — abandon the partial form
- `replaceMaxPending` — backwards-looking appropriateness repair (eq. 31
  p. 287): the speaker notices a problem and substitutes a corrected form

## Architecture

`MaxPending` is the formaliser's name for what Ginzburg models as an
extension of the Pending field tracking incomplete utterances. It lives
in `PrivateState.maxPending : Option MaxPending`. The substrate
operations here lift to TIS so consumers don't have to thread through
`tis.private_` directly.

## Backwards-looking appropriateness repair (eq. 31 p. 287)

Ginzburg's central self-repair rule: when the current maxpending's
content is inappropriate (e.g., the speaker realizes they used the
wrong name), a single update step replaces it with an alternative
form. We model this as `replaceMaxPending` taking the new MaxPending
record directly.

## Connection to LocProp Pending

A completed self-repair feeds the Pending field with a LocProp,
where it then enters the standard grounding/CRification protocol
(`KOS/Grounding.lean`).
-/

namespace Dialogue.KOS

-- ════════════════════════════════════════════════════
-- § 1. MaxPending Operations on TIS
-- ════════════════════════════════════════════════════

/-- Start a self-repair: initialize `MaxPending` with an empty form.

If a MaxPending was already in flight, it is overwritten — this models
the speaker abandoning one repair attempt and starting fresh. -/
def TIS.startRepair {P Fact QContent Cont : Type}
    (tis : TIS P Fact QContent Cont) : TIS P Fact QContent Cont :=
  { tis with private_ := { tis.private_ with maxPending := some {} } }

/-- Extend the in-flight `MaxPending` with additional phonological material.

If no MaxPending is in flight, this is a no-op. -/
def TIS.extendRepair {P Fact QContent Cont : Type}
    (tis : TIS P Fact QContent Cont) (phon : String) : TIS P Fact QContent Cont :=
  { tis with private_ := { tis.private_ with
      maxPending := tis.private_.maxPending.map (fun mp =>
        { mp with phonSoFar := mp.phonSoFar ++ phon }) } }

/-- Complete a self-repair: promote MaxPending to the Pending field as a
full `LocProp`, then clear MaxPending.

The caller supplies the final LocProp (the substrate doesn't impose how
the partial form maps to a complete locutionary proposition — that's
grammar-specific). -/
def TIS.completeRepair {P Fact QContent Cont : Type}
    (tis : TIS P Fact QContent Cont) (final : LocProp Cont) :
    TIS P Fact QContent Cont :=
  { tis with
    dgb := tis.dgb.pushPending final
    private_ := { tis.private_ with maxPending := none } }

/-- Abandon any in-flight MaxPending without promoting. -/
def TIS.clearMaxPending {P Fact QContent Cont : Type}
    (tis : TIS P Fact QContent Cont) : TIS P Fact QContent Cont :=
  { tis with private_ := { tis.private_ with maxPending := none } }

-- ════════════════════════════════════════════════════
-- § 2. Backwards-Looking Appropriateness Repair
-- ════════════════════════════════════════════════════

/-- Backwards-looking appropriateness repair: substitute the current
in-flight MaxPending with a corrected form.

@cite{ginzburg-2012} eq. 31 (p. 287): the speaker recognises that the
current maxpending's content fails appropriateness (wrong word, wrong
referent) and updates it to a candidate replacement.

If no MaxPending is in flight, this initializes one with the supplied
form (lenient default). -/
def TIS.replaceMaxPending {P Fact QContent Cont : Type}
    (tis : TIS P Fact QContent Cont) (replacement : MaxPending) :
    TIS P Fact QContent Cont :=
  { tis with private_ := { tis.private_ with maxPending := some replacement } }

-- ════════════════════════════════════════════════════
-- § 3. Substrate Theorems
-- ════════════════════════════════════════════════════

/-- After `startRepair`, MaxPending is initialized to the empty bundle. -/
theorem startRepair_initializes_maxPending {P Fact QContent Cont : Type}
    (tis : TIS P Fact QContent Cont) :
    tis.startRepair.private_.maxPending = some {} := rfl

/-- `clearMaxPending` clears the field. -/
theorem clearMaxPending_clears {P Fact QContent Cont : Type}
    (tis : TIS P Fact QContent Cont) :
    tis.clearMaxPending.private_.maxPending = none := rfl

/-- After `completeRepair`, MaxPending is cleared. -/
theorem completeRepair_clears_maxPending {P Fact QContent Cont : Type}
    (tis : TIS P Fact QContent Cont) (final : LocProp Cont) :
    (tis.completeRepair final).private_.maxPending = none := rfl

/-- After `completeRepair`, the supplied LocProp is in Pending. -/
theorem completeRepair_pushes_pending {P Fact QContent Cont : Type}
    (tis : TIS P Fact QContent Cont) (final : LocProp Cont) :
    (tis.completeRepair final).dgb.pending = final :: tis.dgb.pending := rfl

/-- After `replaceMaxPending`, MaxPending is the supplied replacement. -/
theorem replaceMaxPending_substitutes {P Fact QContent Cont : Type}
    (tis : TIS P Fact QContent Cont) (replacement : MaxPending) :
    (tis.replaceMaxPending replacement).private_.maxPending = some replacement := rfl

/-- `startRepair` followed by `clearMaxPending` is a no-op on the maxPending
field (returns to none). -/
theorem startRepair_then_clear {P Fact QContent Cont : Type}
    (tis : TIS P Fact QContent Cont) :
    tis.startRepair.clearMaxPending.private_.maxPending = none := rfl

end Dialogue.KOS
