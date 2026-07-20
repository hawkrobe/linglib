import Linglib.Semantics.Evidential.Source
import Linglib.Data.Examples.VonFintelGillies2010
import Linglib.Studies.Izvorski1997

/-!
# von Fintel & Gillies (2010): *Must* ... Stay! Strong!
[von-fintel-gillies-2010] [kratzer-1991]

Epistemic *must* carries an indirect-evidence signal yet is semantically
strong: *must φ* entails φ.

**Karttunen's Problem**: standard modal logic gives *must φ* ⊨ φ, yet the
bare prejacent is felt to convey more confidence than the *must*-claim
([kratzer-1991] p. 645: "I make a stronger claim in uttering (5a) than in
(5b)"). VF&G's resolution keeps *must* at the top of the strength ordering
(p. 352: *must* > *almost certainly* > *presumably* > *might*) and locates
the felt weakness in an evidential presupposition: the speaker's kernel
must not directly settle the prejacent.

## Main declarations

- `EvidenceType`, `EvidenceType.toCoarseSource`: VF&G's evidence-type
  classification and its collapse onto the Aikhenvald taxonomy
- `must_felicitous_iff_indirect`: over the example rows, the modalized
  member of a bare/modal minimal pair is felicitous iff the speaker's
  evidence source `IsIndirect`
- `cant_patterns_with_must`: the same biconditional restricted to the
  *can't* rows, derived from the previous theorem
- `must_entails_prejacent`: every minimal pair records prejacent
  entailment — including the infelicitous direct-evidence rows
- `must_evidence_matches_izvorski_ev`: *must* imposes the same
  indirect-evidence restriction as [izvorski-1997]'s Bulgarian EV
-/

namespace VonFintelGillies2010

open Semantics.Evidential
open Data.Examples

/-! ### Evidence types -/

/-- The type of evidence the speaker has for the prejacent. -/
inductive EvidenceType where
  /-- Direct sensory observation (seeing, hearing). -/
  | direct
  /-- Indirect inference from observable effects. -/
  | indirect
  /-- Elimination reasoning (ruling out alternatives). -/
  | elimination
  deriving Repr, DecidableEq, Inhabited

/-- Collapse to the Aikhenvald taxonomy. Elimination reasoning is
    inference, not direct access: the kernel does not directly settle the
    prejacent — which is why elimination licenses *must* (VF&G ex. 12). -/
def EvidenceType.toCoarseSource : EvidenceType → CoarseSource
  | .direct => .direct
  | .indirect => .inference
  | .elimination => .inference

/-- VF&G evidence types declare their coarse source; the evidential
    perspective derives via the canonical source mapping. -/
instance : HasCoarseSource EvidenceType where
  toCoarseSource e := some e.toCoarseSource

/-- All VF&G evidence types are nonfuture: their perspective is always
    retrospective or contemporaneous (T ≤ A). -/
theorem all_evidence_types_nonfuture (e : EvidenceType) :
    Semantics.Evidential.IsNonfuture e := by
  cases e <;> decide

/-! ### Adapters over the example rows -/

/-- Evidence-type adapter: the row's `evidence` feature as an
    `EvidenceType`. -/
def evidenceOf (row : LinguisticExample) : Option EvidenceType :=
  match row.feature? "evidence" with
  | some "direct" => some .direct
  | some "indirect" => some .indirect
  | some "elimination" => some .elimination
  | _ => none

/-- Rows whose primary text is the modalized member of a bare/modal
    minimal pair. -/
def mustPairs : List LinguisticExample :=
  Examples.all.filter (·.feature? "kind" == some "must_pair")

/-! ### The evidential restriction -/

/-- **Evidential restriction**: a *must*/*can't* sentence is felicitous
    iff the speaker's evidence source `IsIndirect`. Direct perception
    (exx. 6, 23) blocks the modal; inference — causal (exx. 7, 21, 24, 26)
    or by elimination (ex. 12) — licenses it. -/
theorem must_felicitous_iff_indirect :
    ∀ row ∈ mustPairs,
      row.judgment = .acceptable ↔
        ∀ e ∈ evidenceOf row, e.toCoarseSource.IsIndirect := by
  decide

/-- **Can't patterns with must**: the evidential restriction holds
    uniformly on the negative-modal rows (exx. 21, 23, 24) — *can't*
    groups with *must*, not with weak modals. -/
theorem cant_patterns_with_must :
    ∀ row ∈ mustPairs.filter (·.feature? "modal" == some "cant"),
      row.judgment = .acceptable ↔
        ∀ e ∈ evidenceOf row, e.toCoarseSource.IsIndirect :=
  fun row hrow => must_felicitous_iff_indirect row (List.mem_filter.mp hrow).1

/-- ***Must* imposes [izvorski-1997]'s EV restriction**: felicity of the
    modalized member tracks `CoarseSource.IsIndirect` of the evidence
    source in VF&G's *must* rows exactly as in Izvorski's Bulgarian EV
    paradigm — the two epistemic operators presuppose the same coarse
    indirect-evidence basis. -/
theorem must_evidence_matches_izvorski_ev :
    (∀ row ∈ mustPairs,
      row.judgment = .acceptable ↔
        ∀ e ∈ evidenceOf row, e.toCoarseSource.IsIndirect) ∧
    ∀ d ∈ Izvorski1997.evMustData, Izvorski1997.EvRequiresIndirect d :=
  ⟨must_felicitous_iff_indirect, Izvorski1997.all_evRequiresIndirect⟩

/-! ### Must is strong -/

/-- **Must is strong**: every minimal pair records that the modalized
    sentence entails its prejacent — including the direct-evidence rows
    where the modal is infelicitous. The restriction is evidential, not a
    weakening of content. The supporting inference rows (modus ponens is
    valid, *must φ ∧ perhaps ¬φ* is contradictory, retraction fails) are
    in the same JSON under `kind = inference`. -/
theorem must_entails_prejacent :
    ∀ row ∈ mustPairs, row.feature? "must_entails_prejacent" = some "true" := by
  decide

/-- The bare prejacent is felicitous in every context: the felicity
    restriction is contributed by the modal, not by the content. -/
theorem bare_always_felicitous :
    ∀ row ∈ mustPairs, ∀ alt ∈ row.alternatives, alt.2 = .acceptable := by
  decide

end VonFintelGillies2010
