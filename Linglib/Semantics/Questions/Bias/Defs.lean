/-!
# Polar Question Bias — vocabulary
[romero-2024] [romero-han-2004] [ladd-1981] [bring-gunlogson-2000]

Theory-neutral vocabulary for polar question bias, shared by lexical
fragments and the theory layer. Polar questions come in three forms — PosQ,
LoNQ, HiNQ — sensitive to two independent bias dimensions: original speaker
bias (the speaker's prior epistemic lean) and contextual evidence bias
(evidence available in the current discourse).

This file carries only the directional enums and the form/bias compatibility
tables, so that Fragment lexical entries can record which bias a particle
*requires* without importing modal machinery; VERUM semantics with modal
frames lives study-side (`Studies/RomeroHan2004.lean`).

## Main definitions

* `PQForm` — the three polar-question forms.
* `OriginalBias`, `ContextualEvidence` — the two directional bias dimensions.
* `EvidentialBiasStrength` — strength of contextual-evidence bias by negation scope.
* `originalBiasOK`, `evidenceBiasOK` — Romero's compatibility tables.
-/

namespace Semantics.Questions.Bias

/-- The three polar question forms ([romero-2024] §1).

These forms are cross-linguistically attested and constitute the fundamental
typology for polar question bias research. -/
inductive PQForm where
  /-- Positive question: [p?]. "Is Jane coming?" -/
  | PosQ
  /-- Low negation question: [not p?]. "Is Jane not coming?" -/
  | LoNQ
  /-- High negation question: [n't p?]. "Isn't Jane coming?"
      In Czech: interrogative (VSO) word order. -/
  | HiNQ
  deriving DecidableEq, Repr

/-- Original speaker bias: belief or expectation that p is true, based on the
speaker's epistemic state *prior to* the current situation and exchange. -/
inductive OriginalBias where
  /-- Speaker originally expected/believed p. -/
  | forP
  /-- Speaker had no prior expectation about p. -/
  | neutral
  /-- Speaker originally expected/believed ¬p. -/
  | againstP
  deriving DecidableEq, Repr

/-- Contextual evidence bias ([bring-gunlogson-2000]): expectation about `p`
induced by evidence available in the current discourse situation. A felicity
condition on rising declaratives and a bias dimension for polar questions. -/
inductive ContextualEvidence where
  /-- Current context provides evidence for `p`. -/
  | forP
  /-- No contextual evidence either way. -/
  | neutral
  /-- Current context provides evidence against `p`. -/
  | againstP
  deriving DecidableEq, Repr

/-- Strength of contextual-evidence bias associated with a negation scope,
bridging Romero's typology to Staňková's three-way Czech distinction:
inner negation → strong (□_ev(¬p)), medial → weak (¬□_ev(p)), outer (FALSUM)
→ no □_ev involvement. -/
inductive EvidentialBiasStrength where
  /-- Inner: □_ev(¬p). -/
  | strong
  /-- Medial: ¬□_ev(p). -/
  | weak
  /-- Outer: FALSUM, not □_ev-based. -/
  | none_
  deriving DecidableEq, Repr

/-- Original speaker bias conditions on PQ forms ([romero-2024] Table 1).

Only HiNQ *mandatorily* conveys original speaker bias for p. LoNQ can convey
bias for p but can also be neutral. PosQ is compatible with bias for ¬p or
neutrality but was not tested for bias for p. -/
def originalBiasOK : PQForm → OriginalBias → Bool
  | .PosQ, .forP     => true   -- not tested by R&H but compatible
  | .PosQ, .neutral   => true
  | .PosQ, .againstP  => true
  | .LoNQ, .forP      => true
  | .LoNQ, .neutral   => true
  | .LoNQ, .againstP  => false -- not tested
  | .HiNQ, .forP      => true  -- mandatory: HiNQ conveys bias for p
  | .HiNQ, .neutral   => false -- HiNQ is infelicitous without bias
  | .HiNQ, .againstP  => false

/-- HiNQs mandatorily convey original speaker bias for p ([ladd-1981], [romero-han-2004]). -/
theorem hiNQ_requires_bias_for_p :
    originalBiasOK .HiNQ .neutral = false ∧
    originalBiasOK .HiNQ .againstP = false ∧
    originalBiasOK .HiNQ .forP = true := ⟨rfl, rfl, rfl⟩

/-- PosQs can be used in neutral contexts. -/
theorem posQ_neutral_ok : originalBiasOK .PosQ .neutral = true := rfl

/-- LoNQs can be neutral. -/
theorem loNQ_neutral_ok : originalBiasOK .LoNQ .neutral = true := rfl

/-- Contextual evidence bias conditions on PQ forms ([romero-2024] Table 2,
[bring-gunlogson-2000]).

PosQ requires evidence for p (or neutral). LoNQ requires evidence against p.
Outer-HiNQ is felicitous with neutral or against-p evidence. -/
def evidenceBiasOK : PQForm → ContextualEvidence → Bool
  | .PosQ, .forP      => true
  | .PosQ, .neutral    => true
  | .PosQ, .againstP   => false
  | .LoNQ, .forP       => false
  | .LoNQ, .neutral    => false
  | .LoNQ, .againstP   => true
  | .HiNQ, .forP       => false
  | .HiNQ, .neutral    => true
  | .HiNQ, .againstP   => true

/-- LoNQs require contextual evidence against p ([bring-gunlogson-2000]). -/
theorem loNQ_requires_evidence_against_p :
    evidenceBiasOK .LoNQ .forP = false ∧
    evidenceBiasOK .LoNQ .neutral = false ∧
    evidenceBiasOK .LoNQ .againstP = true := ⟨rfl, rfl, rfl⟩

/-- HiNQs are felicitous with evidence against p (contradiction scenarios). -/
theorem hiNQ_evidence_against_ok :
    evidenceBiasOK .HiNQ .againstP = true := rfl

/-- HiNQs are also felicitous with neutral evidence (suggestion scenarios). -/
theorem hiNQ_evidence_neutral_ok :
    evidenceBiasOK .HiNQ .neutral = true := rfl

end Semantics.Questions.Bias
