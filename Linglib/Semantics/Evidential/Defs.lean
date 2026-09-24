module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Evidentials

This file defines the evidential as a lexical object: a form, its realization, and the
information sources it covers. Following [aikhenvald-2004], information source is carved into
six recurrent semantic parameters — visual, non-visual sensory, inference, assumption, hearsay
and quotative — and an evidential covers a set of them: a firsthand term covers visual and
sensory evidence together, a non-firsthand term covers inference, assumption and hearsay, a
visual term covers visual evidence alone. [willett-1988]'s three types of evidence, attested,
reported and inferring, group the six parameters in pairs, and a term is of a type when its
coverage lies within that type's block. A language's inventory is a `List Evidential`
declared in its Fragment; it is well formed when its terms are pairwise disjoint, so that they
partition the parameters the language expresses (`Semantics/Evidential/Basic.lean`).

## Implementation notes

The six parameters are Aikhenvald's recurrent terms and nothing finer: no spoken language has
an evidential for smell, taste or touch alone, and general knowledge is not a parameter but a
meaning an assumed evidential may carry and that many systems cast in the visual, a semantic
extension rather than coverage. A term whose source lies outside the six, such as the Kashaya
performative for the speaker's own act, covers none of them. The realizations are the
grammatical means of Aikhenvald's chapter on marking, where she finds no evidentiality
expressed by apophony or mutation; lexical and parenthetical means are evidentiality
strategies, not evidentials, and an inventory records none.

## Main definitions

* `Evidential.Parameter` — the six semantic parameters of information source.
* `Evidential.EvidenceType`, `Parameter.evidenceType`, `EvidenceType.block` — Willett's
  three types of evidence, the type of a parameter and the parameters of a type.
* `Evidential.Exponent` — how an evidential is realized.
* `Evidential` — the lexical entry; `Evidential.covers` its information sources.
* `Evidential.IsOfType`, `evidenceType?` — the type of evidence a term lies within, and
  `IsDirect`, `IsInferential`, `IsReportative`, `IsNonfirsthand`, the coarse kinds of term.
* `Evidential.WellFormed`, `Evidential.expressed` — a paradigm's disjointness and its span.

## References

* [aikhenvald-2004]
* [willett-1988]
-/

@[expose] public section

namespace Evidential

/-- The six recurrent semantic parameters of information source. -/
inductive Parameter where
  /-- Information acquired through seeing. -/
  | visual
  /-- Information acquired through hearing, typically extended to smell and taste and
  sometimes to touch. -/
  | sensory
  /-- Inference from visible or tangible evidence or result. -/
  | inference
  /-- Assumption from evidence other than visible results: reasoning or general knowledge. -/
  | assumption
  /-- Reported information with no reference to its source. -/
  | hearsay
  /-- Reported information with overt reference to the quoted source. -/
  | quotative
  deriving DecidableEq, Repr, Fintype

/-- Willett's three types of evidence. -/
inductive EvidenceType where
  /-- Evidence attested by the speaker's own senses. -/
  | attested
  /-- Evidence reported to the speaker, at second or third hand or as folklore. -/
  | reported
  /-- Evidence inferred from results or by reasoning. -/
  | inferring
  deriving DecidableEq, Repr

/-- The type of evidence a parameter falls under: Willett's types group the six parameters in
pairs. -/
def Parameter.evidenceType : Parameter → EvidenceType
  | .visual | .sensory => .attested
  | .inference | .assumption => .inferring
  | .hearsay | .quotative => .reported

/-- The block of a type of evidence: the parameters falling under it. -/
def EvidenceType.block (t : EvidenceType) : Finset Parameter :=
  Finset.univ.filter (·.evidenceType = t)

/-- How an evidential is grammatically realized. -/
inductive Exponent where
  /-- An inflectional affix of the verb (Abkhaz *-zaap'*, Kashaya *-yă*). -/
  | verbalAffix
  /-- A term of the tense-aspect paradigm (Turkish *-mIş*, the Bulgarian *l*-form). -/
  | tamFusion
  /-- A clitic, on the first constituent or a focused one (Cuzco Quechua *-si*). -/
  | clitic
  /-- A particle (Warlpiri, Hopi). -/
  | particle
  /-- A copula or auxiliary verb (Lhasa Tibetan *-song*). -/
  | auxiliary
  deriving DecidableEq, Repr

end Evidential

/-- An evidential is a form with its realization and the information sources it covers. -/
structure Evidential where
  /-- A representative morpheme or construction label. -/
  form : String
  /-- The realization strategy. -/
  exponent : Evidential.Exponent
  /-- The semantic parameters the term covers; a term for a source outside the six covers
  none. -/
  covers : Finset Evidential.Parameter
  deriving DecidableEq

namespace Evidential

/-- A term is of a type of evidence when its coverage lies within that type's block. -/
def IsOfType (e : Evidential) (t : EvidenceType) : Prop := e.covers.Nonempty ∧ e.covers ⊆ t.block

instance (e : Evidential) (t : EvidenceType) : Decidable (e.IsOfType t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A direct evidential covers firsthand evidence only. -/
abbrev IsDirect (e : Evidential) : Prop := e.IsOfType .attested

/-- An inferential evidential covers inference or assumption only. -/
abbrev IsInferential (e : Evidential) : Prop := e.IsOfType .inferring

/-- A reportative evidential covers hearsay or quotation only. -/
abbrev IsReportative (e : Evidential) : Prop := e.IsOfType .reported

/-- A non-firsthand evidential covers inference and hearsay together but not visual evidence:
the marked term of a two-choice system. -/
def IsNonfirsthand (e : Evidential) : Prop :=
  .inference ∈ e.covers ∧ .hearsay ∈ e.covers ∧ .visual ∉ e.covers

instance : DecidablePred IsNonfirsthand := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The type of evidence of an evidential, when its coverage lies within one of Willett's
types; a non-firsthand term has none. -/
def evidenceType? (e : Evidential) : Option EvidenceType :=
  if e.IsDirect then some .attested
  else if e.IsInferential then some .inferring
  else if e.IsReportative then some .reported
  else none

/-- The parameters an inventory expresses. -/
def expressed (es : List Evidential) : Finset Parameter := (es.map covers).toFinset.sup id

/-- An inventory is well formed when its terms are pairwise disjoint, so that no parameter is
covered twice; two entries with the same nonempty coverage count as one term covered twice. -/
def WellFormed (es : List Evidential) : Prop := es.Pairwise fun a b ↦ Disjoint a.covers b.covers

instance : DecidablePred WellFormed := fun es ↦
  inferInstanceAs (Decidable (es.Pairwise fun a b ↦ Disjoint a.covers b.covers))

end Evidential
