import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.DeriveFintype

/-!
# Evidentials

This file defines the evidential as a lexical object: a form, its realization, and the
information sources it covers. Following Aikhenvald, information source is carved into six
recurrent semantic parameters — visual, non-visual sensory, inference, assumption, hearsay and
quotative — and an evidential covers a set of them: a firsthand term covers visual and sensory
evidence together, a non-firsthand term covers inference, assumption and hearsay, a visual
term covers visual evidence alone. A language's inventory is a `List Evidential` declared in
its Fragment; it is well formed when no parameter is covered twice, so that the terms
partition the parameters the language expresses (`Semantics/Evidential/Basic.lean`).

## Main definitions

* `Semantics.Evidential.Parameter` — the six semantic parameters of information source.
* `Semantics.Evidential.Exponent` — how an evidential is realized.
* `Evidential` — the lexical entry; `Evidential.covers` its information sources.
* `Evidential.IsDirect`, `IsInferential`, `IsReportative`, `IsNonfirsthand` — the coarse
  kinds of term, as properties of coverage.
* `Evidential.WellFormed`, `Evidential.expressed` — a paradigm's disjointness and its span.

## References

* [aikhenvald-2004], §2.5
* [willett-1988]
-/

namespace Semantics.Evidential

/-- The six recurrent semantic parameters of information source. -/
inductive Parameter where
  /-- Information acquired through seeing. -/
  | visual
  /-- Information acquired through hearing, extended to smell, taste and touch. -/
  | sensory
  /-- Inference from visible or tangible evidence or result. -/
  | inference
  /-- Assumption from reasoning or general knowledge. -/
  | assumption
  /-- Reported information with no reference to its source. -/
  | hearsay
  /-- Reported information with overt reference to the quoted source. -/
  | quotative
  deriving DecidableEq, Repr, Fintype

/-- How an evidential is morphosyntactically realized. -/
inductive Exponent where
  /-- A verbal affix or bound suffix (Kashaya *-yá*, Turkish *-mIş*). -/
  | verbalAffix
  /-- Fused into the TAM paradigm (the Bulgarian *l*-form). -/
  | tamFusion
  /-- A second-position clitic (Cuzco Quechua *-si*, *-chá*). -/
  | clitic2P
  /-- A clausal particle, typically clause-final (Cheyenne *=sėstse*). -/
  | clauseParticle
  /-- A parenthetical or matrix-frame construction (English *I hear*). -/
  | parenthetical
  /-- A grammaticalized lexical frame (Korean *-tay*). -/
  | lexicalFrame
  /-- Tonal or ablaut realization. -/
  | toneAblaut
  deriving DecidableEq, Repr

end Semantics.Evidential

/-- An evidential: its form, its realization, and the information sources it covers. -/
structure Evidential where
  /-- A representative morpheme or construction label. -/
  form : String
  /-- The realization strategy. -/
  exponent : Semantics.Evidential.Exponent
  /-- The semantic parameters the term covers. -/
  covers : Finset Semantics.Evidential.Parameter
  deriving DecidableEq

namespace Evidential

open Semantics.Evidential

/-- A direct evidential covers firsthand evidence only. -/
def IsDirect (e : Evidential) : Prop := e.covers.Nonempty ∧ e.covers ⊆ {.visual, .sensory}

/-- An inferential evidential covers inference or assumption only. -/
def IsInferential (e : Evidential) : Prop :=
  e.covers.Nonempty ∧ e.covers ⊆ {.inference, .assumption}

/-- A reportative evidential covers hearsay or quotation only. -/
def IsReportative (e : Evidential) : Prop :=
  e.covers.Nonempty ∧ e.covers ⊆ {.hearsay, .quotative}

/-- A non-firsthand evidential covers inference and hearsay together but not visual evidence:
the marked term of a two-choice system. -/
def IsNonfirsthand (e : Evidential) : Prop :=
  .inference ∈ e.covers ∧ .hearsay ∈ e.covers ∧ .visual ∉ e.covers

instance : DecidablePred IsDirect := fun _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsInferential := fun _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsReportative := fun _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred IsNonfirsthand := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The parameters an inventory expresses. -/
def expressed (es : List Evidential) : Finset Parameter := (es.map covers).toFinset.sup id

/-- An inventory is well formed when distinct terms cover disjoint parameters. -/
def WellFormed (es : List Evidential) : Prop :=
  ∀ a ∈ es, ∀ b ∈ es, a ≠ b → Disjoint a.covers b.covers

instance : DecidablePred WellFormed := fun es =>
  inferInstanceAs (Decidable (∀ a ∈ es, ∀ b ∈ es, a ≠ b → Disjoint a.covers b.covers))

end Evidential
