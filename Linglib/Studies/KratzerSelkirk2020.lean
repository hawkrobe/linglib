import Linglib.Pragmatics.Expressives.Basic
import Linglib.Semantics.Alternatives.AltMeaning
import Linglib.Semantics.Focus.Control
import Linglib.Studies.HartmannZimmermann2007

/-!
# Two-feature decomposition of information structure

Kratzer & Selkirk's privative-feature analysis: information structure
decomposes into `[FoC]` (introduces alternatives) and `[G]` (presupposes
discourse salience), with no separate feature for newness — merely new
material is unmarked (their §5).

## Main definitions

* `ISFeature`: `FoC` and `G` constructors.
* `applyFoC`, `applyG`: feature contributions to an `AltMeaning`
  (their (45) and (47)); K&S givenness (46) is the substrate's
  `AltMeaning.Given`.
* `ContrastOperator`: the K&S ~ operator (54), which requires contrast
  with each antecedent and collapses alternatives.
* `onlySemantics`: the K&S analysis of *only* (56).
* `isAGiven`: Schwarzschild A-givenness on alternative sets.
* `IsFoCus`, `KSHausaReading`: the fn. 21 reinterpretation of Hausa.

## Main results

* `foc_g_exclusion`: `[FoC]` and `[G]` cannot both hold of a single
  meaning under a non-trivial domain.
* `consumed_alts_given`: ~ consumption yields Givenness — the engine of
  their Second Occurrence Focus analysis (58).
* `givenness_entails_aGivenness`: K&S givenness implies Schwarzschild
  A-givenness; the converse is refuted.

## References

* [kratzer-selkirk-2020], [schwarzschild-1999],
  [beaver-2007], [katz-selkirk-2011], [hartmann-zimmermann-2007].
-/

open Alternatives
open Pragmatics.Expressives

namespace KratzerSelkirk2020

/-- The two privative morphosyntactic features of [kratzer-selkirk-2020].

[FoC] and [G] are genuinely syntactic features: crosslinguistically they
trigger displacement, agreement, and ellipsis (§2). They happen to be
spelled out prosodically in Standard American and British English, but
this is not their defining property. Newness is not a feature — merely
new material is unmarked (§5). -/
inductive ISFeature where
  /-- FoCus: introduces alternatives, signals contrast.
      Resembles [wh] — comes with obligatory ~ operator. -/
  | FoC
  /-- Givenness: presupposes discourse salience, signals match.
      Contributes meaning directly (no operator needed). -/
  | G
  deriving DecidableEq, Repr

/-! ## Contribution of [FoC]

[FoC] does not change the O-value; its A-value is the full domain D_τ
(their (45)) — standard Roothian focus semantics. [FoC] all by itself
triggers no discourse requirement: it merely introduces alternatives,
which alternatives-evaluating operators (the ~ operator, *only*) then
use (their §8). -/

/-- Apply [FoC] to a meaning: O-value unchanged, A-value becomes the
    full domain (their (45)). -/
def applyFoC {α : Type*} (m : AltMeaning α) (domain : List α) : AltMeaning α :=
  { oValue := m.oValue, aValue := domain }

/-- [FoC] preserves O-value ((45) first clause). -/
theorem foc_preserves_oValue {α : Type*} (m : AltMeaning α) (domain : List α) :
    (applyFoC m domain).oValue = m.oValue := rfl

/-! ## Contribution of [G]

[G] is indexed with a contextually salient discourse referent a and
introduces a Givenness requirement (their (47)):

  ⟦[α]_{G_a}⟧_{O,C} is defined iff a is a discourse referent in the
    window preceding C, and α is Given with respect to a.
  If defined, ⟦[α]_{G_a}⟧_{O,C} = ⟦α⟧_{O,C} and ⟦[α]_{G_a}⟧_{A,C} = ⟦α⟧_{A,C}.

The requirement is purely use-conditional/expressive, like German *ja*
and *doch* — a condition on the discourse context, not on truth
conditions. -/

/-- Apply [G], indexed with the salient discourse referent `a`: defined
    only if the meaning is Given with respect to `a` (their (46), the
    substrate's `AltMeaning.Given`); if defined, both values are
    unchanged (their (47)). -/
def applyG {α : Type*} (m : AltMeaning α) (a : α) (_ : m.Given a) : AltMeaning α := m

/-- [G] preserves O-value ((47): if defined, O-value unchanged). -/
theorem g_preserves_oValue {α : Type*} (m : AltMeaning α) (a : α) (h : m.Given a) :
    (applyG m a h).oValue = m.oValue := rfl

/-- [G] preserves A-value ((47): A-value unchanged). -/
theorem g_preserves_aValue {α : Type*} (m : AltMeaning α) (a : α) (h : m.Given a) :
    (applyG m a h).aValue = m.aValue := rfl

/-- [FoC] and [G] are mutually exclusive: no constituent can satisfy both
    the [FoC] A-value condition (the full domain `D_τ`) and the [G] A-value
    condition (`AltMeaning.Given`, a singleton) when the domain has two
    distinct elements — "assuming that no semantic domain is a singleton
    set" (K&S §8 prose immediately preceding (58): "It follows that no
    constituents can be both [G]-marked and [FoC]-marked"). Distinct from
    (58) itself, which states the [G]-can-contain-[FoC]-only-with-consumption
    consequence. -/
theorem foc_g_exclusion {α : Type*} {m : AltMeaning α} {a b : α}
    (ha : a ∈ m.aSet) (hb : b ∈ m.aSet) (hab : a ≠ b) (referent : α) :
    ¬ m.Given referent := fun h => by
  rw [h] at ha hb
  exact hab (ha.trans hb.symm)

/-- [G]'s Givenness requirement and the ~ operator's contrast requirement
    are expressive (use-conditional) in the sense of [potts-2005] — K&S §8
    on (47) and (53); [FoC] itself imposes no discourse requirement.
    Packaged as the CI dimension of a `TwoDimProp`, the requirement
    projects through negation: "It's not the case that [ELIZA]_{FoC}
    mailed the caramels" still signals the contrast. -/
theorem useConditional_projects_through_neg {W : Type*} (atIssue requirement : W → Prop) :
    (TwoDimProp.neg (TwoDimProp.withCI atIssue requirement)).ci
    = (TwoDimProp.withCI atIssue requirement).ci :=
  TwoDimProp.ci_projects_through_neg _

/-! ## The ~ operator

[FoC]-marked constituents must be c-commanded by a ~ operator (their §8).
The ~ operator takes a set of discourse referents 𝔠 as its contextual
variable, requires α to represent a contrast with each member of 𝔠 —
conditions (i) and (ii) of their contrast representation (49): the
referent is among the alternatives and differs from the O-value; the
minimality condition (iii), which prevents overFoCusing by checking
FoC/G-variants, is not formalized here — and consumes the alternatives.

Unlike Rooth's ~, K&S's ~ has no provision for questions as antecedents:
it always signals contrast (their (54) discussion). -/

/-- The ~ operator, allowing multiple antecedents (their (54)):
    ⟦~_𝔠 α⟧_{O,C} is defined iff 𝔠 is a set of discourse referents in C
    and α represents a contrast with each member of 𝔠; if defined, the
    O-value is unchanged and the A-value collapses to {⟦α⟧_{O,C}}. -/
structure ContrastOperator (α : Type*) where
  /-- The expression's meaning -/
  meaning : AltMeaning α
  /-- The contrasting discourse referent(s) -/
  antecedents : List α
  /-- (49i): each antecedent is in the alternatives -/
  antecedents_in_alts : ∀ a ∈ antecedents, a ∈ meaning.aValue
  /-- (49ii): each antecedent differs from the O-value -/
  antecedents_ne_oValue : ∀ a ∈ antecedents, a ≠ meaning.oValue

/-- The ~ operator consumes alternatives: the result A-value is the
    singleton of the O-value. -/
def ContrastOperator.result {α : Type*}
    (op : ContrastOperator α) : AltMeaning α :=
  { oValue := op.meaning.oValue, aValue := [op.meaning.oValue] }

/-- ~ preserves O-value. -/
theorem squiggle_preserves_oValue {α : Type*} (op : ContrastOperator α) :
    op.result.oValue = op.meaning.oValue := rfl

/-- ~ collapses the A-value to a singleton. -/
theorem squiggle_singleton_aValue {α : Type*} (op : ContrastOperator α) :
    op.result.aValue = [op.meaning.oValue] := rfl

/-! ## Semantics of *only*

Their (55b) is Rooth's indirect association verbatim: association with
*only* is mediated by two occurrences of the contextual variable ℭ —
one on *only*, one on the ~ operator that comes with [FoC]. -/

/-- Semantics of *only* with explicit contrast set (their (56)):
`λp λw. ∀q ((q ∈ ℭ ∧ q(w)) → q = p)` — the strong-theory
`Focus.onlyVia` at the list-supplied contrast set, so the
`onlyVia` lemmas (antitonicity, squiggle-resolved exclusion) apply. -/
def onlySemantics {W : Type*} (contrastSet : List (W → Prop)) (prejacent : W → Prop) :
    Set W :=
  Focus.onlyVia {q | q ∈ contrastSet} prejacent

/-! ## [G] containing [FoC] requires alternatives consumption

Their (58): a constituent α containing [FoC]-marked β can be [G]-marked
only if α also contains an operator that consumes the alternatives
generated by β — otherwise α's A-value is not a singleton, so α cannot
be Given. This is the engine of their Second Occurrence Focus analysis:
in "the fáculty only quote [the faculty]_{FoC}" (their (59)/(60)), the
second occurrence is [FoC]-marked inside a [G]-marked VP, possible
because *only* + ~ consume the alternatives below the VP level. -/

/-- After ~ consumption the result is Given (their (46)) with respect to
    the ordinary value: the A-value has collapsed to the singleton
    {O-value}, which is the precondition for [G]-marking. -/
theorem consumed_alts_given {α : Type*} (op : ContrastOperator α) :
    op.result.Given op.meaning.oValue := by
  show op.result.aSet = {op.meaning.oValue}
  ext x
  simp [AltMeaning.mem_aSet, squiggle_singleton_aValue]

/-! ## Prosodic spellout (their §6–§7, not formalized)

In Standard American and British English the features are spelled out at
the syntax-phonology interface (MSO → PI): Match constraints
((27)/(28)/(35)) generate prosodic constituency; [FoC] is spelled out as
a prosodic head — the family {ω, φ, ι}-Level-Head ((34)/(43)) — and [G]
as dephrasing, [G] = No-φ (38). The English rankings are
[G] = No-φ >> MatchPhrase (41) and [G] = No-φ >> [FoC] = φ-Level-Head
(44): when the two spellouts conflict, [G] wins.

Second Occurrence Focus is the flagship prediction ((42), the
[beaver-2007] example *even [the prosecutor]_{FoC} [only named
[Sid]_{FoC} in court today]_{G}*): the SOF *Sid* sits inside a
[G]-marked constituent, so it lacks φ status — hence **no H accent
tone** and no φ-level prominence — while [FoC] = ω-Level-Head still
makes it an ω-level head, realized as the strong pronoun form
requirement and the small duration/intensity differences [beaver-2007]
measured. [katz-selkirk-2011]'s FoC-New / New-FoC / New-New triples
(their (36)) supply the phonetic evidence that FoCus differs from mere
newness: considerable downstep after a FoCus, no downstep or a small
upstep onto a FoCus, small default downstep between merely new phrases.

The pragmatic pressures — [G]-mark what is Given (61), represent
non-trivial contrasts (66) — govern when marking is obligatory. -/

/-! ## Bridge to Schwarzschild A-givenness

Schwarzschild's A-Givenness (stated within Alternatives Semantics,
their §3): α is A-Given in C iff a salient discourse referent is a
member of ⟦α⟧_{A,C}. K&S Givenness (46) is stronger — singleton vs
membership. -/

/-- Schwarzschild's A-Givenness: the referent is in the alternatives set. -/
def isAGiven {α : Type*} (m : AltMeaning α) (referent : α) : Prop :=
  referent ∈ m.aSet

instance instDecidableIsAGiven {α : Type*} [DecidableEq α] (m : AltMeaning α) (referent : α) :
    Decidable (isAGiven m referent) :=
  decidable_of_iff _ AltMeaning.mem_aSet.symm

/-- K&S Givenness entails Schwarzschild A-Givenness ("our Givenness
    falls out as a special case of A-Givenness", their §3): if the
    alternatives set is the singleton {a}, then a is a member of it. -/
theorem givenness_entails_aGivenness {α : Type*} {m : AltMeaning α} {referent : α}
    (h : m.Given referent) :
    isAGiven m referent := by
  rw [isAGiven, h]; rfl

/-- The converse fails: A-Givenness does NOT entail K&S Givenness.
    A non-singleton alternatives set can satisfy A-Givenness but not Givenness.

    This is the Schwarzschild overgeneration problem (K&S fn. 14):
    "Every cat is a complainer" is trivially A-Given because ∃P[every P
    is a complainer] is always true. K&S's singleton condition avoids this. -/
theorem aGivenness_not_sufficient : ∃ (m : AltMeaning Nat) (referent : Nat),
    isAGiven m referent ∧ ¬ m.Given referent := by
  refine ⟨⟨1, [1, 2]⟩, 1, by decide, fun h => ?_⟩
  have h2 : (2 : ℕ) ∈ ({1} : Set ℕ) := h ▸ AltMeaning.mem_aSet.mpr (by decide)
  simp at h2

/-! ## Hausa in situ vs ex situ (their fn. 21)

K&S contest [hartmann-zimmermann-2007]'s conclusion that information
focus is realised both in situ and ex situ in Hausa: without
controlling for accommodated contrasts, an in-situ answer may be
merely new and an ex-situ one contrastive. On the K&S inventory mere
newness is not focus at all, so the reinterpretation is: ex situ
realises [FoC], in situ is unmarked. The corpus tendencies both sides
cite (their fn. 21; H&Z §3.3: 99 vs 25 in situ for new information,
154 vs 12 ex situ for the contrastive family) fit the
reinterpretation; the accounts genuinely diverge only on the minority
cells, which is where the accommodation caveat does its work. -/

/-- The K&S inventory over H&Z's pragmatic-use taxonomy: the
contrastive family is [FoC]; new-information focus is mere newness —
no feature at all. -/
def IsFoCus : Focus.Use → Prop
  | .newInfo => False
  | _        => True

instance (u : Focus.Use) : Decidable (IsFoCus u) := by
  cases u <;> simp [IsFoCus] <;> infer_instance

/-- The fn. 21 reinterpretation of Hausa: ex-situ realisation ↔
[FoC]. -/
def KSHausaReading (u : HartmannZimmermann2007.FocusUtterance) : Prop :=
  u.cfg.strategy = .exSitu ↔ IsFoCus u.pragType

instance (u : HartmannZimmermann2007.FocusUtterance) :
    Decidable (KSHausaReading u) :=
  inferInstanceAs (Decidable (_ ↔ _))

/-- The two accounts diverge on H&Z's own matrix: the ex-situ
new-information cell (their (22)) and the in-situ corrective cell
(their (25)) both violate the reinterpretation. These are exactly the
cells the accommodation caveat targets — the divergence is real but
undecided on minimal pairs, and the corpus asymmetry is the evidence
both sides invoke. -/
theorem hz_matrix_cells_violate_ks_reading :
    ¬ KSHausaReading HartmannZimmermann2007.exSitu_newInfo ∧
    ¬ KSHausaReading HartmannZimmermann2007.inSitu_corrective := by
  decide

end KratzerSelkirk2020
