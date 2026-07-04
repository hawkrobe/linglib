/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Logic.FactorsThroughOn
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Phonology.Prosody.Phrase
import Linglib.Semantics.Focus.Control
import Linglib.Semantics.Focus.Realization
import Linglib.Fragments.Tangale.TAM
import Linglib.Fragments.Tangale.Phonology
import Linglib.Data.Examples.HartmannZimmermann2004

/-!
# Tangale focus strategies

Formalises [hartmann-zimmermann-2004]: Tangale marks focus by four
different devices conditioned on subjecthood, aspect, and transitivity —
obligatory postverbal movement for subjects, the suffix *-i* for
intransitive predicate focus, a prosodic boundary (vowel elision and
left-line delinking blocked) for perfective transitive foci, and
*nothing at all* in the progressive. The boundary underdetermines the
focus extent (V-, VP-, and OBJ-focus are string- and pitch-identical),
and the particle *núm* 'only' associates with any of the three extents
from one fixed DP-adjacent position — association is anaphoric, not
structural.

## Implementation notes

Realisation uses the shared `Semantics.Focus.Realization` vocabulary
(reflex lists; `Strategy` is the paper's label set, derived from the
reflex shape). The aspect frames are grounded in the Tangale fragment
via `Aspect.entry`: the perfective rows carry [kidda-1985]'s singular
perfective suffix and the paper's progressive is the fragment's
continuous (preposed *né*). The *núm* readings use the strong-theory
`Semantics.Focus.onlyVia`: one string, three contrast-set resolutions.

The paper's fn. 6 notes the suffix *-i* does not occur with all
intransitive verbs; `realize` idealises it as the intransitive
perfective strategy. The boundary diagnosis is grounded in
`Fragments/Tangale/Phonology.lean`: `prosodic_reflex_audible` cites
[kidda-1985]'s elision cascade as what makes the boundary reflex
perceptible.

## TODO

* The interleaved elision-feeding-tone-shift derivations of
  [kidda-1985] (34) on lexical forms.
* The paper's two solutions (§6): the prosodic-boundary account vs the
  subjects-vs-non-subjects account as rival `Predict`-style theories.
-/

namespace HartmannZimmermann2004

open Semantics.Focus
open Semantics.Focus.Interpretation (PropFocusValue)

/-! ## The marking system (§4.1, §5.2, §6.2) -/

/-- Verbal aspect, as far as the focus-marking facts require. -/
inductive Aspect where
  | perfective | progressive
  deriving DecidableEq, Repr

/-- The fragment entry realising each aspect frame
(`Fragments/Tangale/TAM.lean`): the perfective rows carry
[kidda-1985]'s singular perfective (the *-gó* of *wai-gó*, *wur-gó*),
and the paper's progressive is the continuous (preposed *né*, the
paper's PROG *n*). -/
def Aspect.entry : Aspect → Tangale.TAMEntry
  | .perfective  => Tangale.perfectiveSg
  | .progressive => Tangale.continuous

/-- The paper's glosses are grounded in the fragment: PERF is the
voiced alternant of the perfective suffix, and PROG is the preposed
continuous marker. -/
theorem aspect_entry_grounds_glosses :
    "gó" ∈ Aspect.perfective.entry.suffixAlternants ∧
    Aspect.progressive.entry.marker = .preposed "né" := by decide

/-- The focused constituent in the paper's paradigm. -/
inductive Focused where
  | subject | verb | vp | object
  deriving DecidableEq, Repr

/-- The four marking strategies. -/
inductive Strategy where
  | postposing | suffixI | boundary | unmarked
  deriving DecidableEq, Repr

/-- A focus configuration: what is focused, in which aspect, with a
transitive or intransitive predicate. -/
structure Config where
  focused    : Focused
  aspect     : Aspect
  transitive : Bool
  deriving DecidableEq, Repr

/-- Object focus presupposes a transitive predicate. -/
def Config.WF (c : Config) : Prop :=
  c.focused = .object → c.transitive = true

instance (c : Config) : Decidable c.WF :=
  inferInstanceAs (Decidable (_ → _))

/-- The overt reflexes of each configuration: subjects surface
displaced in every aspect ((17b)); intransitive predicate focus bears
the morpheme *-i* ((24b)); transitive perfective non-subject foci get
the prosodic boundary after the verb ((25a–c)); progressive non-subject
foci receive nothing ((31)/(32a–c)). -/
def realize : Config → Realization Focused
  | ⟨.subject, _, _⟩        => ⟨.subject, [.displacement .subject]⟩
  | ⟨f, .perfective, false⟩ => ⟨f, [.morpheme f]⟩
  | ⟨f, .perfective, true⟩  => ⟨f, [.boundary .verb]⟩
  | ⟨f, .progressive, _⟩    => ⟨f, []⟩

/-- The paper's strategy labels, classified from the realization
shape — a derived quotient, not a primitive tag. -/
def marking (c : Config) : Strategy :=
  match (realize c).reflexes with
  | [.displacement _] => .postposing
  | [.morpheme _]     => .suffixI
  | [.boundary _]     => .boundary
  | _                 => .unmarked

/-- Focused subjects are overtly marked in every aspect — the paper's
§6 subjects-vs-non-subjects generalization, shared with Hausa. -/
theorem subject_always_marked (c : Config) (h : c.focused = .subject) :
    (realize c).IsOvert := by
  obtain ⟨f, a, t⟩ := c
  cases h
  simp [realize, Realization.IsOvert]

/-- Progressive non-subject foci are wholly unmarked ((31)/(32a–c),
contra Kidda 1993). -/
theorem progressive_nonsubject_unmarked (c : Config)
    (hs : c.focused ≠ .subject) (ha : c.aspect = .progressive) :
    (realize c).reflexes = [] := by
  obtain ⟨f, a, t⟩ := c
  cases ha
  cases f <;> first | exact absurd rfl hs | rfl

/-- Focus marking is not obligatory: a well-formed focus configuration
with no overt reflex — (32a), object focus in the progressive. -/
theorem focus_marking_not_obligatory :
    ∃ c : Config, c.WF ∧ ¬ (realize c).IsOvert :=
  ⟨⟨.object, .progressive, true⟩, fun _ => rfl, fun h => h rfl⟩

/-- Tangale refutes the universalist claim that every focus receives an
overt reflex — the Tangale side of the counterexample the Hausa
chapter states against the Basic Focus Rule. -/
theorem tangale_refutes_perceptibility :
    ¬ Semantics.Focus.EveryFocusPerceptible realize :=
  fun h => h ⟨.object, .progressive, true⟩ rfl

/-- The prosodic reflex is audible: the boundary-blocked perfective
form differs from the phrase-medial elided form — [kidda-1985]'s
elision cascade is what makes `Reflex.boundary` perceptible in the
(25) cells. -/
theorem prosodic_reflex_audible :
    Tangale.blockedForm ≠ Tangale.elidedForm :=
  Tangale.boundary_audible.1

/-- The perfective boundary underdetermines the focus extent: on
transitive perfective non-subject configurations, `focused` does not
factor through the reflexes — (25a–c) are string- and pitch-identical
across the three extents. -/
theorem boundary_underdetermines_extent :
    ¬ Function.FactorsThroughOn
        Config.focused (fun c => (realize c).reflexes)
        {c | c.aspect = .perfective ∧ c.transitive = true ∧
             c.focused ≠ .subject} := by
  rw [Function.not_factorsThroughOn_iff_exists_witness]
  exact ⟨⟨.verb, .perfective, true⟩, ⟨.object, .perfective, true⟩,
    by decide, by decide, rfl, by decide⟩

/-! ## Deriving the boundary ([truckenbrodt-1999]-style alignment)

The perfective boundary is not primitive. Candidate parses wrap the
V–O string into one φ or separate the object into its own φ; a
focus-alignment constraint (the focus's left edge coincides with a
φ-edge) dominates phrasal economy exactly when the object is focused.
The winning parse's φ-edge is the `Reflex.boundary` of `realize`, and
its audibility is the blocked elision cascade
(`prosodic_reflex_audible`). -/

private def ω : Prosody.Tree := .node .om [.node .syl []]

/-- V and O wrapped into one φ. -/
private def wrapped : Prosody.Tree := .node .iota [.node .ph [ω, ω]]

/-- O separated into its own φ. -/
private def separated : Prosody.Tree :=
  .node .iota [.node .ph [ω], .node .ph [ω]]

/-- ALIGN-Focus: violated when no φ-edge sits at the focus's left edge
(leaf offset 1, the object). -/
private def alignFocus : Constraints.Constraint Prosody.Tree :=
  .binary (fun t => ¬ ∃ s ∈ RoseTree.spansOf Prosody.Constituent.isPh t, s.1 = 1)

/-- Phrasal economy: one violation per φ. -/
private def starPhi : Constraints.Constraint Prosody.Tree :=
  fun t => (RoseTree.spansOf Prosody.Constituent.isPh t).length

open OptimalityTheory in
/-- Object focus: alignment dominates economy, and the separated parse
wins — the derived φ-edge after the verb. -/
theorem focused_parse_separates :
    (Tableau.ofRanking [wrapped, separated] [alignFocus, starPhi]).optimal
      = {separated} := by decide

open OptimalityTheory in
/-- All-new: economy decides alone and the wrapped parse wins — no
boundary, the elision cascade applies. -/
theorem neutral_parse_wraps :
    (Tableau.ofRanking [wrapped, separated] [starPhi]).optimal
      = {wrapped} := by decide

/-- The derived contrast grounds the reflex: in the separated parse no
φ spans both leaves, so the V–O juncture is phrase-external and
elision is blocked (`Tangale.boundary_audible` supplies the audible
difference); in the wrapped parse the juncture is φ-internal. -/
theorem separated_edge_wrapped_internal :
    (0, 2) ∉ RoseTree.spansOf Prosody.Constituent.isPh separated ∧
    (0, 2) ∈ RoseTree.spansOf Prosody.Constituent.isPh wrapped := by decide

/-! ## The *núm* readings (§6.3)

*núm* 'only' is syntactically fixed to DP expressions, yet associates
with object, VP, or verb focus — identical structure and identical
pitch across (36a–c). Three contrast-set resolutions of one string,
through the strong-theory `onlyVia`. -/

/-- Worlds tracking what the speaker did with the book and the rest. -/
structure NumWorld where
  boughtBook  : Bool
  boughtShirt : Bool
  readBook    : Bool
  deriving DecidableEq, Repr

def boughtBookP : Set NumWorld := {w | w.boughtBook}
def boughtShirtP : Set NumWorld := {w | w.boughtShirt}
def readBookP : Set NumWorld := {w | w.readBook}

/-- (36a): object association — alternatives to the book. -/
def objReading : Set NumWorld :=
  onlyVia {boughtBookP, boughtShirtP} boughtBookP

/-- (36b): VP association — alternatives to the buying-the-book
activity ('I did nothing else'). -/
def vpReading : Set NumWorld :=
  onlyVia {boughtBookP, boughtShirtP, readBookP} boughtBookP

/-- (36c): verb association — alternative relations to the book ('but
I have not read it yet'). -/
def vReading : Set NumWorld :=
  onlyVia {boughtBookP, readBookP} boughtBookP

/-- Bought the book and read it, bought nothing else: verifies (36a),
falsifies (36c). -/
private def w₁ : NumWorld := ⟨true, false, true⟩
/-- Bought the book and a shirt, read nothing: verifies (36c),
falsifies (36a). -/
private def w₂ : NumWorld := ⟨true, true, false⟩

private theorem readBook_ne_boughtBook : readBookP ≠ boughtBookP := by
  intro h
  have hmem : (⟨false, false, true⟩ : NumWorld) ∈ readBookP := rfl
  rw [h] at hmem
  exact absurd hmem Bool.false_ne_true

private theorem boughtShirt_ne_boughtBook : boughtShirtP ≠ boughtBookP := by
  intro h
  have hmem : (⟨false, true, false⟩ : NumWorld) ∈ boughtShirtP := rfl
  rw [h] at hmem
  exact absurd hmem Bool.false_ne_true

/-- The three associations are semantically distinct readings of one
surface string: the surface form does not determine the association. -/
theorem num_readings_distinct :
    objReading ≠ vReading ∧ objReading ≠ vpReading ∧ vReading ≠ vpReading := by
  have h₁obj : w₁ ∈ objReading := by
    intro q hq hwq
    rcases hq with rfl | rfl
    · rfl
    · exact absurd hwq Bool.false_ne_true
  have h₁v : w₁ ∉ vReading := fun h =>
    readBook_ne_boughtBook (h readBookP (Or.inr rfl) rfl)
  have h₂v : w₂ ∈ vReading := by
    intro q hq hwq
    rcases hq with rfl | rfl
    · rfl
    · exact absurd hwq Bool.false_ne_true
  have h₂obj : w₂ ∉ objReading := fun h =>
    boughtShirt_ne_boughtBook (h boughtShirtP (Or.inr rfl) rfl)
  have h₁vp : w₁ ∉ vpReading := fun h =>
    readBook_ne_boughtBook (h readBookP (Or.inr (Or.inr rfl)) rfl)
  have h₂vp : w₂ ∉ vpReading := fun h =>
    boughtShirt_ne_boughtBook (h boughtShirtP (Or.inr (Or.inl rfl)) rfl)
  exact ⟨fun h => h₁v (h ▸ h₁obj),
         fun h => h₁vp (h ▸ h₁obj),
         fun h => h₂vp (h ▸ h₂v)⟩

/-- The VP association is the strongest reading: 'I did nothing else'
entails both 'I bought nothing else' and 'I did nothing else to the
book' — `onlyVia_antitone` over the contrast-set inclusions. -/
theorem vp_reading_strongest :
    vpReading ⊆ objReading ∧ vpReading ⊆ vReading :=
  ⟨onlyVia_antitone
      (fun _ hq => hq.elim Or.inl fun h => Or.inr (Or.inl h)) _,
   onlyVia_antitone
      (fun _ hq => hq.elim Or.inl fun h => Or.inr (Or.inr h)) _⟩

/-! ## Data linkage

The `marking` function is pinned to the `paperFeatures` of every focus
row in `Data.Examples.HartmannZimmermann2004`. -/

private def strategyLabel : Strategy → String
  | .postposing => "postposing"
  | .suffixI    => "suffixI"
  | .boundary   => "boundary"
  | .unmarked   => "unmarked"

private def focusedLabel : Focused → String
  | .subject => "subject"
  | .verb    => "verb"
  | .vp      => "vp"
  | .object  => "object"

private def aspectLabel : Aspect → String
  | .perfective  => "perfective"
  | .progressive => "progressive"

private def configRows :
    List (Config × Data.Examples.LinguisticExample) :=
  [(⟨.subject, .perfective, false⟩, Examples.ex17b),
   (⟨.vp, .perfective, false⟩, Examples.ex24b),
   (⟨.object, .perfective, true⟩, Examples.ex25a),
   (⟨.vp, .perfective, true⟩, Examples.ex25b),
   (⟨.verb, .perfective, true⟩, Examples.ex25c),
   (⟨.object, .progressive, true⟩, Examples.ex32a),
   (⟨.vp, .progressive, true⟩, Examples.ex32b),
   (⟨.verb, .progressive, true⟩, Examples.ex32c)]

/-- Every focus row's strategy is the `marking` of its configuration:
the conditioning function is derived from the data, not stipulated
beside it. -/
theorem marking_matches_rows :
    ∀ p ∈ configRows,
      p.2.feature? "strategy" = some (strategyLabel (marking p.1)) ∧
      p.2.feature? "focused" = some (focusedLabel p.1.focused) ∧
      p.2.feature? "aspect" = some (aspectLabel p.1.aspect) := by decide

end HartmannZimmermann2004
