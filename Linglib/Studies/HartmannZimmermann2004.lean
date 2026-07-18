/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Tactic.FinCases
import Linglib.Core.Logic.FactorsThroughOn
import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Phonology.Prosody.Phrase
import Linglib.Semantics.Focus.Control
import Linglib.Morphology.Reflex
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
structural. The boundary itself is derived: [truckenbrodt-1999]-style
focus alignment dominating phrasal economy places the φ-edge exactly
in the focused cells, and [kidda-1985]'s elision cascade makes it
audible.

## Implementation notes

Realisation uses the shared `Morphology.Marking` vocabulary
(reflex lists; the paper's strategy labels are read off the reflex
shape in the data linkage). Configurations carry the fragment's
tense–aspect type directly (`Tangale.TAM`): the perfective rows are
[kidda-1985]'s singular perfective and the paper's progressive is the
fragment's continuous (preposed *né*, transcribed *n* by the paper),
with the paradigm restriction in `Config.WF`; `marking_matches_rows`
pins the identification to the data rows. The *núm* readings use the strong-theory
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

open Semantics.Focus Morphology Morphology
open Constraints (Constraint)
open OptimalityTheory (Tableau)

/-! ## The marking system (§4.1, §5.2, §6.2) -/

/-- The focused constituent in the paper's paradigm. -/
inductive Focused where
  | subject | verb | vp | object
  deriving DecidableEq, Repr

/-- A focus configuration of the paper's paradigm. -/
structure Config where
  /-- The focused constituent. -/
  focused : Focused
  /-- The tense–aspect frame, from [kidda-1985]'s inventory. -/
  tam : Tangale.TAM
  /-- Whether the predicate is transitive. -/
  transitive : Bool
  deriving DecidableEq, Repr

/-- The paper's paradigm: object focus needs a transitive predicate,
and only the perfective and continuous (the paper's progressive)
frames are documented. -/
def Config.WF (c : Config) : Prop :=
  (c.focused = .object → c.transitive) ∧
  (c.tam = .perfective ∨ c.tam = .continuous)

instance (c : Config) : Decidable c.WF :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The overt reflexes: subjects surface displaced ((17b));
intransitive predicate focus bears *-i* ((24b)); transitive perfective
foci get the boundary after the verb ((25a–c)); progressive foci
receive nothing ((31)/(32a–c)). Untested frames fall to the unmarked
default, guarded by `Config.WF`. -/
def realize : Config → Marking Focused
  | ⟨.subject, _, _⟩        => ⟨.subject, [.displacement .subject]⟩
  | ⟨f, .perfective, false⟩ => ⟨f, [.morpheme f]⟩
  | ⟨f, .perfective, true⟩  => ⟨f, [.boundary .verb]⟩
  | ⟨f, _, _⟩               => ⟨f, []⟩

/-- Focused subjects are overtly marked in every aspect — the paper's
§6 subjects-vs-non-subjects generalization, shared with Hausa. -/
theorem subject_always_marked :
    ∀ c : Config, c.focused = .subject → (realize c).IsOvert
  | ⟨_, _, _⟩, rfl => List.cons_ne_nil _ _

/-- Progressive non-subject foci are wholly unmarked ((31)/(32a–c),
contra Kidda 1993). -/
theorem progressive_nonsubject_unmarked (c : Config)
    (hs : c.focused ≠ .subject) (ha : c.tam = .continuous) :
    (realize c).reflexes = [] := by
  obtain ⟨f, a, t⟩ := c
  cases ha
  cases f <;> first | exact absurd rfl hs | rfl

/-- Focus marking is not obligatory: a well-formed focus configuration
with no overt reflex — (32a), object focus in the progressive. -/
theorem focus_marking_not_obligatory :
    ∃ c : Config, c.WF ∧ ¬ (realize c).IsOvert :=
  ⟨⟨.object, .continuous, true⟩, ⟨fun _ => rfl, Or.inr rfl⟩, fun h => h rfl⟩

/-- Tangale refutes the universalist claim that every focus receives an
overt reflex — the Tangale side of the counterexample the Hausa
chapter states against the Basic Focus Rule. -/
theorem tangale_refutes_perceptibility :
    ¬ EveryTargetOvert realize :=
  fun h => h ⟨.object, .continuous, true⟩ rfl

/-- The boundary underdetermines the focus extent: on the transitive
perfective non-subject cells, `focused` does not factor through the
reflexes — (25a–c) are string- and pitch-identical. -/
theorem boundary_underdetermines_extent :
    ¬ Function.FactorsThroughOn Config.focused (fun c => (realize c).reflexes)
        {c | c.tam = .perfective ∧ c.transitive ∧ c.focused ≠ .subject} :=
  Function.not_factorsThroughOn_iff_exists_witness.mpr
    ⟨⟨.verb, .perfective, true⟩, ⟨.object, .perfective, true⟩,
      ⟨rfl, rfl, nofun⟩, ⟨rfl, rfl, nofun⟩, rfl, nofun⟩

/-! ## Deriving the boundary ([truckenbrodt-1999]-style alignment)

The perfective boundary is not primitive. Candidate parses wrap the
V–O string into one φ or separate the object into its own φ; a
focus-alignment constraint (the focus's left edge coincides with a
φ-edge) dominates phrasal economy exactly when the object is focused.
The winning parse's φ-edge is the `Reflex.boundary` of `realize`, and
its audibility is the blocked elision cascade
(`prosodic_reflex_audible`). -/

/-- A minimal prosodic word. -/
private def ω : Prosody.Tree := .node .om [.node .syl []]

/-- V and O wrapped into one φ. -/
private def wrapped : Prosody.Tree := .node .iota [.node .ph [ω, ω]]

/-- O separated into its own φ. -/
private def separated : Prosody.Tree :=
  .node .iota [.node .ph [ω], .node .ph [ω]]

/-- ALIGN-Focus: violated when no φ-edge sits at the focus's left edge
(leaf offset 1, the object). -/
private def alignFocus : Constraint Prosody.Tree :=
  .binary (fun t => ¬ ∃ s ∈ RoseTree.spansOf Prosody.Constituent.isPh t, s.1 = 1)

/-- Phrasal economy: one violation per φ. -/
private def starPhi : Constraint Prosody.Tree :=
  fun t => (RoseTree.spansOf Prosody.Constituent.isPh t).length

/-- Object focus: alignment dominates economy, and the separated parse
wins — the derived φ-edge after the verb. -/
theorem focused_parse_separates :
    (Tableau.ofRanking [wrapped, separated] [alignFocus, starPhi]).optimal
      = {separated} := by decide

/-- All-new: economy decides alone and the wrapped parse wins — no
boundary, the elision cascade applies. -/
theorem neutral_parse_wraps :
    (Tableau.ofRanking [wrapped, separated] [starPhi]).optimal
      = {wrapped} := by decide

/-- No φ spans the V–O juncture in the separated parse — elision is
blocked there and applies in the wrapped one. -/
theorem separated_edge_wrapped_internal :
    (0, 2) ∉ RoseTree.spansOf Prosody.Constituent.isPh separated ∧
    (0, 2) ∈ RoseTree.spansOf Prosody.Constituent.isPh wrapped := by decide

/-- The prosodic reflex is audible: the boundary-blocked perfective
form differs from the phrase-medial elided form — [kidda-1985]'s
elision cascade is what makes `Reflex.boundary` perceptible in the
(25) cells. -/
theorem prosodic_reflex_audible :
    Tangale.blockedForm ≠ Tangale.elidedForm :=
  Tangale.boundary_audible.1

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

/-- 'I bought the book.' -/
def boughtBookP : Set NumWorld := {w | w.boughtBook}
/-- 'I bought the shirt.' -/
def boughtShirtP : Set NumWorld := {w | w.boughtShirt}
/-- 'I read the book.' -/
def readBookP : Set NumWorld := {w | w.readBook}

/-- The alternative facts, as an indexed family. -/
def alt : Fin 3 → Set NumWorld := ![boughtBookP, boughtShirtP, readBookP]

/-- The alternatives are irredundant: each can hold while the others
fail — one world per free Boolean field. -/
theorem alt_irredundant : Irredundant alt := by
  intro i
  fin_cases i
  · exact ⟨⟨true, false, false⟩, rfl, fun j hj => by
      fin_cases j <;> first | exact absurd rfl hj | exact Bool.false_ne_true⟩
  · exact ⟨⟨false, true, false⟩, rfl, fun j hj => by
      fin_cases j <;> first | exact absurd rfl hj | exact Bool.false_ne_true⟩
  · exact ⟨⟨false, false, true⟩, rfl, fun j hj => by
      fin_cases j <;> first | exact absurd rfl hj | exact Bool.false_ne_true⟩

/-- The contrast sets by association extent: object ((36a),
alternatives to the book), VP ((36b), 'I did nothing else'), verb
((36c), 'but I have not read it yet'). Subjects are outside the (36)
paradigm; the arm shares the verb value and is never queried. -/
def extAlts : Focused → Finset (Fin 3)
  | .object => {0, 1}
  | .vp     => {0, 1, 2}
  | _       => {0, 2}

/-- The (36) readings: strong-theory *only* over the resolved contrast
set, with 'bought the book' as prejacent. -/
def numReading (x : Focused) : Set NumWorld :=
  onlyVia (alt '' ↑(extAlts x)) (alt 0)

/-- One surface string, three semantically distinct readings: over a
irredundant alternative family, *only* is injective in its
resolution (`Irredundant.onlyVia_injOn`), and the three extents
resolve to three different contrast sets. -/
theorem num_readings_injOn : Set.InjOn numReading {.verb, .vp, .object} :=
  (alt_irredundant.onlyVia_injOn 0).comp
    (by rintro a (rfl | rfl | rfl) b (rfl | rfl | rfl) h <;>
      first | rfl | exact absurd h (by decide))
    (by rintro a (rfl | rfl | rfl) <;> decide)

/-- The VP association is the strongest reading: 'I did nothing else'
entails both 'I bought nothing else' and 'I did nothing else to the
book' — `onlyVia_antitone` over the contrast-set inclusions. -/
theorem vp_reading_strongest :
    numReading .vp ⊆ numReading .object ∧ numReading .vp ⊆ numReading .verb :=
  ⟨onlyVia_antitone (Set.image_mono (Finset.coe_subset.mpr (by decide))) _,
   onlyVia_antitone (Set.image_mono (Finset.coe_subset.mpr (by decide))) _⟩

/-! ## Data linkage

`realize` is pinned to the `paperFeatures` of every focus row in
`Data.Examples.HartmannZimmermann2004`; the paper's strategy label is
read off the reflex shape. -/

private def strategyLabel (c : Config) : String :=
  match (realize c).reflexes with
  | [.displacement _] => "postposing"
  | [.morpheme _]     => "suffixI"
  | [.boundary _]     => "boundary"
  | _                 => "unmarked"

private def focusedLabel : Focused → String
  | .subject => "subject"
  | .verb    => "verb"
  | .vp      => "vp"
  | .object  => "object"

private def aspectLabel : Tangale.TAM → String
  | .perfective => "perfective"
  | .continuous => "progressive"
  | _           => ""

/-- The paradigm cells paired with their data rows. -/
private def configRows :
    List (Config × Data.Examples.LinguisticExample) :=
  [(⟨.subject, .perfective, false⟩, Examples.ex17b),
   (⟨.vp, .perfective, false⟩, Examples.ex24b),
   (⟨.object, .perfective, true⟩, Examples.ex25a),
   (⟨.vp, .perfective, true⟩, Examples.ex25b),
   (⟨.verb, .perfective, true⟩, Examples.ex25c),
   (⟨.object, .continuous, true⟩, Examples.ex32a),
   (⟨.vp, .continuous, true⟩, Examples.ex32b),
   (⟨.verb, .continuous, true⟩, Examples.ex32c)]

/-- Every focus row's strategy label is read off `realize`'s reflexes:
the conditioning function is derived from the data, not stipulated
beside it. -/
theorem marking_matches_rows :
    ∀ p ∈ configRows,
      p.2.feature? "strategy" = some (strategyLabel p.1) ∧
      p.2.feature? "focused" = some (focusedLabel p.1.focused) ∧
      p.2.feature? "aspect" = some (aspectLabel p.1.tam) := by decide

end HartmannZimmermann2004
