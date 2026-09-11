import Linglib.Data.Examples.HofmeisterSag2010
import Linglib.Processing.Cost.Profile

/-!
# Hofmeister and Sag (2010): Cognitive Constraints and Island Effects

This file formalizes [hofmeister-sag-2010]'s processing account of island effects on the
Pareto profiles of `Processing/Cost/Profile`. The paper's four factors, the length of the
filler–gap dependency (§3.1), the referential load of the material it spans (§3.2), the clause
boundaries it crosses (§3.3) and the complexity of the filler (§3.4), are read off a
`Stimulus`, the filler and the words between it and the gap, by `Stimulus.profile`; the items
of Experiments 1 and 2, (48) and (49), are such stimuli. Pareto dominance then predicts the
paper's contrasts: whatever the dependency, a which-N filler is easier than a bare one
(`which_easier`), a bare-filler island is harder than its non-island baseline, the complex-NP
island of Experiment 1 is harder than its baseline even with the richer filler, and the
which-N wh-island of Experiment 2 is incomparable with its bare baseline
(`whIsland_which_incomparable`), where the experiment found no reading-time difference
after the embedded verb.

## Implementation notes

* Each factor is ordinal: a word's referential load follows the accessibility scale of §3.2,
  pronouns below indefinites below definites and names; a clause boundary's cost follows §3.3,
  a declarative complement below an interrogative one; a filler's ease is its complexity; and
  the dependency's length counts the words it spans. No rating or reading time enters a
  theorem, and the paper's acceptability and reading-time results are prose.
* The NP-type factor of Experiment 1 was weak and local in reading times and not significant
  in acceptability; the profiles predict its direction (`cnpc_definite_harder`), not a size.

## References

* [hofmeister-sag-2010]
* [gibson-1998]
* [lewis-vasishth-2005]
* [deane-1991]
* [sprouse-2007]
-/

namespace HofmeisterSag2010

open ProcessingModel

/-! ### Stimuli and profiles -/

/-- The filler of a dependency: a bare wh-word or a which-N phrase. -/
inductive Filler where
  | bare
  | whichN
  deriving DecidableEq

/-- A word between the filler and the gap, as the four factors see it: a discourse reference
of some accessibility, a clause boundary of some kind, or other material. -/
inductive Word where
  | pronoun
  | indefinite
  | definite
  | name
  | that
  | whether
  | other
  deriving DecidableEq

/-- The referential load of a word (§3.2): a pronoun refers to an old referent, an indefinite
creates one, a definite or a name searches for one. -/
def Word.load : Word → ℕ
  | .indefinite => 1
  | .definite => 2
  | .name => 2
  | _ => 0

/-- The cost of the clause boundary a word opens (§3.3): a declarative complement, or an
interrogative one whose alternatives must be considered as well. -/
def Word.boundary : Word → ℕ
  | .that => 1
  | .whether => 2
  | _ => 0

/-- The retrieval ease a filler affords (§3.4): the richer filler resists interference and
rules out early integration sites. -/
def Filler.ease : Filler → ℕ
  | .bare => 0
  | .whichN => 1

/-- A filler–gap dependency as the factors describe it: its filler and the words it spans. -/
structure Stimulus where
  /-- The filler. -/
  filler : Filler
  /-- The words between the filler and the gap. -/
  span : List Word

/-- The processing profile of a stimulus: the length of the span, the boundaries it crosses,
the references it holds, and the filler's ease. -/
def Stimulus.profile (s : Stimulus) : ProcessingProfile where
  locality := s.span.length
  boundaries := (s.span.map Word.boundary).sum
  referentialLoad := (s.span.map Word.load).sum
  ease := s.filler.ease

instance : HasProcessingProfile Stimulus := ⟨Stimulus.profile⟩

/-- Whatever the span, the which-N filler is easier than the bare one: the profiles agree on
every cost and differ on ease alone. -/
theorem which_easier (span : List Word) :
    (Stimulus.mk .bare span).profile.compare (Stimulus.mk .whichN span).profile = .harder := by
  rw [ProcessingProfile.compare_eq_harder, lt_iff_le_and_ne]
  exact ⟨by simp [ProcessingProfile.le_def, Stimulus.profile, Filler.ease],
    by simp [Stimulus.profile, Filler.ease]⟩

/-! ### Experiment 1: the complex-NP island (48) -/

/-- The island-forming NP of (48): definite, indefinite plural, or indefinite singular. -/
inductive IslandNP where
  | definite
  | plural
  | indefinite
  deriving DecidableEq

/-- The island-forming NP as a word of the span. -/
def IslandNP.word : IslandNP → Word
  | .definite => .definite
  | .plural => .indefinite
  | .indefinite => .indefinite

/-- The complex-NP island of (48): *Emma doubted [the report] that we had captured __*. -/
def cnpc (f : Filler) (np : IslandNP) : Stimulus :=
  ⟨f, [.name, .other, np.word, .that, .pronoun, .other, .other]⟩

/-- The baseline of (48), with the which-N filler: *Emma doubted that we had captured __*. -/
def cnpcBaseline : Stimulus := ⟨.whichN, [.name, .other, .that, .pronoun, .other, .other]⟩

/-- A which-N filler eases the complex-NP island for every island NP (§5.2). -/
theorem cnpc_which_easier (np : IslandNP) :
    (cnpc .bare np).profile.compare (cnpc .whichN np).profile = .harder :=
  which_easier _

/-- Every island condition is harder than the baseline, the which-N ones too: the island adds
a reference and a word to the span (§5.3). -/
theorem cnpc_harder_than_baseline (f : Filler) (np : IslandNP) :
    (cnpc f np).profile.compare cnpcBaseline.profile = .harder := by
  cases f <;> cases np <;> decide

/-- A definite island NP is harder than an indefinite one, the direction of the local reading-
time effects at the complementizer and the verb (§5.2). -/
theorem cnpc_definite_harder (f : Filler) :
    (cnpc f .definite).profile.compare (cnpc f .indefinite).profile = .harder := by
  cases f <;> decide

/-- The plural and singular indefinites carry the same load. -/
theorem cnpc_plural_eq_indefinite (f : Filler) :
    (cnpc f .plural).profile = (cnpc f .indefinite).profile := rfl

/-! ### Experiment 2: the wh-island (49) -/

/-- The wh-island of (49): *did Albert learn whether they dismissed __*. -/
def whIsland (f : Filler) : Stimulus := ⟨f, [.other, .name, .other, .whether, .pronoun, .other]⟩

/-- The baseline of (49), with the bare filler: *did Albert learn that they dismissed __*. -/
def whIslandBaseline : Stimulus := ⟨.bare, [.other, .name, .other, .that, .pronoun, .other]⟩

/-- A which-N filler eases the wh-island (§6.2). -/
theorem whIsland_which_easier :
    (whIsland .bare).profile.compare (whIsland .whichN).profile = .harder :=
  which_easier _

/-- The bare wh-island is harder than its baseline: it crosses an interrogative boundary. -/
theorem whIsland_bare_harder_than_baseline :
    (whIsland .bare).profile.compare whIslandBaseline.profile = .harder := by decide

/-- The which-N wh-island against the bare baseline is a trade-off, the interrogative boundary
against the richer filler, which Pareto dominance leaves undecided: the experiment found the
two read alike after the embedded verb. -/
theorem whIsland_which_incomparable :
    (whIsland .whichN).profile.compare whIslandBaseline.profile = .incomparable := by decide

end HofmeisterSag2010
