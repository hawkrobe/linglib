import Linglib.Semantics.Quotation.Demonstration
import Linglib.Discourse.Commitment.Table

/-!
# Farkas-Bruce Performance Ontology Bridge
[rudin-2025b] [farkas-bruce-2010]

Provides a `PerformanceOntology` instance whose `Commits` and
`RaisesIssue` are *derived* from Farkas-Bruce discourse-state updates,
rather than stipulated as primitive properties.

## The Bridge

A *performance* in F&B terms is a discourse-state update determined by
its sentence form (declarative/interrogative), its propositional
content, and its prosodic profile (rising or not, loud/whispered/
neutral). The `FBPerformance` record bundles exactly the data needed
to compute its discourse effect:

- a non-rising declarative `assert`s its content (adds to dcS, pushes
  issue)
- an interrogative `polarQuestion`s its content (pushes issue, no
  dcS commit)
- a rising declarative pushes its content as an issue (no dcS commit) —
  the intermediate prosodic case that drives [rudin-2025b]'s
  empirical engine

`Commits` and `RaisesIssue` are then F&B-grounded predicates: a
performance `Commits` iff its update adds its content to dcS; it
`RaisesIssue` iff its update grows the table. Verb-class meaning
postulates in `SpeechVerbs` see the same Commits / RaisesIssue that
the F&B bridge theorems (in `Discourse/Commitment/Table.lean`)
reason about — the connection is true by construction, not provable
as an equivalence.

## Why this matters

Without the bridge, `Commits` is an axiomatic property of performances
in `PerformanceOntology` — we'd have to *say* that rising declaratives
don't commit. With the bridge, the F&B update semantics *makes them
not commit* (the update doesn't touch dcS), and the Demonstration
postulates inherit that fact directly.

## Anti-correspondences

A `FBPerformance` whose `lingmat` field is `false` and `rising` is
`false` represents a non-linguistic performance (e.g., karate
gestures). We choose `LingMat` to disjoin `lingmat = true ∨ rising =
true` so that every rising-declarative performance is automatically
linguistic material — a structural rather than axiomatic fact.

The `Volume` enumeration (`neutral`, `loud`, `whispered`) makes
`loud_not_whispered` true by construction: a single field cannot
simultaneously be both values.
-/

namespace Dialogue.QuotationFBOntology

open Discourse.Commitment.Table
open Semantics.Mood (IllocutionaryMood)
open Semantics.Quotation.Demonstration

-- ════════════════════════════════════════════════════
-- § 1. FBPerformance: the data of an F&B utterance
-- ════════════════════════════════════════════════════

/-- Volume profile of a performance. The 3-way enumeration ensures that
    `Loud` and `Whispered` are mutually exclusive by construction. -/
inductive Volume where
  | neutral
  | loud
  | whispered
  deriving DecidableEq, Repr, Inhabited

/-- A Farkas-Bruce performance: minimal data to compute its discourse
    update. -/
structure FBPerformance (W : Type*) where
  /-- Sentence form (declarative / interrogative). -/
  form : IllocutionaryMood
  /-- Propositional content. -/
  content : Set W
  /-- Whether the performance is linguistic material. False allows
      modeling non-linguistic gestures (the karate-gestures contrast
      that motivates `LINGMAT`). -/
  lingmat : Bool := true
  /-- Volume profile. -/
  volume : Volume := .neutral
  /-- Rising-declarative intonation (only meaningful with declarative
      form, but field is independent for simplicity). -/
  rising : Bool := false

namespace FBPerformance

variable {W : Type*}

-- ════════════════════════════════════════════════════
-- § 2. F&B Update semantics
-- ════════════════════════════════════════════════════

/-- The F&B-grounded discourse update for the performance.

    - **non-rising declarative**: `assert` (commits + pushes issue)
    - **interrogative**: `polarQuestion` (pushes issue, no commit)
    - **rising declarative**: pushes issue without commit
      (the intermediate prosodic case [rudin-2025b] relies on) -/
def update (u : FBPerformance W) (s : State W) : State W :=
  match u.rising, u.form with
  | true, _ =>
      s.pushItem ⟨.speaker, .addressee, .declarative, [u.content]⟩
  | false, .declarative => assert s u.content
  | false, _ => polarQuestion s u.content

-- ════════════════════════════════════════════════════
-- § 3. Performance properties (F&B-derived where possible)
-- ════════════════════════════════════════════════════

/-- Linguistic-material. Disjoins explicit `lingmat = true` with
    `rising = true`: a rising-declarative performance is linguistic
    material by virtue of being a structured intonation pattern. -/
def LingMat (u : FBPerformance W) : Prop :=
  u.lingmat = true ∨ u.rising = true

/-- Loud: structural property of `Volume`. -/
def Loud (u : FBPerformance W) : Prop := u.volume = .loud

/-- Whispered: structural property of `Volume`. -/
def Whispered (u : FBPerformance W) : Prop := u.volume = .whispered

/-- Rising declarative: rising intonation on declarative form. -/
def RisingDecl (u : FBPerformance W) : Prop :=
  u.rising = true ∧ u.form = .declarative

/-- **F&B-derived** Commits: the performance's update adds its content
    to dcS (computed from the empty initial state). The `assert`
    branch adds, the rising and interrogative branches do not — so this
    matches the structural classification "non-rising declarative". -/
def Commits (u : FBPerformance W) : Prop :=
  u.content ∈ (u.update (DiscourseState.empty : State W)).dcS

/-- **F&B-derived** RaisesIssue: the performance's update grows the
    table. All three branches push to the table, so any well-formed
    speech act raises an issue. (RESP's discriminating power comes
    from `¬ Commits`, not from `RaisesIssue`.) -/
def RaisesIssue (u : FBPerformance W) : Prop :=
  (u.update (DiscourseState.empty : State W)).table ≠ []

-- ════════════════════════════════════════════════════
-- § 4. PerformanceOntology axiom obligations
-- ════════════════════════════════════════════════════

theorem loud_not_whispered (u : FBPerformance W) :
    Loud u → ¬ Whispered u := by
  intro hl hw
  unfold Loud at hl
  unfold Whispered at hw
  rw [hl] at hw
  cases hw

theorem rd_not_commits (u : FBPerformance W) :
    RisingDecl u → ¬ Commits u := by
  rintro ⟨hr, _⟩
  -- After update with rising=true, dcS = empty.dcS = []
  simp [Commits, update, hr]
  exact List.not_mem_nil

theorem rd_raises_issue (u : FBPerformance W) :
    RisingDecl u → RaisesIssue u := by
  rintro ⟨hr, _⟩
  unfold RaisesIssue update
  rw [hr]
  simp

theorem rd_is_lingmat (u : FBPerformance W) :
    RisingDecl u → LingMat u := by
  rintro ⟨hr, _⟩
  exact Or.inr hr

-- ════════════════════════════════════════════════════
-- § 5. The `PerformanceOntology` instance
-- ════════════════════════════════════════════════════

end FBPerformance

/-- The Farkas-Bruce-grounded performance ontology. Plug into a
    `SpeechVerbs` to get verb-class semantics whose Commits /
    RaisesIssue facts come from the F&B discourse-state machinery
    rather than free axioms. -/
def fbOntology (W : Type*) : PerformanceOntology (FBPerformance W) where
  LINGMAT := FBPerformance.LingMat
  Loud := FBPerformance.Loud
  Whispered := FBPerformance.Whispered
  RisingDecl := FBPerformance.RisingDecl
  Commits := FBPerformance.Commits
  RaisesIssue := FBPerformance.RaisesIssue
  loud_not_whispered := FBPerformance.loud_not_whispered
  rd_not_commits := FBPerformance.rd_not_commits
  rd_raises_issue := FBPerformance.rd_raises_issue
  rd_is_lingmat := FBPerformance.rd_is_lingmat

-- ════════════════════════════════════════════════════
-- § 6. F&B grounding theorems
-- ════════════════════════════════════════════════════

namespace FBPerformance

variable {W : Type*}

/-- Structural characterization of `Commits`: a performance commits
    iff it is a non-rising declarative. Derives directly from the F&B
    update semantics. -/
theorem commits_iff (u : FBPerformance W) :
    u.Commits ↔ u.rising = false ∧ u.form = .declarative := by
  cases hr : u.rising <;> cases hf : u.form <;>
    simp [Commits, update, hr, hf] <;>
    first | exact List.not_mem_nil | exact List.mem_cons_self

/-- Structural characterization of `RaisesIssue`: every performance
    raises an issue (declarative or interrogative; rising or non-rising).
    The discriminating empirical content lives in `Commits`, not here. -/
theorem raises_issue_always (u : FBPerformance W) : u.RaisesIssue := by
  unfold RaisesIssue update
  cases u.rising <;> cases u.form <;> simp [polarQuestion]

/-- Bridge: when the performance is a non-rising declarative, its update
    equals `assert s content`, so `assert_dc_speaker_doxasticContents`
    applies directly. -/
theorem update_decl_eq_assert (u : FBPerformance W)
    (hr : u.rising = false) (hf : u.form = .declarative)
    (s : State W) :
    u.update s = assert s u.content := by
  unfold update
  rw [hr, hf]

end FBPerformance

end Dialogue.QuotationFBOntology
