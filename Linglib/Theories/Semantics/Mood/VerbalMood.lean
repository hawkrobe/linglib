import Linglib.Core.Mood.POSW
import Linglib.Core.Mood.POSWQ
import Linglib.Theories.Semantics.Mood.Basic

/-!
# Verbal Mood as POSWQ Component Selection
@cite{portner-2018}

Verbal mood — the indicative/subjunctive/interrogative contrast
visible in the complement clauses of attitude verbs (Romance, Greek,
Balkan, …) — reduces to *which component of the embedding attitude's
POSWQ* the mood operator quantifies over.

@cite{portner-2018} (Ch. 2–3) identifies three intuitions about what
distinguishes complement-clause mood:

- **Truth intuition** (Farkas 1985, Portner 1997 tradition):
  indicative is selected for clauses true throughout a designated
  modal base. Subjunctive is selected when this universal-truth
  pattern fails.
- **Comparison intuition** (Giorgi & Pianesi 1997 tradition):
  subjunctive is selected when the embedding predicate involves
  ordering or comparison among alternatives — preference, doxastic
  ranking, intention.
- **Inquisitive intuition** (@cite{groenendijk-stokhof-1984},
  @cite{roberts-2012} on QUD): question-embedding predicates select
  for clauses *settled by the open question* — clauses with constant
  truth value within each cell of the inquiry partition.

@cite{portner-2018}'s unification: *all three intuitions are correct*
because they target three different POSWQ components. The
**information component** (`cs`) underwrites Truth-style universal
quantification (`POSW.boxCs`); the **preference component** (`lt`)
underwrites Comparison-style quantification over the best-ranked
subset (`POSW.boxLt`); the **inquiry component** (`Setoid W`)
underwrites Inquisitive-style answerhood (`POSWQ.boxAns`). Verbal
mood selectors choose which component the embedded clause is
evaluated against.

This file formalizes that selection as the `interp` function on a
three-element `VerbalMoodOp`, with signature `POSWQ W → (W → Prop)
→ Prop`. The split is *type-driven*: `boxCs`, `boxLt`, and `boxAns`
operate on the same POSWQ and the same proposition; only which
component they consult differs.

## Connection to sentence mood (Portner's full unification)

The sentence-mood / discourse-update side of the same unification
lives in `Core/Discourse/Scoreboard.lean`:

| layer            | declarative                  | imperative                    | interrogative              |
|------------------|------------------------------|-------------------------------|----------------------------|
| sentence mood    | assertion (`+`-update on cs) | direction (`⋆`-update on lt)  | interrogation (`?` on inq) |
| modal necessity  | `boxCs` (informational)      | `boxLt` (preferential)        | `boxAns` (answerhood)      |
| verbal mood      | `interp .indicative`         | `interp .subjunctive`         | `interp .interrogative`    |

The shared substrate is `POSWQ`. Verbal mood is the *modal* row read
as a complementizer-domain selector triggered by lexical class of
the matrix predicate (`MoodSelector` for declarative-embedders;
question-embedding predicates form a separate dimension reachable by
direct construction of `.interrogative`).
-/

namespace Semantics.Mood

open Core.Mood

universe u
variable {W : Type u}

/-- The three principal verbal-mood operators in the
    @cite{portner-2018} POSWQ analysis. The `crossLinguistic` and
    `neutral` cases of `MoodSelector` (Mood/Basic.lean) project to
    `none` via `MoodSelector.toVerbalMood` because their selection
    pattern is not committed to a single POSWQ component by lexical
    class alone. -/
inductive VerbalMoodOp where
  /-- Indicative: universal quantification over the *informational*
      component of the embedding POSWQ. The Truth intuition. -/
  | indicative
  /-- Subjunctive: universal quantification over the *preferential*
      component (best-ranked subset). The Comparison intuition. -/
  | subjunctive
  /-- Interrogative: answerhood with respect to the *inquiry*
      component (constant truth value per cell). The Inquisitive
      intuition. Selected by question-embedding predicates
      (`wonder`, `ask`, `investigate`). -/
  | interrogative
  deriving DecidableEq, Repr

/-- Compositional interpretation of a verbal-mood operator against
    an embedding POSWQ and an embedded proposition. The three cases
    consult disjoint POSWQ components:
    `.indicative ↦ POSW.boxCs`,
    `.subjunctive ↦ POSW.boxLt`,
    `.interrogative ↦ POSWQ.boxAns`. -/
def VerbalMoodOp.interp : VerbalMoodOp → POSWQ W → (W → Prop) → Prop
  | .indicative,    c, p => c.toPOSW.boxCs p
  | .subjunctive,   c, p => c.toPOSW.boxLt p
  | .interrogative, c, p => c.boxAns p

/-! ## §1. Definitional equalities -/

@[simp] theorem interp_indicative (c : POSWQ W) (p : W → Prop) :
    VerbalMoodOp.indicative.interp c p = c.toPOSW.boxCs p := rfl

@[simp] theorem interp_subjunctive (c : POSWQ W) (p : W → Prop) :
    VerbalMoodOp.subjunctive.interp c p = c.toPOSW.boxLt p := rfl

@[simp] theorem interp_interrogative (c : POSWQ W) (p : W → Prop) :
    VerbalMoodOp.interrogative.interp c p = c.boxAns p := rfl

/-! ## §2. Operator-specific monotonicity

`boxCs` and `boxLt` are upward-monotone in the embedded proposition:
strengthening the modal base preserves universal truth there.
`boxAns` is *not* upward-monotone — a strengthening of `p` can break
the constant-truth-per-cell property. The natural monotonicity for
`boxAns` is *anti*-monotone in the inquiry partition (covered by
`POSWQ.boxAns_anti`).

This asymmetry is itself a content claim of @cite{portner-2018}'s
unification: the three operators have *different* natural ordering
behaviors precisely because they consult different POSWQ components,
which carry different lattice structures. -/

theorem interp_indicative_mono (c : POSWQ W) (p q : W → Prop)
    (h : ∀ w, p w → q w) :
    VerbalMoodOp.indicative.interp c p → VerbalMoodOp.indicative.interp c q :=
  POSW.boxCs_mono c.toPOSW p q h

theorem interp_subjunctive_mono (c : POSWQ W) (p q : W → Prop)
    (h : ∀ w, p w → q w) :
    VerbalMoodOp.subjunctive.interp c p → VerbalMoodOp.subjunctive.interp c q :=
  POSW.boxLt_mono c.toPOSW p q h

/-! ## §3. Distinctness witnesses

The three mood operators are pairwise non-equivalent — each consults
a disjoint POSWQ component. We exhibit concrete witnesses showing
that no operator can be defined in terms of the others on the POSWQ
substrate alone. -/

/-- Separation POSW: `cs = ⊤` over `Bool`, with `lt w v = (w = false →
    v = false)`. Under this ordering `false` is the unique element
    `w` such that every `v` satisfies `lt v w`, so `false` is the
    unique world picked out by `POSW.best`. -/
def sepPOSW : POSW Bool where
  cs := fun _ => True
  lt := fun w v => w = false → v = false
  lt_refl  := fun _ _ h => h
  lt_trans := fun _ _ _ _ _ _ hwu huv hw => huv (hwu hw)

/-- Lift of `sepPOSW` to a POSWQ with trivial inquiry. Used to
    distinguish indicative from subjunctive without engaging the
    inquiry component. -/
def sepPOSWQ_triv : POSWQ Bool := POSWQ.ofPOSW sepPOSW

/-- Separation proposition: only `false` satisfies it. -/
def sepProp : Bool → Prop := fun w => w = false

/-- The subjunctive operator accepts `(sepPOSWQ_triv, sepProp)`. -/
theorem subjunctive_accepts_separation :
    VerbalMoodOp.subjunctive.interp sepPOSWQ_triv sepProp := by
  intro w hbest
  exact (hbest.2 false trivial) rfl

/-- The indicative operator rejects `(sepPOSWQ_triv, sepProp)`. -/
theorem indicative_rejects_separation :
    ¬ VerbalMoodOp.indicative.interp sepPOSWQ_triv sepProp := by
  intro h
  exact Bool.noConfusion (h true trivial)

/-- **Indicative ≠ subjunctive**. The two mood operators are
    distinguishable: there exists a POSWQ and a proposition on which
    they disagree. The Truth/Comparison split is genuine, not a
    notational variant. -/
theorem indicative_ne_subjunctive :
    ∃ (c : POSWQ Bool) (p : Bool → Prop),
      VerbalMoodOp.subjunctive.interp c p ∧
      ¬ VerbalMoodOp.indicative.interp c p :=
  ⟨sepPOSWQ_triv, sepProp,
    subjunctive_accepts_separation, indicative_rejects_separation⟩

/-- **Interrogative ≠ indicative**. Reuses the witness from
    `POSWQ.boxAns_not_reducible_to_boxCs`: a POSWQ where the inquiry
    component partitions worlds finely enough that some `p` has
    constant truth value per cell (so `boxAns p`) yet fails to be
    universally true on `cs` (so not `boxCs p`). -/
theorem interrogative_ne_indicative :
    ∃ (c : POSWQ Bool) (p : Bool → Prop),
      VerbalMoodOp.interrogative.interp c p ∧
      ¬ VerbalMoodOp.indicative.interp c p :=
  POSWQ.boxAns_not_reducible_to_boxCs

/-! ## §4. Bridge to `MoodSelector`

The `MoodSelector` enum (Mood/Basic.lean, taxonomic by predicate
class — knowledge/belief, preference/desire, etc.) projects onto
`VerbalMoodOp` for the predicate classes that select the *same*
mood across @cite{portner-2018}'s indicative/subjunctive languages.
Cross-linguistically variable selectors and mood-neutral predicates
project to `none` — they are not committed to either quantification
scheme by lexical-class membership alone.

Question-embedding predicates (`wonder`, `ask`, `investigate`) are a
*different* lexical dimension — they're question-embedders, not
mood-selectors-on-declarative-complements — and so are not in
`MoodSelector`'s scope. The `.interrogative` operator is reachable
by direct construction; a future predicate-class enum specific to
question-embedders can project into it. -/

/-- Project a `MoodSelector` to its `VerbalMoodOp`, when the lexical
    class is committed to a single mood cross-linguistically.
    `MoodSelector` covers declarative-complement-taking predicates;
    question-embedders project to `.interrogative` via a separate
    dimension. -/
def MoodSelector.toVerbalMood : MoodSelector → Option VerbalMoodOp
  | .indicativeSelecting          => some .indicative
  | .subjunctiveSelecting         => some .subjunctive
  | .crossLinguisticallyVariable  => none
  | .moodNeutral                  => none

/-- The `prefersSubjunctive` boolean (Mood/Basic.lean) and the
    `toVerbalMood` projection agree on whether the result is the
    subjunctive operator. Two surface representations of the same
    lexical-class commitment, equivalent by construction. -/
theorem prefersSubjunctive_eq_subjunctive (m : MoodSelector) :
    prefersSubjunctive m = true ↔ m.toVerbalMood = some .subjunctive := by
  cases m <;> simp [prefersSubjunctive, MoodSelector.toVerbalMood]

/-- `MoodSelector.toVerbalMood` never projects to `.interrogative`:
    the declarative-complement classification is *closed* under the
    indicative/subjunctive split. Question-embedding lives elsewhere. -/
theorem toVerbalMood_ne_interrogative (m : MoodSelector) :
    m.toVerbalMood ≠ some .interrogative := by
  cases m <;> simp [MoodSelector.toVerbalMood]

end Semantics.Mood
