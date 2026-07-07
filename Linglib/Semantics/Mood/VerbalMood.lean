import Linglib.Semantics.Mood.POSW
import Linglib.Semantics.Mood.POSWQ
import Linglib.Semantics.Mood.POSWTarget
import Linglib.Semantics.Mood.Basic

/-!
# Verbal Mood as POSWQ Component Selection
[portner-2018] [groenendijk-stokhof-1984]

Verbal mood — the indicative/subjunctive contrast visible in the
complement clauses of attitude verbs (Romance, Greek, Balkan, …) —
reduces, on [portner-2018]'s account, to *which component of the
embedding attitude's POSW* the mood operator quantifies over. We
extend that account to a third operator targeting the inquiry
component for question-embedding predicates.

[portner-2018] (Ch. 2) identifies two main intuitions about what
distinguishes indicative from subjunctive complementation:

- **Truth intuition** ([farkas-1985], [portner-1997] tradition):
  indicative is selected for clauses true throughout a designated
  modal base. Subjunctive is selected when this universal-truth
  pattern fails.
- **Comparison intuition** ([giorgi-pianesi-1997] tradition):
  subjunctive is selected when the embedding predicate involves
  ordering or comparison among alternatives — preference, doxastic
  ranking, intention.

[portner-2018]'s unification of these two: *both intuitions are
correct* because they target two different POSW components. The
**information component** (`cs`) underwrites Truth-style universal
quantification (`POSW.boxCs`); the **preference component** (`le`)
underwrites Comparison-style quantification over the best-ranked
subset (`POSW.boxLe`).

We add a third operator `.interrogative` for question-embedding
predicates (`wonder`, `ask`, `investigate`), which select for clauses
*settled by the open question* — clauses with constant truth value
within each cell of the inquiry partition (`POSWQ.boxAns`,
[groenendijk-stokhof-1984] answerhood). Question embedding is
not part of [portner-2018]'s verbal-mood unification proper,
which is restricted to declarative complementation; we plug it into
the same POSWQ substrate to give all three operators a uniform type.

This file formalizes the selection as the `interp` function on a
three-element `VerbalMoodOp`, with signature `POSWQ W → (W → Prop)
→ Prop`. `interp` is defined as `boxOn ∘ target` — each operator's
`HasPOSWTarget` label selects the component, and the label's modal
projection does the quantifying — so the operator/component
correspondence holds by construction rather than by a bridge
theorem.

## Connection to sentence mood

The sentence-mood / discourse-update side of the same unification
lives in `Studies/Roberts2023.lean`:

| layer            | declarative                  | imperative                    | interrogative              |
|------------------|------------------------------|-------------------------------|----------------------------|
| sentence mood    | assertion (`+`-update on cs) | direction (`⋆`-update on le)  | interrogation (`?` on inq) |
| modal necessity  | `boxCs` (informational)      | `boxLe` (preferential)        | `boxAns` (answerhood)      |
| verbal mood      | `interp .indicative`         | `interp .subjunctive`         | `interp .interrogative`    |

The first two columns are [portner-2018]'s; the third column is
this library's extension (see `Semantics/Mood/POSWQ.lean`). The shared
substrate is `POSWQ`. Verbal mood is the *modal* row read as a
complementizer-domain selector triggered by lexical class of the
matrix predicate (`MoodSelector` for declarative-embedders;
`QuestionEmbedder` for question-embedders).
-/

namespace Semantics.Mood

variable {W : Type*}

/-- The three verbal-mood operators on POSWQ. The `.indicative` and
    `.subjunctive` cases are [portner-2018]'s; `.interrogative`
    is our extension to question-embedding predicates. The
    `crossLinguistic` and `neutral` cases of `MoodSelector`
    (Mood/Basic.lean) project to `none` via
    `MoodSelector.toVerbalMood` because their selection pattern is
    not committed to a single POSWQ component by lexical class
    alone. -/
inductive VerbalMoodOp where
  /-- Indicative: universal quantification over the *informational*
      component of the embedding POSWQ. The Truth intuition. -/
  | indicative
  /-- Subjunctive: universal quantification over the *preferential*
      component (best-ranked subset). The Comparison intuition. -/
  | subjunctive
  /-- Interrogative: answerhood with respect to the *inquiry*
      component (constant truth value per cell), à la
      [groenendijk-stokhof-1984]. Selected by question-embedding
      predicates (`wonder`, `ask`, `investigate`). Our extension —
      not part of [portner-2018]'s verbal-mood unification. -/
  | interrogative
  deriving DecidableEq, Repr

/-- The POSWQ component each verbal-mood operator consults. `target`
    here is selection-side vocabulary: the component the selecting
    predicate's modality quantifies over ([portner-2018], Ch. 2), not
    an operation the mood morpheme performs. Packaged as the same
    `HasPOSWTarget` typeclass that `IllocutionaryMood` instantiates in
    `Semantics/Mood/POSWTarget.lean`. -/
instance : HasPOSWTarget VerbalMoodOp where
  target
    | .indicative    => .informational
    | .subjunctive   => .preferential
    | .interrogative => .partition

@[simp] theorem target_indicative :
    Semantics.Mood.target VerbalMoodOp.indicative = .informational := rfl

@[simp] theorem target_subjunctive :
    Semantics.Mood.target VerbalMoodOp.subjunctive = .preferential := rfl

@[simp] theorem target_interrogative :
    Semantics.Mood.target VerbalMoodOp.interrogative = .partition := rfl

/-- Compositional interpretation of a verbal-mood operator against an
    embedding POSWQ and an embedded proposition: run the necessity
    modal of the operator's POSW target on the embedded proposition.
    Definitionally `boxOn ∘ target`, so the three cases consult
    disjoint POSWQ components:
    `.indicative ↦ POSW.boxCs`,
    `.subjunctive ↦ POSW.boxLe`,
    `.interrogative ↦ POSWQ.boxAns`. -/
def VerbalMoodOp.interp (m : VerbalMoodOp) : POSWQ W → (W → Prop) → Prop :=
  (target m).boxOn

/-- The interpretation is the target component's necessity modal, by
    definition: `target` is not just a typological label. -/
@[simp] theorem interp_eq_target_boxOn (m : VerbalMoodOp) (c : POSWQ W)
    (p : W → Prop) :
    m.interp c p = (Semantics.Mood.target m).boxOn c p := rfl

/-! ### Definitional equalities -/

@[simp] theorem interp_indicative (c : POSWQ W) (p : W → Prop) :
    VerbalMoodOp.indicative.interp c p = c.toPOSW.boxCs p := rfl

@[simp] theorem interp_subjunctive (c : POSWQ W) (p : W → Prop) :
    VerbalMoodOp.subjunctive.interp c p = c.toPOSW.boxLe p := rfl

@[simp] theorem interp_interrogative (c : POSWQ W) (p : W → Prop) :
    VerbalMoodOp.interrogative.interp c p = c.boxAns p := rfl

/-! ### Operator-specific monotonicity

`boxCs` and `boxLe` are upward-monotone in the embedded proposition:
strengthening the modal base preserves universal truth there.
`boxAns` is *not* upward-monotone — a strengthening of `p` can break
the constant-truth-per-cell property. The natural monotonicity for
`boxAns` is *anti*-monotone in the inquiry partition (covered by
`POSWQ.boxAns_anti`).

This asymmetry is itself a content claim of [portner-2018]'s
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
  POSW.boxLe_mono c.toPOSW p q h

/-! ### Distinctness witnesses

The three mood operators are pairwise non-equivalent — each consults
a disjoint POSWQ component. We exhibit concrete witnesses showing
that no operator can be defined in terms of the others on the POSWQ
substrate alone. -/

/-- Separation POSW: `cs = ⊤` over `Bool`, with `le w v = (w = false →
    v = false)`. Under this ordering `false` is the unique element
    `w` such that every `v` satisfies `le v w`, so `false` is the
    unique world picked out by `POSW.best`. -/
def sepPOSW : POSW Bool where
  cs := fun _ => True
  le := fun w v => w = false → v = false
  le_refl  := fun _ _ h => h
  le_trans := fun _ _ _ _ _ _ hwu huv hw => huv (hwu hw)

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

/-! ### Verbal-mood biconditional characterization

`VerbalMoodOp` is in bijection with `POSWTarget`: each operator
*exactly* picks out one POSW component, and conversely each component
is targeted by *exactly* one operator. [portner-2018] states the
corresponding licensing conditions one-way and defeasibly (an
indicative clause's context is relevantly like a root assertion); the
biconditional form below reflects only the bijection between this
three-element operator enum and the three components — at the
verbal-mood layer, mood selection and POSWQ-component selection are
the same thing by construction. -/

theorem verbal_mood_target_informational_iff_indicative (m : VerbalMoodOp) :
    Semantics.Mood.target m = .informational ↔ m = .indicative := by
  cases m <;> decide

theorem verbal_mood_target_preferential_iff_subjunctive (m : VerbalMoodOp) :
    Semantics.Mood.target m = .preferential ↔ m = .subjunctive := by
  cases m <;> decide

theorem verbal_mood_target_partition_iff_interrogative (m : VerbalMoodOp) :
    Semantics.Mood.target m = .partition ↔ m = .interrogative := by
  cases m <;> decide

/-! ### Bridge to `MoodSelector`

The `MoodSelector` enum (Mood/Basic.lean, taxonomic by predicate
class — knowledge/belief, preference/desire, etc.) projects onto
`VerbalMoodOp` for the predicate classes that select the *same*
mood across [portner-2018]'s indicative/subjunctive languages.
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
    indicative/subjunctive split. Question-embedding lives elsewhere
    — see `QuestionEmbedder` below. -/
theorem toVerbalMood_ne_interrogative (m : MoodSelector) :
    m.toVerbalMood ≠ some .interrogative := by
  cases m <;> simp [MoodSelector.toVerbalMood]

/-! ### Bridge to `QuestionEmbedder`

`MoodSelector` covers declarative-complement-taking predicates only;
its `toVerbalMood` projection cannot land in `.interrogative`
(`toVerbalMood_ne_interrogative` above). The dual lexical class —
question-embedding predicates like `wonder`, `ask`, `know-Q`,
`investigate` — gets its own enum here, with the inverse projection
property: every `QuestionEmbedder` projects to `.interrogative`,
never to `.indicative` or `.subjunctive`.

The factive/non-factive split ([karttunen-1977] tradition) is the
standard subdivision of question embedders; we record it for future
expansion (e.g., a finer projection that distinguishes factive-Q
embedders' presupposition profile) without committing to particular
semantic consequences here. -/

/-- Question-embedding predicate class. Disjoint from `MoodSelector`,
    which covers only declarative-complement embedders. The
    factive/non-factive split follows [karttunen-1977]'s typology. -/
inductive QuestionEmbedder where
  /-- Factive question-embedders: `know-Q`, `discover-Q`, `realize-Q`. -/
  | factive
  /-- Non-factive question-embedders: `wonder`, `ask`, `investigate`. -/
  | nonfactive
  deriving DecidableEq, Repr, Inhabited

/-- Every `QuestionEmbedder` projects to the interrogative verbal-mood
    operator. The dual of `MoodSelector.toVerbalMood`: where
    `MoodSelector` ranges over the indicative/subjunctive split,
    `QuestionEmbedder` ranges over the inquiry-component column. -/
def QuestionEmbedder.toVerbalMood : QuestionEmbedder → VerbalMoodOp :=
  fun _ => .interrogative

@[simp] theorem QuestionEmbedder.toVerbalMood_eq (q : QuestionEmbedder) :
    q.toVerbalMood = .interrogative := rfl

/-- `QuestionEmbedder.toVerbalMood` always lands in `.interrogative` —
    the inverse of `toVerbalMood_ne_interrogative` for `MoodSelector`.
    Together these say: the indicative/subjunctive column and the
    interrogative column are reached by *disjoint* lexical-class
    enums, with no overlap and no gap. -/
theorem QuestionEmbedder.toVerbalMood_target (q : QuestionEmbedder) :
    Semantics.Mood.target q.toVerbalMood = .partition := rfl

end Semantics.Mood
