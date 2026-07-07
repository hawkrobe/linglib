import Linglib.Semantics.Mood.Modal
import Linglib.Semantics.Mood.State
import Linglib.Semantics.Mood.Component
import Linglib.Semantics.Mood.Basic

/-!
# Verbal Mood as State Component Selection
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
quantification (`ExpState.boxCs`); the **preference component** (`order`)
underwrites Comparison-style quantification over the best-ranked
subset (`ExpState.boxLe`).

We add a third operator `.interrogative` for question-embedding
predicates (`wonder`, `ask`, `investigate`), which select for clauses
*settled by the open question* — clauses with constant truth value
within each cell of the inquiry partition (`State.boxAns`,
[groenendijk-stokhof-1984] answerhood). Question embedding is
not part of [portner-2018]'s verbal-mood unification proper,
which is restricted to declarative complementation; we plug it into
the same State substrate to give all three operators a uniform type.

This file formalizes the selection as the `interp` function on a
three-element `VerbalOp`, with signature `State W → (W → Prop)
→ Prop`. `interp` is defined as `boxOn ∘ target` — each operator's
`HasTarget` label selects the component, and the label's modal
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
this library's extension (see `Semantics/Mood/State.lean`). The shared
substrate is `State`. Verbal mood is the *modal* row read as a
complementizer-domain selector triggered by lexical class of the
matrix predicate (`Selector` for declarative-embedders;
`QuestionEmbedder` for question-embedders).
-/

namespace Semantics.Mood

open Semantics.Dynamic.Default

variable {W : Type*}

/-- The three verbal-mood operators on State. The `.indicative` and
    `.subjunctive` cases are [portner-2018]'s; `.interrogative`
    is our extension to question-embedding predicates. The
    `crossLinguistic` and `neutral` cases of `Selector`
    (Mood/Basic.lean) project to `none` via
    `Selector.toVerbalOp` because their selection pattern is
    not committed to a single State component by lexical class
    alone. -/
inductive VerbalOp where
  /-- Indicative: universal quantification over the *informational*
      component of the embedding State. The Truth intuition. -/
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

/-- The State component each verbal-mood operator consults. `target`
    here is selection-side vocabulary: the component the selecting
    predicate's modality quantifies over ([portner-2018], Ch. 2), not
    an operation the mood morpheme performs. Packaged as the same
    `HasTarget` typeclass that `Illocutionary` instantiates in
    `Semantics/Mood/Component.lean`. -/
instance : HasTarget VerbalOp where
  target
    | .indicative    => .informational
    | .subjunctive   => .preferential
    | .interrogative => .inquisitive

@[simp] theorem target_indicative :
    Semantics.Mood.target VerbalOp.indicative = .informational := rfl

@[simp] theorem target_subjunctive :
    Semantics.Mood.target VerbalOp.subjunctive = .preferential := rfl

@[simp] theorem target_interrogative :
    Semantics.Mood.target VerbalOp.interrogative = .inquisitive := rfl

/-- Compositional interpretation of a verbal-mood operator against an
    embedding State and an embedded proposition: run the necessity
    modal of the operator's POSW target on the embedded proposition.
    Definitionally `boxOn ∘ target`, so the three cases consult
    disjoint State components:
    `.indicative ↦ ExpState.boxCs`,
    `.subjunctive ↦ ExpState.boxLe`,
    `.interrogative ↦ State.boxAns`. -/
def VerbalOp.interp (m : VerbalOp) : State W → (W → Prop) → Prop :=
  (target m).boxOn

/-- The interpretation is the target component's necessity modal, by
    definition: `target` is not just a typological label. -/
@[simp] theorem interp_eq_target_boxOn (m : VerbalOp) (c : State W)
    (p : W → Prop) :
    m.interp c p = (Semantics.Mood.target m).boxOn c p := rfl

/-! ### Definitional equalities -/

@[simp] theorem interp_indicative (c : State W) (p : W → Prop) :
    VerbalOp.indicative.interp c p = c.toExpState.boxCs p := rfl

@[simp] theorem interp_subjunctive (c : State W) (p : W → Prop) :
    VerbalOp.subjunctive.interp c p = c.toExpState.boxLe p := rfl

@[simp] theorem interp_interrogative (c : State W) (p : W → Prop) :
    VerbalOp.interrogative.interp c p = c.boxAns p := rfl

/-! ### Operator-specific monotonicity

`boxCs` and `boxLe` are upward-monotone in the embedded proposition:
strengthening the modal base preserves universal truth there.
`boxAns` is *not* upward-monotone — a strengthening of `p` can break
the constant-truth-per-cell property. The natural monotonicity for
`boxAns` is *anti*-monotone in the inquiry partition (covered by
`State.boxAns_anti`).

This asymmetry is itself a content claim of [portner-2018]'s
unification: the three operators have *different* natural ordering
behaviors precisely because they consult different State components,
which carry different lattice structures. -/

theorem interp_indicative_mono (c : State W) (p q : W → Prop)
    (h : ∀ w, p w → q w) :
    VerbalOp.indicative.interp c p → VerbalOp.indicative.interp c q :=
  c.toExpState.boxCs_mono p q h

theorem interp_subjunctive_mono (c : State W) (p q : W → Prop)
    (h : ∀ w, p w → q w) :
    VerbalOp.subjunctive.interp c p → VerbalOp.subjunctive.interp c q :=
  c.toExpState.boxLe_mono p q h

/-! ### Distinctness witnesses

The three mood operators are pairwise non-equivalent — each consults
a disjoint State component. We exhibit concrete witnesses showing
that no operator can be defined in terms of the others on the State
substrate alone. -/

/-- Separation state: total information over `Bool`, ordered by the
    criterion preorder for `State.sepProp` (the ordering that
    `ExpState.promote` would install from the total order). Under it
    `false` — the unique `sepProp`-world — is the unique optimal
    world. -/
def sepState : ExpState Bool :=
  ⟨Set.univ, Core.Order.Normality.crit State.sepProp⟩

/-- Lift of `sepState` to a State with trivial inquiry. Used to
    distinguish indicative from subjunctive without engaging the
    inquiry component. -/
def sepStateTriv : State Bool := State.ofExpState sepState

/-- The subjunctive operator accepts `(sepStateTriv, sepProp)`. -/
theorem subjunctive_accepts_separation :
    VerbalOp.subjunctive.interp sepStateTriv State.sepProp := by
  intro w hw
  exact hw.2 (Set.mem_univ false) (fun _ => rfl) rfl

/-- The indicative operator rejects `(sepStateTriv, sepProp)`. -/
theorem indicative_rejects_separation :
    ¬ VerbalOp.indicative.interp sepStateTriv State.sepProp := by
  intro h
  exact Bool.noConfusion (h true (Set.mem_univ true))

/-- **Indicative ≠ subjunctive**. The two mood operators are
    distinguishable: there exists a State and a proposition on which
    they disagree. The Truth/Comparison split is genuine, not a
    notational variant. -/
theorem indicative_ne_subjunctive :
    ∃ (c : State Bool) (p : Bool → Prop),
      VerbalOp.subjunctive.interp c p ∧
      ¬ VerbalOp.indicative.interp c p :=
  ⟨sepStateTriv, State.sepProp,
    subjunctive_accepts_separation, indicative_rejects_separation⟩

/-- **Interrogative ≠ indicative**. Reuses the witness from
    `State.boxAns_not_reducible_to_boxCs`: a State where the inquiry
    component partitions worlds finely enough that some `p` has
    constant truth value per cell (so `boxAns p`) yet fails to be
    universally true on `cs` (so not `boxCs p`). -/
theorem interrogative_ne_indicative :
    ∃ (c : State Bool) (p : Bool → Prop),
      VerbalOp.interrogative.interp c p ∧
      ¬ VerbalOp.indicative.interp c p :=
  State.boxAns_not_reducible_to_boxCs

/-! ### Verbal-mood biconditional characterization

`VerbalOp` is in bijection with `Component`: each operator
*exactly* picks out one POSW component, and conversely each component
is targeted by *exactly* one operator. [portner-2018] states his
**Indicative and Subjunctive principles** one-way — "If a clause φ is
operated on by the informational modal, its form is indicative"; "If
a clause φ is operated on by the preference modal, its form is
subjunctive" — with an update-based variant pair (via his (11)
fixpoints) and the note that a theory may endorse one or both, the
other mood arising by default. The biconditional form below reflects
only the bijection between this three-element operator enum and the
three components — at the verbal-mood layer, mood selection and
State-component selection are the same thing by construction. -/

theorem verbal_mood_target_informational_iff_indicative (m : VerbalOp) :
    Semantics.Mood.target m = .informational ↔ m = .indicative := by
  cases m <;> decide

theorem verbal_mood_target_preferential_iff_subjunctive (m : VerbalOp) :
    Semantics.Mood.target m = .preferential ↔ m = .subjunctive := by
  cases m <;> decide

theorem verbal_mood_target_inquisitive_iff_interrogative (m : VerbalOp) :
    Semantics.Mood.target m = .inquisitive ↔ m = .interrogative := by
  cases m <;> decide

/-! ### Bridge to `Selector`

The `Selector` enum (Mood/Basic.lean, taxonomic by predicate
class — knowledge/belief, preference/desire, etc.) projects onto
`VerbalOp` for the predicate classes that select the *same*
mood across [portner-2018]'s indicative/subjunctive languages.
Cross-linguistically variable selectors and mood-neutral predicates
project to `none` — they are not committed to either quantification
scheme by lexical-class membership alone.

Question-embedding predicates (`wonder`, `ask`, `investigate`) are a
*different* lexical dimension — they're question-embedders, not
mood-selectors-on-declarative-complements — and so are not in
`Selector`'s scope. The `.interrogative` operator is reachable
by direct construction; a future predicate-class enum specific to
question-embedders can project into it. -/

/-- Project a `Selector` to its `VerbalOp`, when the lexical
    class is committed to a single mood cross-linguistically.
    `Selector` covers declarative-complement-taking predicates;
    question-embedders project to `.interrogative` via a separate
    dimension. -/
def Selector.toVerbalOp : Selector → Option VerbalOp
  | .indicativeSelecting          => some .indicative
  | .subjunctiveSelecting         => some .subjunctive
  | .crossLinguisticallyVariable  => none
  | .moodNeutral                  => none

/-- The `prefersSubjunctive` boolean (Mood/Basic.lean) and the
    `toVerbalOp` projection agree on whether the result is the
    subjunctive operator. Two surface representations of the same
    lexical-class commitment, equivalent by construction. -/
theorem prefersSubjunctive_eq_subjunctive (m : Selector) :
    prefersSubjunctive m = true ↔ m.toVerbalOp = some .subjunctive := by
  cases m <;> simp [prefersSubjunctive, Selector.toVerbalOp]

/-- `Selector.toVerbalOp` never projects to `.interrogative`:
    the declarative-complement classification is *closed* under the
    indicative/subjunctive split. Question-embedding lives elsewhere
    — see `QuestionEmbedder` below. -/
theorem toVerbalOp_ne_interrogative (m : Selector) :
    m.toVerbalOp ≠ some .interrogative := by
  cases m <;> simp [Selector.toVerbalOp]

/-! ### Bridge to `QuestionEmbedder`

`Selector` covers declarative-complement-taking predicates only;
its `toVerbalOp` projection cannot land in `.interrogative`
(`toVerbalOp_ne_interrogative` above). The dual lexical class —
question-embedding predicates like `wonder`, `ask`, `know-Q`,
`investigate` — gets its own enum here, with the inverse projection
property: every `QuestionEmbedder` projects to `.interrogative`,
never to `.indicative` or `.subjunctive`.

The factive/non-factive split ([karttunen-1977] tradition) is the
standard subdivision of question embedders; we record it for future
expansion (e.g., a finer projection that distinguishes factive-Q
embedders' presupposition profile) without committing to particular
semantic consequences here. -/

/-- Question-embedding predicate class. Disjoint from `Selector`,
    which covers only declarative-complement embedders. The
    factive/non-factive split follows [karttunen-1977]'s typology. -/
inductive QuestionEmbedder where
  /-- Factive question-embedders: `know-Q`, `discover-Q`, `realize-Q`. -/
  | factive
  /-- Non-factive question-embedders: `wonder`, `ask`, `investigate`. -/
  | nonfactive
  deriving DecidableEq, Repr, Inhabited

/-- Every `QuestionEmbedder` projects to the interrogative verbal-mood
    operator. The dual of `Selector.toVerbalOp`: where
    `Selector` ranges over the indicative/subjunctive split,
    `QuestionEmbedder` ranges over the inquiry-component column. -/
def QuestionEmbedder.toVerbalOp : QuestionEmbedder → VerbalOp :=
  fun _ => .interrogative

@[simp] theorem QuestionEmbedder.toVerbalOp_eq (q : QuestionEmbedder) :
    q.toVerbalOp = .interrogative := rfl

/-- `QuestionEmbedder.toVerbalOp` always lands in `.interrogative` —
    the inverse of `toVerbalOp_ne_interrogative` for `Selector`.
    Together these say: the indicative/subjunctive column and the
    interrogative column are reached by *disjoint* lexical-class
    enums, with no overlap and no gap. -/
theorem QuestionEmbedder.toVerbalOp_target (q : QuestionEmbedder) :
    Semantics.Mood.target q.toVerbalOp = .inquisitive := rfl

end Semantics.Mood
