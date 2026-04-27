import Mathlib.Logic.Basic
import Mathlib.Data.Set.Basic

/-!
# Question Support — cross-tradition `s ⊨ Q` interface

A theory-neutral typeclass for the relation "state `s` supports / resolves
question `Q`". The literature calls this *support* in inquisitive semantics
(`s ⊨ Q`); the @cite{ginzburg-2012} KOS framework calls it *answerhood*
(a fact resolves a question); decision-theoretic and TTR variants give
yet other names. This file fixes the shared mathlib-shaped interface.

## Why two classes

Different consumers of the support relation have different decidability
profiles. Mathlib's pattern (compare `LE` vs `LinearOrder`) is to
expose the bare relation as one typeclass and refine it for
decidable-evaluation use cases:

* `Support State Question` — bare Prop-valued relation. Inquisitive
  `(Set W) ⊨ (Question W)` lives here: set membership in a `LowerSet`
  is generally undecidable, so the substrate provides only the
  relation.
* `DecidableSupport State Question` — extends `Support` with per-pair
  decidability. KOS's String/String, partition, and TTR instances all
  live here: their underlying `=` / `BEq` / pattern-match resolution
  is genuinely decidable. KOS QUD-downdate (`DGB.downdateQud`) and the
  list-based `allResolvedList` aggregator demand this refinement.

Consumers requiring only the relation take `[Support …]`; consumers
that evaluate the relation (filter, `decide`, list aggregation) take
`[DecidableSupport …]`.

## Notation

Scoped `s ⊨ q` for `Support.supports s q` lives in `Core.Question` so
it can coexist with the inquisitive `s ⊨ p` from `Core.Question.Basic`
(once the namespace consolidates, this notation simply becomes the
canonical one).

## Specialisations

* `Core.Question.Relevance` — `partiallyAnswers` and `moveRelevant`
  (Roberts QUD-relevance) over `Question W`. Specific notions, not a
  typeclass.
* `Semantics.Questions.Resolution` — `Resolves`, `MentionSome`,
  `MentionAll` over `Set W → Question W`. Each is a candidate `Support`
  instance for the inquisitive substrate.
* `Semantics.Questions.Probabilistic` — IKW
  @cite{ippolito-kiss-williams-2025} evidential SUPPORT: doxastic +
  probabilistic. Prior-parameterised, so it does **not** fit this
  typeclass; see that file's `Supports` directly.
-/

namespace Core.Question

/-- The state `s` supports / resolves the question `q`.

In inquisitive semantics this is `s ⊨ Q`
(@cite{ciardelli-groenendijk-roelofsen-2018}); in @cite{ginzburg-2012}
this is "FACTS contextually entail an answer to q". The interface is
intentionally minimal: just the binary relation. The specialisations
— exhaustive, mention-some, partial, probabilistic — each refine
this base. -/
class Support (State Question : Type*) where
  /-- The support / resolution relation. -/
  supports : State → Question → Prop

@[inherit_doc] scoped notation:50 s " ⊨ " q => Support.supports s q

/-- Support relation with decidable evaluation. Refines `Support` with
the per-pair decidability needed by KOS QUD-downdate and similar
consumers. Mirrors mathlib's `LinearOrder extends PartialOrder`
pattern, where the refinement adds `decidableLE` etc. fields. -/
class DecidableSupport (State Question : Type*) extends Support State Question where
  /-- Per-pair decidability of `Support.supports`. -/
  decSupports (s : State) (q : Question) : Decidable (supports s q)

attribute [reducible, instance] DecidableSupport.decSupports

namespace Support

variable {State Question : Type*}

/-- Every question in `questions` is supported by some state in
    `states`. The carrier-agnostic mathlib shape: `Set` quantification
    over the support relation. -/
def AllResolved [Support State Question]
    (states : Set State) (questions : Set Question) : Prop :=
  ∀ q ∈ questions, ∃ s ∈ states, s ⊨ q

end Support

namespace DecidableSupport

variable {State Question : Type*}

/-- Every question in the list is supported by some state in the list.
    Specialisation of `Support.AllResolved` for ordered carriers (KOS
    QUD stacks). -/
def allResolvedList [DecidableSupport State Question]
    (states : List State) (questions : List Question) : Prop :=
  ∀ q ∈ questions, ∃ s ∈ states, Support.supports s q

instance allResolvedList.instDecidable [DecidableSupport State Question]
    (states : List State) (questions : List Question) :
    Decidable (allResolvedList states questions) := by
  unfold allResolvedList; infer_instance

end DecidableSupport

end Core.Question
