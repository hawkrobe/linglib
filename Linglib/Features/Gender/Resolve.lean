import Linglib.Features.Gender.Basic

/-!
# Gender resolution
[corbett-1991] [willer-gold-2023] [marusic-nevins-badecker-2015]
[adamson-anagnostopoulou-2025] [bhatt-walkow-2013] [nevins-weisser-2019]

Resolution of gender with coordinated nominals, over a language's own
controller-gender carrier. Unlike `Number.resolve` — which *derives* from
the join-semilattice of individuals — gender resolution has no
lattice-theoretic ground: the attested mechanisms are an inventory of
strategies ([nevins-weisser-2019] for the survey), and which one applies is
language- and configuration-particular data.

## Main declarations

* `Gender.Strategy` — the strategy inventory: language-particular
  resolution rules (`res`, [corbett-1991]; computed by feature intersection
  in [adamson-anagnostopoulou-2025]), default value insertion (`dvi`,
  no-peeking/percolation-failure, [marusic-nevins-badecker-2015]), and the
  single-conjunct strategies (`closest`/`highest`,
  [marusic-nevins-badecker-2015]'s three coexisting grammars).
* `Gender.System.resolve` — per-strategy resolution, `Option`-valued:
  ineffability is a predicted outcome ([adamson-anagnostopoulou-2025]
  derive resolution without all-purpose default insertion;
  [bhatt-walkow-2013]'s bidirectional-agreement matching effects are a
  second ineffability source).
* `Gender.System.resolveIn` — the value *set* produced by a set of active
  strategies: within-speaker optionality is parallel grammars
  ([willer-gold-2023] Fig. 1), not nondeterminism inside a strategy
  ([bhatt-walkow-2013]: Hindi-Urdu F+F subjects resolve F, or M only when
  animate — a choice between strategies).
* `Gender.Locus` — where resolution applies: on the ConjP goal (early) or
  on the probe after copying (late), [willer-gold-2023]'s experimental
  contrast. [bhatt-walkow-2013]'s syntactic-resolved vs post-syntactic-CCA
  split is the same axis from the theory side; both are implementable as
  the timing of Agree-Copy ([smith-2021]).

## Implementation notes

* **Strategies are arguments, not `System` fields**: one language can use
  different strategies in different agreement configurations
  ([bhatt-walkow-2013]: Hindi-Urdu T resolves subjects but takes
  closest-conjunct agreement with case-licensed objects, LCA preverbally
  and FCA postverbally).
* The `res` table is language-particular data; its derivation from feature
  intersection over interpretable features is
  [adamson-anagnostopoulou-2025]'s mechanism, formalized in
  `Studies/AdamsonAnagnostopoulou2025.lean` (`resolve`/`resolveN`).
* Binary resolution only; n-ary conjunctions fold once consumers need them
  (cf. `AdamsonAnagnostopoulou2025.resolveN`).
* The strategy layer (closest/highest/resolved/default) is φ-generic —
  [bhatt-walkow-2013]'s CCA is one mechanism across number and gender — and
  hoists to shared substrate when a second feature module consumes it.
* For `closest`/`highest` the convention is: the first argument is the
  structurally higher / linearly first conjunct.
-/

set_option autoImplicit false

namespace Gender

variable {G : Type*}

/-- A gender-resolution strategy ([nevins-weisser-2019]). The `res` table is
    the language's resolution rules ([corbett-1991]); `dvi` inserts the
    system default; `closest`/`highest` are single-conjunct agreement. -/
inductive Strategy (G : Type*) where
  /-- Resolution rules: equal contribution of both conjuncts, computed by a
      language-particular table; `none` = ineffable conflict. -/
  | res (table : G → G → Option G)
  /-- Default value insertion: the system default regardless of conjunct
      values (no-peeking / percolation failure). -/
  | dvi
  /-- Closest conjunct agreement (second argument). -/
  | closest
  /-- Highest conjunct agreement (first argument). -/
  | highest

/-- A resolution table treats congruent conjuncts trivially: shared gender
    resolves to itself ([willer-gold-2023]'s congruent-conjunct baseline). -/
def Strategy.Congruent (table : G → G → Option G) : Prop :=
  ∀ g, table g g = some g

namespace System

variable (S : System G)

/-- Resolve the gender of two coordinated conjuncts by a strategy.
    `none` = ineffability (no grammatical output). -/
def resolve : Strategy G → G → G → Option G
  | .res t,   a, b => t a b
  | .dvi,     _, _ => some S.default
  | .closest, _, b => some b
  | .highest, a, _ => some a

@[simp] theorem resolve_res (t : G → G → Option G) (a b : G) :
    S.resolve (.res t) a b = t a b := rfl

@[simp] theorem resolve_dvi (a b : G) :
    S.resolve .dvi a b = some S.default := rfl

@[simp] theorem resolve_closest (a b : G) :
    S.resolve .closest a b = some b := rfl

@[simp] theorem resolve_highest (a b : G) :
    S.resolve .highest a b = some a := rfl

/-- Closest- and highest-conjunct agreement are order duals. -/
theorem resolve_closest_swap (a b : G) :
    S.resolve .closest a b = S.resolve .highest b a := rfl

/-- A congruent table resolves shared gender to itself. -/
theorem resolve_res_self {t : G → G → Option G}
    (h : Strategy.Congruent t) (g : G) :
    S.resolve (.res t) g g = some g := h g

/-- The values produced by a set of active strategies — within-speaker and
    cross-configuration variation as parallel grammars
    ([willer-gold-2023]; [bhatt-walkow-2013]). -/
def resolveIn (strats : Set (Strategy G)) (a b : G) : Set G :=
  {g | ∃ st ∈ strats, S.resolve st a b = some g}

/-- More active strategies produce more values. -/
theorem resolveIn_mono {s₁ s₂ : Set (Strategy G)} (h : s₁ ⊆ s₂) (a b : G) :
    S.resolveIn s₁ a b ⊆ S.resolveIn s₂ a b :=
  λ _ ⟨st, hst, he⟩ => ⟨st, h hst, he⟩

/-- A single active strategy produces exactly its output. -/
theorem resolveIn_singleton (st : Strategy G) (a b g : G) :
    g ∈ S.resolveIn {st} a b ↔ S.resolve st a b = some g :=
  ⟨λ ⟨_, hst, he⟩ => hst ▸ he, λ he => ⟨st, rfl, he⟩⟩

end System

/-- Where resolution applies ([willer-gold-2023]): on the ConjP goal
    (early — the value is present before the probe agrees) or on the probe
    (late — after copying from both conjuncts). Implementable as the timing
    of Agree-Copy ([smith-2021]); [bhatt-walkow-2013]'s syntactic vs
    post-syntactic split is the same axis. -/
inductive Locus where
  /-- Goal resolution: ConjP valued before probing. -/
  | goal
  /-- Probe resolution: valuation on the probe after Multiple Agree. -/
  | probe
  deriving DecidableEq, Repr, Fintype

end Gender
