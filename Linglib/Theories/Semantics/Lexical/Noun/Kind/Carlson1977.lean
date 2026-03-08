/-!
# A Unified Analysis of the English Bare Plural
@cite{carlson-1977}

Linguistics and Philosophy 1(3): 413--457, 1977.

## The Core Insight

Bare plurals are proper names of kinds, which are abstract individuals that can
be spatially unbounded. The generic/existential distinction arises from
the PREDICATE, not from an ambiguous determiner.

## Sorted Ontology (§4)

@cite{carlson-1977} partitions entities into three sorts:
- **Stages**: Spatially AND temporally bounded slices (a dog at a time & place)
- **Ordinary individuals**: Spatially bounded (one place at a time)
- **Kinds**: Spatially UNbounded (can be "here and there" simultaneously)

The **realization relation** R connects stages to the individuals/kinds they
realize. R is sorted: its domain is stages, its range is individuals or kinds.
This rules out pathological configurations (kinds realizing kinds, stages of
stages) and is captured formally in `CarlsonModel`.

## Predicate Level

@cite{milsark-1974} and @cite{siegel-1976} distinguished:
- **Stage-level** predicates ("states"): hungry, available, in the room
- **Individual-level** predicates ("properties"): intelligent, tall, a mammal

@cite{carlson-1977} connects this to bare plural interpretation:
- Stage-level predicates → existential reading ("Dogs are in the yard")
- Individual-level predicates → generic reading ("Dogs are intelligent")

The existential comes from the **predicate** (via R), not from the NP.

## Habitual Readings (§4)

For habitual readings like "Dogs run" in simple present tense,
@cite{carlson-1977} treats the habitual as **direct kind predication**:

    "Dogs run" → run'(d)

The habitual is individual/kind-level — `run'` is predicated directly of the
kind, just like `intelligent'`. The progressive turns it stage-level:

    "Dogs are running" → ∃x[R(x, d) ∧ run'(x)]

Later work (@cite{krifka-etal-1995} and others) introduced a covert GEN
operator for habituals, but @cite{carlson-1977} handles them via direct
kind predication without any generic quantifier.

## Connection to Subsequent Work

- @cite{chierchia-1998}: Formalizes R as the ∪ operator, adds ∩/∪ kind↔property
  mapping
- @cite{krifka-2004}: Rejects kinds as basic; bare NPs are properties
- @cite{dayal-2004}: Extends with singular kinds and Meaning Preservation

See `Phenomena/Generics/Compare.lean` for cross-theory comparison.
-/

namespace Semantics.Lexical.Noun.Kind.Carlson1977

-- ═══════════════════════════════════════════════════════════════════════
-- §1  Sorted Ontology
-- ═══════════════════════════════════════════════════════════════════════

/-- The three ontological sorts in @cite{carlson-1977}'s system (§4).

Entities are partitioned into stages, (ordinary) individuals, and kinds.
This three-way distinction is the foundation: the realization relation R
only connects stages to individuals/kinds, never the reverse. -/
inductive EntitySort where
  | stage        -- spatially AND temporally bounded
  | individual   -- spatially bounded, temporally persistent
  | kind         -- spatially UNbounded
  deriving DecidableEq, Repr

/-- A Carlson model: a sorted domain with a typed realization relation R.

The sort constraints on R capture genuine formal content from §4:
- `R_domain`: only stages realize things (R's source is always a stage)
- `R_range`: stages realize individuals or kinds (R's target is never a stage)

These constraints rule out pathological models where kinds realize kinds,
individuals are stages of other individuals, or R chains through stages. -/
structure CarlsonModel (Entity : Type) where
  /-- Sort assignment: every entity has exactly one sort. -/
  sort : Entity → EntitySort
  /-- R(y, x): y is a realization (stage) of x. -/
  R : Entity → Entity → Prop
  /-- R's domain is stages: only stages realize anything. -/
  R_domain : ∀ y x, R y x → sort y = .stage
  /-- R's range is individuals or kinds: stages realize persistent entities. -/
  R_range : ∀ y x, R y x → sort x = .individual ∨ sort x = .kind

/-- The realization relation: x R y means "x is a stage/realization of y." -/
abbrev RealizationRel (Entity : Type) := Entity → Entity → Prop

-- ═══════════════════════════════════════════════════════════════════════
-- §2  Predicate Level Classification
-- ═══════════════════════════════════════════════════════════════════════

/-- Stage-level vs individual-level predicate classification.

- Stage-level ("states" in @cite{milsark-1974}): hungry, available, in the room
- Individual-level ("properties"): intelligent, tall, a mammal

This determines whether bare plurals get existential or generic readings. -/
inductive PredicateLevel where
  | stageLevel       -- "States" in Milsark's terminology
  | individualLevel  -- "Properties" in Milsark's terminology
  deriving DecidableEq, Repr

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Semantic Composition
-- ═══════════════════════════════════════════════════════════════════════

variable (Entity : Type)

/-- Individual-level predicate semantics: direct predication of the kind.

`⟦be intelligent⟧ = I'`

"Dogs are intelligent" = I'(d) where d is the kind DOGS.
No existential quantifier involved. -/
abbrev IndividualLevelPred := Entity → Bool

/-- Stage-level predicate semantics: predication via the R relation.

`⟦be in the yard⟧ = λx.∃y[R(y,x) ∧ in-yard'(y)]`

"Dogs are in the yard" = ∃y[R(y,d) ∧ in-yard'(y)]

The existential comes from THE PREDICATE, not from the NP.
This is why bare plurals get existential readings with stage-level predicates. -/
def stageLevelPred (R : RealizationRel Entity) (P : Entity → Bool) : Entity → Prop :=
  λ x => ∃ y, R y x ∧ P y = true

/-- The progressive turns any predicate into stage-level (§4, p. 450).

@cite{carlson-1977}: the progressive has "the function of predicating a verb
of a stage, but not of an individual."

- "Dogs run" → run'(d) (habitual — individual-level, direct kind predication)
- "Dogs are running" → ∃x[R(x,d) ∧ run'(x)] (progressive makes it stage-level) -/
def progressive (R : RealizationRel Entity) (P : Entity → Bool) : Entity → Prop :=
  stageLevelPred Entity R P

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Derivations: Generic vs Existential
-- ═══════════════════════════════════════════════════════════════════════

variable {Entity : Type}

/-- Generic reading derivation: individual-level predicate + kind.

"Dogs are intelligent"
1. ⟦dogs⟧ = d (the kind)
2. ⟦be intelligent⟧ = I' (individual-level)
3. Composition: I'(d)

Result: A property is directly attributed to the kind.

This also covers habitual readings in @cite{carlson-1977}'s system:
"Dogs run" = run'(d), where the habitual is individual/kind-level. -/
def genericDerivation
    (kind : Entity)
    (pred : IndividualLevelPred Entity)
    : Bool :=
  pred kind

/-- Existential reading derivation: stage-level predicate + kind.

"Dogs are in the yard"
1. ⟦dogs⟧ = d (the kind)
2. ⟦be in the yard⟧ = λx.∃y[R(y,x) ∧ in-yard'(y)] (stage-level)
3. Composition: ∃y[R(y,d) ∧ in-yard'(y)]

Result: The predicate introduces existential quantification over stages. -/
def existentialDerivation
    (R : RealizationRel Entity)
    (kind : Entity)
    (stagePred : Entity → Bool)
    : Prop :=
  stageLevelPred Entity R stagePred kind

-- ═══════════════════════════════════════════════════════════════════════
-- §5  Bare Plurals as Proper Names
-- ═══════════════════════════════════════════════════════════════════════

/-- @cite{carlson-1977}'s central claim: the bare plural is never ambiguous.

The different "readings" (generic vs existential) arise from:
1. The predicate's level (individual vs stage)
2. Not from different meanings of the NP

This is why there's no scope ambiguity with bare plurals —
they're just proper names, and proper names don't scope. -/
theorem bare_plural_not_ambiguous
    (kind : Entity)
    (R : RealizationRel Entity)
    (indPred : IndividualLevelPred Entity)
    (stagePred : Entity → Bool)
    : (genericDerivation kind indPred = indPred kind) ∧
      (existentialDerivation R kind stagePred = ∃ y, R y kind ∧ stagePred y = true) :=
  ⟨rfl, rfl⟩

/-- Bare plural semantics: λP.P{k} (§4, p. 450)

"'Dogs' translates as: λPP{d}."

Just like "Jake" denotes the individual Jake,
"dogs" denotes the kind DOGS. No determiner, no quantifier — just a
proper name. -/
def barePluralTranslation (k : Entity) : (Entity → Bool) → Bool :=
  λ P => P k

/-- Bare plurals behave like proper names, not quantifiers.

The bare plural "dogs" denotes a fixed entity k. Applying any predicate P
to the bare plural just evaluates P at k — no quantificational structure,
no scope interaction. -/
theorem bare_plural_rigid_designator
    (k : Entity)
    (P : Entity → Bool)
    : barePluralTranslation k P = P k := rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §6  Model-Theoretic Consequences
-- ═══════════════════════════════════════════════════════════════════════

/-- Kinds can't realize anything: only stages are in R's domain.

If k has sort `.kind`, then R(k, x) is impossible — because `R_domain`
requires the source to be a stage, and kind ≠ stage. -/
theorem kind_cannot_realize (M : CarlsonModel Entity) {k x : Entity}
    (hk : M.sort k = .kind) (hR : M.R k x) : False := by
  have := M.R_domain k x hR
  rw [hk] at this; exact EntitySort.noConfusion this

/-- Individuals can't realize anything either: R's domain is stages only. -/
theorem individual_cannot_realize (M : CarlsonModel Entity) {i x : Entity}
    (hi : M.sort i = .individual) (hR : M.R i x) : False := by
  have := M.R_domain i x hR
  rw [hi] at this; exact EntitySort.noConfusion this

/-- R doesn't chain: there are no "stages of stages."

If R(y, x) and R(z, y), then y must be simultaneously:
- a stage (from `R_domain` applied to R(y, x))
- an individual or kind (from `R_range` applied to R(z, y))

Sort disjointness gives a contradiction. This means the ontological
hierarchy has exactly depth 1: stages realize individuals/kinds, full stop. -/
theorem R_no_chain (M : CarlsonModel Entity) {z y x : Entity}
    (hRyx : M.R y x) (hRzy : M.R z y) : False := by
  have hy_stage := M.R_domain y x hRyx
  have hy_persistent := M.R_range z y hRzy
  cases hy_persistent with
  | inl h => rw [hy_stage] at h; exact EntitySort.noConfusion h
  | inr h => rw [hy_stage] at h; exact EntitySort.noConfusion h

/-- Stage-level predication of a kind: the existential witness is a stage.

When P is stage-level and we evaluate `stageLevelPred R P k`, the witness
y satisfying R(y, k) ∧ P(y) is guaranteed to be a stage by `R_domain`.
This is a genuine constraint: the thing that "is in the yard" when we
say "Dogs are in the yard" must be a spatiotemporally bounded entity. -/
theorem stage_witness_is_stage (M : CarlsonModel Entity) (P : Entity → Bool) (k : Entity)
    (h : stageLevelPred Entity M.R P k) :
    ∃ y, M.R y k ∧ P y = true ∧ M.sort y = .stage := by
  obtain ⟨y, hRy, hPy⟩ := h
  exact ⟨y, hRy, hPy, M.R_domain y k hRy⟩

/-- Individual-level predication bypasses stages entirely.

When P is individual-level, `genericDerivation k P` applies P directly
to k. No R relation is involved, so no stage-sorting constraint applies. -/
theorem individual_level_bypasses_R
    (P : IndividualLevelPred Entity) (k : Entity)
    : genericDerivation k P = P k := rfl

-- ═══════════════════════════════════════════════════════════════════════
-- §7  Scope and Opacity
-- ═══════════════════════════════════════════════════════════════════════

/-- "be everywhere" as a stage-level predicate over locations (§4, p. 454).

    ∀y[Place'(y) → ∃z[R(z,k) ∧ At(z,y)]]

Different places can have different realizations — this is why "Dogs were
everywhere" is natural (different dogs in different places) while "A dog
was everywhere" is bizarre (same dog everywhere). -/
def beEverywhere
    (R : RealizationRel Entity)
    (places : List Entity)
    (atPred : Entity → Entity → Bool)
    : Entity → Prop :=
  λ x => ∀ p ∈ places, ∃ y, R y x ∧ atPred y p = true

/-- Differentiated scope: for a kind k, "k was everywhere" allows different
realizations at each place. The ∃ over stages is INSIDE the ∀ over places. -/
theorem kind_allows_differentiated_scope
    (R : RealizationRel Entity)
    (k : Entity)
    (places : List Entity)
    (atPred : Entity → Entity → Bool)
    : beEverywhere R places atPred k =
      (∀ p ∈ places, ∃ y, R y k ∧ atPred y p = true) := rfl

/-- Differentiated scope with model constraints: the witnesses at each
place are guaranteed to be stages (spatiotemporally bounded entities). -/
theorem differentiated_scope_witnesses_are_stages
    (M : CarlsonModel Entity)
    (k : Entity)
    (places : List Entity)
    (atPred : Entity → Entity → Bool)
    (h : beEverywhere M.R places atPred k) :
    ∀ p ∈ places, ∃ y, M.R y k ∧ atPred y p = true ∧ M.sort y = .stage := by
  intro p hp
  obtain ⟨y, hRy, hAt⟩ := h p hp
  exact ⟨y, hRy, hAt, M.R_domain y k hRy⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §8  Scopelessness: Bare Plurals vs Quantified NPs
-- ═══════════════════════════════════════════════════════════════════════

/-- @cite{carlson-1977}'s central argument (§4, sentence 134):
bare plurals yield ONLY the contradictory reading under conjunction
with negation.

"Cats are here and cats aren't here" — whether "be here" is stage-level
or individual-level, the bare plural contributes the SAME constant c
in both conjuncts. The result is P ∧ ¬P for some P, which is
unsatisfiable.

This is a consequence of the proper-name analysis: constants force
coreference across conjuncts. -/
theorem bare_plural_narrow_scope_only
    (P : Entity → Prop) (c : Entity) :
    ¬(P c ∧ ¬P c) :=
  fun ⟨h, hn⟩ => hn h

/-- Instantiated for stage-level predicates: "Cats are here and cats
aren't here" with `here` as stage-level (via R) is still contradictory.

    ∃y[R(y,c) ∧ Here'(y)] ∧ ¬∃y[R(y,c) ∧ Here'(y)] = ⊥ -/
theorem bare_plural_stage_level_contradiction
    (R : RealizationRel Entity) (P : Entity → Bool) (c : Entity) :
    ¬(stageLevelPred Entity R P c ∧ ¬stageLevelPred Entity R P c) :=
  bare_plural_narrow_scope_only (stageLevelPred Entity R P) c

/-- Contrast: quantified NPs allow non-contradictory readings because
different witnesses can satisfy the two conjuncts.

"Some cats are here and some cats aren't here" is satisfiable:
one cat can be here while another isn't. We construct an explicit
witness showing satisfiability.

This is the CONTRAST that makes Carlson's argument: proper names
(bare plurals) force contradiction; quantifiers (indefinites) don't.
The structural reason is that proper names contribute a constant,
while quantifiers introduce a variable that can take different values. -/
theorem quantified_np_non_contradictory
    (Cat Here : Entity → Bool)
    (c₁ c₂ : Entity)
    (hCat₁ : Cat c₁ = true) (hHere₁ : Here c₁ = true)
    (hCat₂ : Cat c₂ = true) (hHere₂ : Here c₂ = false) :
    (∃ x, Cat x = true ∧ Here x = true) ∧
    (∃ x, Cat x = true ∧ Here x = false) :=
  ⟨⟨c₁, hCat₁, hHere₁⟩, ⟨c₂, hCat₂, hHere₂⟩⟩

/-- The contrast also holds for stage-level predication via R:
"Some cats are here and some cats aren't here" with `here` as
stage-level is satisfiable when different individuals have stages
in different locations. -/
theorem quantified_np_stage_level_non_contradictory
    (Cat : Entity → Bool) (R : RealizationRel Entity) (P : Entity → Bool)
    (c₁ c₂ y₁ : Entity)
    (hCat₁ : Cat c₁ = true) (hR₁ : R y₁ c₁) (hP₁ : P y₁ = true)
    (hCat₂ : Cat c₂ = true) (hNoStage : ¬∃ y, R y c₂ ∧ P y = true) :
    (∃ x, Cat x = true ∧ stageLevelPred Entity R P x) ∧
    (∃ x, Cat x = true ∧ ¬stageLevelPred Entity R P x) :=
  ⟨⟨c₁, hCat₁, ⟨y₁, hR₁, hP₁⟩⟩, ⟨c₂, hCat₂, hNoStage⟩⟩

-- ═══════════════════════════════════════════════════════════════════════
-- §9  Examples from the Paper
-- ═══════════════════════════════════════════════════════════════════════

/-!
## Key Examples from @cite{carlson-1977}

### Generic readings (individual-level predicates)
- "Horses are mammals" — mammals'(HORSES) (direct kind predication)
- "Dogs are intelligent" — intelligent'(DOGS) (direct kind predication)
- "Dogs run" — run'(DOGS) (habitual = individual-level kind predication)

### Existential readings (stage-level predicates)
- "Dogs are in the next room" — ∃y[R(y, DOGS) ∧ in-next-room'(y)]
- "Dogs are running" — ∃y[R(y, DOGS) ∧ running'(y)] (progressive = stage-level)

### Narrow scope (§4, sentence 134)
- "Cats are here and cats aren't here"
  = ∃y[R(y,c) ∧ Here'(y)] ∧ ¬∃y[R(y,c) ∧ Here'(y)] = CONTRADICTION
  Since "cats" denotes a constant c (not a variable), the two conjuncts
  are P ∧ ¬P. Contrast with "some cats" where different witnesses can
  satisfy the two existentials.

### Differentiated scope (§4, sentence 135c)
- "Dogs were everywhere" — ∀y[Place'(y) → ∃z[R(z, DOGS) ∧ At(z,y)]]
  Natural: different dogs in different places
- "A dog was everywhere" — bizarre: same dog in every place

### Opacity (§4, sentence 132)
- "Max believes dogs are here"
  = Bel'(^∃y[R(y, d) ∧ Here'(y)])(m)
  Since d is a kind (no reference to particular dogs), the ∃ is inside
  the belief — only the opaque reading is available.
-/

end Semantics.Lexical.Noun.Kind.Carlson1977
