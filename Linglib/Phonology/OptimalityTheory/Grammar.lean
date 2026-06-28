import Linglib.Phonology.OptimalityTheory.Antimatroid

/-!
# OT grammars: the leg-set / ERC-set / antimatroid hub

In Optimality Theory the linguistically fundamental object is not a single
ranking but a **grammar**: the set of all rankings ("legs") that yield the same
optima ([prince-2002]; [prince-smolensky-1993]). A grammar has three equivalent
faces ([merchant-riggle-2016]): a **leg set** (the satisfying rankings), an
**ERC set** (its ranking conditions), and an **antimatroid**. This file makes the
grammar a first-class type, taking the leg set as its canonical identity and
exhibiting the other two faces as views.

Taking the leg set as identity makes grammar equality decidable and dissolves the
"up to entailment" hedge that the ERC-set presentation carries: two consistent ERC
sets present the *same* grammar exactly when they are mutually entailing
(`Grammar.ofERCSet_eq_iff_entails`), because they then have the same legs. The
transitive-reduction ambiguity that forces [merchant-riggle-2016] Theorem 2 to be
stated up to logical equivalence becomes literal `Grammar` equality here.

The antimatroid face (`Grammar.toAntimatroid`) is a one-directional view: every
grammar is an antimatroid, but the converse — that every antimatroid is some
grammar's — rests on [dietrich-1987]'s rooted-circuit characterization and is
carried as honest `sorry`s in `OptimalityTheory.Antimatroid` (`Antimat_RCErc_inv`,
`RCErc_Antimat_inv`). The feasible family is read directly off the legs and is
independent of the presenting ERC set, since `MChain` depends only on the
satisfying rankings.

## Main definitions

* `Grammar n` — a realizable leg set: a `Finset (Ranking n)` equal to the linear
  extensions of some consistent ERC set.
* `Grammar.ofERCSet` — the canonical grammar of a consistent ERC set (the ERC face,
  as a constructor).
* `Grammar.feasible` / `Grammar.toAntimatroid` — the antimatroid face.

## Main results

* `Grammar.ofERCSet_eq_iff_entails` — two consistent ERC sets present the same
  grammar iff they are mutually entailing (the entailment quotient dissolves).
* `Grammar.feasible_ofERCSet` — the antimatroid family of `ofERCSet E` is `MChain E`.
* `Grammar.toAntimatroid_isFeasible` — the antimatroid face's feasible sets are
  exactly the prefixes of the grammar's legs.

## Categorical structure

All the structure here is the order-theoretic specialization of category theory —
the categories are *thin* (posetal), not monoidal. `(Set (Ranking n), ⊆)` and
`(Set (ERC n), ⊆)` are thin categories; `subset_models_iff` exhibits `conditions`
and `models` as a **(dual) adjunction** between them. The induced monad
`grammarClosure = models ∘ conditions` is the **idempotent closure monad**, and its
algebras — the closed objects (`IsGrammarClosed`) — are exactly the grammars: a
**reflective subcategory** of ranking-space with `grammarClosure` as the reflector.
On `Grammar n` itself this lands as a `PartialOrder` (the specificity = entailment
order, `ofERCSet_le_iff_entails`) with a **terminal object** (`OrderTop`, the trivial
grammar) and **binary coproducts** (`superGrammar`, the super-grammar join, with
universal property `superGrammar_le`). Binary products (meets) may be empty, so the
full complete lattice lives on the closed sets, not on `Grammar`.

## References

* [merchant-riggle-2016]
* [prince-2002]
* [prince-smolensky-1993]
-/

namespace OptimalityTheory

variable {n : ℕ}

/-! ### The grammar–condition Galois connection

The leg-set / ERC-set duality is the antitone Galois connection — the
formal-concept "polarity" ([merchant-riggle-2016]; the framing is
Birkhoff / Ganter–Wille) — induced by the satisfaction relation on
`Ord(S.Con) × ERC`. `models A` collects the rankings satisfying every condition in
`A`; `conditions R` collects the conditions satisfied by every ranking in `R`.
Grammars are exactly the closed sets `models (conditions R)`, the *extents* of
this context. -/

/-- The rankings satisfying every condition in `A` (the extent polarity). -/
def models (A : Set (ERC n)) : Set (Ranking n) := {r | ∀ α ∈ A, ERC.satisfiedBy r α}

/-- The conditions satisfied by every ranking in `R` (the intent polarity). -/
def conditions (R : Set (Ranking n)) : Set (ERC n) := {α | ∀ r ∈ R, ERC.satisfiedBy r α}

@[simp] theorem mem_models {A : Set (ERC n)} {r : Ranking n} :
    r ∈ models A ↔ ∀ α ∈ A, ERC.satisfiedBy r α := Iff.rfl

@[simp] theorem mem_conditions {R : Set (Ranking n)} {α : ERC n} :
    α ∈ conditions R ↔ ∀ r ∈ R, ERC.satisfiedBy r α := Iff.rfl

/-- **The grammar–condition Galois connection.** `R ⊆ models A ↔ A ⊆ conditions R`:
both sides say every ranking in `R` satisfies every condition in `A`. -/
theorem subset_models_iff {A : Set (ERC n)} {R : Set (Ranking n)} :
    R ⊆ models A ↔ A ⊆ conditions R := by
  constructor
  · intro h α hα r hr; exact h hr α hα
  · intro h r hr α hα; exact h hα r hr

theorem models_antitone : Antitone (models : Set (ERC n) → Set (Ranking n)) := by
  intro A B hAB r hr α hα; exact hr α (hAB hα)

theorem conditions_antitone : Antitone (conditions : Set (Ranking n) → Set (ERC n)) := by
  intro R S hRS α hα r hr; exact hα r (hRS hr)

/-- The closure operator on ranking-space — the **reflector** onto the grammars,
i.e. the idempotent monad `models ∘ conditions` induced by the Galois adjunction.
Its fixed points (the algebras / closed objects) are exactly the grammars. -/
def grammarClosure (R : Set (Ranking n)) : Set (Ranking n) := models (conditions R)

theorem subset_grammarClosure (R : Set (Ranking n)) : R ⊆ grammarClosure R := by
  intro r hr α hα; exact hα r hr

theorem grammarClosure_mono : Monotone (grammarClosure : Set (Ranking n) → Set (Ranking n)) :=
  fun _ _ h => models_antitone (conditions_antitone h)

theorem conditions_grammarClosure (R : Set (Ranking n)) :
    conditions (grammarClosure R) = conditions R :=
  le_antisymm (conditions_antitone (subset_grammarClosure R)) (subset_models_iff.mp le_rfl)

theorem grammarClosure_idem (R : Set (Ranking n)) :
    grammarClosure (grammarClosure R) = grammarClosure R := by
  show models (conditions (grammarClosure R)) = models (conditions R)
  rw [conditions_grammarClosure]

/-- A ranking-set is **grammar-closed** iff it equals its closure — iff it is the
models of some condition set. These are the closure monad's algebras (the closed
objects of the reflective subcategory), exactly the leg sets of grammars
(`Grammar.coe_legs_isGrammarClosed`, `Grammar.exists_grammar_of_isGrammarClosed`). -/
def IsGrammarClosed (R : Set (Ranking n)) : Prop := grammarClosure R = R

theorem isGrammarClosed_models (A : Set (ERC n)) : IsGrammarClosed (models A) :=
  le_antisymm (models_antitone (subset_models_iff.mp le_rfl)) (subset_grammarClosure (models A))

theorem isGrammarClosed_iff_exists_models {R : Set (Ranking n)} :
    IsGrammarClosed R ↔ ∃ A, R = models A :=
  ⟨fun h => ⟨conditions R, h.symm⟩, by rintro ⟨A, rfl⟩; exact isGrammarClosed_models A⟩

/-! ### The closure system: meet and the super-grammar join

The closed sets form a closure system, hence a complete lattice. The **meet** of
two grammars is the intersection of their legs (`isGrammarClosed_inter`) — conjoin
their conditions (`models_union`). The **join** is `grammarClosure (R ∪ R')`, the
smallest grammar containing both: the closure of the union of legs. This is the
*super-grammar* that coarsens a typology by unioning grammars; closing the union
is exactly what guarantees the result is again a grammar. -/

theorem models_union (A B : Set (ERC n)) : models (A ∪ B) = models A ∩ models B := by
  ext r; simp only [mem_models, Set.mem_union, or_imp, forall_and, Set.mem_inter_iff]

/-- The closure of any set is closed: `grammarClosure R` is a grammar (the
super-grammar generated by `R`). -/
theorem isGrammarClosed_grammarClosure (R : Set (Ranking n)) :
    IsGrammarClosed (grammarClosure R) := isGrammarClosed_models _

/-- **Meet.** The intersection of two grammars' leg sets is again closed — the
greatest grammar contained in both. -/
theorem isGrammarClosed_inter {R R' : Set (Ranking n)}
    (hR : IsGrammarClosed R) (hR' : IsGrammarClosed R') : IsGrammarClosed (R ∩ R') := by
  refine le_antisymm (Set.subset_inter ?_ ?_) (subset_grammarClosure _)
  · exact (grammarClosure_mono Set.inter_subset_left).trans hR.le
  · exact (grammarClosure_mono Set.inter_subset_right).trans hR'.le

/-- The coerced linear-extension set of an ERC list is the `models` of that list's
conditions — the bridge from the `ERCSet` presentation to the Galois polarity. -/
theorem coe_linearExtensions_eq_models (E : ERCSet n) :
    (↑E.linearExtensions : Set (Ranking n)) = models {α | α ∈ E} := by
  ext r
  simp only [Finset.mem_coe, ERCSet.mem_linearExtensions, mem_models, Set.mem_setOf_eq]
  rfl

/-- The empty ERC set is satisfied by every ranking: its linear extensions are all
of `Ord(S.Con)`. This is the trivial grammar (no ranking conditions). -/
@[simp] theorem ERCSet.linearExtensions_nil :
    ERCSet.linearExtensions ([] : ERCSet n) = Finset.univ := by
  ext r; simp [ERCSet.mem_linearExtensions, ERCSet.satisfiedBy]

/-- An OT **grammar**: a set of rankings realizable as the linear extensions of
some consistent ERC set ([merchant-riggle-2016]). The leg set is the grammar's
canonical identity; the ERC-set and antimatroid presentations are views. -/
structure Grammar (n : ℕ) where
  /-- The grammar's legs: the rankings that select its language's optima. -/
  legs : Finset (Ranking n)
  /-- Every grammar is the linear-extension set of some consistent ERC set. -/
  realizable : ∃ E : ERCSet n, ERCSet.consistent E ∧ legs = E.linearExtensions

namespace Grammar

/-- A grammar is determined by its legs: the realizability witness is a `Prop`,
so leg-set equality is grammar equality. -/
@[ext] theorem ext {G G' : Grammar n} (h : G.legs = G'.legs) : G = G' := by
  cases G; cases G'; cases h; rfl

/-- The grammar of a consistent ERC set — the ERC face, as a constructor. -/
def ofERCSet (E : ERCSet n) (hcons : ERCSet.consistent E) : Grammar n where
  legs := E.linearExtensions
  realizable := ⟨E, hcons, rfl⟩

@[simp] theorem legs_ofERCSet (E : ERCSet n) (hcons : ERCSet.consistent E) :
    (ofERCSet E hcons).legs = E.linearExtensions := rfl

/-- Membership: `r ∈ G` means `r` is one of `G`'s legs. -/
instance : Membership (Ranking n) (Grammar n) where
  mem G r := r ∈ G.legs

@[simp] theorem mem_iff {G : Grammar n} {r : Ranking n} : r ∈ G ↔ r ∈ G.legs := Iff.rfl

@[simp] theorem mem_ofERCSet {E : ERCSet n} {hcons : ERCSet.consistent E} {r : Ranking n} :
    r ∈ ofERCSet E hcons ↔ ERCSet.satisfiedBy r E := by
  simp [mem_iff, ofERCSet]

/-- A grammar has at least one leg: a harmonically-bounded row gives no grammar
([prince-2002]). -/
theorem legs_nonempty (G : Grammar n) : G.legs.Nonempty := by
  obtain ⟨E, hcons, hlegs⟩ := G.realizable
  obtain ⟨r, hr⟩ := hcons
  exact ⟨r, by rw [hlegs]; exact ERCSet.mem_linearExtensions.mpr hr⟩

/-! ### The ERC face: grammar equality is mutual entailment -/

/-- **The entailment quotient dissolves at the grammar level.** Two consistent ERC
sets present the same grammar iff they are mutually entailing — iff they have the
same legs. This is why the leg set, not the ERC set, is the grammar's identity:
the "logically equivalent, not literally equal" hedge of the ERC presentation
([merchant-riggle-2016] Theorem 2) becomes literal `Grammar` equality. -/
theorem ofERCSet_eq_iff_entails {E E' : ERCSet n}
    (h : ERCSet.consistent E) (h' : ERCSet.consistent E') :
    ofERCSet E h = ofERCSet E' h' ↔ ERCSet.entails E E' ∧ ERCSet.entails E' E := by
  constructor
  · intro he
    have hl : E.linearExtensions = E'.linearExtensions := congrArg Grammar.legs he
    rw [Finset.ext_iff] at hl
    simp only [ERCSet.mem_linearExtensions] at hl
    exact ⟨fun r => (hl r).mp, fun r => (hl r).mpr⟩
  · rintro ⟨h12, h21⟩
    apply ext
    simp only [legs_ofERCSet, Finset.ext_iff, ERCSet.mem_linearExtensions]
    exact fun r => ⟨h12 r, h21 r⟩

/-! ### The antimatroid face -/

/-- The feasible family of a grammar: the prefixes of its legs. This reads the
antimatroid `MChain` family directly off the legs, independent of any ERC
presentation. -/
def feasible (G : Grammar n) (S : Set (Fin n)) : Prop :=
  ∃ r : Ranking n, r ∈ G.legs ∧ ∃ k : Fin (n + 1), maximalChain r k = S

/-- The feasible family of `ofERCSet E` is exactly `MChain E`: the antimatroid face
agrees with [merchant-riggle-2016]'s `Antimat E` construction. -/
theorem feasible_ofERCSet (E : ERCSet n) (hcons : ERCSet.consistent E) (S : Set (Fin n)) :
    (ofERCSet E hcons).feasible S ↔ MChain E S := by
  simp only [feasible, legs_ofERCSet, ERCSet.mem_linearExtensions, MChain]

/-- The feasible family is presentation-independent: it depends only on the legs,
so any consistent ERC set realizing `G` computes it. -/
theorem feasible_eq_mChain (G : Grammar n) {E : ERCSet n}
    (hlegs : G.legs = E.linearExtensions) : G.feasible = MChain E := by
  funext S
  simp only [feasible, hlegs, ERCSet.mem_linearExtensions, MChain]

/-- The **antimatroid face** of a grammar ([merchant-riggle-2016]): ground set the
constraints, feasible sets the prefixes of the legs. Every grammar is an
antimatroid; the converse rests on [dietrich-1987] (`Antimat_RCErc_inv`). The
structure's accessibility and union-closure transfer from any realizing
`Antimat E` via `feasible_eq_mChain`. -/
def toAntimatroid (G : Grammar n) : Antimatroid (Fin n) where
  E := Set.univ
  IsFeasible := G.feasible
  empty_feasible := by
    obtain ⟨E, hcons, hlegs⟩ := G.realizable
    rw [G.feasible_eq_mChain hlegs]; exact (Antimat E hcons).empty_feasible
  feasible_sub := fun _ _ => Set.subset_univ _
  ground_feasible := by
    obtain ⟨E, hcons, hlegs⟩ := G.realizable
    rw [G.feasible_eq_mChain hlegs]; exact (Antimat E hcons).ground_feasible
  augmentation := by
    obtain ⟨E, hcons, hlegs⟩ := G.realizable
    rw [G.feasible_eq_mChain hlegs]; exact (Antimat E hcons).augmentation
  removal := by
    obtain ⟨E, hcons, hlegs⟩ := G.realizable
    rw [G.feasible_eq_mChain hlegs]; exact (Antimat E hcons).removal
  union_closed := by
    obtain ⟨E, hcons, hlegs⟩ := G.realizable
    rw [G.feasible_eq_mChain hlegs]; exact (Antimat E hcons).union_closed

@[simp] theorem toAntimatroid_isFeasible (G : Grammar n) (S : Set (Fin n)) :
    G.toAntimatroid.IsFeasible S ↔ G.feasible S := Iff.rfl

/-- The antimatroid face of `ofERCSet E` has the same feasible sets as `Antimat E`. -/
theorem toAntimatroid_ofERCSet_isFeasible (E : ERCSet n) (hcons : ERCSet.consistent E)
    (S : Set (Fin n)) :
    (ofERCSet E hcons).toAntimatroid.IsFeasible S ↔ (Antimat E hcons).IsFeasible S := by
  rw [toAntimatroid_isFeasible, feasible_ofERCSet]
  exact Iff.rfl

/-! ### Grammars are exactly the nonempty closed sets -/

/-- A grammar's legs form a closed set of ranking-space — the extent of its
conditions. -/
theorem coe_legs_isGrammarClosed (G : Grammar n) :
    IsGrammarClosed (↑G.legs : Set (Ranking n)) := by
  obtain ⟨E, _, hlegs⟩ := G.realizable
  rw [hlegs, coe_linearExtensions_eq_models]
  exact isGrammarClosed_models _

/-- Conversely, every nonempty grammar-closed set of rankings is some grammar's
leg set. With `coe_legs_isGrammarClosed`, grammars *are* the nonempty closed sets
of the grammar–condition Galois connection. -/
theorem exists_grammar_of_isGrammarClosed {R : Set (Ranking n)}
    (hcl : IsGrammarClosed R) (hne : R.Nonempty) :
    ∃ G : Grammar n, (↑G.legs : Set (Ranking n)) = R := by
  obtain ⟨E, hAeq⟩ : ∃ E : ERCSet n, {α | α ∈ E} = conditions R := by
    refine ⟨(Set.toFinite (conditions R)).toFinset.toList, ?_⟩
    ext α; simp [Set.Finite.mem_toFinset, Finset.mem_toList]
  have hReq : (↑E.linearExtensions : Set (Ranking n)) = R := by
    rw [coe_linearExtensions_eq_models, hAeq]; exact hcl
  have hcons : ERCSet.consistent E := by
    obtain ⟨r, hr⟩ := hne
    have hmem : r ∈ (↑E.linearExtensions : Set (Ranking n)) := hReq ▸ hr
    rw [Finset.mem_coe, ERCSet.mem_linearExtensions] at hmem
    exact ⟨r, hmem⟩
  exact ⟨⟨E.linearExtensions, E, hcons, rfl⟩, hReq⟩

/-! ### The specificity order: grammars as a thin category

`Grammar n` is a **poset** — a thin category — under leg-set inclusion: `G ≤ G'`
means `G` is *more specific* (fewer legs, more ranking conditions). On the ERC face
this is exactly the entailment order (`ofERCSet_le_iff_entails`), the order side of
the Galois adjunction. `grammarClosure` is the **reflector** onto this subcategory
(grammars are its closed objects — the algebras of the idempotent closure monad).
The **terminal object** is the trivial grammar (`OrderTop`); the **coproduct** of
two grammars is their super-grammar — the closure of the union of legs. Binary
products (meets) may be empty, so the full lattice lives on the closed sets, with
`Grammar n` the nonempty part. -/

instance : PartialOrder (Grammar n) where
  le G G' := G.legs ⊆ G'.legs
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ h h' := Finset.Subset.trans h h'
  le_antisymm _ _ h h' := ext (Finset.Subset.antisymm h h')

theorem le_iff_legs {G G' : Grammar n} : G ≤ G' ↔ G.legs ⊆ G'.legs := Iff.rfl

/-- The specificity order on grammars **is** the entailment order on their ERC sets
— the order side of the grammar–condition Galois adjunction. -/
theorem ofERCSet_le_iff_entails {E E' : ERCSet n}
    (h : ERCSet.consistent E) (h' : ERCSet.consistent E') :
    ofERCSet E h ≤ ofERCSet E' h' ↔ ERCSet.entails E E' := by
  rw [le_iff_legs]
  constructor
  · intro hle r hr
    exact ERCSet.mem_linearExtensions.mp (hle (ERCSet.mem_linearExtensions.mpr hr))
  · intro hent r hr
    exact ERCSet.mem_linearExtensions.mpr (hent r (ERCSet.mem_linearExtensions.mp hr))

/-- The **trivial grammar** — the terminal object of the specificity order: all
rankings, no ranking conditions (`ofERCSet []`). -/
def trivial : Grammar n := ofERCSet [] ⟨Ranking.id n, by simp [ERCSet.satisfiedBy]⟩

@[simp] theorem legs_trivial : (Grammar.trivial : Grammar n).legs = Finset.univ := by
  simp only [Grammar.trivial, legs_ofERCSet, ERCSet.linearExtensions_nil]

instance : OrderTop (Grammar n) where
  top := trivial
  le_top G := by rw [le_iff_legs, legs_trivial]; exact Finset.subset_univ _

theorem grammarClosure_union_nonempty (G G' : Grammar n) :
    (grammarClosure (↑G.legs ∪ ↑G'.legs : Set (Ranking n))).Nonempty := by
  obtain ⟨r, hr⟩ := G.legs_nonempty
  exact ⟨r, subset_grammarClosure _ (Set.mem_union_left _ (Finset.mem_coe.mpr hr))⟩

/-- The **super-grammar** (the coproduct / join in the thin category of grammars):
the least grammar containing both `G` and `G'`, the closure of the union of their
legs. This is [merchant-riggle-2016]'s typology coarsening — union the legs, then
close to land back inside `Grammar`. -/
noncomputable def superGrammar (G G' : Grammar n) : Grammar n :=
  (exists_grammar_of_isGrammarClosed (isGrammarClosed_grammarClosure _)
    (grammarClosure_union_nonempty G G')).choose

theorem coe_superGrammar_legs (G G' : Grammar n) :
    (↑(superGrammar G G').legs : Set (Ranking n))
      = grammarClosure (↑G.legs ∪ ↑G'.legs : Set (Ranking n)) :=
  (exists_grammar_of_isGrammarClosed (isGrammarClosed_grammarClosure _)
    (grammarClosure_union_nonempty G G')).choose_spec

theorem le_superGrammar_left (G G' : Grammar n) : G ≤ superGrammar G G' := by
  rw [le_iff_legs, ← Finset.coe_subset, coe_superGrammar_legs]
  exact Set.Subset.trans Set.subset_union_left (subset_grammarClosure _)

theorem le_superGrammar_right (G G' : Grammar n) : G' ≤ superGrammar G G' := by
  rw [le_iff_legs, ← Finset.coe_subset, coe_superGrammar_legs]
  exact Set.Subset.trans Set.subset_union_right (subset_grammarClosure _)

/-- **Universal property of the super-grammar**: it is the least grammar above both
— the coproduct of `G` and `G'` in the thin category of grammars. -/
theorem superGrammar_le {G G' K : Grammar n} (hG : G ≤ K) (hG' : G' ≤ K) :
    superGrammar G G' ≤ K := by
  have hK : grammarClosure (↑K.legs : Set (Ranking n)) = ↑K.legs := coe_legs_isGrammarClosed K
  rw [le_iff_legs, ← Finset.coe_subset, coe_superGrammar_legs]
  refine Set.Subset.trans (grammarClosure_mono (Set.union_subset ?_ ?_)) hK.subset
  · exact Finset.coe_subset.mpr (le_iff_legs.mp hG)
  · exact Finset.coe_subset.mpr (le_iff_legs.mp hG')

end Grammar

end OptimalityTheory
