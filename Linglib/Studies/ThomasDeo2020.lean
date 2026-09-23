module

public import Linglib.Semantics.Degree.Granularity
public import Linglib.Semantics.Exhaustification.Chain
public import Linglib.Data.Examples.ThomasDeo2020

/-!
# Thomas and Deo (2020): The Interaction of *just* with Modified Scalar Predicates

This file formalizes [thomas-deo-2020]'s analysis of the approximative use of *just* with
equatives and comparatives, *just as tall as* and *just older than*, (4) and (5). The use is
distinguished from the exclusive one by focus on *just* itself, (17)–(18), and, unlike *only*,
tolerates a prejacent stronger than the context expects, (14)–(15). It has two effects: the
prejacent is true at a high level of precision, and it is false at any lower level of precision
that would make a stronger claim, section 3.3, both at issue rather than presupposed,
(31)–(35). Levels of precision are the scale granularities of [sauerland-stateva-2011]: a
degree expression denotes the open cell of the grain's width around its degree, (42)–(43), an
equative places the subject's degree above the infimum of the standard's cell, (45), and a
comparative above its supremum, (49). Equatives therefore make stronger claims at finer grains,
(47), and comparatives at coarser grains, (51), so *just* adds nothing to an equative, (48),
and bounds a comparative from above: *just older than Siri* is true at the finest grain and at
no coarser one, so the difference in age lies within the next grain, which cannot be cancelled,
(24), while *just as tall as* admits *if not taller*, (16).

The meaning of *just*, (44), is `just`, with `equative` and `comparative` the constructions at
a grain and `AtLeastAsStrong` the entailment ranking of footnote 10. The monotonicity of the
constructions in the grain is `equative_mono` and `comparative_anti`; the two readings are
`just_equative` and `just_comparative_iff`, whence the non-cancellable upper bound
`just.not_comparative`, the consistency of a taller continuation
`just_equative_of_comparative`, and the two ways of denying *just older*,
`not_just_comparative_iff`. Over the grains no finer than the finest, the negative component of *just* with a comparative is
exhaustification over the chain of grains, `just_comparative_Ici_iff`, which with a next grain
above the finest is the single negation of the comparative at that grain,
`just_comparative_iff_succ`. At one grain a comparative and its reversed equative cannot both be
true, `not_equative_of_comparative`, the contradiction of (30) that a granularity-insensitive
comparative would allow.

## Implementation notes

Degrees form a linearly ordered additive group, and a construction is a relation between the
grain width, the standard and the subject's degree, with the subject's maximal degree standing
in for the existential over degrees of (45) and (49). The finest grain of (44) is a parameter,
as are the contextual grains, which are assumed no finer than it. The determination of the
finest grain by magnitude, permitted error and roundness (section 4) and the interaction with
expectations of section 3.4 are not formalized. The examples are the rows of
`Data.Examples.ThomasDeo2020`.

## References

* [thomas-deo-2020]
* [sauerland-stateva-2011]
* [kennedy-mcnally-2005]
* [coppock-beaver-2014]
* [beaver-clark-2008]
* [lasersohn-1999]
* [krifka-2007]
-/

@[expose] public section

namespace ThomasDeo2020

open Degree.Granularity Exhaustification

variable {D : Type*} [AddCommGroup D] [LinearOrder D]

/-! ### Constructions at a grain (sections 4.1 and 4.2) -/

/-- The equative at a grain, (45): the subject's degree exceeds the infimum of the standard's
cell. -/
def equative (ε dc μx : D) : Prop := (mkGranInterval ε dc).lo < μx

/-- The comparative at a grain, (49): the subject's degree exceeds the supremum of the
standard's cell. -/
def comparative (ε dc μx : D) : Prop := (mkGranInterval ε dc).hi < μx

variable {ε ε₁ ε₂ εf dc μx : D} {G : Set D}

theorem equative_iff : equative ε dc μx ↔ dc - ε < μx := Iff.rfl

theorem comparative_iff : comparative ε dc μx ↔ dc + ε < μx := Iff.rfl

/-- Strength, footnote 10: a construction at one grain is at least as strong as at another
when it entails it at every degree. -/
def AtLeastAsStrong (p : D → D → Prop) (ε₁ ε₂ : D) : Prop := ∀ μx, p ε₁ μx → p ε₂ μx

/-- (44): the prejacent holds at the finest grain, and at no grain of the contextual set at
which it would make a stronger claim. -/
def just (p : D → D → Prop) (G : Set D) (εf μx : D) : Prop :=
  p εf μx ∧ ∀ ε ∈ G, p ε μx → AtLeastAsStrong p εf ε

variable [IsOrderedAddMonoid D]

/-- (47): an equative at a finer grain is at least as strong. -/
theorem equative_mono (h : ε₁ ≤ ε₂) : AtLeastAsStrong (equative · dc) ε₁ ε₂ :=
  λ _ hμ => lt_of_le_of_lt (finer_contained ε₁ ε₂ dc h).1 hμ

/-- (51): a comparative at a coarser grain is at least as strong. -/
theorem comparative_anti (h : ε₁ ≤ ε₂) : AtLeastAsStrong (comparative · dc) ε₂ ε₁ :=
  λ _ hμ => lt_of_le_of_lt (finer_contained ε₁ ε₂ dc h).2 hμ

/-- (30): at one grain a comparative and its reversed equative cannot both hold: the
difference in degree that the comparative requires is what the equative excludes. -/
theorem not_equative_of_comparative {μF dS : D} (h : comparative ε dS μF) :
    ¬ equative ε μF dS :=
  λ h' => lt_asymm h (sub_lt_iff_lt_add.1 h')

/-! ### Approximative *just* (44) -/

/-- (48): with an equative the negative component is vacuous, and *just as tall as* is the
equative at the finest grain. -/
theorem just_equative (hG : ∀ ε ∈ G, εf ≤ ε) :
    just (equative · dc) G εf μx ↔ equative εf dc μx :=
  ⟨And.left, λ h => ⟨h, λ ε hε _ => equative_mono (hG ε hε)⟩⟩

/-- (16): an equative with *just* enforces no upper bound: the subject may exceed the
standard by any grain. -/
theorem just_equative_of_comparative (hG : ∀ ε ∈ G, εf ≤ ε) (hf : 0 ≤ εf) (hε : 0 ≤ ε)
    (h : comparative ε dc μx) : just (equative · dc) G εf μx :=
  (just_equative hG).2
    (lt_of_le_of_lt ((sub_le_self dc hf).trans (le_add_of_nonneg_right hε)) h)

/-- (24): with a comparative the negative component excludes every coarser grain, so the
upper bound cannot be cancelled. -/
theorem just.not_comparative (h : just (comparative · dc) G εf μx) (hε : ε ∈ G)
    (hlt : εf < ε) : ¬ comparative ε dc μx :=
  λ hc => lt_irrefl (dc + ε) (h.2 ε hε hc (dc + ε) (add_lt_add_of_le_of_lt le_rfl hlt))

/-- *Just older than*: the comparative holds at the finest grain and at no coarser one. -/
theorem just_comparative_iff (hG : ∀ ε ∈ G, εf ≤ ε) :
    just (comparative · dc) G εf μx ↔
      dc + εf < μx ∧ ∀ ε ∈ G, εf < ε → μx ≤ dc + ε := by
  refine ⟨λ h => ⟨h.1, λ ε hε hlt => not_lt.1 (h.not_comparative hε hlt)⟩, λ h => ⟨h.1, ?_⟩⟩
  intro ε hε hc
  rcases (hG ε hε).lt_or_eq with hlt | rfl
  · exact absurd hc (not_lt.2 (h.2 ε hε hlt))
  · exact λ _ h => h

/-- (31): denying *just older* denies the comparative at the finest grain or asserts it at a
coarser one, that the subject is significantly older. -/
theorem not_just_comparative_iff (hG : ∀ ε ∈ G, εf ≤ ε) :
    ¬ just (comparative · dc) G εf μx ↔
      μx ≤ dc + εf ∨ ∃ ε ∈ G, εf < ε ∧ dc + ε < μx := by
  rw [just_comparative_iff hG]
  constructor
  · intro h
    by_cases h1 : dc + εf < μx
    · push Not at h
      exact Or.inr (h h1)
    · exact Or.inl (not_lt.1 h1)
  · rintro (h | ⟨ε, hε, hlt, h2⟩) ⟨h1, h3⟩
    · exact absurd h1 (not_lt.2 h)
    · exact absurd h2 (not_lt.2 (h3 ε hε hlt))

/-- Over the grains no finer than the finest, the negative component of *just* with a
comparative is exhaustification against the strictly coarser grains, the stronger alternatives
of the chain (section 5). -/
theorem just_comparative_Ici_iff :
    just (comparative · dc) (Set.Ici εf) εf μx ↔ exhChain (comparative · dc) εf μx :=
  (just_comparative_iff λ _ hε => hε).trans
    ⟨λ h => ⟨h.1, λ ε hε => not_lt.2 (h.2 ε (le_of_lt hε) hε)⟩,
      λ h => ⟨h.1, λ ε _ hε => not_lt.1 (h.2 ε hε)⟩⟩

/-- With a next grain above the finest, *just older than* places the subject within that grain
above the standard: Fafen's age is Siri's plus the finest grain, section 4.2. -/
theorem just_comparative_iff_succ {ε' : D} (his : εf < ε') (hleast : ∀ ε, εf < ε → ε' ≤ ε) :
    just (comparative · dc) (Set.Ici εf) εf μx ↔ dc + εf < μx ∧ μx ≤ dc + ε' := by
  rw [just_comparative_Ici_iff, exhChain_iff_succ (φ := λ ε => comparative ε dc)
    (λ _ _ h => comparative_anti h) his hleast, comparative_iff, comparative_iff, not_lt]

end ThomasDeo2020
