import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Syntax.Category.Determiner.Basic
import Linglib.Fragments.German.Determiners
import Linglib.Studies.Schwarz2009

/-!
# Patel-Grosz and Grosz (2017): Revisiting Pronominal Typology

This file formalizes the account in [patel-grosz-grosz-2017] of the German personal pronouns
*er*, *sie*, *es* and the so-called demonstrative pronouns *der*, *die*, *das*. Both series
are definite determiners over a null noun phrase; the demonstratives add a DP shell hosting
an anaphoric index, so they are the strong article of [schwarz-2009] and the personal
pronouns the weak one, and nothing genuinely demonstrative distinguishes them
(`PronounSystem`, `german`). Corpus and experimental data on gender mismatch, equally
available to both series, support the shared null noun phrase, and the two-series languages
are those with two article forms (`german_weakAndStrong`). Where the two articles diverge,
the demonstrative is anaphoric in a way the personal pronoun is not (`der_er_can_diverge`).
The distribution follows from structural economy, Minimize DP!, which prefers the structure
with fewer DP shells unless the added index does pragmatic work: emotivity, disambiguation
away from the most prominent antecedent, or colloquial register (`DEMLicensingContext`,
`Series.Optimal`, `optimal_iff`).

## Implementation notes

The German forms are typed as `PersonalPronoun`, article strength being a property of the
series; deixis is the separate `DemonstrativePronoun` of the pronoun substrate, which *der*
lacks. The divergence reuses the two-satisfier scenario of the Schwarz study, and Minimize
DP! is a comparison of shell counts among the structures that achieve the intended
interpretation; the gender-mismatch corpus counts are described in prose.

## References

* [patel-grosz-grosz-2017]
* [schwarz-2009]
* [elbourne-2005]
* [cardinaletti-starke-1999]
-/

namespace PatelGroszGrosz2017

open Definiteness

/-- The pragmatic effects that license the strong-article series (§5): the speaker's
emotional engagement with the referent, disambiguation away from the most prominent
antecedent, and colloquial or dialectal register. -/
inductive DEMLicensingContext where
  | emotivity
  | disambiguation
  | register
  deriving DecidableEq

/-! ### The German inventory -/

/-- The weak series: *er*. -/
def er : PersonalPronoun :=
  { form := "er", person := some .third, number := some .singular, gender := some .masculine }

/-- The weak series: *sie*. -/
def sie : PersonalPronoun :=
  { form := "sie", person := some .third, number := some .singular, gender := some .feminine }

/-- The weak series: *es*. -/
def es : PersonalPronoun :=
  { form := "es", person := some .third, number := some .singular, gender := some .neuter }

/-- The strong series: *der*, the same core plus the anaphoric index. -/
def der : PersonalPronoun :=
  { form := "der", person := some .third, number := some .singular, gender := some .masculine }

/-- The strong series: *die*. -/
def die : PersonalPronoun :=
  { form := "die", person := some .third, number := some .singular, gender := some .feminine }

/-- The strong series: *das*. -/
def das : PersonalPronoun :=
  { form := "das", person := some .third, number := some .singular, gender := some .neuter }

/-- A language's third-person pronoun system: the weak and strong series, the article
inventory, and the pragmatic effects that license the strong series. -/
structure PronounSystem where
  weak : List PersonalPronoun
  strong : List PersonalPronoun
  determiners : Determiner.Inventory
  licensing : List DEMLicensingContext

/-- German: the weak series *er*, *sie*, *es*, the strong series *der*, *die*, *das*, the
weak and strong articles, and all three licensing effects. -/
def german : PronounSystem where
  weak := [er, sie, es]
  strong := [der, die, das]
  determiners := German.Determiners.inventory
  licensing := [.emotivity, .disambiguation, .register]

/-- German has two article forms, read off the determiner inventory, matching its two pronoun
series (§4). -/
theorem german_weakAndStrong : german.determiners.articleType = .weakAndStrong := by decide

/-- The strong series is anaphoric in a way the weak one is not: over one restrictor with
two satisfiers, the weak description of *er* fails uniqueness while the strong description
of *der* reads its referent off the discourse index, the two-satisfier scenario of the
Schwarz study. -/
theorem der_er_can_diverge :
    Definiteness.interpret
        (Definiteness.Description.ofPresupType .uniqueness Schwarz2009.studentRestr 0)
        Schwarz2009.gAlice Schwarz2009.gs0 ≠
      Definiteness.interpret
        (Definiteness.Description.ofPresupType .familiarity Schwarz2009.studentRestr 0)
        Schwarz2009.gAlice Schwarz2009.gs0 :=
  Schwarz2009.two_articles_can_disagree

/-! ### Minimize DP! (§5) -/

/-- The two series as structures: the weak series is a single DP, the strong series adds a
shell hosting the anaphoric index. -/
inductive Series where
  | weak
  | strong
  deriving DecidableEq

/-- The number of DP shells. -/
def Series.shells : Series → ℕ
  | .weak => 1
  | .strong => 2

/-- Whether the series carries an anaphoric index. -/
def Series.HasIndex : Series → Prop
  | .weak => False
  | .strong => True

/-- A series achieves an interpretation if it carries an index whenever the interpretation
requires one. -/
def Series.Achieves (needsIndex : Prop) (s : Series) : Prop := needsIndex → s.HasIndex

/-- Minimize DP!: among the series that achieve the interpretation, use the one with the
fewest DP shells. -/
def Series.Optimal (needsIndex : Prop) (s : Series) : Prop :=
  s.Achieves needsIndex ∧ ∀ s' : Series, s'.Achieves needsIndex → s.shells ≤ s'.shells

/-- The weak series is the default and the strong series surfaces exactly when the index does
pragmatic work: a series is optimal for an interpretation iff it is the strong series
precisely when the interpretation needs the index. -/
theorem optimal_iff (needsIndex : Prop) (s : Series) :
    s.Optimal needsIndex ↔ (needsIndex ↔ s = .strong) := by
  constructor
  · rintro ⟨hach, hmin⟩
    cases s with
    | weak => exact ⟨λ hp => (hach hp).elim, λ h => Series.noConfusion h⟩
    | strong =>
      refine ⟨λ _ => rfl, λ _ => Classical.byContradiction λ hp => ?_⟩
      exact absurd (hmin .weak λ h => (hp h).elim) (by decide)
  · intro h
    cases s with
    | weak =>
      refine ⟨λ hp => Series.noConfusion (h.1 hp), λ s' _ => ?_⟩
      cases s' <;> decide
    | strong =>
      refine ⟨λ _ => trivial, λ s' hs' => ?_⟩
      cases s' with
      | weak => exact (hs' (h.2 rfl)).elim
      | strong => exact le_rfl

end PatelGroszGrosz2017
