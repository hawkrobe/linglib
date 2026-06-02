import Linglib.Fragments.Hungarian.Focus
import Linglib.Core.Logic.FactorsThroughOn

/-!
# Hungarian preverbal/postverbal focus contrast

Formalises the §1 minimal pairs, the §2 structural claim that
position determines focus type, and the §3 distributional
restrictions of É. Kiss (1998) on Hungarian focus.

## Main definitions

* `preverbal_identificational`, `postverbal_information`: paper eq. (5a)/(5b).
* `preverbal_hat`, `postverbal_hat`: paper eq. (8a)/(8b).
* `starred_universal_identificational`, `universal_information`: eq. (17b)/(19b).

## Main results

* `position_determines_focusType`: on licensed configs, `focusType`
  factors through `position`. Kiss's §2 structural claim.
* `preverbal_iff_exhaustive`: exhaustivity equivalent to preverbal
  position on licensed configs.
* `starred_universal_identificational_not_licensed`,
  `universal_information_licensed`, `only_information_not_licensed`,
  `someIndef_neither_licensed`: §3 restrictions.

## Implementation notes

Kiss's exhaustivity claim has been substantially revised in later
work (Onea & Beaver 2011, Horváth 2010, Wedgwood 2005). The
theorems below formalise Kiss's 1998 position faithfully without
adjudicating between Kiss and her successors.

The same factor-through schema (`Function.FactorsThroughOn`) is
instantiated for Hausa in `HartmannZimmermann2007.lean`, where it is
refuted.

## TODO

* §4 scope (identificational focus binds variables).
* §5.2 cleft realisation in English.
* §9 cross-linguistic feature typology for Italian, Romanian,
  Catalan, Greek, Arabic, Finnish.
* §7 focus iteration and projection (eq. 51-53).

## References

* [kiss-1998].
-/

namespace Kiss1998

open Hungarian.Focus

/-! ## Cells (paper §1, eq. 5a/5b, 8a/8b, 17b, 19b) -/

/-- Eq. (5a): *Tegnap este Marinak mutattam be Pétert*
    'It was to MARY that I introduced Peter last night.'
    Identificational/preverbal: of the relevant set of persons, it was
    Mary and no one else that I introduced Peter to. -/
def preverbal_identificational : FocusConfig :=
  mkIdentificational .regular (by simp [ConstituentClass.compatibleWith])

/-- Eq. (5b): *Tegnap este be mutattam Pétert MARINAK*
    'Last night I introduced Peter TO MARY.'
    Information/postverbal: presents Mary as nonpresupposed
    information, without suggesting Mary was the only one. -/
def postverbal_information : FocusConfig :=
  mkInformation .regular (by simp [ConstituentClass.compatibleWith])

/-- Eq. (8a): *Mari egy kalapot nézett ki magának*
    'It was a HAT that Mary picked for herself.'
    Identificational/preverbal of a regular DP. -/
def preverbal_hat : FocusConfig :=
  mkIdentificational .regular (by simp [ConstituentClass.compatibleWith])

/-- Eq. (8b): *Mari ki nézett magának EGY KALAPOT*
    'Mary picked for herself A HAT.'
    Information/postverbal of a regular DP — non-exhaustive. -/
def postverbal_hat : FocusConfig :=
  mkInformation .regular (by simp [ConstituentClass.compatibleWith])

/-- Eq. (17b — starred): *\*Mari minden kalapot nézett ki magának*
    'It was every hat that Mary picked for herself.'
    Universal quantifier in identificational focus position is
    ungrammatical (paper §3). Constructed directly to demonstrate the
    distributional restriction has bite. -/
def starred_universal_identificational : FocusConfig :=
  ⟨.preverbal, .identificational, .universal⟩

/-- Eq. (19b): *Minden kollégámat meg hívtam*
    'I invited EVERY COLLEAGUE OF MINE.'
    Universal quantifier as postverbal information focus —
    grammatical, demonstrating that *minden* is barred only from
    identificational position, not from focus altogether. -/
def universal_information : FocusConfig :=
  mkInformation .universal (by simp [ConstituentClass.compatibleWith])

/-! ## Position determines focus type (paper §2)

Kiss's §2 (p. 246, property list (1)-(6); p. 249 prose after eq. (9))
argues that the two Hungarian focus positions encode genuinely distinct
focus *types*, not merely interpretational variants of a single focus.
Formalised here as: among licensed configurations, `focusType` factors
through `position` (i.e. position determines type).

The same schema is instantiated for Hausa in `HartmannZimmermann2007.lean`
with `cfg.strategy` for the structural projection and `pragType` for the
interpretation, and is *refuted* there — making the typological contrast
a difference of verdict on a single shared factor-through schema. -/

/-- Position determines focus type on licensed configurations: Kiss's
§2 structural claim. -/
theorem position_determines_focusType :
    Function.FactorsThroughOn
      FocusConfig.focusType FocusConfig.position {c | c.Licensed} := by
  intro c₁ c₂ h₁ h₂ hpos
  obtain ⟨hpos₁, _⟩ := h₁
  obtain ⟨hpos₂, _⟩ := h₂
  have heq : positionFor c₁.focusType = positionFor c₂.focusType := by
    rw [← hpos₁, ← hpos₂]; exact hpos
  cases ft₁ : c₁.focusType <;> cases ft₂ : c₂.focusType <;>
    rw [ft₁, ft₂] at heq <;> simp [positionFor] at heq

/-- Position equivalence with exhaustivity: composition of the
position-type and type-exhaustivity equivalences. The semantic payoff
of Kiss's §2 structural distinction. -/
theorem preverbal_iff_exhaustive (c : FocusConfig) (h : c.Licensed) :
    c.position = .preverbal ↔ c.focusType.IsExhaustive := by
  rw [licensed_position_determines_type c h]
  cases c.focusType <;> simp [FocusType.IsExhaustive]

/-! ## Distributional restrictions (paper §3, eq. 17) -/

/-- **Universal quantifiers cannot be identificational foci** (paper
    eq. 17b). The `starred_universal_identificational` configuration
    fails licensing because `universal.compatibleWith
    .identificational = False`. -/
theorem starred_universal_identificational_not_licensed :
    ¬ starred_universal_identificational.Licensed := by decide

/-- **Universal quantifiers can be information foci** (paper eq. 19b).
    The same `universal` class that is barred from preverbal position
    is admissible postverbally. The asymmetry is exactly the §3
    typological observation. -/
theorem universal_information_licensed : universal_information.Licensed :=
  mkInformation_licensed _ _

/-- **Only-phrases must be identificational foci** (paper §3 last
    paragraph): the *csak X* construction is obligatorily realised as
    identificational focus. The information-focus alternative is
    therefore ill-licensed. -/
theorem only_information_not_licensed :
    ¬ (FocusConfig.mk .postverbal .information .onlyPhrase).Licensed := by
  decide

/-- **Indefinite *valami/valaki* is barred from both focus types**
    (paper eq. 17e). Both attempted licensings fail. -/
theorem someIndef_neither_licensed :
    ¬ (FocusConfig.mk .preverbal .identificational .someIndef).Licensed ∧
    ¬ (FocusConfig.mk .postverbal .information .someIndef).Licensed := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## Cell properties -/

theorem preverbal_identificational_licensed :
    preverbal_identificational.Licensed :=
  mkIdentificational_licensed _ _

theorem postverbal_information_licensed :
    postverbal_information.Licensed :=
  mkInformation_licensed _ _

/-- The eq. (5a/5b) minimal pair: same constituent (a regular DP),
    different positions, different focus types — both licensed,
    validating the paper's claim that the two positions encode
    genuinely distinct focus types rather than free interpretational
    variants. -/
theorem minimal_pair_distinct_types :
    preverbal_hat.focusType ≠ postverbal_hat.focusType := by decide

end Kiss1998
