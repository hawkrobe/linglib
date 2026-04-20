import Linglib.Fragments.Hungarian.Focus
import Linglib.Theories.Semantics.Focus.MeaningStructureMapping

/-!
# É. Kiss (1998) — Identificational Focus versus Information Focus
@cite{kiss-1998} @cite{hartmann-zimmermann-2007}

@cite{kiss-1998} argues for a structural distinction between two
focus types in Hungarian:

- **Identificational focus** moves to Spec,FP (immediately preverbal)
  and expresses *exhaustive identification* — selecting the maximal
  subset of contextually-given alternatives for which the predicate
  holds.
- **Information focus** stays VP-internal (postverbal); it merely
  marks nonpresupposed information without exhaustivity.

Hungarian is the empirical pivot in the typological debate that
@cite{hartmann-zimmermann-2007} later use Hausa to challenge:
Hungarian **validates** the Meaning-Structure Mapping Hypothesis
(focus position determines focus type and exhaustivity); Hausa
*refutes* it.

This file is the second of two studies that instantiate
`Theories.Semantics.Focus.MSMH.MeaningStructureMapping` (the
polymorphic hypothesis). The contrast is deep, not analogical: the
*same* theorem statement holds for Hungarian (`hungarian_satisfies_MSMH`
below) and fails for Hausa (`hausa_falsifies_MSMH` in
`HartmannZimmermann2007.lean`). The two refutations / validations use
the same predicate from `Theories/Semantics/Focus/`.

The §3 distributional restrictions are encoded via
`Fragments.Hungarian.Focus.ConstituentClass.compatibleWith`. The
positive theorems `onlyPhrase_forces_identificational` and
`someIndef_never_licensed` live at the Fragment level (they are
universal closures over arbitrary licensed configs); this file only
adds the empirical cells from the paper and the typological
contrast theorems.

Out of scope: §4 *scope* (identificational focus binds variables;
information focus does not); §5.2 the cleft-construction realisation
of identificational focus in English (would need an English Cleft
Fragment); §6 the cross-linguistic feature typology
([±exhaustive], [±contrastive]) parametrising Italian, Romanian,
Catalan, Greek, Arabic, Finnish; §7 focus iteration and projection
(eq. 51–53). The §1 examples are tagged in docstring prose with
cell labels rather than encoded as separate per-PAC cells (Hungarian
PACs are not yet formalised as a TAM type).
-/

namespace Phenomena.Focus.Studies.Kiss1998

open Fragments.Hungarian.Focus
open Theories.Semantics.Focus.MSMH

-- ============================================================================
-- § 1: Cells (paper eq. 5a/5b minimal pair, eq. 8a/8b, eq. 17b)
-- ============================================================================

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

-- ============================================================================
-- § 2: MSMH instantiation (paper §2, eq. 9)
-- ============================================================================

/-- **MSMH instantiated for Hungarian.** The polymorphic hypothesis
    from `Theories/Semantics/Focus/MeaningStructureMapping.lean`,
    specialised with `FocusConfig.Licensed` as the admissibility
    filter, `position` as the structural projection, and `focusType`
    as the interpretation projection. -/
def HungarianMSMH : Prop :=
  MeaningStructureMapping
    FocusConfig.Licensed
    FocusConfig.position
    FocusConfig.focusType

/-- **Hungarian satisfies the MSMH.** Two licensed configurations with
    the same position must have the same focus type. The proof
    reduces to `licensed_position_determines_type`: the Hungarian
    fragment encodes the position–type pairing in `Licensed`, so
    sameness of position transports along the pairing. -/
theorem hungarian_satisfies_MSMH : HungarianMSMH := by
  intro c₁ c₂ h₁ h₂ hpos
  obtain ⟨hpos₁, _⟩ := h₁
  obtain ⟨hpos₂, _⟩ := h₂
  have heq : positionFor c₁.focusType = positionFor c₂.focusType := by
    rw [← hpos₁, ← hpos₂]; exact hpos
  cases ft₁ : c₁.focusType <;> cases ft₂ : c₂.focusType <;>
    rw [ft₁, ft₂] at heq <;> simp [positionFor] at heq

/-- **Position determines exhaustivity for licensed Hungarian focus.**
    Composition of the position–type and type–exhaustivity
    equivalences. The semantic payoff of the §2 structural
    distinction. -/
theorem preverbal_iff_exhaustive (c : FocusConfig) (h : c.Licensed) :
    c.position = .preverbal ↔ c.focusType.IsExhaustive := by
  rw [licensed_position_determines_type c h]
  cases c.focusType <;> simp [FocusType.IsExhaustive]

-- ============================================================================
-- § 3: Distributional Restriction Cells (paper §3, eq. 17)
-- ============================================================================

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

-- ============================================================================
-- § 4: Cell Properties
-- ============================================================================

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

end Phenomena.Focus.Studies.Kiss1998
