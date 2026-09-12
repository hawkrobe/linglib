/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Relation.FactorsThroughOn
import Linglib.Semantics.Focus.Control

/-!
# É. Kiss (1998): Identificational Focus versus Information Focus

This file formalizes [kiss-1998]'s distinction between identificational focus, which moves to
the specifier of a functional projection immediately before the verb and expresses exhaustive
identification, and information focus, which stays in situ after the verb and merely conveys
new information. On licensed configurations the position determines the focus type
(`position_determines_focusType`), and the distributional restrictions of §3 follow from the
compatibility of a constituent's class with a focus type: universals and *is*-phrases are
barred from identificational focus, *csak*-phrases are obligatorily identificational, and
*valami* and *valaki* are barred from both (`FocusConfig.Licensed`). Identificational focus is
the prejacent exhaustified over the resolved alternatives, the substrate's `Focus.onlyVia`, and
the coordination test and the dialogue test by which the paper diagnoses exhaustivity come out
as theorems on the hat-and-coat scenario of its examples (`szabolcsi_test`, `farkas_test`).

## Implementation notes

* `Position`, `FocusType`, `ConstituentClass` and `FocusConfig` are the paper's analytical
  classification of Hungarian focus, not consensus typology, so they live here rather than in
  a Fragment.

## TODO

* §4 scope, §5.2 the cleft as the English realisation of identificational focus, §7 focus
  iteration and projection, and §9 the [+exhaustive] and [+contrastive] parametrisation
  across Italian, Romanian, Catalan, Greek, Arabic and Finnish.

## References

* [kiss-1998]
-/

namespace Kiss1998

/-! ### Structural position and focus type (§1, §2) -/

/-- The two structural positions of a focused constituent in Hungarian: `preverbal` is
Spec,FP, the identificational slot, `postverbal` is in situ inside the VP. -/
inductive Position
  | preverbal
  | postverbal
  deriving DecidableEq, Repr

/-- The two focus types: identificational focus carries an exhaustivity entailment,
information focus does not. -/
inductive FocusType
  | identificational
  | information
  deriving DecidableEq, Repr, Inhabited

/-- Whether the focus type carries an exhaustivity entailment (§2). -/
def FocusType.IsExhaustive (t : FocusType) : Prop := t = .identificational

/-- The canonical position of a focus type (§2): identificational focus moves to Spec,FP,
information focus stays postverbal. -/
def positionFor : FocusType → Position
  | .identificational => .preverbal
  | .information => .postverbal

/-! ### Constituent classes and licensing (§3) -/

/-- The classes of focused constituent behind the distributional facts of §3: `regular` DPs
occur as either focus type, `universal` is the *minden*, *X is* and *még … is* class barred from
identificational focus (17b–d), `onlyPhrase` is *csak X*, obligatorily identificational, and
`someIndef` is *valami* and *valaki*, barred from both (17e). -/
inductive ConstituentClass
  | regular
  | universal
  | onlyPhrase
  | someIndef
  deriving DecidableEq, Repr

/-- Class–type compatibility (§3). -/
def ConstituentClass.compatibleWith : ConstituentClass → FocusType → Prop
  | .regular, _ => True
  | .universal, .identificational => False
  | .universal, .information => True
  | .onlyPhrase, .identificational => True
  | .onlyPhrase, .information => False
  | .someIndef, _ => False

instance (c : ConstituentClass) (t : FocusType) : Decidable (c.compatibleWith t) := by
  cases c <;> cases t <;> unfold ConstituentClass.compatibleWith <;> infer_instance

/-- A Hungarian focused-clause configuration. -/
structure FocusConfig where
  /-- The structural position of the focused constituent. -/
  position : Position
  /-- The focus type. -/
  focusType : FocusType
  /-- The class of the focused constituent. -/
  cclass : ConstituentClass
  deriving DecidableEq, Repr

/-- A configuration is licensed when its position is canonical for its focus type (§2) and
its constituent class is compatible with that type (§3). -/
def FocusConfig.Licensed (c : FocusConfig) : Prop :=
  c.position = positionFor c.focusType ∧ c.cclass.compatibleWith c.focusType

instance (c : FocusConfig) : Decidable c.Licensed := inferInstanceAs (Decidable (_ ∧ _))

/-- On licensed configurations the preverbal position is the identificational focus. -/
theorem licensed_position_determines_type {c : FocusConfig} (h : c.Licensed) :
    c.position = .preverbal ↔ c.focusType = .identificational := by
  obtain ⟨p, t, _⟩ := c
  cases p <;> cases t <;> simp_all [FocusConfig.Licensed, positionFor]

/-- *csak*-phrases are identificational foci (§3). -/
theorem onlyPhrase_forces_identificational {c : FocusConfig} (h : c.Licensed)
    (hcc : c.cclass = .onlyPhrase) : c.focusType = .identificational := by
  obtain ⟨_, t, _⟩ := c
  subst hcc
  cases t <;> simp_all [FocusConfig.Licensed, ConstituentClass.compatibleWith]

/-- *valami* and *valaki* can never be focused (17e): no licensed configuration has a
`someIndef` constituent. -/
theorem someIndef_never_licensed {c : FocusConfig} (h : c.Licensed) : c.cclass ≠ .someIndef := by
  obtain ⟨_, t, _⟩ := c
  rintro rfl
  cases t <;> exact (h.2 : False).elim

/-! ### Position determines focus type (§2) -/

/-- The factor witnessing §2: the focus type as a function of the position. -/
def typeOfPosition : Position → FocusType
  | .preverbal => .identificational
  | .postverbal => .information

/-- On licensed configurations the focus type is `typeOfPosition` of the position. -/
theorem focusType_eqOn_typeOfPosition :
    Set.EqOn FocusConfig.focusType (typeOfPosition ∘ FocusConfig.position) {c | c.Licensed} := by
  rintro c ⟨hpos, -⟩
  rw [Function.comp_apply, hpos]
  cases c.focusType <;> rfl

/-- Position determines focus type on licensed configurations, the structural claim of §2. -/
theorem position_determines_focusType :
    Function.FactorsThroughOn FocusConfig.focusType FocusConfig.position {c | c.Licensed} :=
  Function.factorsThroughOn_iff_exists_eqOn.mpr ⟨typeOfPosition, focusType_eqOn_typeOfPosition⟩

/-- The semantic payoff of §2: on licensed configurations the preverbal position is the
exhaustive one. -/
theorem preverbal_iff_exhaustive {c : FocusConfig} (h : c.Licensed) :
    c.position = .preverbal ↔ c.focusType.IsExhaustive :=
  licensed_position_determines_type h

/-! ### The paper's configurations, (8), (17b) and (19b) -/

/-- (8a) *Mari egy kalapot nézett ki magának* 'It was a HAT that Mary picked for herself':
a regular DP in preverbal identificational focus, the configuration also of (5a). -/
def preverbalHat : FocusConfig := ⟨.preverbal, .identificational, .regular⟩

/-- (8b) *Mari ki nézett magának EGY KALAPOT* 'Mary picked for herself A HAT': a regular DP
in postverbal information focus, the configuration also of (5b). -/
def postverbalHat : FocusConfig := ⟨.postverbal, .information, .regular⟩

/-- (17b) \**Mari minden kalapot nézett ki magának*: a universal in the identificational
position. -/
def starredUniversal : FocusConfig := ⟨.preverbal, .identificational, .universal⟩

/-- (19b) *Minden kollégámat meg hívtam* 'I invited EVERY COLLEAGUE OF MINE': a universal as
postverbal information focus. -/
def universalInformation : FocusConfig := ⟨.postverbal, .information, .universal⟩

/-- The minimal pair (8) and the universal of (19b) are licensed; a universal in the
identificational position (17b), *csak X* as information focus and *valami* in either position
are not. -/
theorem licensing :
    preverbalHat.Licensed ∧ postverbalHat.Licensed ∧ universalInformation.Licensed ∧
      ¬ starredUniversal.Licensed ∧
      ¬ (FocusConfig.mk .postverbal .information .onlyPhrase).Licensed ∧
      ¬ (FocusConfig.mk .preverbal .identificational .someIndef).Licensed ∧
      ¬ (FocusConfig.mk .postverbal .information .someIndef).Licensed := by
  decide

/-! ### Exhaustive identification (§2)

The hat-and-coat model of the paper's test sentences, (8) and (12)–(15). Identificational
focus is the prejacent exhaustified over the resolved alternatives, a covert obligatory
`Focus.onlyVia`, and information focus is the bare prejacent. -/

open Focus (onlyVia)

/-- Worlds tracking what Mary picked for herself. -/
inductive HatWorld
  | hatOnly
  | coatOnly
  | both
  | neither
  deriving DecidableEq, Repr

/-- Mary picked a hat, at least. -/
def pickedHat : Set HatWorld := {.hatOnly, .both}

/-- Mary picked a coat, at least. -/
def pickedCoat : Set HatWorld := {.coatOnly, .both}

/-- The resolved atomic alternatives of the picking scenario. -/
def hatAlts : Focus.Interpretation.PropFocusValue HatWorld := {pickedHat, pickedCoat}

/-- Identificational focus: the prejacent exhaustified over the resolved alternatives, the
exhaustive subset of the relevant set of §2. -/
def identificational (p : Set HatWorld) : Set HatWorld := p ∩ onlyVia hatAlts p

/-- The identificational meaning of (8a) is that Mary picked exactly a hat. -/
theorem identificational_hat_eq : identificational pickedHat = {HatWorld.hatOnly} := by
  ext w
  constructor
  · rintro ⟨hp, hw⟩
    have hcoat := hw pickedCoat (Or.inr rfl)
    cases w with
    | hatOnly => rfl
    | coatOnly => exact absurd hp (λ h => h.elim nofun nofun)
    | both =>
      have heq : pickedCoat = pickedHat := hcoat (Or.inr rfl)
      have hmem : HatWorld.coatOnly ∈ pickedHat :=
        heq ▸ (show HatWorld.coatOnly ∈ pickedCoat from Or.inl rfl)
      exact absurd hmem (λ h => h.elim nofun nofun)
    | neither => exact absurd hp (λ h => h.elim nofun nofun)
  · rintro rfl
    refine ⟨Or.inl rfl, λ q hq hwq => ?_⟩
    rcases hq with rfl | rfl
    · rfl
    · exact absurd hwq (λ h => h.elim nofun nofun)

/-- The coordination test, (12) against (13): the identificational *a hat* contradicts the
hat-and-coat content, while the information-focus *a hat* is entailed by it. -/
theorem szabolcsi_test :
    identificational pickedHat ∩ (pickedHat ∩ pickedCoat) = ∅ ∧
      pickedHat ∩ pickedCoat ⊆ pickedHat := by
  refine ⟨?_, Set.inter_subset_left⟩
  rw [identificational_hat_eq]
  ext w
  constructor
  · rintro ⟨rfl, -, hcoat⟩
    exact absurd hcoat (λ h => h.elim nofun nofun)
  · exact λ h => h.elim

/-- The dialogue test, (15): where Mary picked a coat too, the identificational claim is false,
so the reply *No, she picked a coat, too* denies its exhaustivity, while the information-focus
claim is true and the denial is out of place. -/
theorem farkas_test :
    HatWorld.both ∉ identificational pickedHat ∧ HatWorld.both ∈ pickedHat := by
  refine ⟨?_, Or.inr rfl⟩
  rw [identificational_hat_eq]
  exact nofun

/-- The denotation of each focus type for the hat prejacent. -/
def semanticsOf : FocusType → Set HatWorld
  | .identificational => identificational pickedHat
  | .information => pickedHat

/-- Position determines the semantics: the preverbal slot's meaning is exhaustified, the
postverbal one's is plain. -/
theorem position_determines_exhaustification :
    semanticsOf (typeOfPosition .preverbal) = {HatWorld.hatOnly} ∧
      semanticsOf (typeOfPosition .postverbal) = pickedHat :=
  ⟨identificational_hat_eq, rfl⟩

end Kiss1998
