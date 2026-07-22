/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Logic.FactorsThroughOn
import Linglib.Semantics.Focus.Control

/-!
# Hungarian preverbal/postverbal focus contrast

Formalises [kiss-1998]: identificational focus moves to the immediately
preverbal Spec,FP and expresses exhaustive identification; information
focus stays postverbal and carries no exhaustivity. Position determines
focus type on licensed configurations, and the §3 distributional
restrictions (universals, *csak*-phrases, *valami/valaki*) follow from
class–type compatibility.

## Implementation notes

The apparatus (`Position`, `FocusType`, `ConstituentClass`,
`FocusConfig`) is Kiss's analytical classification, not consensus
typology, so it lives here rather than in a Fragment.

Kiss's exhaustivity claim has been substantially revised in later work
(Onea & Beaver 2011, Horváth 2010, Wedgwood 2005); the theorems
formalise the 1998 position without adjudicating.

The factor-through schema (`Function.FactorsThroughOn`) is instantiated
for Hausa in `HartmannZimmermann2007.lean`, where it is *refuted*.

## TODO

* §4 scope (identificational focus binds variables).
* §5.2 cleft realisation in English.
* §9 cross-linguistic feature typology for Italian, Romanian,
  Catalan, Greek, Arabic, Finnish.
* §7 focus iteration and projection (eq. 51-53).
-/

namespace Kiss1998

/-! ### Structural position and focus type (§1, §2) -/

/-- The two structural positions for focused constituents in Hungarian:
`preverbal` = Spec,FP (the identificational slot), `postverbal` =
VP-internal in situ. -/
inductive Position where
  | preverbal
  | postverbal
  deriving DecidableEq, Repr, Inhabited

/-- The two focus types: *identificational* carries an exhaustivity
entailment, *information* does not. -/
inductive FocusType where
  | identificational
  | information
  deriving DecidableEq, Repr, Inhabited

/-- Whether the focus type carries an exhaustivity entailment (§2, the
Szabolcsi–Farkas test). -/
def FocusType.IsExhaustive : FocusType → Prop
  | .identificational => True
  | .information      => False

instance (t : FocusType) : Decidable t.IsExhaustive := by
  cases t <;> simp [FocusType.IsExhaustive] <;> infer_instance

/-! ### Constituent classes and licensing (§3) -/

/-- Coarse classification of the focused constituent for the §3
distributional facts: `regular` DPs occur as either type; `universal`
covers the *minden / X+is / még…is* class barred from identificational
focus (17b–d); `onlyPhrase` is *csak X*, obligatorily identificational;
`someIndef` is *valami/valaki*, barred from both (17e). -/
inductive ConstituentClass where
  | regular
  | universal
  | onlyPhrase
  | someIndef
  deriving DecidableEq, Repr, Inhabited

/-- A Hungarian focused-clause configuration; `Licensed` enforces the
position–type and class–type pairings. -/
structure FocusConfig where
  /-- The structural position of the focused constituent. -/
  position  : Position
  /-- The focus type (identificational vs information). -/
  focusType : FocusType
  /-- The lexical class of the focused constituent. -/
  cclass    : ConstituentClass
  deriving DecidableEq, Repr, Inhabited

/-- The canonical position for a focus type (§2): identificational
moves to Spec,FP, information stays postverbal. -/
def positionFor : FocusType → Position
  | .identificational => .preverbal
  | .information      => .postverbal

/-- Class–type compatibility (§3): `universal` is barred from
identificational focus (17b–d); `onlyPhrase` is "obligatorily realized
as identificational" (§3); `someIndef` is barred from both — starred
identificationally (17e) and "cannot function as information foci,
either" (§3). -/
def ConstituentClass.compatibleWith : ConstituentClass → FocusType → Prop
  | .regular,    _                  => True
  | .universal,  .identificational  => False
  | .universal,  .information       => True
  | .onlyPhrase, .identificational  => True
  | .onlyPhrase, .information       => False
  | .someIndef,  _                  => False

instance (c : ConstituentClass) (t : FocusType) :
    Decidable (c.compatibleWith t) := by
  cases c <;> cases t <;> simp [ConstituentClass.compatibleWith] <;>
    infer_instance

/-- A configuration is licensed iff its position is canonical for its
focus type (§2) and its constituent class is compatible with that type
(§3). -/
def FocusConfig.Licensed (c : FocusConfig) : Prop :=
  c.position = positionFor c.focusType ∧ c.cclass.compatibleWith c.focusType

instance (c : FocusConfig) : Decidable c.Licensed :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A preverbal identificational focus over a compatible class. -/
def mkIdentificational (cc : ConstituentClass)
    (_h : cc.compatibleWith .identificational) : FocusConfig :=
  ⟨.preverbal, .identificational, cc⟩

/-- A postverbal information focus over a compatible class. -/
def mkInformation (cc : ConstituentClass)
    (_h : cc.compatibleWith .information) : FocusConfig :=
  ⟨.postverbal, .information, cc⟩

theorem mkIdentificational_licensed (cc : ConstituentClass)
    (h : cc.compatibleWith .identificational) :
    (mkIdentificational cc h).Licensed :=
  ⟨rfl, h⟩

theorem mkInformation_licensed (cc : ConstituentClass)
    (h : cc.compatibleWith .information) :
    (mkInformation cc h).Licensed :=
  ⟨rfl, h⟩

/-- Position determines focus type on licensed configurations — the
biconditional behind the Meaning-Structure Mapping verdict for
Hungarian. -/
theorem licensed_position_determines_type (c : FocusConfig)
    (h : c.Licensed) :
    (c.position = .preverbal ↔ c.focusType = .identificational) := by
  obtain ⟨hpos, _⟩ := h
  unfold positionFor at hpos
  cases ht : c.focusType <;> rw [ht] at hpos <;> simp_all

/-- *csak*-phrases must be identificational foci (§3). -/
theorem onlyPhrase_forces_identificational (c : FocusConfig)
    (h : c.Licensed) (hcc : c.cclass = .onlyPhrase) :
    c.focusType = .identificational := by
  obtain ⟨_, hcompat⟩ := h
  rw [hcc] at hcompat
  cases hft : c.focusType
  case identificational => rfl
  case information =>
    rw [hft] at hcompat
    simp [ConstituentClass.compatibleWith] at hcompat

/-- *valami/valaki* can never be focused (17e): no licensed
configuration has a `someIndef` constituent. -/
theorem someIndef_never_licensed (c : FocusConfig) (h : c.Licensed) :
    c.cclass ≠ .someIndef := by
  intro hcc
  obtain ⟨_, hcompat⟩ := h
  rw [hcc] at hcompat
  cases hft : c.focusType <;>
    rw [hft] at hcompat <;>
    simp [ConstituentClass.compatibleWith] at hcompat

/-! ### Cells (§1, eq. 5a/5b, 8a/8b, 17b, 19b) -/

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

/-! ### Position determines focus type (paper §2)

Among licensed configurations, `focusType` factors through `position`.
The same schema is instantiated for Hausa in
`HartmannZimmermann2007.lean` (with `cfg.strategy` and `pragType`) and
*refuted* there — a difference of verdict on one shared predicate. -/

/-- The factor witnessing §2: focus type as a function of position. -/
def typeOfPosition : Position → FocusType
  | .preverbal  => .identificational
  | .postverbal => .information

/-- On licensed configurations the focus type is literally
`typeOfPosition` of the position — the §2 claim in factored form. -/
theorem focusType_eqOn_typeOfPosition :
    Set.EqOn FocusConfig.focusType
      (typeOfPosition ∘ FocusConfig.position) {c | c.Licensed} := by
  rintro c ⟨hpos, -⟩
  rw [Function.comp_apply, hpos]
  cases c.focusType <;> rfl

/-- Position determines focus type on licensed configurations: Kiss's
§2 structural claim, derived from the explicit factor. -/
theorem position_determines_focusType :
    Function.FactorsThroughOn
      FocusConfig.focusType FocusConfig.position {c | c.Licensed} :=
  Function.factorsThroughOn_iff_exists_eqOn.mpr
    ⟨typeOfPosition, focusType_eqOn_typeOfPosition⟩

/-- Position equivalence with exhaustivity: composition of the
position-type and type-exhaustivity equivalences. The semantic payoff
of Kiss's §2 structural distinction. -/
theorem preverbal_iff_exhaustive (c : FocusConfig) (h : c.Licensed) :
    c.position = .preverbal ↔ c.focusType.IsExhaustive := by
  rw [licensed_position_determines_type c h]
  cases c.focusType <;> simp [FocusType.IsExhaustive]

/-! ### Distributional restrictions (paper §3, eq. 17) -/

/-- Universal quantifiers cannot be identificational foci (17b):
`starred_universal_identificational` fails licensing. -/
theorem starred_universal_identificational_not_licensed :
    ¬ starred_universal_identificational.Licensed := by decide

/-- Universal quantifiers can be information foci (19b): the class
barred preverbally is admissible postverbally. -/
theorem universal_information_licensed : universal_information.Licensed :=
  mkInformation_licensed _ _

/-- The *csak X* construction is obligatorily identificational (§3):
the information-focus alternative is ill-licensed. -/
theorem only_information_not_licensed :
    ¬ (FocusConfig.mk .postverbal .information .onlyPhrase).Licensed := by
  decide

/-- Indefinite *valami/valaki* is barred from both focus types (17e). -/
theorem someIndef_neither_licensed :
    ¬ (FocusConfig.mk .preverbal .identificational .someIndef).Licensed ∧
    ¬ (FocusConfig.mk .postverbal .information .someIndef).Licensed := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### Cell properties -/

theorem preverbal_identificational_licensed :
    preverbal_identificational.Licensed :=
  mkIdentificational_licensed _ _

theorem postverbal_information_licensed :
    postverbal_information.Licensed :=
  mkInformation_licensed _ _

/-- The eq. (5a/5b) minimal pair: same constituent, different
positions, different focus types — both licensed. -/
theorem minimal_pair_distinct_types :
    preverbal_hat.focusType ≠ postverbal_hat.focusType := by decide

/-! ### Exhaustive identification semantics (§2)

The hat/coat model of the paper's own test sentences ((8), (12)–(15)).
Identificational focus is the prejacent exhaustified over the resolved
alternatives — covert obligatory `Focus.onlyVia` — while
information focus is the bare prejacent. Szabolcsi's coordination test
and Farkas's dialogue test come out as theorems, and position
*determines* whether exhaustification applies: the like-for-like
counterpart of `HartmannZimmermann2007.exhAnswer_eq`, where
exhaustification is strategy-blind. -/

open Focus (onlyVia)

/-- Worlds tracking what Mary picked for herself. -/
inductive HatWorld where
  | hatOnly | coatOnly | both | neither
  deriving DecidableEq, Repr

/-- 'Mary picked a hat' (at least). -/
def pickedHat : Set HatWorld := {.hatOnly, .both}
/-- 'Mary picked a coat' (at least). -/
def pickedCoat : Set HatWorld := {.coatOnly, .both}

/-- The resolved atomic alternatives for the picking scenario. -/
def hatAlts : Focus.Interpretation.PropFocusValue HatWorld :=
  {pickedHat, pickedCoat}

/-- Identificational focus: the prejacent exhaustified over the
resolved alternatives (§2's "exhaustive subset of the relevant set"). -/
def identificational (p : Set HatWorld) : Set HatWorld :=
  p ∩ onlyVia hatAlts p

/-- The identificational meaning of (8a)/(12b) computes to
picked-exactly-a-hat. -/
theorem identificational_hat_eq :
    identificational pickedHat = {HatWorld.hatOnly} := by
  ext w
  constructor
  · rintro ⟨hp, hw⟩
    have hcoat := hw pickedCoat (Or.inr rfl)
    cases w with
    | hatOnly => rfl
    | coatOnly => exact absurd hp (fun h => h.elim nofun nofun)
    | both =>
      have heq : pickedCoat = pickedHat := hcoat (Or.inr rfl)
      have hmem : HatWorld.coatOnly ∈ pickedHat :=
        heq ▸ (show HatWorld.coatOnly ∈ pickedCoat from Or.inl rfl)
      exact absurd hmem (fun h => h.elim nofun nofun)
    | neither => exact absurd hp (fun h => h.elim nofun nofun)
  · rintro rfl
    refine ⟨Or.inl rfl, fun q hq hwq => ?_⟩
    rcases hq with rfl | rfl
    · rfl
    · exact absurd hwq (fun h => h.elim nofun nofun)

/-- **Szabolcsi's coordination test** ((12) vs (13)): the
identificational *a hat* contradicts the *hat-and-coat* content, while
the information-focus *a hat* is entailed by it. -/
theorem szabolcsi_test :
    identificational pickedHat ∩ (pickedHat ∩ pickedCoat) = ∅ ∧
    pickedHat ∩ pickedCoat ⊆ pickedHat := by
  refine ⟨?_, Set.inter_subset_left⟩
  rw [identificational_hat_eq]
  ext w
  constructor
  · rintro ⟨rfl, -, hcoat⟩
    exact absurd hcoat (fun h => h.elim nofun nofun)
  · exact fun h => h.elim

/-- **Farkas's dialogue test** ((15)): in the situation where Mary
picked a coat too, the identificational claim is false (so B's "No,
she picked a coat, too" is a coherent denial of exhaustivity), while
the information-focus claim is true (so the denial is infelicitous). -/
theorem farkas_test :
    HatWorld.both ∉ identificational pickedHat ∧
    HatWorld.both ∈ pickedHat := by
  refine ⟨?_, Or.inr rfl⟩
  rw [identificational_hat_eq]
  exact nofun

/-- The two focus types' denotations for the hat prejacent. -/
def semanticsOf : FocusType → Set HatWorld
  | .identificational => identificational pickedHat
  | .information      => pickedHat

/-- **Position determines the semantics**: the preverbal slot's meaning
is exhaustified, the postverbal one's is plain — Kiss's §2 claim cashed
out through the factor `typeOfPosition`. The Hausa counterpart
(`HartmannZimmermann2007.exhAnswer_eq`) shows exhaustification
*strategy-blind*: the two-verdict contrast at the level of one
semantic operator. -/
theorem position_determines_exhaustification :
    semanticsOf (typeOfPosition .preverbal) = {HatWorld.hatOnly} ∧
    semanticsOf (typeOfPosition .postverbal) = pickedHat :=
  ⟨identificational_hat_eq, rfl⟩

end Kiss1998
