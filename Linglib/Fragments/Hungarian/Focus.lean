/-!
# Hungarian Focus and the Identificational/Information Distinction
@cite{kiss-1998}

@cite{kiss-1998} argues that two structurally distinct focus types must
be distinguished in Hungarian:

1. **Identificational focus** moves to the specifier of a left-peripheral
   functional projection (Spec,FP), surfacing in the **immediately
   preverbal** position. It expresses *exhaustive identification* —
   selecting the maximal subset of contextually-given alternatives for
   which the predicate holds.
2. **Information focus** stays VP-internal in the **postverbal**
   domain, marked only by pitch accent. It conveys nonpresupposed
   information without exhaustivity.

The two are *not* interpretational variants of one operator: they
occupy distinct structural positions and trigger distinct semantic
operations. This is the structural basis for the Hungarian–English
parallel @cite{kiss-1998} draws (English clefts realise
identificational focus) and the typological pivot for the
@cite{hartmann-zimmermann-2007} debate (Hausa is the *negative*
counterpart: in-situ position does not block focus interpretation).

Distributional restrictions (paper §3): identificational focus is
barred from universal quantifiers (*minden* 'every'), additive
*also*-phrases (*X+is*) and *even*-phrases (*még…is*), and the
existential *valami/valaki* 'somebody/something'. *Csak* 'only'-phrases
are obligatorily realised as identificational foci. The minimal class
encoding here lets us state and prove these restrictions as theorems
rather than stipulate them inline.

`FocusConfig.Licensed` is propositional (`Prop` with `Decidable`).
The structure carries a position, a focus type, and a constituent
class; licensing combines the position–type pairing with the §3
class-based distributional facts. Smart constructors `mkIdentificational`
and `mkInformation` package the position–type pairing automatically;
ill-licensed combinations are constructed directly to demonstrate the
predicate has bite.
-/

namespace Fragments.Hungarian.Focus

-- ============================================================================
-- § 1: Structural Position (paper §1, §2)
-- ============================================================================

/-- The two structural positions for focused constituents in Hungarian.
    `preverbal` = Spec,FP (the immediately preverbal identificational
    focus slot, see @cite{kiss-1998} eq. 5a); `postverbal` = VP-internal
    in situ (the information focus position, see eq. 5b). -/
inductive Position where
  | preverbal
  | postverbal
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- § 2: Focus Type (paper §1, eq. 9)
-- ============================================================================

/-- The two focus types @cite{kiss-1998} distinguishes. The
    *identificational* type carries an exhaustivity entailment;
    *information* focus does not. The eq. 5a vs 5b minimal pair is
    the empirical pivot. -/
inductive FocusType where
  | identificational
  | information
  deriving DecidableEq, Repr, Inhabited

/-- Whether the focus type carries an exhaustivity entailment. Direct
    consequence of @cite{kiss-1998} §2 (the Szabolcsi–Farkas test).
    Stated at the `FocusType` level — exhaustivity is intrinsic to the
    type, independent of any particular configuration. -/
def FocusType.IsExhaustive : FocusType → Prop
  | .identificational => True
  | .information      => False

instance (t : FocusType) : Decidable t.IsExhaustive := by
  cases t <;> simp [FocusType.IsExhaustive] <;> infer_instance

-- ============================================================================
-- § 3: Constituent Class (paper §3 — distributional restrictions)
-- ============================================================================

/-- Coarse classification of the focused constituent for the §3
    distributional facts. `regular` covers ordinary DPs that can occur
    as either focus type; `universal` is the *minden 'every' / X+is
    'also' / még…is 'even'* class barred from identificational focus
    (paper eq. 17b–d); `onlyPhrase` is *csak X 'only X'*, obligatorily
    identificational; `someIndef` is *valami/valaki 'somebody/something'*,
    barred from both focus positions (paper eq. 17e). -/
inductive ConstituentClass where
  | regular
  | universal
  | onlyPhrase
  | someIndef
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- § 4: Focus Configurations
-- ============================================================================

/-- A Hungarian focused-clause configuration. Position, focus type, and
    constituent class are independent fields at the structure level;
    `Licensed` enforces the @cite{kiss-1998} pairings. -/
structure FocusConfig where
  /-- The structural position of the focused constituent. -/
  position  : Position
  /-- The focus type (identificational vs information). -/
  focusType : FocusType
  /-- The lexical class of the focused constituent. -/
  cclass    : ConstituentClass
  deriving DecidableEq, Repr, Inhabited

/-- The canonical position for a given focus type. Paper §2: in
    Hungarian, identificational focus moves to Spec,FP (preverbal);
    information focus stays VP-internal (postverbal). -/
def positionFor : FocusType → Position
  | .identificational => .preverbal
  | .information      => .postverbal

-- ============================================================================
-- § 5: Licensing (paper §1, §2, §3)
-- ============================================================================

/-- A constituent class is **compatible** with a focus type per
    @cite{kiss-1998} §3:
    - `regular` works as either type;
    - `universal` is barred from identificational (eq. 17b–d) but
      can be information focus (eq. 19b);
    - `onlyPhrase` is obligatorily identificational (paper §3 last ¶);
    - `someIndef` is barred from both focus positions (eq. 17e and
      surrounding prose: "*Some-phrases* … cannot function as
      information foci, either"). -/
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

/-- A FocusConfig is **licensed** iff (i) its position is the canonical
    position for its focus type (paper §2) and (ii) its constituent
    class is compatible with that focus type (paper §3). -/
def FocusConfig.Licensed (c : FocusConfig) : Prop :=
  c.position = positionFor c.focusType ∧ c.cclass.compatibleWith c.focusType

instance (c : FocusConfig) : Decidable c.Licensed :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ============================================================================
-- § 6: Smart Constructors
-- ============================================================================

/-- Smart constructor for a preverbal identificational focus. The
    position–type pairing is automatic; the caller supplies the
    constituent class and a proof of compatibility. -/
def mkIdentificational (cc : ConstituentClass)
    (_h : cc.compatibleWith .identificational) : FocusConfig :=
  ⟨.preverbal, .identificational, cc⟩

/-- Smart constructor for a postverbal information focus. The
    position–type pairing is automatic; the caller supplies the
    constituent class and a proof of compatibility. -/
def mkInformation (cc : ConstituentClass)
    (_h : cc.compatibleWith .information) : FocusConfig :=
  ⟨.postverbal, .information, cc⟩

/-- Configurations built by `mkIdentificational` are licensed. -/
theorem mkIdentificational_licensed (cc : ConstituentClass)
    (h : cc.compatibleWith .identificational) :
    (mkIdentificational cc h).Licensed :=
  ⟨rfl, h⟩

/-- Configurations built by `mkInformation` are licensed. -/
theorem mkInformation_licensed (cc : ConstituentClass)
    (h : cc.compatibleWith .information) :
    (mkInformation cc h).Licensed :=
  ⟨rfl, h⟩

-- ============================================================================
-- § 7: Universal Theorems
-- ============================================================================

/-- **Position determines focus type for licensed configurations.** The
    structural pairing in `FocusConfig.Licensed` makes the focus type a
    function of the position. This is the load-bearing biconditional
    that lets the Meaning-Structure Mapping Hypothesis be *proved* for
    Hungarian (vs *refuted* for Hausa). -/
theorem licensed_position_determines_type (c : FocusConfig)
    (h : c.Licensed) :
    (c.position = .preverbal ↔ c.focusType = .identificational) := by
  obtain ⟨hpos, _⟩ := h
  unfold positionFor at hpos
  cases ht : c.focusType <;> rw [ht] at hpos <;> simp_all

/-- **csak-phrases must be identificational foci** (paper §3 last
    paragraph, eq. 51–53). Any licensed configuration with an
    `onlyPhrase` constituent has identificational focus type. -/
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

/-- ***valami/valaki* can never be focused** (paper eq. 17e and
    surrounding prose). No licensed configuration has an `someIndef`
    constituent — neither focus type accepts it. -/
theorem someIndef_never_licensed (c : FocusConfig) (h : c.Licensed) :
    c.cclass ≠ .someIndef := by
  intro hcc
  obtain ⟨_, hcompat⟩ := h
  rw [hcc] at hcompat
  cases hft : c.focusType <;>
    rw [hft] at hcompat <;>
    simp [ConstituentClass.compatibleWith] at hcompat

end Fragments.Hungarian.Focus
