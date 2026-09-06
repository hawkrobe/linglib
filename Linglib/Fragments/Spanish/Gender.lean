import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Category.Noun.Basic

/-!
# Spanish Noun Gender
[butt-benjamin-2019] [kramer-2015] [kramer-2020]
[harris-1991]

Spanish has two genders, masculine and feminine
([butt-benjamin-2019] §1.1). Per [butt-benjamin-2019] §1.2,
Group A: nouns referring to humans + a few well-known animals get
natural gender; per §1.3, Group B (lifeless things, plants, other
animals) get arbitrary gender. Per §1.2.11, a small set of common-gender
nouns (e.g. *persona*, *víctima*, *ángel*) take fixed gender regardless
of referent.

## Theory-neutral data layer

Each entry is a `GenderedNoun` over the two controller genders: its
`gender` is the agreement-trigger fact (verified against
[butt-benjamin-2019] §1.2-1.3), and `isNaturalGender` records whether
that gender is semantically motivated by the referent's biological sex.
False for inanimates, for non-natural-gender animals (cf. §1.3.1), and
for the §1.2.11 fixed-gender common-gender exceptions (*persona*,
*ángel*).

These two fields suffice to project every entry's structural analysis
under [kramer-2015] Ch. 6's Set-1 DM categorizer (the projection
lives in `Studies/Kramer2020.lean`); they also support
[harris-1991]'s lexical-rule analysis directly (Harris's [FEMALE]
and [HUMAN] features map onto the gender and the natural-gender
inference).

## Per-entry verification

Entries explicitly named in [kramer-2015]: *hombre*, *mujer*,
*niño*, *niña*, *mesa*, *cama*, *persona*, *libro*, *soldado*,
*estudiante*, *artista*. Other entries (*rey/reina/gato/gata,
silla/casa/puerta/ventana, zapato/coche/árbol/cielo/vaso, ángel*) are
extrapolations from Kramer's framework, anchored on the
textbook-consensus genders documented in [butt-benjamin-2019].
-/

namespace Spanish.Gender

/-- Spanish's two controller genders — the carrier of its `Gender.System`
    ([corbett-1991]; [kramer-2015]). -/
inductive Value where
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

/-- The comparative label of each gender. -/
def Value.toLabel : Value → Gender
  | .masc => .masculine
  | .fem => .feminine

instance : HasGender Value := ⟨λ g => genderOf g.toLabel⟩

/-- A Spanish noun: its gender, the agreement it takes ([butt-benjamin-2019]),
    and whether that gender follows the referent's sex — false for
    inanimates, for non-natural-gender animals, and for the §1.2.11
    common-gender exceptions (*persona* feminine for any sex; *ángel*
    masculine for any sex). -/
abbrev Noun := GenderedNoun Value

-- ============================================================================
-- § 1: Natural-Gender Nouns (Group A, [butt-benjamin-2019] §1.2)
-- ============================================================================

def hombre : Noun := ⟨⟨"hombre", "man"⟩, .masc, true⟩
def mujer : Noun := ⟨⟨"mujer", "woman"⟩, .fem, true⟩
def niño : Noun := ⟨⟨"niño", "boy"⟩, .masc, true⟩
def niña : Noun := ⟨⟨"niña", "girl"⟩, .fem, true⟩
def rey : Noun := ⟨⟨"rey", "king"⟩, .masc, true⟩
def reina : Noun := ⟨⟨"reina", "queen"⟩, .fem, true⟩
def gato : Noun := ⟨⟨"gato", "cat.M"⟩, .masc, true⟩
def gata : Noun := ⟨⟨"gata", "cat.F"⟩, .fem, true⟩

-- ============================================================================
-- § 2: Arbitrary Feminines (Group B, [butt-benjamin-2019] §1.3)
-- ============================================================================

def mesa : Noun := ⟨⟨"mesa", "table"⟩, .fem, false⟩
def silla : Noun := ⟨⟨"silla", "chair"⟩, .fem, false⟩
def casa : Noun := ⟨⟨"casa", "house"⟩, .fem, false⟩
def puerta : Noun := ⟨⟨"puerta", "door"⟩, .fem, false⟩
def ventana : Noun := ⟨⟨"ventana", "window"⟩, .fem, false⟩
def cama : Noun := ⟨⟨"cama", "bed"⟩, .fem, false⟩
/-- *persona* 'person': common-gender noun ([butt-benjamin-2019]
    §1.2.11) — feminine regardless of referent's sex. The famous
    [kramer-2015] §6.2 exception: human-denoting noun with
    structurally arbitrary feminine gender. `isNaturalGender = false`
    captures that the gender does NOT come from biological sex (even
    though referent is human). -/
def persona : Noun := ⟨⟨"persona", "person"⟩, .fem, false⟩

-- ============================================================================
-- § 3: Default Masculines (Group B, [butt-benjamin-2019] §1.3)
-- ============================================================================

def libro : Noun := ⟨⟨"libro", "book"⟩, .masc, false⟩
def zapato : Noun := ⟨⟨"zapato", "shoe"⟩, .masc, false⟩
def coche : Noun := ⟨⟨"coche", "car"⟩, .masc, false⟩
def árbol : Noun := ⟨⟨"árbol", "tree"⟩, .masc, false⟩
def cielo : Noun := ⟨⟨"cielo", "sky"⟩, .masc, false⟩
def vaso : Noun := ⟨⟨"vaso", "glass"⟩, .masc, false⟩
/-- *ángel* 'angel': common-gender noun ([butt-benjamin-2019]
    §1.2.11) — masculine for any sex. Companion to *persona*: the
    masculine fixed-gender exception. `isNaturalGender = false`. -/
def ángel : Noun := ⟨⟨"ángel", "angel"⟩, .masc, false⟩

-- ============================================================================
-- § 4: Same-Root Nominals ([kramer-2020] §2.2.3)
-- ============================================================================

/-- Same-root nominals: a single root that surfaces as either masculine
    or feminine depending on the referent's sex. Empirically polymorphic
    in gender (one form, two genders), so a noun entry without a fixed
    gender. The DM analysis (combination with i[+FEM] vs i[−FEM]) lives
    in `Studies/Kramer2020.lean`. -/
abbrev SameRootEntry := _root_.Noun

def soldado : SameRootEntry := ⟨"soldado", "soldier"⟩
def estudiante : SameRootEntry := ⟨"estudiante", "student"⟩
def artista : SameRootEntry := ⟨"artista", "artist"⟩

-- ============================================================================
-- § 5: Inventory
-- ============================================================================

def naturalFemNouns : List Noun :=
  [mujer, niña, reina, gata]

def naturalMascNouns : List Noun :=
  [hombre, niño, rey, gato]

def arbitraryFemNouns : List Noun :=
  [mesa, silla, casa, puerta, ventana, cama, persona]

def defaultMascNouns : List Noun :=
  [libro, zapato, coche, árbol, cielo, vaso, ángel]

def allNouns : List Noun :=
  naturalFemNouns ++ naturalMascNouns ++ arbitraryFemNouns ++ defaultMascNouns

def sameRootNouns : List SameRootEntry :=
  [soldado, estudiante, artista]

-- ============================================================================
-- § 6: Gender System (`Gender.System` instantiation)
-- ============================================================================

/-- Adjectival concord exponents: the *-o* vs *-a* desinence contrast
    ([butt-benjamin-2019]). Evidence type for `Gender.Faithful`. -/
inductive Concord where
  | o
  | a
  deriving DecidableEq, Repr

/-- Per-gender adjectival concord. -/
def Value.concord : Value → Concord
  | .masc => .o
  | .fem  => .a

/-- The Spanish gender system over its own carrier: full comparative
    labelling; masculine is the morphosyntactic default (plain-*n* roots
    surface masculine — the underspecified determiner of
    [kramer-2020] (25), at `Kramer2020.determiner_iMasc_eq_plain`). -/
def system : Gender.System Value where
  label := λ g => some g.toLabel
  default := .masc

/-- The assigned system: every noun gets its controller gender. -/
def assigned : Gender.System.Assigned Noun Value := { system with assign := (·.gender) }

/-- The carrier is faithful to the adjectival concord evidence: *-o* vs
    *-a* distinguishes the two genders. [corbett-1991]'s
    genders-are-agreement-classes criterion. -/
theorem faithful_concord : Function.Injective Value.concord := by decide

/-- [kramer-2015]'s (7ii) / [dahl-2000]'s generalization instantiated:
    the natural-gender nouns (Group A) form a semantic core, their gender
    being the referent-sex classification (that is what `isNaturalGender`
    asserts). *persona* and *ángel* are outside the core
    (`isNaturalGender = false`), so the fixed-gender exceptions do not
    disturb the factoring. -/
theorem assigned_semanticCore :
    assigned.SemanticCore {n | n.isNaturalGender = true} (·.gender) :=
  ⟨⟨mujer, rfl⟩, λ _ _ _ _ h => h⟩

end Spanish.Gender
