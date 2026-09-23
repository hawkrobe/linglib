module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Noun.Basic

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
[butt-benjamin-2019] §1.2-1.3), and `naturalGender` records whether
that gender is semantically motivated by the referent's gender.
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

@[expose] public section

namespace Spanish.Gender

/-- Spanish's two controller genders — the carrier
    ([corbett-1991]; [kramer-2015]). -/
inductive Value where
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

/-- The comparative label of each gender. -/
def Value.toLabel : Value → Gender
  | .masc => .masculine
  | .fem => .feminine

/-- A Spanish noun: its gender, the agreement it takes ([butt-benjamin-2019]),
    and the gender of its referents where it has one — none for
    inanimates, for non-natural-gender animals, and for the §1.2.11
    common-gender exceptions (*persona* feminine for any referent; *ángel*
    masculine for any referent). -/
abbrev Noun := GenderedNoun Value

-- ============================================================================
-- § 1: Natural-Gender Nouns (Group A, [butt-benjamin-2019] §1.2)
-- ============================================================================

def hombre : Noun := ⟨⟨"hombre", "man"⟩, .masc, some .masculine⟩
def mujer : Noun := ⟨⟨"mujer", "woman"⟩, .fem, some .feminine⟩
def niño : Noun := ⟨⟨"niño", "boy"⟩, .masc, some .masculine⟩
def niña : Noun := ⟨⟨"niña", "girl"⟩, .fem, some .feminine⟩
def rey : Noun := ⟨⟨"rey", "king"⟩, .masc, some .masculine⟩
def reina : Noun := ⟨⟨"reina", "queen"⟩, .fem, some .feminine⟩
def gato : Noun := ⟨⟨"gato", "cat.M"⟩, .masc, some .masculine⟩
def gata : Noun := ⟨⟨"gata", "cat.F"⟩, .fem, some .feminine⟩

-- ============================================================================
-- § 2: Arbitrary Feminines (Group B, [butt-benjamin-2019] §1.3)
-- ============================================================================

def mesa : Noun := ⟨⟨"mesa", "table"⟩, .fem, none⟩
def silla : Noun := ⟨⟨"silla", "chair"⟩, .fem, none⟩
def casa : Noun := ⟨⟨"casa", "house"⟩, .fem, none⟩
def puerta : Noun := ⟨⟨"puerta", "door"⟩, .fem, none⟩
def ventana : Noun := ⟨⟨"ventana", "window"⟩, .fem, none⟩
def cama : Noun := ⟨⟨"cama", "bed"⟩, .fem, none⟩
/-- *persona* 'person': common-gender noun ([butt-benjamin-2019]
    §1.2.11) — feminine regardless of the referent's gender. The famous
    [kramer-2015] §6.2 exception: human-denoting noun with
    structurally arbitrary feminine gender. `naturalGender = none`
    captures that the gender does NOT come from the referent's gender (even
    though referent is human). -/
def persona : Noun := ⟨⟨"persona", "person"⟩, .fem, none⟩

-- ============================================================================
-- § 3: Default Masculines (Group B, [butt-benjamin-2019] §1.3)
-- ============================================================================

def libro : Noun := ⟨⟨"libro", "book"⟩, .masc, none⟩
def zapato : Noun := ⟨⟨"zapato", "shoe"⟩, .masc, none⟩
def coche : Noun := ⟨⟨"coche", "car"⟩, .masc, none⟩
def árbol : Noun := ⟨⟨"árbol", "tree"⟩, .masc, none⟩
def cielo : Noun := ⟨⟨"cielo", "sky"⟩, .masc, none⟩
def vaso : Noun := ⟨⟨"vaso", "glass"⟩, .masc, none⟩
/-- *ángel* 'angel': common-gender noun ([butt-benjamin-2019]
    §1.2.11) — masculine for any referent. Companion to *persona*: the
    masculine fixed-gender exception. `naturalGender = none`. -/
def ángel : Noun := ⟨⟨"ángel", "angel"⟩, .masc, none⟩

-- ============================================================================
-- § 4: Same-Root Nominals ([kramer-2020] §2.2.3)
-- ============================================================================

/-- Same-root nominals: a single root that surfaces as either masculine
    or feminine depending on the referent's gender. Empirically polymorphic
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
-- § 6: Concord evidence
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

/-- The carrier is faithful to the adjectival concord evidence: *-o* vs
    *-a* distinguishes the two genders. [corbett-1991]'s
    genders-are-agreement-classes criterion. -/
theorem faithful_concord : Function.Injective Value.concord := by decide

end Spanish.Gender
