import Linglib.Theories.Morphology.DM.Categorizer

/-!
# Spanish Noun Gender @cite{kramer-2015}

Gender assignments for Spanish nouns, typed by the DM categorizing head
(n) that each noun merges with (@cite{kramer-2015} Ch 6).

Spanish is a **Set 1** language: the four n-types in the [±FEM] dimension are
- n i[+FEM]: natural feminine (female referents)
- n i[−FEM]: natural masculine (male referents)
- n u[+FEM]: arbitrary feminine (no semantic motivation)
- plain n: default (masculine by VI)
-/

namespace Fragments.Spanish.Gender

open Morphology.DM

-- ============================================================================
-- § 1: Spanish Noun with Gender
-- ============================================================================

/-- A Spanish noun annotated with its categorizing head, enabling
    gender derivation from the structural approach. -/
structure SpanishNoun where
  form : String
  gloss : String
  nHead : CatHead
  deriving Repr

-- ============================================================================
-- § 2: Natural Gender Nouns (i[+FEM] / i[−FEM])
-- ============================================================================

def hombre   : SpanishNoun := ⟨"hombre",    "man",      CatHead.n_iMasc⟩
def mujer    : SpanishNoun := ⟨"mujer",     "woman",    CatHead.n_iFem⟩
def niño     : SpanishNoun := ⟨"niño",      "boy",      CatHead.n_iMasc⟩
def niña     : SpanishNoun := ⟨"niña",      "girl",     CatHead.n_iFem⟩
def rey      : SpanishNoun := ⟨"rey",       "king",     CatHead.n_iMasc⟩
def reina    : SpanishNoun := ⟨"reina",     "queen",    CatHead.n_iFem⟩
def gato     : SpanishNoun := ⟨"gato",      "cat.M",    CatHead.n_iMasc⟩
def gata     : SpanishNoun := ⟨"gata",      "cat.F",    CatHead.n_iFem⟩

-- ============================================================================
-- § 3: Arbitrary Feminine Nouns (u[+FEM])
-- ============================================================================

def mesa     : SpanishNoun := ⟨"mesa",      "table",    CatHead.n_uFem⟩
def silla    : SpanishNoun := ⟨"silla",     "chair",    CatHead.n_uFem⟩
def casa     : SpanishNoun := ⟨"casa",      "house",    CatHead.n_uFem⟩
def puerta   : SpanishNoun := ⟨"puerta",    "door",     CatHead.n_uFem⟩
def ventana  : SpanishNoun := ⟨"ventana",   "window",   CatHead.n_uFem⟩
def cama     : SpanishNoun := ⟨"cama",      "bed",      CatHead.n_uFem⟩
def persona  : SpanishNoun := ⟨"persona",   "person",   CatHead.n_uFem⟩

-- ============================================================================
-- § 4: Default Masculine Nouns (plain n)
-- ============================================================================

def libro    : SpanishNoun := ⟨"libro",     "book",     CatHead.n_plain⟩
def zapato   : SpanishNoun := ⟨"zapato",    "shoe",     CatHead.n_plain⟩
def coche    : SpanishNoun := ⟨"coche",     "car",      CatHead.n_plain⟩
def árbol    : SpanishNoun := ⟨"árbol",     "tree",     CatHead.n_plain⟩
def cielo    : SpanishNoun := ⟨"cielo",     "sky",      CatHead.n_plain⟩
def vaso     : SpanishNoun := ⟨"vaso",      "glass",    CatHead.n_plain⟩
def ángel    : SpanishNoun := ⟨"ángel",     "angel",    CatHead.n_plain⟩

-- ============================================================================
-- § 5: Same-Root Nominals
-- ============================================================================

/-- Same-root nominals: a single root that merges with either i[+FEM]
    or i[−FEM] depending on the referent's sex. -/
structure SameRootEntry where
  form : String
  gloss : String
  mascHead : CatHead := CatHead.n_iMasc
  femHead  : CatHead := CatHead.n_iFem
  deriving Repr

/-- The possible n heads for a same-root entry (always two: masc and fem). -/
def SameRootEntry.possibleNHeads (e : SameRootEntry) : List CatHead :=
  [e.femHead, e.mascHead]

def soldado    : SameRootEntry := { form := "soldado",    gloss := "soldier" }
def estudiante : SameRootEntry := { form := "estudiante", gloss := "student" }
def artista    : SameRootEntry := { form := "artista",    gloss := "artist"  }

-- ============================================================================
-- § 6: Inventory
-- ============================================================================

def naturalFemNouns : List SpanishNoun :=
  [mujer, niña, reina, gata]

def naturalMascNouns : List SpanishNoun :=
  [hombre, niño, rey, gato]

def arbitraryFemNouns : List SpanishNoun :=
  [mesa, silla, casa, puerta, ventana, cama, persona]

def defaultMascNouns : List SpanishNoun :=
  [libro, zapato, coche, árbol, cielo, vaso, ángel]

def allNouns : List SpanishNoun :=
  naturalFemNouns ++ naturalMascNouns ++ arbitraryFemNouns ++ defaultMascNouns

def sameRootNouns : List SameRootEntry :=
  [soldado, estudiante, artista]

-- ============================================================================
-- § 7: Verification
-- ============================================================================

theorem naturalFem_all_iFem :
    naturalFemNouns.all (·.nHead == CatHead.n_iFem) = true := by native_decide

theorem naturalMasc_all_iMasc :
    naturalMascNouns.all (·.nHead == CatHead.n_iMasc) = true := by native_decide

theorem arbitraryFem_all_uFem :
    arbitraryFemNouns.all (·.nHead == CatHead.n_uFem) = true := by native_decide

theorem defaultMasc_all_plain :
    defaultMascNouns.all (·.nHead == CatHead.n_plain) = true := by native_decide

/-- *persona* 'person' is always feminine regardless of referent's sex:
    the gender is arbitrary (u[+FEM]), not interpretable. -/
theorem persona_arbitrary_fem :
    persona.nHead.phi.gender = some ⟨.u, ⟨.fem, .pos⟩⟩ := rfl

/-- *ángel* 'angel' is always masculine (plain n, default gender). -/
theorem ángel_default_masc :
    ángel.nHead.phi.gender = none := rfl

/-- All four n-types are represented in the inventory. -/
theorem four_n_types_covered :
    allNouns.any (·.nHead == CatHead.n_iFem) = true ∧
    allNouns.any (·.nHead == CatHead.n_iMasc) = true ∧
    allNouns.any (·.nHead == CatHead.n_uFem) = true ∧
    allNouns.any (·.nHead == CatHead.n_plain) = true := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

end Fragments.Spanish.Gender
