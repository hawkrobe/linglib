import Linglib.Core.Case.Basic
import Linglib.Core.Case.Hierarchy
import Linglib.Features.Prominence

/-!
# Shawi Agreement Fragment @cite{clem-deal-2024}

Shawi (Chayahuita; ISO 639-3: cbt; Glottocode: chay1248) is a Kawapanan
language spoken in Peru. The data formalized here are based on
@cite{clem-deal-2024}, drawing on the corpus and descriptive work of
Bourdeau (2015), Barraza de García (2005), Hart (1988), and Ulloa (in
preparation).

## What this fragment captures (theory-neutral)

- **Subject and object agreement paradigms** as suffix tables
  (@cite{clem-deal-2024} Tables 1–2). Number is "minimal/augmented",
  following Ulloa's treatment of the system; we abbreviate as `min`
  and `aug` (≈ singular/plural for non-inclusive persons).
- **Ergative case marker** `-ri`, attaching to some transitive subjects
  (@cite{clem-deal-2024} (4)).
- **"Object agreement on subject" (OAgr-on-S) morpheme**, the suffix
  doubling object φ-features on the subject right after `-ri`
  (@cite{clem-deal-2024} (12), (32)). It uses the same forms as
  ordinary object agreement, hence reuses `objectMarkers`.
- **3rd-person object syntactic position** (high vs low) as a binary
  parameter that any analysis of the optional `-ri` with 3rd-person
  objects must consume (@cite{clem-deal-2024} §3.2 around (30)).
- **External object syntax** (overt-postverbal vs. fronted vs.
  *pro*-dropped). Paper (9), (21): when `-ri` surfaces, the object
  cannot remain overt-postverbal — it must be either fronted (OSV)
  or *pro*-dropped.

This file imports only `Core/`. All theoretical analysis — the mapping
of ergative distribution to a particular Agree configuration — lives in
`Phenomena/Agreement/Studies/ClemDeal2024.lean`.
-/

namespace Fragments.Kawapanan.Shawi

open Features.Prominence (PersonLevel)

-- ============================================================================
-- § 1: Number system
-- ============================================================================

/-- Shawi uses a minimal/augmented number system rather than singular/plural;
    1INCL "minimal" picks out the speaker+hearer dyad, etc.
    (@cite{clem-deal-2024} fn. 4, after Corbett 2000). For non-inclusive
    persons `min`/`aug` correspond closely to singular/plural. -/
inductive Number where
  | min   -- minimal (≈ singular for 1EXCL/2/3; speaker+hearer for 1INCL)
  | aug   -- augmented (≈ plural)
  deriving DecidableEq, Repr

/-- Inclusivity dimension orthogonal to PersonLevel; only relevant for
    1st person (1INCL vs 1EXCL). -/
inductive Clusivity where
  | excl
  | incl
  | na    -- not applicable (2nd and 3rd person)
  deriving DecidableEq, Repr

/-- A φ-feature bundle for a Shawi argument. Field order matches the
    `subjectMarkers` / `objectMarkers` row layout: person, clusivity, number. -/
structure Phi where
  person    : PersonLevel
  clusivity : Clusivity
  number    : Number
  deriving DecidableEq, Repr

-- ============================================================================
-- § 2: Subject agreement (Table 1, indicative)
-- ============================================================================

/-- Subject agreement suffixes, indicative mood (@cite{clem-deal-2024}
    Table 1, after Hart 1988, Barraza de García 2005, Ulloa to appear).
    Glottal stop is written `'`; optional `(a)` reflects source variation. -/
def subjectMarkers : List (PersonLevel × Clusivity × Number × Option String) :=
  [ (.first,  .excl, .min, some "-(a)we")
  , (.first,  .excl, .aug, some "-ai")
  , (.first,  .incl, .min, some "-e'")
  , (.first,  .incl, .aug, some "-ewa'")
  , (.second, .na,   .min, some "-(a)n")
  , (.second, .na,   .aug, some "-(a)ma'")
  , (.third,  .na,   .min, some "-in")
  , (.third,  .na,   .aug, some "-pi") ]

-- ============================================================================
-- § 3: Object agreement (Table 2)
-- ============================================================================

/-- Object agreement suffixes (@cite{clem-deal-2024} Table 2). 3rd person
    objects show no overt agreement (`∅`); we encode this directly with
    `none` rather than an empty-string sentinel. -/
def objectMarkers : List (PersonLevel × Clusivity × Number × Option String) :=
  [ (.first,  .excl, .min, some "-ku")
  , (.first,  .excl, .aug, some "-kui")
  , (.first,  .incl, .min, some "-(n)pu'")
  , (.first,  .incl, .aug, some "-(n)pua'")
  , (.second, .na,   .min, some "-(n)ken")
  , (.second, .na,   .aug, some "-((n)ke)ma'")
  , (.third,  .na,   .min, none)
  , (.third,  .na,   .aug, none) ]

/-- Lookup an agreement suffix; returns `none` if the row is absent or
    the cell itself is null (3rd-person object). -/
def lookupMarker
    (paradigm : List (PersonLevel × Clusivity × Number × Option String))
    (φ : Phi) : Option String :=
  (paradigm.find? (λ ⟨p, c, n, _⟩ =>
      p == φ.person && c == φ.clusivity && n == φ.number)).bind (·.2.2.2)

def subjectMarker (φ : Phi) : Option String := lookupMarker subjectMarkers φ
def objectMarker  (φ : Phi) : Option String := lookupMarker objectMarkers  φ

-- ============================================================================
-- § 4: Ergative and OAgr-on-S
-- ============================================================================

/-- The ergative case suffix (@cite{clem-deal-2024} (4)). Attaches to some
    transitive subjects; the `-(*ri)` notation in the paper indicates that
    the form is `-ri` when present and ungrammatical when absent in the
    relevant configurations. -/
def ergativeMarker : String := "-ri"

/-- "Object agreement on subject" exponent, doubling the object's φ on the
    subject immediately after `-ri` (@cite{clem-deal-2024} (12), (32)).
    Reuses the object-agreement paradigm. -/
def oagrOnSMarker (objectPhi : Phi) : Option String := objectMarker objectPhi

-- ============================================================================
-- § 5: Structural position of the object
-- ============================================================================

/-- Position of an object inside the vP (@cite{clem-deal-2024} §3.2, (30)).
    `low` = inside the inner v_cat phase, invisible to the v probe;
    `high` = outside the inner phase (Spec,v_cat or higher), visible. -/
inductive ObjectPosition where
  | low
  | high
  deriving DecidableEq, Repr

/-- Local-person (1/2) objects obligatorily move to the high position
    (@cite{clem-deal-2024} §3.2). 3rd-person objects may but need not. -/
def mustBeHigh : PersonLevel → Bool
  | .first  => true
  | .second => true
  | .third  => false

-- ============================================================================
-- § 6: External syntax of the object
-- ============================================================================

/-- External-syntax options for an object in a transitive clause. The
    surface order is determined by which option is realized:
    overt-postverbal corresponds to canonical SVO; fronted to OSV;
    `pro`-dropped to subject-only surface form (@cite{clem-deal-2024}
    (9), (20)–(21), (26)). -/
inductive ObjectSyntax where
  | overtPostverbal
  | overtFronted
  | proDropped
  deriving DecidableEq, Repr

/-- When the subject bears `-ri`, the object cannot remain
    overt-postverbal: it must be either fronted (OSV) or
    *pro*-dropped (@cite{clem-deal-2024} (9), (21)). When the subject
    does not bear `-ri`, all three options are available. -/
def objectSyntaxLicit (subjBearsErg : Bool) : ObjectSyntax → Bool
  | .overtPostverbal => !subjBearsErg
  | .overtFronted    => true
  | .proDropped      => true

-- ============================================================================
-- § 7: Case inventory
-- ============================================================================

/-- Shawi's morphological case inventory: nominative (unmarked) and
    ergative (-ri). No accusative; objects are unmarked. -/
def caseInventory : Finset Core.Case := {.nom, .erg}

/-- The {NOM, ERG} inventory passes the cross-linguistic case-hierarchy
    check (Blake's hierarchy: ERG and NOM are both rank-6 core cases). -/
example : Core.Case.IsValidInventory caseInventory := by decide

-- ============================================================================
-- § 8: Sanity checks on the paradigms
-- ============================================================================

/-- Subject paradigm fully covers the 8 person×clusivity×number cells. -/
example : subjectMarkers.length = 8 := by decide

/-- Object paradigm covers the same 8 cells; 3rd-person rows are null. -/
example : objectMarkers.length = 8 := by decide

/-- Looking up a 1EXCL.MIN object yields `-ku`. -/
example :
    objectMarker ⟨.first, .excl, .min⟩ = some "-ku" := by decide

/-- 3rd-person object agreement is null. -/
example :
    objectMarker ⟨.third, .na, .min⟩ = none := by decide

/-- 2PL object agreement is `-((n)ke)ma'`; this is the form that surfaces
    as OAgr-on-S in (12). -/
example :
    oagrOnSMarker ⟨.second, .na, .aug⟩ = some "-((n)ke)ma'" := by decide

/-- Overt-postverbal object is blocked when the subject bears `-ri`. -/
example : objectSyntaxLicit true .overtPostverbal = false := by decide

/-- Fronted (OSV) and *pro*-dropped objects are always licit. -/
example :
    objectSyntaxLicit true .overtFronted = true ∧
    objectSyntaxLicit true .proDropped = true := by decide

end Fragments.Kawapanan.Shawi
