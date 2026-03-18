import Linglib.Theories.Syntax.Minimalism.Ellipsis.DeletionDomain

/-!
# Benz & Salzmann (2025): Evidence from German for N-stranding NP-ellipsis
@cite{benz-salzmann-2025}

Evidence from German for N-stranding NP-ellipsis.
Proceedings of the Chicago Linguistic Society 60.

## Overview

German has N-stranding NP-ellipsis: ellipsis of NP after N-to-n head
movement, which strands the moved noun outside
the deletion domain. What looks like deletion of individual constituents
(PPs, relative clauses, genitives) is actually NP-ellipsis with N having
evacuated.

## Key Claims

1. **X-stranding diagnostic** (@cite{liptak-saab-2014}): if a language has
   both X-movement out of XP and XP-ellipsis, X-stranding XP-ellipsis
   should exist. German has N-to-n movement and NP-ellipsis → N-stranding
   NP-ellipsis exists.

2. **Variable [E] placement**: [E] can be on D, Num, or n, producing
   different-sized deletion domains.

3. **Contrast condition**: n[E] (N-stranding) requires the noun to be
   contrastive. When N is not contrastive, [E] must be on a higher head
   (Num or D), and N is deleted along with the rest.

4. **Against individual deletion**: Apparent deletion of individual PPs or
   relatives is actually NP-ellipsis after N-movement — there is no
   mechanism for deleting arbitrary individual constituents within DP.
   No [E] position can delete prenominal modifiers without also deleting N.

5. **Against pragmatic recovery**: Bound variable readings inside elided
   material prove these are genuine syntactic ellipsis, not pragmatic
   inference.

6. **Gender mismatch parallel**: N-stranding tolerates gender mismatches
   (n hosts gender, n is external under n[E]) — paralleling voice mismatch
   tolerance in VPE (Voice external under Voice[E]).

## Architecture

This study imports `DeletionDomain.lean`: the generic `DeletionSpine`
class, the clausal `SpinePos` instance, and the nominal `NomSpinePos`
instance with `NomEllipsisType` and the `xStranding` theorem.

N-to-n head movement is assumed but not formally instantiated; the
deletion-domain predictions are independent of the movement mechanism.

The core predictions are derived from the `NomSpinePos` deletion domain:
- n[E]: NP deleted, N/adj/num survive (N-stranding)
- Num[E]: nP deleted, num/D survive (standard NP-ellipsis)
- D[E]: NumP deleted, only D survives

All already proved in `DeletionDomain.lean` §§ 11-12. This file adds
the German empirical data and verifies it against those predictions.
-/

namespace Phenomena.Ellipsis.Studies.BenzSalzmann2025

open Minimalism.Ellipsis

-- ════════════════════════════════════════════════════════════════
-- § 1: German NP-Ellipsis Data
-- ════════════════════════════════════════════════════════════════

/-- Grammaticality judgment for a DP-ellipsis example. -/
structure DPEllipsisDatum where
  /-- German sentence -/
  sentence : String
  /-- English translation -/
  translation : String
  /-- Is the ellipsis grammatical? -/
  grammatical : Bool
  /-- Which [E] position licenses (or fails to license) this? -/
  ePosition : NomSpinePos
  /-- Is the noun contrastive? -/
  nounContrastive : Bool
  /-- Source example number -/
  source : String
  deriving Repr

-- § 1.1: NP-ellipsis exists in German (§2.2)

/-- ex. (11): Deletion of more than just the noun — NP-ellipsis deletes
    N + PP modifier. -/
def ex11 : DPEllipsisDatum :=
  { sentence := "Ich kaufte zwei Bücher über Chomsky und du kauftest drei"
  , translation := "I bought two books about Chomsky and you bought three."
  , grammatical := true
  , ePosition := .Num
  , nounContrastive := false
  , source := "Benz & Salzmann 2025, (11)" }

/-- ex. (12): PP complement of elided noun survives — the elided noun
    *Angst* selects *vor*, showing syntactic structure in the ellipsis site. -/
def ex12 : DPEllipsisDatum :=
  { sentence := "Die Angst vor Monstern ist grösser als die vor Spinnen"
  , translation := "The fear of monsters is bigger than that of spiders."
  , grammatical := true
  , ePosition := .Num
  , nounContrastive := false
  , source := "Benz & Salzmann 2025, (12)" }

-- § 1.2: N-stranding with contrastive N (§2.1)

/-- ex. (6a): PP *der Physik* recovered in second conjunct — noun is
    contrastive (*Studenten* vs *Professoren*), enabling N-stranding.
    The PP dependent of the elided NP is interpreted in the ellipsis site. -/
def ex6a : DPEllipsisDatum :=
  { sentence := "Peter sprach mit zwei Studenten der Physik und ich sprach mit zwei Professoren"
  , translation := "Peter spoke with two students of physics and I spoke with two professors (of physics)."
  , grammatical := true
  , ePosition := .n
  , nounContrastive := true
  , source := "Benz & Salzmann 2025, (6a)" }

-- § 1.3: N-stranding blocked without contrastive N (§1.2, §2.1)

/-- ex. (5): Non-contrastive noun blocks N-stranding (Spanish;
    @cite{liptak-saab-2014}) — only the numeral contrasts (*tres* vs
    *dos*), not the noun *estudiantes*. Since N is not contrastive, n[E]
    is unavailable. [E] must be on Num or higher, deleting N and its
    PP dependent. The PP *de física* cannot be recovered. -/
def ex5_analog : DPEllipsisDatum :=
  { sentence := "Juan habló con tres estudiantes de física y yo hablé con dos"
  , translation := "Juan talked with three students of physics and I talked with two (students, not of physics)."
  , grammatical := false
  , ePosition := .Num  -- N not contrastive → [E] on Num, not n; PP deleted with N
  , nounContrastive := false
  , source := "Benz & Salzmann 2025, (5) / Lipták & Saab 2014" }

/-- ex. (27): N not contrastive but adjective contrastive → N-stranding
    blocked. *Zerstörung* is the same noun in both conjuncts; only the
    ordinal (*erste* vs *zweite*) contrasts. Since N is not contrastive,
    [E] must be on a higher head, deleting N along with the genitive
    argument *Roms*. The genitive cannot be recovered. -/
def ex27 : DPEllipsisDatum :=
  { sentence := "*Ich sah die erste Zerstörung Roms und du sahst die zweite Zerstörung"
  , translation := "Intended: I saw the first destruction of Rome and you saw the second (of Rome)."
  , grammatical := false
  , ePosition := .Num  -- N not contrastive → [E] on Num; genitive deleted with N
  , nounContrastive := false
  , source := "Benz & Salzmann 2025, (27)" }

-- § 1.4: Against individual deletion (§2.3)

/-- ex. (25a): Prenominal adjective cannot be individually deleted —
    *schönste* cannot be elided while N (*Auto*/*Motorrad*) contrasts.
    No [E] position achieves this: n[E] leaves adj external; Num[E] and
    D[E] delete both adj and N. See `no_individual_prenominal_deletion`. -/
def ex25a : DPEllipsisDatum :=
  { sentence := "*Ich habe das schönste Auto und du das Motorrad"
  , translation := "Intended: I have the prettiest car and you the (prettiest) motorbike."
  , grammatical := false
  , ePosition := .Num  -- nearest [E] that deletes adj, but it also deletes N
  , nounContrastive := true
  , source := "Benz & Salzmann 2025, (25a)" }

/-- ex. (25b): Numeral cannot be individually deleted — *zwei* cannot
    be elided while N (*Bücher*/*Romane*) contrasts.
    D[E] is the only position that could delete Num, but it also
    deletes N, adj, and n. -/
def ex25b : DPEllipsisDatum :=
  { sentence := "*Ich las diese zwei Bücher und du last diese Romane"
  , translation := "Intended: I read these two books and you read these (two) novels."
  , grammatical := false
  , ePosition := .D  -- only D[E] puts Num in deletion domain, but deletes everything
  , nounContrastive := true
  , source := "Benz & Salzmann 2025, (25b)" }

/-- ex. (26a): Prenominal genitive (in Spec,DP) cannot be deleted and
    recovered. Even D[E] (the highest [E] position) deletes only D's
    complement — Spec,DP is never in any deletion domain. -/
def ex26a : DPEllipsisDatum :=
  { sentence := "*Ich schätze Goethes Romane aber du bevorzugst Gedichte"
  , translation := "Intended: I appreciate Goethe's novels but you prefer (Goethe's) poems."
  , grammatical := false
  , ePosition := .D  -- even D[E] cannot delete Spec,DP material
  , nounContrastive := true
  , source := "Benz & Salzmann 2025, (26a)" }

/-- ex. (26b): Postnominal *von*-PP CAN be deleted — this IS NP-ellipsis
    after N-stranding, not individual constituent deletion. -/
def ex26b : DPEllipsisDatum :=
  { sentence := "Ich schätze Goethes Romane aber du bevorzugst die Gedichte von Goethe"
  , translation := "I appreciate Goethe's novels but you prefer the poems by Goethe."
  , grammatical := true
  , ePosition := .n
  , nounContrastive := true
  , source := "Benz & Salzmann 2025, (26b)" }

-- § 1.5: All-or-nothing postnominal deletion and bound variables (§2.3)

/-- ex. (28a): One PP (*von jedem Studenten*) remains while the second
    (*vor seinem Professor*) is attempted to be recovered — UNGRAMMATICAL.
    If one postnominal modifier survives, NP-ellipsis did not apply,
    and the second modifier cannot be individually deleted. -/
def ex28a : DPEllipsisDatum :=
  { sentence := "*Die Angst von jedem Studenten vor seinem Professor ist grösser als der Respekt von jedem Studenten"
  , translation := "Intended: Every student's fear of his professor is greater than every student's respect (of his professor)."
  , grammatical := false
  , ePosition := .n  -- n[E] would delete ALL NP material, not just one PP
  , nounContrastive := true
  , source := "Benz & Salzmann 2025, (28a)" }

/-- ex. (28b): BOTH PPs deleted — GRAMMATICAL. This is genuine
    N-stranding NP-ellipsis: *Angst* vs *Respekt* are contrastive,
    n[E] applies, and the entire NP (both PPs) is deleted.
    The bound pronoun *seinem* (bound by *jedem Studenten*) in the
    elided material proves genuine syntactic ellipsis — pragmatic
    recovery cannot bind variables. -/
def ex28b : DPEllipsisDatum :=
  { sentence := "Die Angst von jedem Studenten vor seinem Professor ist grösser als der Respekt"
  , translation := "Every student's fear of his professor is greater than the respect."
  , grammatical := true
  , ePosition := .n
  , nounContrastive := true
  , source := "Benz & Salzmann 2025, (28b)" }

-- ════════════════════════════════════════════════════════════════
-- § 2: Contrast Condition
-- ════════════════════════════════════════════════════════════════

/-- The contrast condition on [E] placement: n[E] (N-stranding) is
    available only when the noun is contrastive. When N is not contrastive,
    [E] must be on a higher head (Num or D), causing N to be deleted too.

    This predicts:
    - Contrastive N + postnominal modifier → N-stranding OK (ex. 6a)
    - Non-contrastive N + postnominal modifier → modifier not recovered (ex. 5, 27) -/
def ePositionFromContrast (nounContrastive : Bool) : NomSpinePos :=
  if nounContrastive then .n else .Num

/-- When N is contrastive, [E] is on n. The n head (to which N has moved)
    is external → the noun survives via its moved copy at n. -/
theorem contrastive_nHead_survives :
    nomSurvives .n ⟨ePositionFromContrast true, ""⟩ = true := rfl

/-- When N is not contrastive, [E] is on Num. Both N (base position)
    and n are in the deletion domain — the noun is deleted along with
    all NP-internal and nP-internal material. -/
theorem nonContrastive_noun_deleted :
    nomInDeletionDomain .N ⟨ePositionFromContrast false, ""⟩ = true ∧
    nomInDeletionDomain .n ⟨ePositionFromContrast false, ""⟩ = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 3: Predictions — Prenominal vs. Postnominal Asymmetry
-- ════════════════════════════════════════════════════════════════

/-- The central asymmetry (@cite{benz-salzmann-2025} §2.3):
    - Prenominal modifiers (adjectives, numerals, prenominal genitives)
      CANNOT be individually deleted → they are above n
    - Postnominal modifiers (PPs, relative clauses, postnominal genitives)
      CAN be deleted under N-stranding → they are inside NP (below n)

    This follows directly from the `NomSpinePos` deletion domain:
    under n[E], only material below n (= NP-internal) is deleted. -/
theorem prenominal_postnominal_asymmetry :
    -- Postnominal material (NP-internal = below n): deleted under n[E]
    nomInDeletionDomain .N nStrandingNPE = true ∧
    -- Prenominal adjectives (nP-internal = above NP): survive n[E]
    nomSurvives .NP_adj nStrandingNPE = true ∧
    -- Numerals (at Num level): survive n[E]
    nomSurvives .Num nStrandingNPE = true ∧
    -- D (determiner): always survives
    nomSurvives .D nStrandingNPE = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Individual prenominal deletion is impossible: any [E] position that
    puts the prenominal adjective in the deletion domain also puts N
    in the deletion domain. So you cannot delete an adjective without
    also deleting the noun — ruling out individual adjective deletion
    when N is contrastive (ex. 25a).

    This follows from NP_adj being structurally above N: N is below
    NP_adj in the complement hierarchy, so any complement that contains
    NP_adj also contains N. -/
theorem no_individual_prenominal_deletion (p : NomSpinePos) :
    NomSpinePos.NP_adj.isBelow p = true → NomSpinePos.N.isBelow p = true := by
  cases p <;> simp [NomSpinePos.isBelow]

/-- Individual numeral deletion is impossible: any [E] position that
    puts Num in the deletion domain also puts N in the deletion domain.
    Only D[E] deletes Num, and D[E] also deletes everything else (ex. 25b). -/
theorem no_individual_numeral_deletion (p : NomSpinePos) :
    NomSpinePos.Num.isBelow p = true → NomSpinePos.N.isBelow p = true := by
  cases p <;> simp [NomSpinePos.isBelow]

/-- Under N-stranding, if one postnominal modifier remains, ALL must remain
    (ex. 28a vs 28b). Ellipsis targets the entire NP projection, not
    individual constituents.

    If [E] is NOT on n (no N-stranding), then [E] must be higher (Num or D),
    and all postnominal material plus N is deleted — so individual PP
    recovery is impossible. The only way to recover a PP is N-stranding,
    which deletes the entire NP. -/
theorem all_or_nothing_postnominal :
    -- Under N-stranding: ALL NP-internal material is deleted
    nomInDeletionDomain .N nStrandingNPE = true ∧
    -- Under nP-ellipsis: NP-internal material PLUS n-level material deleted
    nomInDeletionDomain .N nPEllipsis = true ∧
    nomInDeletionDomain .NP_adj nPEllipsis = true ∧
    nomInDeletionDomain .n nPEllipsis = true := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 4: N-Stranding as X-Stranding
-- ════════════════════════════════════════════════════════════════

/-- N-stranding NP-ellipsis is an instance of the generic X-stranding
    pattern, just as V-stranding VPE is. Both are proved by the same
    `xStranding` theorem from `DeletionDomain.lean` § 0.

    The parallel: V:v :: N:n — the lexical head moves to the categorizer,
    and when [E] is on the categorizer, the lexical head's complement
    (VP/NP) is deleted while the moved head survives. -/
theorem n_stranding_parallels_v_stranding :
    -- N-stranding: n external under n[E], N's base deleted under n[E]
    nomSurvives .n nStrandingNPE = true ∧
    nomInDeletionDomain .N nStrandingNPE = true ∧
    -- V-stranding: v external under v[E], V deleted under v[E]
    (isInDeletionDomain .v vVPE = false) ∧
    isInDeletionDomain .V vVPE = true ∧
    -- Same structural reason: lexical head below categorizer in both spines
    NomSpinePos.N.isBelow NomSpinePos.n = true ∧
    SpinePos.V.isBelow SpinePos.v = true := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 5: Connection to Saab (2026)
-- ════════════════════════════════════════════════════════════════

/-- German N-stranding (n[E]) and Spanish Num[E] are different [E]
    placements in the same nominal spine. German n[E] produces a strictly
    smaller deletion domain than Spanish Num[E].

    This is the nominal analogue of the clausal vVPE vs. English VPE
    distinction: lower [E] → smaller deletion domain → more survivors. -/
theorem german_spanish_e_height :
    -- German N-stranding: [E] on n
    nStrandingNPE.ePosition = NomSpinePos.n ∧
    -- Spanish Num[E] / standard nP-ellipsis: [E] on Num
    nPEllipsis.ePosition = NomSpinePos.Num ∧
    -- n is structurally below Num
    NomSpinePos.n.isAtOrBelow NomSpinePos.Num = true := ⟨rfl, rfl, rfl⟩

/-- Monotonicity: German N-stranding tolerates more "mismatches" (i.e.,
    more positions survive) than Spanish nP-ellipsis, because n < Num.
    Adjectives survive German n[E] but not Spanish Num[E]. -/
theorem german_more_survivors_than_spanish :
    -- Adjective survives German N-stranding
    nomSurvives .NP_adj nStrandingNPE = true ∧
    -- Adjective does NOT survive Spanish nP-ellipsis
    nomSurvives .NP_adj nPEllipsis = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 6: Gender Mismatch Parallel
-- ════════════════════════════════════════════════════════════════

/-- Gender mismatches under N-stranding parallel voice mismatches
    under VPE. Both involve the categorizer head being external to
    the deletion domain when [E] is at that categorizer:

    - N-stranding (n[E]): n hosts gender features, n is external
      → gender mismatches tolerated
    - English VPE (Voice[E]): Voice hosts voice features, Voice is
      external → voice mismatches tolerated

    Conversely, when [E] is higher:
    - nP-ellipsis (Num[E]): n is internal → gender mismatches blocked
    - Sluicing (C[E]): Voice is internal → voice mismatches blocked

    @cite{benz-salzmann-2025} p.62-63: "while gender mismatches are
    normally not possible in nominal ellipsis [...], such mismatches
    do become possible in our N-stranding NP-ellipsis data." -/
theorem gender_voice_parallel :
    -- n external under n[E] → gender mismatch tolerated
    nomSurvives .n nStrandingNPE = true ∧
    -- Voice external under Voice[E] → voice mismatch tolerated
    canMismatch englishVPE voiceMismatch = true ∧
    -- n internal under Num[E] → gender mismatch blocked
    nomInDeletionDomain .n nPEllipsis = true ∧
    -- Voice internal under C[E] → voice mismatch blocked
    canMismatch sluicing voiceMismatch = false := ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.Ellipsis.Studies.BenzSalzmann2025
