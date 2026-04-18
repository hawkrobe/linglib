import Linglib.Core.Case
import Linglib.Theories.Interfaces.Morphosyntax.CaseContainment
import Linglib.Fragments.Russian.Case
import Linglib.Fragments.Russian.Gender

/-!
# @cite{pesetsky-2013} — Russian Case Morphology and the Syntactic Categories

Pesetsky's central thesis: **morphological case is the realization of a
syntactic part-of-speech category**. The four major cases line up with
the four traditional lexical categories:

| Case        | POS category | Assigner                       |
|-------------|--------------|--------------------------------|
| Genitive    | N            | every noun (universal default) |
| Nominative  | D            | the D head of a DP             |
| Accusative  | V            | a transitive V (under VACC)    |
| Oblique     | P            | a P head                       |

Two corollaries reshape standard Case theory:

1. **Every noun is "born genitive."** A bare N projects an N-stratum
   case shell, hidden in surface morphology by the One-Suffix Rule but
   visible in case-stacking languages (Lardil — @cite{richards-2013},
   on whose analysis the proposal directly builds).

2. **The Case Filter dissolves.** There is no separate `uCase` feature
   needing valuation; case morphology *is* the realization of categorial
   structure. The Schütze-style default-nominative residue covers
   apparent "caseless" DPs (@cite{schuetze-2001}).

## Architecture in the formalization

We model FA (Feature Assignment) as a recursive `assignDown` over a
node-and-stack tree: when an assigner of POS-category α merges with
β, α is pushed onto the case stack of every leaf β dominates. The
**One-Suffix Rule** is then a single-line filter (`head?`); Lardil is
the same grammar minus the filter.

The empirical core — Russian paucal (*dva*, *tri*, *četyre*) selecting
an N-stratum complement and surfacing as GEN.SG — falls out as a
kernel-checkable computation: `numeralCaseAssignment .paucal = .N`.

Connections:

- `Core.Case` (Blake) gives the cross-linguistic case inventory; we
  bridge `POSCat → Core.Case` so Pesetsky's primitives plug into the
  existing typology.
- `Theories/Morphology/CaseContainment.lean` (Caha) formalizes the
  containment hierarchy `[[[[[NOM]ACC]GEN]DAT]P]`. Caha's bottom-up
  containment in the *morphological* domain mirrors Pesetsky's
  bottom-up case stacking in the *derivational* domain (with the
  important inversion that for Pesetsky the bottom is N=GEN, not NOM).
- `Fragments/Russian/Gender.lean` already supplies declension classes
  and the hybrid noun *vrač*; Pesetsky's feminizing Ж analysis is
  noted but not re-formalized here.
- `Fragments/Russian/Case.lean` lists the Russian 6-case inventory.

## Out of scope (deferred for separate study files)

- The full FA rule's six developmental versions (Ch. 2–8). We model the
  endpoint version: feature copy on Merge, percolation to all dominated
  leaves.
- The complete VACC restriction with referent-feature interaction.
- The D-headed PP analysis of POBL↔VACC spatial alternations (Ch. 7).
- Spell-Out / phase locality on adnominal case (Ch. 8).
-/

namespace Phenomena.Case.Studies.Pesetsky2013

-- ============================================================================
-- § 1: POS Categories as Case Primitives
-- ============================================================================

/-- The four part-of-speech categories that double as case strata in
    Pesetsky's framework. Each category, when it serves as an assigner,
    realizes morphologically as the case shown in the table at the top
    of this file. -/
inductive POSCat where
  | N    -- Genitive — the universal noun stratum
  | D    -- Nominative — assigned by D
  | V    -- Accusative — assigned by transitive V (subject to VACC)
  | P    -- Dative — assigned by P (covers PDAT/POBL)
  deriving DecidableEq, Repr, Inhabited

/-- Bridge from Pesetsky's POS-as-case primitives to @cite{blake-1994}'s
    cross-linguistic inventory in `Core.Case`. P maps to dat as the
    most-general oblique target. -/
def POSCat.toCase : POSCat → Core.Case
  | .N => .gen
  | .D => .nom
  | .V => .acc
  | .P => .dat

/-- Each POS category appears as the source of a unique case in
    `Core.Case`. -/
theorem POSCat.toCase_injective :
    POSCat.toCase .N ≠ POSCat.toCase .D ∧
    POSCat.toCase .N ≠ POSCat.toCase .V ∧
    POSCat.toCase .N ≠ POSCat.toCase .P ∧
    POSCat.toCase .D ≠ POSCat.toCase .V ∧
    POSCat.toCase .D ≠ POSCat.toCase .P ∧
    POSCat.toCase .V ≠ POSCat.toCase .P := by
  decide

-- ============================================================================
-- § 2: Trees with Case Stacks (FA Rule input/output)
-- ============================================================================

/-- A skeletal tree carrying a POS label on each internal node and a
    *case stack* on each leaf. Stacks are innermost-on-the-right
    (the `cons` end is outermost), matching the order in which FA
    applies: outer assigners are added later, hence prepended. -/
inductive PesTree where
  | leaf : String → List POSCat → PesTree
  | node : POSCat → List PesTree → PesTree
  deriving Repr

mutual
  /-- The Feature Assignment rule (final form, Ch. 8): on Merge, the
      assigner's category is copied as a case feature onto every leaf
      in its sister's domain.

      We model this as a recursive descent that prepends `assigner`
      to every leaf's stack. Real FA only targets the sister, but for
      a single Merge step the result is the same as a full descent
      because the assigner doesn't yet dominate anything else. -/
  def assignDown (assigner : POSCat) : PesTree → PesTree
    | .leaf w stack => .leaf w (assigner :: stack)
    | .node c kids  => .node c (assignDownList assigner kids)
  /-- Helper for `assignDown`: applies FA to each child in turn. -/
  def assignDownList (assigner : POSCat) : List PesTree → List PesTree
    | []      => []
    | t :: ts => assignDown assigner t :: assignDownList assigner ts
end

/-- Extract a leaf's case stack (returns `[]` for non-leaves). -/
def PesTree.stack : PesTree → List POSCat
  | .leaf _ s => s
  | .node _ _ => []

/-- A bare leaf has the empty stack. -/
theorem stack_leaf_empty (w : String) : (PesTree.leaf w []).stack = [] := rfl

/-- FA prepends to the stack. -/
theorem assignDown_prepends (a : POSCat) (w : String) (s : List POSCat) :
    (assignDown a (.leaf w s)).stack = a :: s := rfl

-- ============================================================================
-- § 3: The One-Suffix Rule (Russian) vs. Stacking (Lardil)
-- ============================================================================

/-- The **One-Suffix Rule** (@cite{pesetsky-2013} Ch. 3). Russian
    pronounces only the *outermost* case stratum on each noun, deleting
    inner strata. This is why the universal "born-genitive" stratum
    (the bottom of the stack) is invisible in Russian morphology. -/
def oneSuffix : List POSCat → Option POSCat
  | s :: _ => some s
  | []     => none

/-- Lardil (@cite{richards-2013}, the empirical anchor for the
    proposal) realizes the *entire* case stack overtly. The "rule"
    here is the identity — Lardil is what Russian would look like
    without the One-Suffix filter. -/
def lardilSpellOut : List POSCat → List POSCat := id

/-- One-Suffix on an empty stack yields nothing (no overt case marker). -/
theorem oneSuffix_empty : oneSuffix [] = none := rfl

/-- One-Suffix retains only the outermost stratum. -/
theorem oneSuffix_outermost (a : POSCat) (rest : List POSCat) :
    oneSuffix (a :: rest) = some a := rfl

/-- Lardil and Russian agree only when the stack has at most one element.
    With ≥ 2 strata, they diverge: Russian shows only the outer, Lardil
    shows both. This is the core morphological signature of the
    proposal. -/
theorem lardil_russian_divergence (a b : POSCat) (rest : List POSCat) :
    lardilSpellOut (a :: b :: rest) ≠ (oneSuffix (a :: b :: rest)).toList := by
  simp [lardilSpellOut, oneSuffix, Option.toList]

-- ============================================================================
-- § 4: Every Noun is "Born Genitive"
-- ============================================================================

/-- A bare noun, before any FA application, projects an N-stratum
    (Pesetsky's "every noun is born genitive"). We model this by
    saying: the canonical leaf for a noun starts with `[.N]`, not `[]`.

    This is the formalization of the universal default. -/
def bornGenitive (w : String) : PesTree :=
  .leaf w [.N]

/-- Russian *kniga* 'book': bare, surface case is GEN (the N stratum)
    when no further FA applies — i.e. the noun is on its own and only
    its inherent N-stratum is realized. -/
theorem bare_noun_surface_gen (w : String) :
    oneSuffix (bornGenitive w).stack = some .N := rfl

/-- When a transitive V then assigns its V-stratum, the Russian surface
    shows only V (the outer); the N stratum is *masked* by One-Suffix
    but still derivationally present. -/
theorem v_assignment_masks_n (w : String) :
    let stacked := assignDown .V (bornGenitive w)
    oneSuffix stacked.stack = some .V := rfl

/-- The same derivation in a Lardil-style grammar shows BOTH strata
    overtly: GEN (inner) plus ACC (outer). This is Pesetsky's
    cross-linguistic argument: Russian and Lardil have the *same*
    derivation; they differ only in whether the One-Suffix filter
    applies. -/
theorem lardil_shows_both_strata (w : String) :
    let stacked := assignDown .V (bornGenitive w)
    lardilSpellOut stacked.stack = [.V, .N] := rfl

-- ============================================================================
-- § 5: Russian Paucals (dva, tri, četyre)
-- ============================================================================

/-- Three numeral classes in Russian (@cite{pesetsky-2013} Ch. 4–6):

    - **paucal** (`dva`, `tri`, `četyre`): NBR head merged low; the
      "GEN.SG" appearance on the noun is FA-assigned N from the
      paucal head.
    - **higher** (`pjat'`, `šest'`, ...): assign GEN.PL.
    - **quant** (`mnogo`, `nemnogo`, `skol'ko`): the QUANT category;
      QUANT-to-D movement with NBR pied-piping. Also assigns GEN.PL. -/
inductive RusNumClass where
  | paucal
  | higher
  | quant
  deriving DecidableEq, Repr

/-- A Russian numeral lexical entry. Minimal — just form and class. -/
structure RusNumeral where
  form : String
  cls  : RusNumClass
  deriving Repr

def dva    : RusNumeral := ⟨"dva", .paucal⟩
def tri    : RusNumeral := ⟨"tri", .paucal⟩
def četyre : RusNumeral := ⟨"četyre", .paucal⟩
def pjat'  : RusNumeral := ⟨"pjat'", .higher⟩
def šest'  : RusNumeral := ⟨"šest'", .higher⟩
def mnogo  : RusNumeral := ⟨"mnogo", .quant⟩
def skol'ko : RusNumeral := ⟨"skol'ko", .quant⟩

/-- All three numeral classes assign the N stratum (= genitive) to
    their complement noun. This is the unifying empirical claim:
    paucal vs. higher vs. quant all force "of-genitive" morphology
    on what they combine with — the differences are in *which*
    genitive (SG vs. PL) and in the syntactic position of the
    numeral itself. -/
def numeralCaseAssignment : RusNumClass → POSCat
  | .paucal => .N
  | .higher => .N
  | .quant  => .N

/-- All three numeral classes assign N. The unification is the
    centerpiece of @cite{pesetsky-2013} Ch. 4–6. -/
theorem numerals_all_assign_N :
    numeralCaseAssignment .paucal = .N ∧
    numeralCaseAssignment .higher = .N ∧
    numeralCaseAssignment .quant  = .N := ⟨rfl, rfl, rfl⟩

/-- Apply a numeral to a (born-genitive) noun. The numeral's FA pushes
    its assigned stratum onto the noun's stack. -/
def applyNumeral (num : RusNumeral) (n : String) : PesTree :=
  assignDown (numeralCaseAssignment num.cls) (bornGenitive n)

/-- *dva stola* 'two tables' — the noun's stack is `[.N, .N]` after
    the paucal applies; surface is GEN under One-Suffix. -/
theorem dva_stola_surface_gen :
    oneSuffix (applyNumeral dva "stol").stack = some .N := rfl

/-- *pjat' stolov* 'five tables' — same surface case (GEN). The fact
    that this is GEN.PL while *dva stola* is GEN.SG is a feature of
    NBR/SG marking, not of which case is assigned. -/
theorem pjat'_stolov_surface_gen :
    oneSuffix (applyNumeral pjat' "stol").stack = some .N := rfl

/-- *mnogo studentov* 'many students' — QUANT also assigns N. -/
theorem mnogo_studentov_surface_gen :
    oneSuffix (applyNumeral mnogo "student").stack = some .N := rfl

/-- The N-stratum from FA is *additional* to the universal "born-genitive"
    N stratum already on the noun. So the stack ends with `[.N, .N]`. -/
theorem paucal_stack_double_N :
    (applyNumeral dva "stol").stack = [.N, .N] := rfl

/-- In a Lardil-style grammar, the double N stratum would be visible
    overtly. (Lardil itself doesn't have paucals — this is a thought
    experiment about what Pesetsky's analysis predicts under different
    spell-out parameters.) -/
theorem paucal_lardil_shows_double :
    lardilSpellOut (applyNumeral dva "stol").stack = [.N, .N] := rfl

-- ============================================================================
-- § 6: Nominative as D-Assignment, Accusative as V-Assignment
-- ============================================================================

/-- A subject DP receives nominative because D assigns it. The
    derivation: bare noun (born GEN) → numeral may apply (still GEN
    under One-Suffix) → D applies (now NOM under One-Suffix). -/
theorem subject_surface_nom (n : String) :
    let dp := assignDown .D (bornGenitive n)
    oneSuffix dp.stack = some .D := rfl

/-- An object DP receives accusative because V assigns it. Same
    derivation but with V instead of D. -/
theorem object_surface_acc (n : String) :
    let dp := assignDown .V (bornGenitive n)
    oneSuffix dp.stack = some .V := rfl

/-- Subject vs. object differ only in the *outermost* assigner.
    The N stratum underneath is identical. -/
theorem subject_object_same_inner (n : String) :
    let subj := assignDown .D (bornGenitive n)
    let obj  := assignDown .V (bornGenitive n)
    subj.stack.tail = obj.stack.tail := rfl

-- ============================================================================
-- § 7: Bridges to existing infrastructure
-- ============================================================================

/-- The Russian 4-case spine NOM/ACC/GEN/OBL is precisely
    the image of `POSCat` in `Core.Case`. -/
theorem pos_image_in_core :
    POSCat.toCase .N = Core.Case.gen ∧
    POSCat.toCase .D = Core.Case.nom ∧
    POSCat.toCase .V = Core.Case.acc ∧
    POSCat.toCase .P = Core.Case.dat := ⟨rfl, rfl, rfl, rfl⟩

/-- The four POS-as-case primitives, lifted into `Core.Case` —
    Pesetsky's reduction yields exactly NOM, ACC, GEN, DAT, the core
    four of the Russian inventory. INST and LOC remain outside the
    image. -/
def pesetskyCore : List Core.Case :=
  [POSCat.D, POSCat.V, POSCat.N, POSCat.P].map POSCat.toCase

theorem pesetskyCore_subset_russian_inventory :
    pesetskyCore.all (· ∈ Fragments.Russian.Case.caseInventory) = true := by decide

theorem inst_loc_outside_pesetsky :
    Core.Case.inst ∉ pesetskyCore ∧ Core.Case.loc ∉ pesetskyCore := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Caha's containment rank for the three core cases that POSCat covers
    (NOM/ACC/GEN). Nominative is innermost (rank 0), accusative
    contains it (rank 1), genitive contains both (rank 2). This is
    the *morphological* containment order; Pesetsky's *derivational*
    order is the inverse for nouns (N is the innermost stratum,
    added first; D may be added later). The two views are
    consistent under the inversion. -/
theorem caha_containment_inverts_pesetsky :
    Interfaces.Morphosyntax.CaseContainment.containmentRank Core.Case.nom = some 0 ∧
    Interfaces.Morphosyntax.CaseContainment.containmentRank Core.Case.acc = some 1 ∧
    Interfaces.Morphosyntax.CaseContainment.containmentRank Core.Case.gen = some 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- Pesetsky's feminizing analysis of *vrač* 'doctor' (Ch. 5) interacts
    with the existing hybrid-noun analysis in `Fragments.Russian.Gender`.
    Pesetsky posits a null Ж morpheme above `vrač` when the referent
    is female; that morpheme licenses feminine agreement. The hybrid
    declension class assignment in `vrač.declClass = some .I` from the
    fragment is preserved. -/
theorem vrač_morphological_class_unchanged :
    Fragments.Russian.Gender.vrač.declClass = some Fragments.Russian.Gender.DeclClass.I := rfl

end Phenomena.Case.Studies.Pesetsky2013
