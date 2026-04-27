import Linglib.Core.Case.Basic
import Linglib.Fragments.Slavic.Russian.Case
import Linglib.Fragments.Slavic.Russian.Gender
import Linglib.Theories.Interfaces.Morphosyntax.CaseContainment

/-!
# @cite{pesetsky-2013} — Russian Case Morphology and the Syntactic Categories

Pesetsky's central thesis: **morphological case is the realization of a
syntactic part-of-speech category**. The four major cases line up with
the four traditional lexical categories:

| Case          | POS category | Assigner                              |
|---------------|--------------|---------------------------------------|
| Genitive      | N            | every noun (Primeval Genitive, p. 9)  |
| Nominative    | D            | the D head of a DP                    |
| Accusative    | V            | a transitive V (under VACC)           |
| Obliques      | P            | a P head; DAT is the canonical exemplar |

Pesetsky writes (p. 7) that "only the distinctions among these oblique
cases in Russian will fail to correspond to a traditional part-of-speech
distinction"; P_OBL is the canonical P category and P_DAT is one
exemplar with additional features. In this formalization `POSCat.cases`
returns the full oblique series for `.P`, and `POSCat.canonicalExemplar`
picks DAT as Pesetsky's exemplar.

Two corollaries reshape standard Case theory:

1. **The Primeval Genitive Conjecture** (eq. (6), p. 9): the genitive
   morpheme `NGEN` categorizes a Russian root as a noun in the lexicon.
   This is a categorizing-head property in the spirit of
   @cite{marantz-1997}, not a syntactic stack initialization. Lardil
   morphology — surveyed by @cite{richards-2013} — supplies the
   morphological precedent for treating Russian as having an underlying
   case stack visible only when language-particular spell-out preserves
   it.

2. **The Case Filter is recast, not invoked.** Case morphology *is* the
   realization of categorial structure; there is no separate `[uCase]`
   feature needing valuation. The default-nominative residue for
   apparent "caseless" DPs is left to the language-particular spell-out
   rules of Ch 2–3.

## Architecture in the formalization

FA (Feature Assignment) is a recursive `assignDown` over a node-and-stack
tree: when an assigner of POS-category α merges with β, α is pushed onto
the case stack of every leaf β dominates. The **One-Suffix Rule** is
then a single-line filter (`head?`); Lardil-style spell-out is the
identity.

Connections:

- `Core.Case` (Blake) gives the cross-linguistic case inventory; we
  bridge `POSCat → Finset Core.Case` (`POSCat.cases`) so Pesetsky's
  primitives plug into the existing typology with the multi-case
  oblique class made explicit.
- `Theories/Interfaces/Morphosyntax/CaseContainment.lean` (Caha) provides
  the morphological containment ranks. Whether Caha-style containment
  and Pesetsky-style derivational stack-order are actually inversely
  related is a separate question taken up by neither author and is not
  formalized here; we only reuse the rank function for NOM/ACC/GEN
  inspection.
- `Fragments/Slavic/Russian/Gender.lean` supplies declension classes and
  the hybrid noun *vrač*; Pesetsky's feminizing Ж analysis (Ch 5) is
  noted but not re-formalized.
- `Fragments/Slavic/Russian/Case.lean` lists the Russian 6-case
  inventory.

## Out of scope (deferred for separate study files)

- The full FA rule's developmental versions (Ch 2–8). The endpoint
  version is modeled: feature copy on Merge, percolation to all
  dominated leaves.
- The complete VACC restriction with referent-feature interaction.
- The D-headed PP analysis of POBL↔VACC spatial alternations (Ch 7).
- The locality restrictions on adnominal case (Ch 8 §8.2–8.3) and the
  loose-end *Prepositions That Appear to Assign NGEN* (§8.5).
- The Number Mismatch puzzle for paucals (Ch 4) — *dva stola* showing
  SG on the noun but PL on demonstratives/adjectives — and the
  Lebanese Arabic # parallel (Ch 5.3). The structural derivation that
  blocks D-NOM in numeral phrases (Quant-to-D with NBR pied-piping,
  eq. (61) p. 54) is the actual content of Ch 4–6 and is left to a
  follow-on study.
-/

namespace Phenomena.Case.Studies.Pesetsky2013

-- ============================================================================
-- § 1: POS Categories as Case Primitives
-- ============================================================================

/-- The four part-of-speech categories that double as case strata in
    Pesetsky's framework. Each category, when it serves as an assigner,
    realizes morphologically as the case(s) shown in the table at the top
    of this file. -/
inductive POSCat where
  /-- Genitive — the universal noun stratum (Primeval Genitive). -/
  | N
  /-- Nominative — assigned by D. -/
  | D
  /-- Accusative — assigned by transitive V, subject to VACC. -/
  | V
  /-- Obliques (DAT/INS/LOC/ABL/…) — assigned by P. Pesetsky writes the
      category as P_OBL with P_DAT as one exemplar (p. 7); the file does
      not refine the oblique class by POS, mirroring the paper. -/
  | P
  deriving DecidableEq, Repr

/-- The cases each POS category realizes as in `Core.Case`. N/D/V each
    map to a singleton; P maps to the oblique series since
    @cite{pesetsky-2013} (p. 7) explicitly does *not* refine the obliques
    by POS. The set listed for `.P` covers Russian's productive obliques —
    DAT, INS, LOC — plus ABL as a cross-linguistic placeholder. -/
def POSCat.cases : POSCat → Finset Core.Case
  | .N => {.gen}
  | .D => {.nom}
  | .V => {.acc}
  | .P => {.dat, .inst, .loc, .abl}

/-- The canonical exemplar case Pesetsky uses when naming each POS
    category. For P, the exemplar is DAT (p. 7); see `POSCat.cases` for
    the full oblique series. -/
def POSCat.canonicalExemplar : POSCat → Core.Case
  | .N => .gen
  | .D => .nom
  | .V => .acc
  | .P => .dat

/-- The canonical-exemplar projection is injective: each POS category has
    a distinct exemplar case in `Core.Case`. -/
theorem POSCat.canonicalExemplar_injective :
    Function.Injective POSCat.canonicalExemplar := by
  intro a b h; cases a <;> cases b <;> first | rfl | cases h

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

/-! `assignDown` and its helper are written as a `mutual` block because
    `PesTree` recurses through `List` and the leaf-case `rfl` proofs in
    §4–§6 require `assignDown` to reduce definitionally on `.leaf` —
    which the `kids.attach.map` form (compiled via well-founded
    recursion) does not provide. -/
mutual
  /-- The Feature Assignment rule (final form, Ch 8): on Merge, the
      assigner's category is copied as a case feature onto every leaf in
      its sister's domain. Modeled as a recursive descent that prepends
      `assigner` to every leaf's stack. Real FA only targets the
      sister, but for a single Merge step the result is the same as a
      full descent because the assigner doesn't yet dominate anything
      else. -/
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

/-- The **One-Suffix Rule** (@cite{pesetsky-2013} Ch 3). Russian
    pronounces only the *outermost* case stratum on each noun, deleting
    inner strata. This is why the universal primeval-N stratum (the
    bottom of the stack) is invisible in Russian morphology. -/
def oneSuffix : List POSCat → Option POSCat
  | s :: _ => some s
  | []     => none

/-- Lardil (@cite{richards-2013}, the morphological precedent that
    motivates the case-stacking analysis — Pesetsky cites it as the
    inspiration for treating Russian's underlying stack analogously)
    realizes the *entire* case stack overtly. The "rule" here is the
    identity — Lardil is what Russian would look like without the
    One-Suffix filter. -/
def lardilSpellOut : List POSCat → List POSCat := id

/-- One-Suffix on an empty stack yields nothing (no overt case marker). -/
theorem oneSuffix_empty : oneSuffix [] = none := rfl

/-- One-Suffix retains only the outermost stratum. -/
theorem oneSuffix_outermost (a : POSCat) (rest : List POSCat) :
    oneSuffix (a :: rest) = some a := rfl

/-- Lardil and Russian diverge whenever the stack has ≥ 2 strata: Russian
    shows only the outer, Lardil shows both. This is the core
    morphological signature of the proposal. -/
theorem lardil_russian_divergence (a b : POSCat) (rest : List POSCat) :
    lardilSpellOut (a :: b :: rest) ≠ (oneSuffix (a :: b :: rest)).toList := by
  simp only [lardilSpellOut, oneSuffix, Option.toList, id, ne_eq,
    List.cons.injEq, not_and]
  intro _; exact List.cons_ne_nil _ _

-- ============================================================================
-- § 4: The Primeval Genitive
-- ============================================================================

/-- The **Primeval Genitive Conjecture** (@cite{pesetsky-2013} eq. (6),
    p. 9): "NGEN categorizes a Russian root as a noun (in the lexicon)."
    A bare noun, before any further FA application, projects an N-stratum
    case feature.

    This is a categorizing-head property in the spirit of
    @cite{marantz-1997}'s root + categorizer architecture, not a
    syntactic stack initialization at the leaf. We approximate it here
    by giving the canonical leaf for a noun an initial `[.N]` stack;
    deriving this from a `Root → CategorizedNoun` morphism is left to a
    future refinement. -/
def primevalGenitive (w : String) : PesTree :=
  .leaf w [.N]

/-- Russian *kniga* 'book': bare, surface case is GEN (the N stratum)
    when no further FA applies — i.e. the noun is on its own and only
    its inherent N-stratum is realized. -/
theorem primeval_noun_surface_gen (w : String) :
    oneSuffix (primevalGenitive w).stack = some .N := rfl

/-- When a transitive V assigns its V-stratum, the Russian surface shows
    only V (the outer); the N stratum is *masked* by One-Suffix but
    still derivationally present. -/
theorem v_assignment_masks_n (w : String) :
    let stacked := assignDown .V (primevalGenitive w)
    oneSuffix stacked.stack = some .V := rfl

/-- The same derivation in a Lardil-style grammar shows both strata
    overtly: GEN (inner) plus ACC (outer). This is Pesetsky's
    cross-linguistic argument: Russian and Lardil have the *same*
    derivation; they differ only in whether the One-Suffix filter
    applies. -/
theorem lardil_shows_both_strata (w : String) :
    let stacked := assignDown .V (primevalGenitive w)
    lardilSpellOut stacked.stack = [.V, .N] := rfl

-- ============================================================================
-- § 5: Russian Numerals — Structural Roles, Not Case Assigners
-- ============================================================================

/-- Three numeral classes in Russian (@cite{pesetsky-2013} Ch 4–6). The
    classes differ in *where they merge* and *whether they raise to D*,
    not in case-assignment behavior — none of them is itself an FA case
    assigner in Pesetsky's framework:

    - **paucal** (`dva`, `tri`, `četyre`): an instance of NBR, base-merged
      directly with a numberless N inside NP (eq. (61), p. 54). The GEN
      morphology on the head noun is the *primeval* NGEN, not an
      assignment from the paucal.
    - **higher** (`pjat'`, `šest'`, …): an instance of QUANT, base-merged
      higher within NP and pied-piping NBR to D.
    - **quant** (`mnogo`, `nemnogo`, `skol'ko`): also QUANT, with the
      raising option absent for the indefinite-quantity exponents.

    Across all three the noun's surface case is GEN, but for a
    *structural* reason: the derivation blocks D from probing the noun
    (Quant-to-D with NBR pied-piping), so the primeval N stratum is the
    only one One-Suffix has to project. The full Quant-to-D derivation
    is the empirical core of Ch 4–6 and is **out of scope** for this
    file; this section only carries the lexical inventory and a
    sanity-check theorem on the surface prediction. -/
inductive RusNumClass where
  | paucal
  | higher
  | quant
  deriving DecidableEq, Repr

/-- A Russian numeral lexical entry. Minimal — just form and class.
    TODO: when a `Fragments/Slavic/Russian/Numerals.lean` exists, these
    entries should move there as theory-neutral lexical data. -/
structure RusNumeral where
  form : String
  cls  : RusNumClass
  deriving DecidableEq, Repr

def dva     : RusNumeral := ⟨"dva", .paucal⟩
def tri     : RusNumeral := ⟨"tri", .paucal⟩
def četyre  : RusNumeral := ⟨"četyre", .paucal⟩
def pjat'   : RusNumeral := ⟨"pjat'", .higher⟩
def šest'   : RusNumeral := ⟨"šest'", .higher⟩
def mnogo   : RusNumeral := ⟨"mnogo", .quant⟩
def skol'ko : RusNumeral := ⟨"skol'ko", .quant⟩

/-- The structural role of each numeral class within the extended NP. -/
inductive NumeralRole where
  /-- NBR head, base-merged inside NP with a numberless N. -/
  | nbrHead
  /-- QUANT head, base-merged above NP, may raise to D. -/
  | quantHead
  deriving DecidableEq, Repr

def RusNumClass.role : RusNumClass → NumeralRole
  | .paucal => .nbrHead
  | .higher => .quantHead
  | .quant  => .quantHead

/-- Paucals are NBR heads; higher and quant are QUANT heads. -/
theorem role_partitions_classes :
    RusNumClass.paucal.role = .nbrHead ∧
    RusNumClass.higher.role = .quantHead ∧
    RusNumClass.quant.role  = .quantHead := ⟨rfl, rfl, rfl⟩

/-! Surface prediction shared by *dva stola*, *pjat' stolov*, *mnogo
    studentov*: GEN morphology on the head noun. In this file's
    simplified model — where numerals do not themselves invoke FA — the
    noun retains its primeval `[.N]` stack and One-Suffix selects N.
    The witness is `primeval_noun_surface_gen` from §4; no separate
    numeral-indexed theorem is needed because the file's apparatus has
    no way for the numeral to influence the head noun's stack. The
    *structural* mechanism that prevents later FA from D (Quant-to-D,
    eq. (61) p. 54) is the actual content of Pesetsky Ch 4–6 and is
    out of scope. -/

-- ============================================================================
-- § 6: Nominative as D-Assignment, Accusative as V-Assignment
-- ============================================================================

/-- A subject DP receives nominative because D assigns it. The
    derivation: bare noun with primeval N stratum → D applies (now NOM
    under One-Suffix). -/
theorem subject_surface_nom (n : String) :
    let dp := assignDown .D (primevalGenitive n)
    oneSuffix dp.stack = some .D := rfl

/-- An object DP receives accusative because V assigns it. Same
    derivation but with V instead of D. -/
theorem object_surface_acc (n : String) :
    let dp := assignDown .V (primevalGenitive n)
    oneSuffix dp.stack = some .V := rfl

/-- Subject vs. object derivations differ only in the *outermost*
    assigner; the primeval-N stratum underneath is identical. -/
theorem subject_object_same_inner (n : String) :
    let subj := assignDown .D (primevalGenitive n)
    let obj  := assignDown .V (primevalGenitive n)
    subj.stack.tail = obj.stack.tail := rfl

-- ============================================================================
-- § 7: Bridges to existing infrastructure
-- ============================================================================

/-- The cases realized by Pesetsky's four POS categories — the union of
    `POSCat.cases` over the four categories. Stated as an explicit
    literal so membership reduces under `decide` without unfolding
    `Finset.biUnion` through `Quot.lift`; equivalence to the biUnion
    form is recorded by `pesetskyCore_eq_image` below. -/
def pesetskyCore : Finset Core.Case :=
  {.gen, .nom, .acc, .dat, .inst, .loc, .abl}

/-- `pesetskyCore` agrees with the union of `POSCat.cases` over all four
    POS categories. -/
theorem pesetskyCore_eq_image :
    pesetskyCore =
      POSCat.cases .N ∪ POSCat.cases .D ∪ POSCat.cases .V ∪ POSCat.cases .P :=
  rfl

/-- Every case in the canonical-exemplar image lies in `pesetskyCore`. -/
theorem canonicalExemplar_mem_pesetskyCore (p : POSCat) :
    p.canonicalExemplar ∈ pesetskyCore := by
  cases p <;> decide

/-- The Russian 4-case canonical spine — the image of `POSCat` under
    `canonicalExemplar` — sits inside the Russian inventory. -/
theorem canonicalExemplar_image_in_russian_inventory (p : POSCat) :
    p.canonicalExemplar ∈ Fragments.Slavic.Russian.Case.caseInventory := by
  cases p <;> decide

/-- The three productive Russian obliques are all in `pesetskyCore`,
    contributed by the P category. The file's earlier formulation —
    that INS and LOC were "outside" the image — relied on `toCase`
    projecting `.P` to `.dat` alone, which the expanded `cases` map
    corrects in line with @cite{pesetsky-2013} p. 7. -/
theorem russian_obliques_in_pesetsky_core :
    (.dat : Core.Case) ∈ pesetskyCore ∧
    (.inst : Core.Case) ∈ pesetskyCore ∧
    (.loc : Core.Case) ∈ pesetskyCore := by decide

/-- `containmentRank` (@cite{caha-2009}) for the three cases covered by
    the `POSCat`-canonical-exemplar image other than DAT. The bare ranks
    are recorded here for inspection by callers; whether Caha's
    morphological containment and Pesetsky's derivational stack-order
    are systematically inversely related is a question taken up by
    neither author and is *not* claimed by this file. -/
theorem caha_ranks_for_pesetsky_core_n_d_v :
    Core.Case.containmentRank .nom = some 0 ∧
    Core.Case.containmentRank .acc = some 1 ∧
    Core.Case.containmentRank .gen = some 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- Pesetsky's feminizing analysis of *vrač* 'doctor' (Ch 5) interacts
    with the existing hybrid-noun analysis in
    `Fragments.Slavic.Russian.Gender`. Pesetsky posits a null Ж morpheme
    above `vrač` when the referent is female; that morpheme licenses
    feminine agreement. The hybrid declension class assignment
    `vrač.declClass = some .I` from the fragment is preserved. -/
theorem vrač_morphological_class_unchanged :
    Fragments.Slavic.Russian.Gender.vrač.declClass =
      some Fragments.Slavic.Russian.Gender.DeclClass.I := rfl

end Phenomena.Case.Studies.Pesetsky2013
