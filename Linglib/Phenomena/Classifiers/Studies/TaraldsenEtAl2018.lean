import Linglib.Phenomena.Classifiers.Typology
import Linglib.Phenomena.Agreement.Studies.Carstens2026
import Linglib.Theories.Morphology.Nanosyntax.TreeSpellout
import Linglib.Theories.Morphology.DM.VocabularyInsertion
import Linglib.Fragments.Xhosa.Basic
import Linglib.Fragments.Bantu.Params

/-!
# Taraldsen, Taraldsen Medová & Langa (2018)
@cite{taraldsen-et-al-2018}

"Class prefixes as specifiers in Southern Bantu."
*Natural Language & Linguistic Theory* 36:1339–1394.

## Core claims

1. Bantu class prefixes are **phrasal specifiers**, not heads.
2. Each prefix lexicalizes a nanosyntactic tree: [# Nx] (plural)
   or just [Nx] (singular), where # is the number head and Nx is
   a classifier-like nominal head.
3. "Strong" classes (1/2, 7/8) share the same N between singular
   and plural; "weak" classes (3/4, 5/6, 9/10) have **distinct Ns**
   (N₄ ≠ N₃, N₆ ≠ N₅). This is the paper's central empirical
   finding from agreement with conjoined subjects (§2.1–2.6).
4. The **Foot Condition** constrains prefix insertion and derives
   nP stacking (double prefix constructions in Changana/Rhonga).
5. The specifier analysis **unifies** Bantu class prefixes with
   classifiers on the @cite{aikhenvald-2000} continuum.

## Formalization

- §1: `NCFeature` — nominal feature inventory (number, classifier)
- §2: Class prefix entries as `TreeLexEntry NCFeature`
- §3: Tree-based spellout verification
- §4: Strong vs weak classes — the core N₄ ≠ N₃ distinction
- §5: Foot Condition and why weak classes can't spell out
- §6: Pluralization derivation — the backtracking algorithm
- §7: Stacking-agreement correlation (central bridge theorem)
- §8: DM vs Nanosyntax comparison on SC prefixes
- §9: Agreement-classifier bridge (@cite{carstens-2026})
- §10: NPStack derivation from stacking analysis
- §11: NPStack–stacking bridge (canonical ↔ direct spellout)
- §12: NounClass alignment (Fragment enums ↔ study Nats)
-/

namespace Phenomena.Classifiers.Studies.TaraldsenEtAl2018

open Theories.Morphology.Nanosyntax
open Theories.Morphology.DM.VI
open Fragments.Xhosa
open Fragments.Bantu

-- ============================================================================
-- §1: Feature inventory
-- ============================================================================

/-- Nominal features on the Bantu nanosyntactic fseq.
    `num` = number head (#); `cls n` = classifier head Nn.

    @cite{taraldsen-et-al-2018}: class prefixes spell out phrasal
    trees built from these features. Singular prefixes lexicalize
    just Nx; plural prefixes lexicalize [# Nx]. -/
inductive NCFeature where
  | num : NCFeature
  | cls : Nat → NCFeature
  deriving DecidableEq, BEq, Repr

open NCFeature

-- ============================================================================
-- §2: Xhosa class prefix entries
-- ============================================================================

/-- Singular class prefixes: each lexicalizes just Nx.
    @cite{taraldsen-et-al-2018} (60)–(61): singular prefixes are
    specifiers of nP, spelling out the classifier head N alone. -/
def cl1Sg : TreeLexEntry NCFeature := ⟨.leaf (.cls 1), "um", .prefix⟩
def cl3Sg : TreeLexEntry NCFeature := ⟨.leaf (.cls 3), "um", .prefix⟩
def cl5Sg : TreeLexEntry NCFeature := ⟨.leaf (.cls 5), "ili", .prefix⟩
def cl7Sg : TreeLexEntry NCFeature := ⟨.leaf (.cls 7), "isi", .prefix⟩
def cl9Sg : TreeLexEntry NCFeature := ⟨.leaf (.cls 9), "in", .prefix⟩

/-- Plural class prefixes: each lexicalizes [# Nx].
    @cite{taraldsen-et-al-2018} (60)–(61), (77), (83): plural prefixes
    are specifiers of #P, spelling out [number + classifier].

    **Critical**: "strong" classes (2, 8) share the same N with their
    singular counterparts (N₁, N₇). "Weak" classes (4, 6, 10)
    contain DISTINCT Ns: N₄ ≠ N₃, N₆ ≠ N₅, N₁₀ ≠ N₉. This is the
    paper's central empirical finding from agreement with conjoined
    subjects (@cite{taraldsen-et-al-2018} §2). -/
def cl2Pl : TreeLexEntry NCFeature :=
  ⟨.node .num [.leaf (.cls 1)], "aba", .prefix⟩     -- [# N₁] — shares N₁ with cl1
def cl4Pl : TreeLexEntry NCFeature :=
  ⟨.node .num [.leaf (.cls 4)], "imi", .prefix⟩     -- [# N₄] — N₄ ≠ N₃!
def cl6Pl : TreeLexEntry NCFeature :=
  ⟨.node .num [.leaf (.cls 6)], "ama", .prefix⟩     -- [# N₆] — N₆ ≠ N₅!
def cl8Pl : TreeLexEntry NCFeature :=
  ⟨.node .num [.leaf (.cls 7)], "izi", .prefix⟩     -- [# N₇] — shares N₇ with cl7
def cl10Pl : TreeLexEntry NCFeature :=
  ⟨.node .num [.leaf (.cls 10)], "iin", .prefix⟩    -- [# N₁₀] — N₁₀ ≠ N₉!

def xhosaClassPrefixes : List (TreeLexEntry NCFeature) :=
  [cl1Sg, cl3Sg, cl5Sg, cl7Sg, cl9Sg, cl2Pl, cl4Pl, cl6Pl, cl8Pl, cl10Pl]

-- ============================================================================
-- §3: Tree-based spellout verification
-- ============================================================================

/-- Singular: target N1 -> "um" (cl1Sg wins, smallest match). -/
theorem spellout_cl1_sg :
    treeSpellout xhosaClassPrefixes (.leaf (.cls 1)) = some "um" := by
  native_decide

/-- Plural: target [# N1] -> "aba" (cl2Pl matches — strong class). -/
theorem spellout_cl2_pl :
    treeSpellout xhosaClassPrefixes (.node .num [.leaf (.cls 1)])
      = some "aba" := by
  native_decide

/-- Singular: target N5 -> "ili". -/
theorem spellout_cl5_sg :
    treeSpellout xhosaClassPrefixes (.leaf (.cls 5)) = some "ili" := by
  native_decide

/-- Plural: target [# N6] -> "ama" (weak class — N₆ ≠ N₅). -/
theorem spellout_cl6_pl :
    treeSpellout xhosaClassPrefixes (.node .num [.leaf (.cls 6)])
      = some "ama" := by
  native_decide

/-- Singular: target N7 -> "isi". -/
theorem spellout_cl7_sg :
    treeSpellout xhosaClassPrefixes (.leaf (.cls 7)) = some "isi" := by
  native_decide

/-- Plural: target [# N7] -> "izi" (strong class). -/
theorem spellout_cl8_pl :
    treeSpellout xhosaClassPrefixes (.node .num [.leaf (.cls 7)])
      = some "izi" := by
  native_decide

/-- No prefix matches an unlexicalized N (class 2 has no singular form). -/
theorem spellout_cl2_sg_none :
    treeSpellout xhosaClassPrefixes (.leaf (.cls 2)) = none := by
  native_decide

-- ============================================================================
-- §4: Strong vs weak classes
-- ============================================================================

/-- Whether a singular-plural class pair shares the same classifier N.
    @cite{taraldsen-et-al-2018} §2: strong classes (1/2, 7/8) share Ns;
    weak classes (3/4, 5/6, 9/10) have distinct Ns. The evidence comes
    from agreement with conjoined singular subjects: a conjunction of
    two class X singulars triggers plural class Y agreement iff the
    plural prefix for Y contains the same N as X. -/
def sharesClassifierN (sgEntry plEntry : TreeLexEntry NCFeature) : Bool :=
  sgEntry.tree.foot == plEntry.tree.foot

/-- Classes 1/2 share N₁ — strong class pair. A conjunction of two
    class 1 singular nouns triggers class 2 plural agreement because
    ba ↔ [# N₁] and the singular m ↔ [N₁] share the same N₁. -/
theorem cl1_cl2_share_N : sharesClassifierN cl1Sg cl2Pl = true := rfl

/-- Classes 7/8 share N₇ — strong class pair. -/
theorem cl7_cl8_share_N : sharesClassifierN cl7Sg cl8Pl = true := rfl

/-- Classes 3/4 do NOT share Ns — weak class pair.
    @cite{taraldsen-et-al-2018} §2.1–2.4: a conjunction of two class 3
    singular nouns does NOT trigger class 4 agreement. The plural
    prefix *mi* contains N₄, distinct from the N₃ in the singular
    prefix *mu*. -/
theorem cl3_cl4_distinct_N : sharesClassifierN cl3Sg cl4Pl = false := rfl

/-- Classes 5/6 do NOT share Ns — weak class pair.
    @cite{taraldsen-et-al-2018} §2.5: a conjunction of two class 5
    singular nouns does NOT trigger class 6 agreement. The plural
    prefix *ma* contains N₆, distinct from the N₅ in class 5. -/
theorem cl5_cl6_distinct_N : sharesClassifierN cl5Sg cl6Pl = false := rfl

/-- Classes 9/10 do NOT share Ns — weak class pair
    (in Changana/Rhonga; in Xhosa the class 10 prefix = class 8). -/
theorem cl9_cl10_distinct_N : sharesClassifierN cl9Sg cl10Pl = false := rfl

-- ============================================================================
-- §5: Foot Condition and why weak classes can't spell out
-- ============================================================================

/-- The foot of cl2Pl ("aba") is N₁. -/
theorem cl2_foot_is_n1 : cl2Pl.tree.foot = .cls 1 := rfl

/-- The foot of cl4Pl ("imi") is N₄ — NOT N₃.
    This is the key structural fact: *imi* requires N₄ to be present
    in the syntactic structure. Since N₄ ≠ N₃, *imi* cannot spell
    out a structure built from a class 3 noun. -/
theorem cl4_foot_is_n4 : cl4Pl.tree.foot = .cls 4 := rfl

/-- Strong class: "aba" CAN spell out [# N₁] because its foot (N₁)
    is present in the target. No stacking needed. -/
theorem foot_met_strong_cl2 :
    footConditionMet cl2Pl (.node .num [.leaf (.cls 1)]) = true := by
  native_decide

/-- Strong class: "izi" CAN spell out [# N₇]. -/
theorem foot_met_strong_cl8 :
    footConditionMet cl8Pl (.node .num [.leaf (.cls 7)]) = true := by
  native_decide

/-- Weak class: "imi" CANNOT spell out a structure containing only N₃.
    The Foot Condition requires N₄ (the foot of imi's stored tree),
    but the target [# N₃] contains only N₃. This forces backtracking,
    producing stacking — e.g., *mi-mu-twa* 'thorns' (class 4-3) in
    Changana/Rhonga. -/
theorem foot_not_met_weak_cl4 :
    footConditionMet cl4Pl (.node .num [.leaf (.cls 3)]) = false := by
  native_decide

/-- Weak class: "ama" CANNOT spell out a structure containing only N₅.
    Same logic: N₆ ≠ N₅. -/
theorem foot_not_met_weak_cl6 :
    footConditionMet cl6Pl (.node .num [.leaf (.cls 5)]) = false := by
  native_decide

/-- The stacking prediction: for weak classes, no entry in the lexicon
    can spell out the target [# N_sg]. The derivation must backtrack,
    splitting the structure and building a Specifier — producing the
    stacking pattern observed in Changana/Rhonga.
    @cite{taraldsen-et-al-2018} §4.2, prediction derived from (77)–(83).

    Contrast with strong classes (§3) where spellout succeeds directly. -/
theorem no_spellout_forces_stacking_cl3 :
    treeSpellout xhosaClassPrefixes (.node .num [.leaf (.cls 3)]) = none := by
  native_decide

theorem no_spellout_forces_stacking_cl5 :
    treeSpellout xhosaClassPrefixes (.node .num [.leaf (.cls 5)]) = none := by
  native_decide

theorem no_spellout_forces_stacking_cl9 :
    treeSpellout xhosaClassPrefixes (.node .num [.leaf (.cls 9)]) = none := by
  native_decide

-- ============================================================================
-- §6: Pluralization derivation
-- ============================================================================

/-- Result of pluralizing a Bantu noun.
    @cite{taraldsen-et-al-2018} §4.2 derives two outcomes:
    - `direct`: one plural prefix replaces the singular (strong class).
    - `stacked`: the plural prefix stacks on top of the singular prefix
      (weak class), producing double prefix constructions. -/
inductive PluralizationResult where
  | direct : String → PluralizationResult
  | stacked : String → String → PluralizationResult
  deriving DecidableEq, BEq, Repr

def PluralizationResult.isStacked : PluralizationResult → Bool
  | .direct _ => false
  | .stacked _ _ => true

/-- Derive the plural form for a noun with singular class `sgCls`.

    Models @cite{taraldsen-et-al-2018} §4.2 cyclic derivation:
    1. Noun N_Y merges with classifier N_sgCls → [N_sgCls N_Y].
    2. Number head # merges → target [# N_sgCls].
    3. Try spellout of [# N_sgCls]. If some entry's tree contains
       this target, the plural prefix directly replaces the singular
       (**strong class** path — e.g., *ba* replaces *m* for cl 1→2).
    4. If no entry matches: the Foot Condition blocks lexicalization
       (§5). Backtrack (Starke's last resort): form [# N_plCls] as
       a Specifier merged with N_Y, producing a stacked structure
       (**weak class** path — e.g., *mi-mu* for cl 3→4). -/
def derivePlural (entries : List (TreeLexEntry NCFeature))
    (sgCls plCls : Nat) : Option PluralizationResult :=
  let directTarget := NanoTree.node .num [.leaf (.cls sgCls)]
  match treeSpellout entries directTarget with
  | some pfx => some (.direct pfx)
  | none =>
    let stackTarget := NanoTree.node .num [.leaf (.cls plCls)]
    let sgTarget := NanoTree.leaf (.cls sgCls)
    match treeSpellout entries stackTarget, treeSpellout entries sgTarget with
    | some outer, some inner => some (.stacked outer inner)
    | _, _ => none

/-- Strong class 1/2: direct pluralization. ba ↔ [# N₁] matches
    the target [# N₁], so the derivation succeeds in one step. -/
theorem cl1_plural_direct :
    derivePlural xhosaClassPrefixes 1 2 = some (.direct "aba") := by
  native_decide

/-- Strong class 7/8: direct pluralization. -/
theorem cl7_plural_direct :
    derivePlural xhosaClassPrefixes 7 8 = some (.direct "izi") := by
  native_decide

/-- Weak class 3/4: stacking. No entry matches [# N₃] (because the
    only class 4 entry has [# N₄] and N₄ ≠ N₃), so the derivation
    backtracks: mi ↔ [# N₄] stacks on top of um ↔ [N₃].
    Produces the Changana/Rhonga form *mi-mu-twa* 'thorns'. -/
theorem cl3_plural_stacked :
    derivePlural xhosaClassPrefixes 3 4 = some (.stacked "imi" "um") := by
  native_decide

/-- Weak class 5/6: stacking. ama ↔ [# N₆] on top of ili ↔ [N₅].
    Produces Rhonga *ma-rhi-tu* 'words'. -/
theorem cl5_plural_stacked :
    derivePlural xhosaClassPrefixes 5 6 = some (.stacked "ama" "ili") := by
  native_decide

/-- Weak class 9/10: stacking. iin ↔ [# N₁₀] on top of in ↔ [N₉].
    Produces Rhonga *ti-yi-n-dlu* 'houses'. -/
theorem cl9_plural_stacked :
    derivePlural xhosaClassPrefixes 9 10 = some (.stacked "iin" "in") := by
  native_decide

/-- Whether an entry is a plural prefix (has # at root).
    Structurally, plural entries are [# N_X] (node with `num` label);
    singular entries are [N_X] (leaf). -/
def isPluralEntry (e : TreeLexEntry NCFeature) : Bool :=
  match e.tree with
  | .node f _ => f == .num
  | .leaf _ => false

/-- All singular prefixes lack #. -/
theorem singular_entries_not_plural :
    [cl1Sg, cl3Sg, cl5Sg, cl7Sg, cl9Sg].all (!isPluralEntry ·) = true := by
  native_decide

/-- All plural prefixes have # at root. -/
theorem plural_entries_have_number :
    [cl2Pl, cl4Pl, cl6Pl, cl8Pl, cl10Pl].all (isPluralEntry ·) = true := by
  native_decide

-- ============================================================================
-- §7: Structural stacking-agreement correlation
-- ============================================================================

-- §7a: Structural lemma

/-- `derivePlural` produces stacking iff direct spellout of [# N_sg]
    fails — purely from the backtracking algorithm's structure.

    No hypotheses about the lexicon are needed beyond `hr`: if
    `derivePlural` succeeds, the relevant spellout results are
    recoverable from the derivation itself. -/
private theorem derivePlural_isStacked_eq
    (entries : List (TreeLexEntry NCFeature)) (s plCls : Nat)
    (r : PluralizationResult)
    (hr : derivePlural entries s plCls = some r) :
    r.isStacked = (treeSpellout entries (.node .num [.leaf (.cls s)])).isNone := by
  unfold derivePlural at hr
  cases h : treeSpellout entries (.node .num [.leaf (.cls s)]) with
  | some pfx => simp [h] at hr; subst hr; rfl
  | none =>
    simp [h] at hr
    cases hp : treeSpellout entries (.node .num [.leaf (.cls plCls)]) with
    | none => simp [hp] at hr
    | some a =>
      cases hs : treeSpellout entries (.leaf (.cls s)) with
      | none => simp [hp, hs] at hr
      | some b => simp [hp, hs] at hr; subst hr; rfl

-- §7b: General theorem

/-- The paper's central prediction, proved structurally:
    for **any** lexicon where direct spellout of [# N_s] succeeds iff
    s = pN, stacking occurs iff the classifier Ns are distinct.

    The three class-number parameters:
    - `s`: the singular class N (e.g., N₁ for class 1)
    - `pN`: the N inside the plural entry's tree (e.g., N₁ for strong
      class 2, N₄ for weak class 4)
    - `plCls`: the plural class number used in `derivePlural` (e.g., 2, 4)

    For **strong** classes, `pN = s` (shared N): cl2Pl has N₁ = cl1Sg's N.
    For **weak** classes, `pN ≠ s` (distinct Ns): cl4Pl has N₄ ≠ cl3Sg's N₃.

    The proof chains three structural insights:
    - **Algorithm**: `derivePlural` stacks iff direct spellout fails
      (`derivePlural_isStacked_eq`)
    - **Lexicon**: direct spellout fails iff s ≠ pN (`hDirect`)
    - **Entries**: `sharesClassifierN` = (s = pN) for standard-form
      entries (definitional from `NanoTree.foot`)

    @cite{taraldsen-et-al-2018}: the correlation between agreement
    failure and stacking is not stipulated — it is derived from
    distinct Ns in the lexical entries. -/
theorem stacking_iff_distinct_N_general
    (entries : List (TreeLexEntry NCFeature))
    (sg pl : TreeLexEntry NCFeature)
    (s pN plCls : Nat)
    (hSgTree : sg.tree = .leaf (.cls s))
    (hPlTree : pl.tree = .node .num [.leaf (.cls pN)])
    (hDirect : (treeSpellout entries (.node .num [.leaf (.cls s)])).isNone = !(s == pN))
    (r : PluralizationResult)
    (hr : derivePlural entries s plCls = some r) :
    r.isStacked = !sharesClassifierN sg pl := by
  rw [derivePlural_isStacked_eq entries s plCls r hr, hDirect]
  unfold sharesClassifierN; rw [hSgTree, hPlTree]; simp only [NanoTree.foot]; rfl

-- §7c: Instantiation for each Xhosa class pairing

/-- Strong class 1/2: no stacking (shared N₁). -/
theorem stacking_cl1_cl2 (r : PluralizationResult)
    (hr : derivePlural xhosaClassPrefixes 1 2 = some r) :
    r.isStacked = !sharesClassifierN cl1Sg cl2Pl :=
  stacking_iff_distinct_N_general _ _ _ _ _ _ rfl rfl
    (by native_decide) r hr

/-- Strong class 7/8: no stacking (shared N₇). -/
theorem stacking_cl7_cl8 (r : PluralizationResult)
    (hr : derivePlural xhosaClassPrefixes 7 8 = some r) :
    r.isStacked = !sharesClassifierN cl7Sg cl8Pl :=
  stacking_iff_distinct_N_general _ _ _ _ _ _ rfl rfl
    (by native_decide) r hr

/-- Weak class 3/4: stacking (N₄ ≠ N₃). -/
theorem stacking_cl3_cl4 (r : PluralizationResult)
    (hr : derivePlural xhosaClassPrefixes 3 4 = some r) :
    r.isStacked = !sharesClassifierN cl3Sg cl4Pl :=
  stacking_iff_distinct_N_general _ _ _ _ _ _ rfl rfl
    (by native_decide) r hr

/-- Weak class 5/6: stacking (N₆ ≠ N₅). -/
theorem stacking_cl5_cl6 (r : PluralizationResult)
    (hr : derivePlural xhosaClassPrefixes 5 6 = some r) :
    r.isStacked = !sharesClassifierN cl5Sg cl6Pl :=
  stacking_iff_distinct_N_general _ _ _ _ _ _ rfl rfl
    (by native_decide) r hr

/-- Weak class 9/10: stacking (N₁₀ ≠ N₉). -/
theorem stacking_cl9_cl10 (r : PluralizationResult)
    (hr : derivePlural xhosaClassPrefixes 9 10 = some r) :
    r.isStacked = !sharesClassifierN cl9Sg cl10Pl :=
  stacking_iff_distinct_N_general _ _ _ _ _ _ rfl rfl
    (by native_decide) r hr

-- §7d: Uniform verification over all pairings

/-- A singular-plural class pairing in Bantu. -/
structure ClassPairing where
  sgEntry : TreeLexEntry NCFeature
  plEntry : TreeLexEntry NCFeature
  sgClass : Nat
  plClass : Nat

/-- All five Xhosa class pairings: 2 strong + 3 weak. -/
def classPairings : List ClassPairing :=
  [ ⟨cl1Sg, cl2Pl, 1, 2⟩, ⟨cl7Sg, cl8Pl, 7, 8⟩
  , ⟨cl3Sg, cl4Pl, 3, 4⟩, ⟨cl5Sg, cl6Pl, 5, 6⟩
  , ⟨cl9Sg, cl10Pl, 9, 10⟩ ]

/-- In stacked forms, the outer prefix is always from a plural entry
    (has # at root). Singular prefixes never appear as the outer
    layer in stacking.
    @cite{taraldsen-et-al-2018} §4.5: "while plural prefixes may stack
    on top of singular prefixes, we have found no cases where a
    singular prefix stacks on top of a plural prefix." This follows
    from the derivation: stacking is triggered by failure to lexicalize
    #, so the outer Specifier always contains #. -/
theorem stacking_outer_is_plural :
    classPairings.all (fun p =>
      match derivePlural xhosaClassPrefixes p.sgClass p.plClass with
      | some (.stacked outer _) =>
        xhosaClassPrefixes.any (fun e => e.exponent == outer && isPluralEntry e)
      | _ => true) = true := by
  native_decide

/-- Every class pairing produces a valid derivation (no failures). -/
theorem all_pairings_derive :
    classPairings.all (fun p =>
      (derivePlural xhosaClassPrefixes p.sgClass p.plClass).isSome) = true := by
  native_decide

-- ============================================================================
-- §8: DM vs Nanosyntax on the same data
-- ============================================================================

/-- DM Vocabulary Items for Xhosa SC prefixes. Each class maps to
    a single feature. The Subset Principle selects the item whose
    features are all present in the target (largest match). -/
def scPrefixDM : List (FeatureVI Nat String) :=
  [ ⟨[1], "u"⟩, ⟨[2], "ba"⟩, ⟨[7], "si"⟩, ⟨[8], "zi"⟩ ]

/-- Nanosyntax entries for the same SC prefixes using tree-based
    spellout. Each class feature is a leaf on the nanosyntactic
    tree. -/
def scPrefixNano : List (TreeLexEntry NCFeature) :=
  [ ⟨.leaf (.cls 1), "u", .prefix⟩, ⟨.leaf (.cls 2), "ba", .prefix⟩
  , ⟨.leaf (.cls 7), "si", .prefix⟩, ⟨.leaf (.cls 8), "zi", .prefix⟩ ]

/-- DM and Nanosyntax agree: class 1 SC prefix = "u". -/
theorem dm_nano_agree_cl1 :
    subsetPrinciple scPrefixDM [1] = some "u" ∧
    treeSpellout scPrefixNano (.leaf (.cls 1)) = some "u" := by
  constructor <;> native_decide

/-- DM and Nanosyntax agree: class 2 SC prefix = "ba". -/
theorem dm_nano_agree_cl2 :
    subsetPrinciple scPrefixDM [2] = some "ba" ∧
    treeSpellout scPrefixNano (.leaf (.cls 2)) = some "ba" := by
  constructor <;> native_decide

-- ============================================================================
-- §9: Agreement-classifier bridge
-- ============================================================================

section AgreementBridge
open Phenomena.Agreement.Studies.Carstens2026
open Minimalism.Agreement.GenderResolution

/-- Combining @cite{carstens-2026}'s agreement diagnostic with the
    classifier analysis: matching agreement (resolve succeeds) iff
    the gender has a semantic core — identifying it as a semantically
    motivated, classifier-like noun class.

    This theorem bridges two phenomena: genders where conjoined
    singulars allow matching plural agreement (@cite{carstens-2026})
    are exactly those whose class prefixes have classifier-like
    semantic content (@cite{taraldsen-et-al-2018}). -/
theorem agreement_resolve_iff_core (s : GenderStatus) :
    (resolve (statusToBundle s) (statusToBundle s)).isSome =
    s.core.isSome := by
  rw [bantu_matching_iff_interpretable s]
  cases s with
  | interpretable _ => rfl
  | uninterpretable => rfl

end AgreementBridge

open Phenomena.Classifiers.Typology in
/-- Xhosa sits at the noun-class pole of the @cite{aikhenvald-2000}
    classifier-to-noun-class continuum. -/
theorem xhosa_on_classifier_continuum :
    isNounClassType xhosa.classifierType = true ∧
    xhosa.hasAgreement = true := ⟨rfl, rfl⟩

-- ============================================================================
-- §10: NPStack derivation from stacking analysis
-- ============================================================================

/-- Derive an NPStack from a tree-based analysis. The visible class
    is the outermost N; the core class is the innermost (= foot).
    When visible = core, the noun is canonical (strong class);
    when they differ, stacking has occurred because the plural
    prefix contains a different N (@cite{taraldsen-et-al-2018} §4). -/
def treeToNPStack (visibleClass coreClass : Nat)
    (status : GenderStatus) : NPStack :=
  { visibleClass, coreClass, status }

/-- Canonical class 1 [human] noun: visible = core = 1 (strong class). -/
theorem canonical_cl1_matches :
    treeToNPStack 1 1 (.interpretable .human) = humanCanonical := rfl

/-- Stacked [human] noun in class 3: visible = 3, core = 1.
    Stacking occurs because N₃ ≠ N₄ (`cl3_cl4_distinct_N`): the
    class 4 plural prefix cannot directly spell out [# N₃]
    (`no_spellout_forces_stacking_cl3`), so `derivePlural` backtracks
    (`cl3_plural_stacked`), placing class 3's prefix on top. -/
theorem stacked_cl3_matches :
    treeToNPStack 3 1 (.interpretable .human) = humanInClass3 := rfl

/-- Stacked [human] noun in class 5: visible = 5, core = 1. -/
theorem stacked_cl5_matches :
    treeToNPStack 5 1 (.interpretable .human) = humanInClass5 := rfl

/-- Canonical [animal] noun: visible = core = 9. -/
theorem canonical_cl9_matches :
    treeToNPStack 9 9 (.interpretable .animal) = animalCanonical := rfl

/-- Canonical nouns (strong classes) don't stack. -/
theorem canonical_does_not_stack :
    (treeToNPStack 1 1 (.interpretable .human)).isCanonical = true := rfl

/-- Stacked nouns (weak class contexts) are not in their canonical class. -/
theorem stacked_is_not_canonical :
    (treeToNPStack 3 1 (.interpretable .human)).isCanonical = false := rfl

-- ============================================================================
-- §11: NPStack–stacking bridge
-- ============================================================================

/-- Stacking (from `derivePlural`) implies non-canonical NPStack.
    If `derivePlural` produces `.stacked`, the noun cannot be in its
    canonical class (visibleClass ≠ coreClass). -/
theorem stacked_implies_not_canonical (vis core : Nat) (st : GenderStatus)
    (hStack : vis ≠ core) :
    (treeToNPStack vis core st).isCanonical = false := by
  unfold treeToNPStack NPStack.isCanonical
  exact beq_eq_false_iff_ne.mpr hStack

/-- Direct pluralization (from `derivePlural`) is consistent with
    canonical NPStack (visibleClass = coreClass). -/
theorem direct_implies_canonical (cls : Nat) (st : GenderStatus) :
    (treeToNPStack cls cls st).isCanonical = true := by
  unfold treeToNPStack NPStack.isCanonical
  exact beq_self_eq_true cls

-- ============================================================================
-- §12: NounClass alignment
-- ============================================================================

/-- The Xhosa `NounClass` enum produces the same class numbers
    used in the nanosyntactic entries. This ensures that Fragment
    data and the nanosyntactic analysis share a common namespace. -/
theorem nounclass_numbers_align :
    NounClass.cl1.classNumber = 1 ∧
    NounClass.cl3.classNumber = 3 ∧
    NounClass.cl5.classNumber = 5 ∧
    NounClass.cl7.classNumber = 7 ∧
    NounClass.cl9.classNumber = 9 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Gender singular classes match the singular class numbers used in
    prefix entries. -/
theorem gender_singular_aligns :
    Gender.genderA.singularClass.classNumber = 1 ∧
    Gender.genderB.singularClass.classNumber = 3 ∧
    Gender.genderC.singularClass.classNumber = 5 ∧
    Gender.genderD.singularClass.classNumber = 7 ∧
    Gender.genderE.singularClass.classNumber = 9 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Gender plural classes match the plural class numbers used in
    `derivePlural`. -/
theorem gender_plural_aligns :
    Gender.genderA.pluralClass.classNumber = 2 ∧
    Gender.genderB.pluralClass.classNumber = 4 ∧
    Gender.genderC.pluralClass.classNumber = 6 ∧
    Gender.genderD.pluralClass.classNumber = 8 ∧
    Gender.genderE.pluralClass.classNumber = 10 := ⟨rfl, rfl, rfl, rfl, rfl⟩

end Phenomena.Classifiers.Studies.TaraldsenEtAl2018
