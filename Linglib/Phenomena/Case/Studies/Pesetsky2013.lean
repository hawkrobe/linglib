import Linglib.Core.Case.Basic
import Linglib.Core.Case.Order
import Linglib.Fragments.Slavic.Russian.Case
import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Theories.Syntax.Minimalist.Basic

/-!
# @cite{pesetsky-2013} — Russian Case Morphology and the Syntactic Categories

Pesetsky's central thesis: **morphological case is the realization of a
syntactic part-of-speech category**. The four major cases line up with
the four traditional lexical categories, formalized here as a
restriction of Minimalism's `Cat`:

| Case          | POS category | Assigner                                  |
|---------------|--------------|-------------------------------------------|
| Genitive      | N            | every noun (Primeval Genitive, p. 9)      |
| Nominative    | D            | the D head of a DP                        |
| Accusative    | V            | a transitive V (under VACC, eq. 77 p. 66) |
| Obliques      | P            | a P head; DAT canonical exemplar (p. 7)   |

Pesetsky writes (book p. 7): "only the distinctions among these oblique
cases in Russian will fail to correspond to a traditional
part-of-speech distinction" — P_OBL is canonical, P_DAT is one
exemplar with additional features. `POSCat.cases` returns the Russian
oblique series for `.P` (DAT/INS/LOC, matching
`Fragments.Slavic.Russian.Case.caseInventory`); `POSCat.canonicalExemplar`
picks DAT.

## Architecture: layered grounding on Minimalism

This is a **Minimalist study**. Its tree is `SyntacticObject`
(@cite{marcolli-chomsky-berwick-2025}, formalized in
`Theories/Syntax/Minimalist/Basic.lean`); its structure-building
operation is `merge`; its categories are members of `Cat`. Per-leaf
case stacks are a **derived structural property** of the
`SyntacticObject` — `caseStackAt` walks the tree, treating left-Merge
as "head + complement" per Pesetsky's Minimalist convention, and
prepends the head's POSCat to the complement's leaves. **No external
state, no side-map**: the case stack at a leaf is a function of the
tree structure plus the leaf's identity.

The genuinely paper-specific apparatus is small:

1. **POSCat** — the {N,D,V,P} restriction of Minimalism's `Cat` to the
   four case-bearing categories. The injection `POSCat.toCat` makes
   the restriction structural rather than parallel.
2. **caseStackAt / surfaceCase** — Pesetsky's FA realized as
   structural recursion over the SO. Each `.node head body` step in
   the tree corresponds to a Merge; if `head.outerCat` is a POSCat
   and the queried leaf is in `body`, the head's category is
   prepended to the leaf's stack. This is FA "version 3 of 6"
   (@cite{pesetsky-2013} eq. (76), book p. 65) made implicit:
   complementation-requirements gating is not modeled (treated as
   always satisfied), and "designated as feature assigner for β" is
   exactly the `POSCat.ofCat? head.outerCat` test (only N/D/V/P heads
   FA).
3. **One-Suffix Rule** (Ch 3) — Russian's spell-out: the outermost
   stratum (head of the stack) is realized; inner strata are deleted.
   Encoded by `surfaceCase = (caseStackAt ...).head?.map ...`.
4. **Primeval Genitive Conjecture** (eq. (6), p. 9) — NGEN
   categorizes a Russian root as a noun in the lexicon, in the spirit
   of @cite{marantz-1997}'s root + categorizer. **Automatic from the
   recursion**: a leaf with `outerCat = .N` carries `[POSCat.N]` in
   its base case, so any noun-categorized LIToken has primeval N
   without explicit initialization. The structural bridge to DM
   `Categorizer.n` is `primevalN_via_dm_categorizer`.

## Two corollaries reshape standard Case theory

1. **Every noun is "born" with NGEN** in the lexicon. The base case
   of `caseStackAt` for an `outerCat = .N` leaf returns `[POSCat.N]`
   without input.

2. **Nominative as Schützean default**. D-Merge assigns DNOM (eq. (87)
   p. 73 — D *does* assign nominative morphology); but DNOM is
   "default" in the sense of Schütze 1997, 2001 (cited p. 73): D's
   assignment survives in subject position because Russian finite T
   does not assign features under FA, so nothing later overwrites it.
   When V intervenes (transitive object under eq. 77 conditions), V
   overwrites with VACC; otherwise DNOM stays. This inverts the
   standard "T assigns NOM" view — Pesetsky writes (p. 72) that he
   has "never needed to assume that nominative morphology is assigned
   to the elements of DP by anything other than D itself."

## What is and isn't modeled

**Modeled:** FA version 3 of 6 (eq. (76) p. 65) with α-cat / β-target
entanglement implicit in the structural recursion; Russian One-Suffix
Rule; Primeval Genitive (with DM Categorizer.n bridge); the four POS
categories as restriction of `Cat`; the basic NOM/ACC/GEN/OBL bridge;
`noDeletionSpellOut` as the limiting "no deletion" case (Lardil
itself has *partial* deletion per Ch 3 §3.2 — modeled here as the
limit, with the actual Lardil pattern deferred); cross-framework
agreement bridge with @cite{caha-2009}.

**Out of scope (deferred to follow-on study files or commits):**
- The complete VACC restriction (eq. 77 p. 66 — `[+FEM,+SG] ∨ [+ANIM]
  ∨ [+PRONOMINAL]`) **plus** the realization rules eq. (80) p. 67
  (assignment-vs-realization is a two-layer story); to be added in a
  follow-on commit with a paper-local phi-feature side-map.
- FA versions 4-6: Spell-Out locality (Ch 8 §8.3 eq. (110)/(111)
  p. 87-88) and the Prototype mechanism (Ch 9). The current
  `caseStackAt` realizes onto every leaf of body; this is wrong for
  multi-leaf body under Spell-Out — for the single-leaf cases §6
  models, the difference doesn't arise.
- The Number Mismatch puzzle for paucals (Ch 4) — *dva stola* showing
  SG on the noun but PL on demonstratives/adjectives — and the
  Lebanese Arabic # parallel (Ch 5.3). The structural derivation
  (Quant-to-D with NBR pied-piping, eq. (61) p. 54) is left to a
  follow-on study.
- The full D-headed PP analysis of POBL↔VACC alternations (Ch 7).
- The realistic `[DP D [NP A N]]` Russian DP geometry (eq. (62)
  p. 54) — §6 theorems use the schematic `D + N` direct-merge.
- The complementation-requirements gate (eq. (76a)). The current
  recursion treats every Merge as FA-firing; modeling the gate
  requires either a Bool-tagged `Step` extension or filtering the
  derivation history.

## Connections

- `Theories/Syntax/Minimalist/Basic.lean` — the substrate. `Cat`,
  `SyntacticObject`, `LIToken`, `merge` all consumed here. The
  derivation-step infrastructure in
  `Theories/Syntax/Minimalist/Derivation.lean` is the natural next
  layer once FA gating is modeled.
- `Theories/Morphology/DM/Categorizer.lean` (@cite{harley-2014}) —
  the structural bridge `primevalN_via_dm_categorizer` connects
  `POSCat.N` to DM `Categorizer.n` via `Cat.N`.
- `Core.Case` (Blake) gives the cross-linguistic case inventory; we
  bridge `POSCat → Finset Core.Case` (`POSCat.cases`) so Pesetsky's
  primitives plug into the existing typology.
- `Core.Case.Order` provides Caha's `containmentRank`; the
  `pesetsky_caha_compatible_prefix` theorem records the cross-
  framework agreement (Pesetsky's on-Caha-hierarchy image equals
  Caha's full hierarchy).
- `Fragments/Slavic/Russian/Case.lean` lists the Russian 6-case
  inventory.
- *vrač* and Pesetsky's feminizing Ж analysis (Ch 5) are noted; the
  morphological-declension claim itself is owned by
  `Phenomena/Gender/Studies/Kramer2020.lean::vrač_morph_masculine`.
-/

namespace Phenomena.Case.Studies.Pesetsky2013

open Minimalist (Cat SyntacticObject LIToken LexicalItem merge mkLeaf
  mkLeafPhon)

-- ============================================================================
-- § 1: POS Categories as Restriction of Minimalism's Cat
-- ============================================================================

/-- Pesetsky's four POS-as-case categories. Each is the homonym of a
    member of Minimalism's `Cat`; `toCat` is the structural injection,
    `toCat_injective` proves the embedding faithful.

    Implementation note: this is an inductive type rather than a
    `Subtype` of `Cat` because pattern matching on a subtype requires
    totality branches for the unreachable Cat constructors — `Cat` has
    25+ constructors of which only 4 are POSCat-relevant. The
    inductive form with `toCat` injection carries the same content
    (the four-way restriction is provable, not just intended) without
    polluting every match with a `_ => unreachable`. -/
inductive POSCat where
  /-- Genitive — the universal noun stratum (Primeval Genitive). -/
  | N
  /-- Nominative — assigned by D. -/
  | D
  /-- Accusative — assigned by transitive V, subject to the eq. 77
      restriction. -/
  | V
  /-- Obliques (DAT/INS/LOC) — assigned by P. Pesetsky writes the
      category as P_OBL with P_DAT as the canonical exemplar
      (book p. 7); the file does not refine the oblique class by POS,
      mirroring the paper. -/
  | P
  deriving DecidableEq, Repr, Fintype

namespace POSCat

/-- Structural injection of POSCat into Minimalism's `Cat`. Each
    POSCat constructor maps to its homonym in Cat. -/
def toCat : POSCat → Cat
  | .N => .N
  | .D => .D
  | .V => .V
  | .P => .P

instance : Coe POSCat Cat := ⟨toCat⟩

theorem toCat_injective : Function.Injective toCat := by
  intro a b h; cases a <;> cases b <;> first | rfl | cases h

/-- The cases each POSCat realizes as in `Core.Case`. N/D/V each map
    to a singleton; P maps to the Russian productive oblique series
    (DAT/INS/LOC, matching `Fragments.Slavic.Russian.Case.caseInventory`)
    since @cite{pesetsky-2013} (p. 7) explicitly does *not* refine
    the obliques by POS. -/
def cases : POSCat → Finset Core.Case
  | .N => {.gen}
  | .D => {.nom}
  | .V => {.acc}
  | .P => {.dat, .inst, .loc}

/-- The canonical exemplar case Pesetsky uses when naming each POSCat.
    For P, the exemplar is DAT (p. 7); see `cases` for the full
    oblique series. -/
def canonicalExemplar : POSCat → Core.Case
  | .N => .gen
  | .D => .nom
  | .V => .acc
  | .P => .dat

theorem canonicalExemplar_injective :
    Function.Injective canonicalExemplar := by
  intro a b h; cases a <;> cases b <;> first | rfl | cases h

/-- Recover a POSCat from the corresponding Cat constructor, when
    possible. Returns `none` for non-case-bearing categories (T, C, v,
    n, Voice, Place, Path, ...). The `none` cases include the DM
    categorizers (`.n`, `.v`, `.a`) and Pesetsky's "non-FA-bearing"
    functional heads. -/
def ofCat? : Cat → Option POSCat
  | .N => some .N
  | .D => some .D
  | .V => some .V
  | .P => some .P
  | _  => none

theorem ofCat?_toCat (p : POSCat) : ofCat? p.toCat = some p := by
  cases p <;> rfl

end POSCat

-- ============================================================================
-- § 2: Case Stack as Structural Property of the SyntacticObject
-- ============================================================================

/-- Decidable membership of an LIToken in a SyntacticObject's leaves.
    Computed structurally without materializing the linearization. -/
def containsLeaf : SyntacticObject → LIToken → Bool
  | .leaf tok', tok => decide (tok = tok')
  | .node l r, tok => containsLeaf l tok || containsLeaf r tok

/-- The case stack at a leaf, computed by structural recursion over
    the SyntacticObject. **No external state**.

    Base case (leaf): if the queried leaf matches and its outerCat is
    `.N`, return `[POSCat.N]` (the Primeval Genitive — automatic from
    the categorial structure). Otherwise empty.

    Recursive case (node): standard Minimalist convention is left-
    headed binary Merge, so `.node head body` represents a Merge of
    `head` with `body` as its complement/sister. Per Pesetsky's
    eq. (76) p. 65 ("FA version 3 of 6"): if `head` is a designated
    feature assigner — formalized here as `head.outerCat ∈ {N,D,V,P}`
    — its POSCat is copied onto every leaf of `body`. The recursion
    finds which side the queried leaf is in: if in `head`, no FA
    contribution from this Merge; if in `body`, prepend the head's
    POSCat (when applicable) to whatever `body`'s recursive call
    returns. -/
def caseStackAt : SyntacticObject → LIToken → List POSCat
  | .leaf tok', tok =>
    if tok = tok' ∧ tok'.item.outerCat = .N then [POSCat.N] else []
  | .node head body, tok =>
    if containsLeaf head tok then
      caseStackAt head tok
    else if containsLeaf body tok then
      let bodyStack := caseStackAt body tok
      match POSCat.ofCat? head.outerCat with
      | some c => c :: bodyStack
      | none => bodyStack
    else []

/-- Russian One-Suffix Rule (@cite{pesetsky-2013} Ch 3): the outermost
    stratum (head of the stack) is realized as morphology; inner
    strata are deleted. Returns `none` for empty stacks (no overt
    case marker). -/
def surfaceCase (so : SyntacticObject) (tok : LIToken) : Option Core.Case :=
  (caseStackAt so tok).head?.map POSCat.canonicalExemplar

-- ============================================================================
-- § 3: One-Suffix Rule (Russian) vs. No-Deletion Spell-Out (Lardil limit)
-- ============================================================================

/-- The "no deletion" spell-out: realize the *entire* case stack
    overtly. The "rule" is the identity on stacks.

    This is the **limiting case** of "no deletion at all", not a
    faithful description of Lardil itself. Per @cite{richards-2013}
    and @cite{pesetsky-2013} Ch 3 §3.2, Lardil has *partial* deletion
    (e.g., FUT only stacks outside GEN, not outside ACC); a faithful
    Lardil model requires modeling the partial-deletion pattern, left
    for a follow-on `Phenomena/Case/Studies/Richards2013.lean`. -/
def noDeletionSpellOut : List POSCat → List POSCat := id

/-- No-deletion spell-out and Russian One-Suffix diverge whenever the
    stack has ≥ 2 strata: Russian shows only the outer (via
    `List.head?`), no-deletion shows both. This is the core
    morphological signature of the proposal — Russian being the
    deletion limit, Lardil-style stacking being intermediate. -/
theorem noDeletion_russian_divergence (a b : POSCat) (rest : List POSCat) :
    noDeletionSpellOut (a :: b :: rest) ≠ ((a :: b :: rest).head?).toList := by
  simp only [noDeletionSpellOut, id, List.head?_cons, Option.toList, ne_eq,
    List.cons.injEq, not_and]
  intro _; exact List.cons_ne_nil _ _

-- ============================================================================
-- § 4: The Primeval Genitive
-- ============================================================================

/-- The **Primeval Genitive Conjecture** (@cite{pesetsky-2013} eq. (6),
    book p. 9): "NGEN categorizes a Russian root as a noun (in the
    lexicon)." A bare noun, before any further FA application, has an
    N-stratum case feature.

    This is a categorizing-head property in the spirit of
    @cite{marantz-1997}'s root + categorizer architecture — the
    structural bridge to DM's `Categorizer.n` is recorded in
    `primevalN_via_dm_categorizer` below. In this file, **Primeval
    Genitive is automatic from the recursion**: a leaf with
    `outerCat = .N` returns `[POSCat.N]` from `caseStackAt`'s base
    case without any explicit initialization step.

    This convenience constructor builds an N-categorized leaf with
    the given phonological form. -/
def primevalGenitive (w : String) (id : Nat) : SyntacticObject :=
  mkLeafPhon .N [] w id

/-- Russian *kniga* 'book': bare, surface case is GEN (the N stratum
    realized via One-Suffix). The Primeval Genitive is automatic
    from the structural recursion — no explicit initialization needed. -/
theorem primeval_noun_surface_gen (w : String) (id : Nat) :
    surfaceCase (primevalGenitive w id)
        ⟨LexicalItem.simple .N [] (phonForm := w), id⟩ = some .gen := by
  simp [primevalGenitive, mkLeafPhon, surfaceCase, caseStackAt,
        LexicalItem.outerCat, LexicalItem.simple, POSCat.canonicalExemplar]

/-- Structural bridge: the N-stratum that `caseStackAt` produces for
    an N-categorized leaf agrees with the syntactic category produced
    by DM's `n` categorizer (@cite{harley-2014}, @cite{marantz-1997}).
    The Primeval Genitive Conjecture is the case-bearing reflection
    of root-level n-categorization — both produce `Cat.N` as the
    syntactic category. -/
theorem primevalN_via_dm_categorizer :
    POSCat.N.toCat = Morphology.DM.Categorizer.toCategory .n := rfl

/-- The cross-categorial dual: `POSCat.V` agrees with DM `Categorizer.v`.
    Together with `primevalN_via_dm_categorizer`, this records the
    structural alignment between Pesetsky's case-bearing categories
    and DM's lexical-category categorizers. P and D are not DM
    categorizers (they are functional heads), so no analog applies. -/
theorem posCatV_via_dm_categorizer :
    POSCat.V.toCat = Morphology.DM.Categorizer.toCategory .v := rfl

-- ============================================================================
-- § 5: Russian Numerals — Structural Roles, Not Case Assigners
-- ============================================================================

/-- Three numeral classes in Russian (@cite{pesetsky-2013} Ch 4–6).
    The classes differ in *where they merge* and *whether they raise
    to D*, not in case-assignment behavior — none of them is itself an
    FA case assigner in Pesetsky's framework:

    - **paucal** (`dva`, `tri`, `četyre`): an instance of NBR,
      base-merged directly with a numberless N inside NP (eq. (61),
      p. 54). The GEN morphology on the head noun is the *primeval*
      NGEN, not an assignment from the paucal.
    - **higher** (`pjat'`, `šest'`, …): an instance of QUANT,
      base-merged higher within NP and pied-piping NBR to D.
    - **quant** (`mnogo`, `nemnogo`, `skol'ko`): also QUANT, with the
      raising option absent for the indefinite-quantity exponents.

    Across all three the noun's surface case is GEN, but for a
    *structural* reason: the derivation blocks D from probing the noun
    (Quant-to-D with NBR pied-piping), so the primeval N stratum is
    the only one One-Suffix has to project. The full Quant-to-D
    derivation is the empirical core of Ch 4–6 and is **out of scope**
    for this file. -/
inductive RusNumClass where
  | paucal
  | higher
  | quant
  deriving DecidableEq, Repr

/-- A Russian numeral lexical entry. Minimal — just form and class.
    TODO: when a `Fragments/Slavic/Russian/Numerals.lean` exists,
    these entries should move there as theory-neutral lexical data. -/
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

/-- Iff form: paucals are exactly the NBR-head numerals. -/
theorem RusNumClass.role_eq_nbrHead_iff (c : RusNumClass) :
    c.role = .nbrHead ↔ c = .paucal := by
  cases c <;> simp [role]

/-- Iff form: higher and quant are exactly the QUANT-head numerals. -/
theorem RusNumClass.role_eq_quantHead_iff (c : RusNumClass) :
    c.role = .quantHead ↔ (c = .higher ∨ c = .quant) := by
  cases c <;> simp [role]

/-! Surface prediction shared by *dva stola*, *pjat' stolov*, *mnogo
    studentov*: GEN morphology on the head noun. In this file's
    simplified model — where numerals do not themselves invoke FA —
    the noun retains its primeval `[POSCat.N]` stack and One-Suffix
    selects N. The witness is `primeval_noun_surface_gen` from §4; no
    separate numeral-indexed theorem is needed because the file's
    apparatus has no way for the numeral to influence the head noun's
    stack. The *structural* mechanism that prevents later FA from D
    (Quant-to-D, eq. (61) p. 54) is the actual content of Pesetsky
    Ch 4–6 and is out of scope. -/

-- ============================================================================
-- § 6: Nominative as D-Assignment, Accusative as V-Assignment
-- ============================================================================

/-- Subject DP receives DNOM via D-Merge. The Schützean default
    framing (Pesetsky Ch 7 §7.2, eq. (87) p. 73): D *does* assign
    DNOM (book p. 72: "I have never needed to assume that nominative
    morphology is assigned to the elements of DP by anything other
    than D itself"); but DNOM is "default" in Schütze's sense (1997,
    2001 cited p. 73) because Russian finite T does not assign
    features under FA, so D's DNOM survives — nothing later
    overwrites it in subject position.

    Schematic geometry: this theorem uses the minimal `D + N`
    direct-merge demonstrating FA mechanics. The realistic Russian DP
    (eq. (62) p. 54) is `[DP D [NP A N]]` and is left to a follow-on
    commit. Note: distinctness of the noun's and D-head's LITokens is
    automatic from their different `item` fields (different cats);
    the LIToken IDs may even coincide harmlessly. -/
theorem subject_surface_nom (w : String) (idN idD : Nat) :
    let nounTok : LIToken := ⟨LexicalItem.simple .N [] (phonForm := w), idN⟩
    let dHead : SyntacticObject := mkLeaf .D [.N] idD
    surfaceCase (merge dHead (.leaf nounTok)) nounTok = some .nom := by
  simp [merge, surfaceCase, caseStackAt, containsLeaf, mkLeaf,
        SyntacticObject.outerCat, SyntacticObject.leftmostLeaf,
        LexicalItem.outerCat, LexicalItem.simple, POSCat.ofCat?,
        POSCat.canonicalExemplar]

/-- Object DP receives VACC via V-Merge — when Pesetsky's eq. (77)
    restriction is satisfied (the [+FEM,+SG] / [+ANIM] / [+PRONOMINAL]
    disjunction; modeled in a follow-on commit). This *unrestricted*
    version is the schematic FA-success case; eq. (77) gates whether
    FA *applies*, eq. (80) gates whether VACC is *realized* — the
    file currently models neither of these two layers, hence the
    `unrestricted` naming. -/
theorem object_surface_acc_unrestricted
    (w : String) (idN idV : Nat) :
    let nounTok : LIToken := ⟨LexicalItem.simple .N [] (phonForm := w), idN⟩
    let vHead : SyntacticObject := mkLeaf .V [.N] idV
    surfaceCase (merge vHead (.leaf nounTok)) nounTok = some .acc := by
  simp [merge, surfaceCase, caseStackAt, containsLeaf, mkLeaf,
        SyntacticObject.outerCat, SyntacticObject.leftmostLeaf,
        LexicalItem.outerCat, LexicalItem.simple, POSCat.ofCat?,
        POSCat.canonicalExemplar]

/-- Subject vs. object derivations differ only in the *outermost*
    assigner; the primeval-N stratum underneath is identical. -/
theorem subject_object_same_inner (w : String) (idN idD idV : Nat) :
    let nounTok : LIToken := ⟨LexicalItem.simple .N [] (phonForm := w), idN⟩
    let dHead : SyntacticObject := mkLeaf .D [.N] idD
    let vHead : SyntacticObject := mkLeaf .V [.N] idV
    (caseStackAt (merge dHead (.leaf nounTok)) nounTok).tail =
      (caseStackAt (merge vHead (.leaf nounTok)) nounTok).tail := by
  simp [merge, caseStackAt, containsLeaf, mkLeaf,
        SyntacticObject.outerCat, SyntacticObject.leftmostLeaf,
        LexicalItem.outerCat, LexicalItem.simple, POSCat.ofCat?]

-- ============================================================================
-- § 7: Bridges to Existing Infrastructure
-- ============================================================================

/-- The image of POSCat in `Cat` is exactly the four case-bearing
    members. This is the structural alignment with Minimalism: POSCat
    is not a separate enum but the {N,D,V,P} restriction of `Cat`. -/
theorem POSCat.image_in_cat :
    Set.range POSCat.toCat = ({Cat.N, Cat.D, Cat.V, Cat.P} : Set Cat) := by
  ext c
  constructor
  · rintro ⟨p, rfl⟩; cases p <;> simp [POSCat.toCat]
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨.N, rfl⟩, ⟨.D, rfl⟩, ⟨.V, rfl⟩, ⟨.P, rfl⟩]

/-- The cases realized by Pesetsky's four POS categories. Defined as
    an explicit literal so membership reduces under `decide` —
    `Finset.biUnion` (the conceptually purer form) blocks `decide` on
    its `Multiset.Quot.lift` reduction. -/
def pesetskyCore : Finset Core.Case :=
  {.gen, .nom, .acc, .dat, .inst, .loc}

/-- `pesetskyCore` is the union of `POSCat.cases` over all four POS
    categories — the content the literal definition is shorthand for. -/
theorem pesetskyCore_eq_biUnion_image (c : Core.Case) :
    c ∈ pesetskyCore ↔ ∃ p : POSCat, c ∈ p.cases := by
  constructor
  · intro hc
    simp only [pesetskyCore, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨.N, by decide⟩, ⟨.D, by decide⟩, ⟨.V, by decide⟩,
            ⟨.P, by decide⟩, ⟨.P, by decide⟩, ⟨.P, by decide⟩]
  · rintro ⟨p, hp⟩
    cases p <;> · simp only [POSCat.cases, Finset.mem_insert,
                              Finset.mem_singleton] at hp
                  rcases hp with rfl | rfl | rfl <;> decide

/-- Every case in the canonical-exemplar image lies in `pesetskyCore`. -/
theorem canonicalExemplar_mem_pesetskyCore (p : POSCat) :
    p.canonicalExemplar ∈ pesetskyCore := by
  cases p <;> decide

/-- The canonical-exemplar image sits inside the Russian inventory. -/
theorem canonicalExemplar_image_in_russian_inventory (p : POSCat) :
    p.canonicalExemplar ∈ Fragments.Slavic.Russian.Case.caseInventory := by
  cases p <;> decide

/-- The three productive Russian obliques are all in `pesetskyCore`,
    contributed by the P category per @cite{pesetsky-2013} p. 7. -/
theorem russian_obliques_in_pesetsky_core :
    (.dat : Core.Case) ∈ pesetskyCore ∧
    (.inst : Core.Case) ∈ pesetskyCore ∧
    (.loc : Core.Case) ∈ pesetskyCore := by decide

/-- **Cross-framework agreement with @cite{caha-2009}**: Pesetsky's
    POS-as-case image, restricted to the cases that have a
    `containmentRank` in Caha's hierarchy
    (NOM⊂ACC⊂GEN⊂DAT⊂LOC⊂...), coincides with the standard
    five-case core. Pesetsky additionally puts INST in `pesetskyCore`
    (via `.P`) — this is the case Caha's hierarchy doesn't rank
    (compare `Core/Case/Order.lean`'s docstring listing
    "ERG, ABS, INST, COM" as off-hierarchy).

    A non-trivial *agreement* — not refutation. The two frameworks
    identify the same five-case core, with Pesetsky adding INST
    outside the Caha hierarchy. -/
theorem pesetsky_caha_compatible_prefix :
    pesetskyCore.filter (fun c => (Core.Case.containmentRank c).isSome) =
      ({.nom, .acc, .gen, .dat, .loc} : Finset Core.Case) := by
  decide

end Phenomena.Case.Studies.Pesetsky2013
