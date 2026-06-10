import Linglib.Morphology.Nanosyntax.TreeSpellout
import Linglib.Fragments.Xhosa.Basic

/-!
# Taraldsen, Taraldsen Medová & Langa (2018): class prefixes as specifiers

[taraldsen-et-al-2018] (*NLLT* 36, 1339–1394) analyzes Southern Bantu noun-class
prefixes as morphemes lexicalizing phrasal Specifiers built around a silent
classifier-like noun Nₓ — [Nₓ] for singulars, [# Nₓ] for plurals ((48)–(50),
pp. 1357–1358) — rather than single functional heads. Agreement with conjoined
singular subjects (§2) shows which singular/plural class pairs share one N
(Xhosa: 1/2, 7/8, 9/10) and which pair distinct Ns (3/4, 5/6). Where the plural
entry's N is distinct and the language cannot merge it directly with the root,
the Foot Condition blocks direct spellout and Starke-style backtracking yields
prefix *stacking*: Changana/Rhonga *mi-mu-twa* 'thorns', *ma-rhi-tu* 'words',
*ti-yi-n-dlu* 'houses' ((62), p. 1361, from [bachetti-2006]). Xhosa instead
first-merges the plural N ((82)–(83), p. 1366) and never stacks.

## Main declarations

- `NCFeature`: number (#) and classifier (Nₓ) features
- `xhosaSg`/`xhosaPl`, `rhongaSg`/`rhongaPl`: the Xhosa and Changana/Rhonga
  lexica ((41), (48)–(50), (76)–(80))
- `SharesClassifierN`: a singular/plural entry pair shares its classifier N
- `derivePlural`: cyclic spellout with last-resort backtracking (§4.2, (70)–(75))
- `derivePluralFirstMerge`: the first-merge option ((82)–(83)) — Xhosa's route
- `isStacked_iff_not_sharesClassifierN`: stacking iff distinct Ns, for any
  lexicon where direct spellout succeeds exactly on shared-N targets
- `not_isStacked_of_firstMerge`: the first-merge option makes stacking
  underivable — the paper's account of stacking-free Xhosa

The bridge to [carstens-2026]'s interpretable-gender agreement diagnostic lives
in `Linglib.Studies.Carstens2026` (the later paper hosts the comparison). The
paper's DM comparison (§3.4, portmanteaux and Fusion) is not yet formalized.
-/

namespace TaraldsenEtAl2018

open Morphology.Nanosyntax

/-! ### Feature inventory -/

/-- Nominal features on the Bantu nanosyntactic structures: `num` is the
    number head #, `cls n` the classifier-like silent noun Nₙ. Singular
    prefixes lexicalize [Nₓ]; plural prefixes lexicalize [# Nₓ]
    ((48)–(50), pp. 1357–1358). -/
inductive NCFeature where
  | num : NCFeature
  | cls : Nat → NCFeature
  deriving DecidableEq, Repr

/-! ### The Xhosa lexicon

Exponents are the paper's analytical units — the post-augment prefix
(p. 1340 restricts "prefix" to exclude the augment; surface *u-m-*, *a-ba-*
etc. add the augment vowel). Entries by gender pair:

| gender | sg | tree | source | pl | tree | source |
|--------|----|------|--------|----|------|--------|
| A (1/2)  | *m*  | [N₁] | (48a) | *ba* | [# N₁] | (48b) |
| B (3/4)  | *m*  | [N₃] | implied, cf. (25a), p. 1358 | *mi* | [# N₄] | (41a) |
| C (5/6)  | *li* | [N₅] | (50a) | *ma* | [# N₆] | (50b) |
| D (7/8)  | *si* | [N₇] | (49a) | *zi* | [# N₇] | (49b) |
| E (9/10) | *n*  | [N₉] | the homorganic nasal, set aside in fn. 39 | *zi* | [# N₉] | implied by §2.3, fn. 40 |

Class-10 *zi* is accidentally syncretic with class-8 *zi* (fn. 11); it must
contain N₉ because conjoined class-9 singulars allow class-10 formal agreement
in Xhosa (§2.3, (10)–(12); fn. 40). The plural shape [# Nₓ] is not
exceptionless across Bantu: Shona *mi* lexicalizes bare [N₄] ((89), fn. 42),
which is how Shona double plurals like *ma-mi-sha* arise (§4.3). -/

/-- Xhosa singular class-prefix entries: each lexicalizes a bare classifier
    [Nₓ]. See the table in the section docstring for per-entry sources. -/
def xhosaSg : Xhosa.Gender → TreeLexEntry NCFeature
  | .genderA => ⟨.leaf (.cls 1), "m", .prefix⟩
  | .genderB => ⟨.leaf (.cls 3), "m", .prefix⟩
  | .genderC => ⟨.leaf (.cls 5), "li", .prefix⟩
  | .genderD => ⟨.leaf (.cls 7), "si", .prefix⟩
  | .genderE => ⟨.leaf (.cls 9), "n", .prefix⟩

/-- Xhosa plural class-prefix entries: each lexicalizes [# Nₓ]. Genders A, D,
    E share their N with the singular; B and C contain distinct Ns (N₄ ≠ N₃,
    N₆ ≠ N₅) — the §2 conjoined-agreement finding. -/
def xhosaPl : Xhosa.Gender → TreeLexEntry NCFeature
  | .genderA => ⟨.node .num [.leaf (.cls 1)], "ba", .prefix⟩
  | .genderB => ⟨.node .num [.leaf (.cls 4)], "mi", .prefix⟩
  | .genderC => ⟨.node .num [.leaf (.cls 6)], "ma", .prefix⟩
  | .genderD => ⟨.node .num [.leaf (.cls 7)], "zi", .prefix⟩
  | .genderE => ⟨.node .num [.leaf (.cls 9)], "zi", .prefix⟩

/-- The five Xhosa genders, in Fragment order. -/
def xhosaGenders : List Xhosa.Gender :=
  [.genderA, .genderB, .genderC, .genderD, .genderE]

/-- The full Xhosa class-prefix lexicon. -/
def xhosaPrefixes : List (TreeLexEntry NCFeature) :=
  xhosaGenders.map xhosaSg ++ xhosaGenders.map xhosaPl

/-! ### The Changana/Rhonga lexicon

The stacking languages ((76)–(80), pp. 1365–1366). Here the plural-specific
classifiers N₄, N₆, N₁₀ are distinct from every singular's N, and — unlike in
Xhosa — may not be first-merged with the root, so pluralization of classes
3, 5, 9 must stack ((62), p. 1361). Entries by gender pair:

| gender | sg | tree | source | pl | tree | source |
|--------|----|------|--------|----|------|--------|
| A (1/2)  | *mu*  | [N₁] | (79a) | *va*  | [# N₁]  | (79b) |
| B (3/4)  | *mu*  | [N₃] | (76a) | *mi*  | [# N₄]  | (77a) |
| C (5/6)  | *rhi* | [N₅] | (76b), printed *ri/rhi* | *ma* | [# N₆] | (77b) |
| D (7/8)  | *xi*  | [N₇] | (80a) | *swi* | [# N₇]  | (80b) |
| E (9/10) | *yi*  | [N₉] | (76c) | *ti*  | [# N₁₀] | (77c) | -/

/-- The five Changana/Rhonga gender pairs, indexed like Xhosa's A–E
    (no Tsonga Fragment exists yet, so the index is study-local). -/
inductive RhongaGender where
  | gA | gB | gC | gD | gE
  deriving DecidableEq, Repr

/-- Changana/Rhonga singular class-prefix entries ((76), (79a), (80a)). -/
def rhongaSg : RhongaGender → TreeLexEntry NCFeature
  | .gA => ⟨.leaf (.cls 1), "mu", .prefix⟩
  | .gB => ⟨.leaf (.cls 3), "mu", .prefix⟩
  | .gC => ⟨.leaf (.cls 5), "rhi", .prefix⟩
  | .gD => ⟨.leaf (.cls 7), "xi", .prefix⟩
  | .gE => ⟨.leaf (.cls 9), "yi", .prefix⟩

/-- Changana/Rhonga plural class-prefix entries ((77), (79b), (80b)). -/
def rhongaPl : RhongaGender → TreeLexEntry NCFeature
  | .gA => ⟨.node .num [.leaf (.cls 1)], "va", .prefix⟩
  | .gB => ⟨.node .num [.leaf (.cls 4)], "mi", .prefix⟩
  | .gC => ⟨.node .num [.leaf (.cls 6)], "ma", .prefix⟩
  | .gD => ⟨.node .num [.leaf (.cls 7)], "swi", .prefix⟩
  | .gE => ⟨.node .num [.leaf (.cls 10)], "ti", .prefix⟩

/-- The singular's classifier index per gender — the N the noun structure is
    built on in the Tsonga languages, which lack the first-merge option. -/
def rhongaBaseN : RhongaGender → Nat
  | .gA => 1 | .gB => 3 | .gC => 5 | .gD => 7 | .gE => 9

/-- The plural entry's classifier index per gender — the backtrack target. -/
def rhongaPlN : RhongaGender → Nat
  | .gA => 1 | .gB => 4 | .gC => 6 | .gD => 7 | .gE => 10

/-- The five Changana/Rhonga genders. -/
def rhongaGenders : List RhongaGender := [.gA, .gB, .gC, .gD, .gE]

/-- The full Changana/Rhonga class-prefix lexicon. -/
def rhongaPrefixes : List (TreeLexEntry NCFeature) :=
  rhongaGenders.map rhongaSg ++ rhongaGenders.map rhongaPl

/-! ### Spellout sanity checks -/

/-- [N₁] spells out as *m*: the singular entry wins over *ba* ↔ [# N₁]
    (which also contains [N₁]) by the Elsewhere Condition — smallest match. -/
theorem xhosa_spellout_n1 :
    treeSpellout xhosaPrefixes (.leaf (.cls 1)) = some "m" := by decide

/-- [# N₁] spells out as *ba* ((48b)). -/
theorem xhosa_spellout_num_n1 :
    treeSpellout xhosaPrefixes (.node .num [.leaf (.cls 1)]) = some "ba" := by
  decide

/-- [# N₉] spells out as class-10 *zi*. -/
theorem xhosa_spellout_num_n9 :
    treeSpellout xhosaPrefixes (.node .num [.leaf (.cls 9)]) = some "zi" := by
  decide

/-- No Xhosa entry lexicalizes a bare N₂ — class 2 has no singular form. -/
theorem xhosa_spellout_n2_eq_none :
    treeSpellout xhosaPrefixes (.leaf (.cls 2)) = none := by decide

/-! ### Shared vs distinct classifier Ns

The conjoined-subject diagnostic (§2.2–2.7): a conjunction of two class-X
singulars triggers matching plural class-Y agreement iff Y's prefix contains
the same N as X's prefix. -/

/-- Whether a singular and a plural prefix entry contain the same classifier
    N — the N at the foot of each stored tree. -/
def SharesClassifierN (sg pl : TreeLexEntry NCFeature) : Prop :=
  sg.tree.foot = pl.tree.foot

instance : DecidableRel SharesClassifierN :=
  fun _ _ => inferInstanceAs (Decidable (_ = _))

/-- Gender A (1/2): *m* and *ba* share N₁ ((48)) — conjoined class-1
    singulars take class-2 agreement. -/
theorem xhosa_genderA_sharesClassifierN :
    SharesClassifierN (xhosaSg .genderA) (xhosaPl .genderA) := rfl

/-- Gender D (7/8): *si* and *zi* share N₇ ((49)). -/
theorem xhosa_genderD_sharesClassifierN :
    SharesClassifierN (xhosaSg .genderD) (xhosaPl .genderD) := rfl

/-- Gender E (9/10): shared N₉ — conjoined class-9 singulars allow class-10
    formal agreement in Xhosa (§2.3, (10)–(12); fn. 40). -/
theorem xhosa_genderE_sharesClassifierN :
    SharesClassifierN (xhosaSg .genderE) (xhosaPl .genderE) := rfl

/-- Gender B (3/4): *mi* contains N₄, distinct from the N₃ in singular *m*
    (§2.6, (18)–(19)) — no matching agreement from conjoined class-3
    singulars. -/
theorem xhosa_genderB_not_sharesClassifierN :
    ¬ SharesClassifierN (xhosaSg .genderB) (xhosaPl .genderB) := by decide

/-- Gender C (5/6): *ma* contains N₆, distinct from N₅ (§2.5, (16)–(17)). -/
theorem xhosa_genderC_not_sharesClassifierN :
    ¬ SharesClassifierN (xhosaSg .genderC) (xhosaPl .genderC) := by decide

/-! ### Foot Condition: why distinct-N plurals cannot spell out -/

/-- Rhonga *mi* ↔ [# N₄] cannot spell out [# N₃]: its foot N₄ is absent from
    the target (the Foot Condition). -/
theorem rhonga_mi_foot_not_met :
    footConditionMet (rhongaPl .gB) (.node .num [.leaf (.cls 3)]) = false := by
  decide

/-- Rhonga *va* ↔ [# N₁] can spell out [# N₁]: its foot N₁ is present. -/
theorem rhonga_va_foot_met :
    footConditionMet (rhongaPl .gA) (.node .num [.leaf (.cls 1)]) = true := by
  decide

/-- No Rhonga entry spells out [# N₃] — the lexicalization failure that
    forces backtracking and stacking ((70)–(75), p. 1364). -/
theorem rhonga_spellout_num_n3_eq_none :
    treeSpellout rhongaPrefixes (.node .num [.leaf (.cls 3)]) = none := by
  decide

/-! ### Pluralization: direct spellout vs stacking -/

/-- Result of pluralizing a Bantu noun (§4.2): `direct` — one plural prefix
    forms the sole Specifier; `stacked` — the plural prefix stacks on top of
    the singular prefix ((75)). -/
inductive PluralizationResult where
  | direct : String → PluralizationResult
  | stacked : String → String → PluralizationResult
  deriving DecidableEq, Repr

/-- A stacked outcome. -/
def PluralizationResult.IsStacked : PluralizationResult → Prop
  | .direct _ => False
  | .stacked _ _ => True

instance : DecidablePred PluralizationResult.IsStacked
  | .direct _ => .isFalse id
  | .stacked _ _ => .isTrue trivial

/-- Derive a plural form by cyclic spellout with last-resort backtracking
    (§4.2, (70)–(75)):

    1. The plural structure [# N_baseN] is built, where `baseN` is the
       classifier merged with the root at the first step. Which classifier
       that is, is the cross-linguistic parameter ((82)–(83), p. 1366): Xhosa
       may (and prefers to) first-merge the plural entry's N
       (`derivePluralFirstMerge`); Changana/Rhonga must use the singular's N.
    2. If some entry spells out [# N_baseN], the derivation is `direct`.
    3. Otherwise backtracking builds a second Specifier [# N_plN] inside the
       first, spelled out on top of the singular prefix [N_baseN] — `stacked`.
       By construction the outer prefix always lexicalizes a # -containing
       target, deriving §4.5's observation that singular prefixes never stack
       on top of plural ones.

    Which [# N_W] entry the backtrack targets (`plN`) is not derived by the
    spellout calculus: the paper attributes prefix–noun pairing to semantic
    compatibility with the silent N or to idiom listing (§5.3, §5.5), so
    `plN` is a parameter here. -/
def derivePlural (entries : List (TreeLexEntry NCFeature)) (baseN plN : Nat) :
    Option PluralizationResult :=
  match treeSpellout entries (.node .num [.leaf (.cls baseN)]) with
  | some pfx => some (.direct pfx)
  | none =>
    match treeSpellout entries (.node .num [.leaf (.cls plN)]),
          treeSpellout entries (.leaf (.cls baseN)) with
    | some outer, some inner => some (.stacked outer inner)
    | _, _ => none

/-- The first-merge option ((82)–(83), p. 1366): the plural entry's N merges
    with the root directly, so the built structure and the backtrack target
    coincide. Xhosa takes this option in preference to stacking; the Tsonga
    languages cannot. -/
def derivePluralFirstMerge (entries : List (TreeLexEntry NCFeature))
    (plN : Nat) : Option PluralizationResult :=
  derivePlural entries plN plN

/-- Changana/Rhonga gender B: class 3 nouns stack — *mi-mu-twa* 'thorns'
    ((62a), [bachetti-2006]). -/
theorem rhonga_cl3_cl4_stacked :
    derivePlural rhongaPrefixes 3 4 = some (.stacked "mi" "mu") := by decide

/-- Rhonga gender C: class 5 nouns stack — *ma-rhi-tu* 'words' ((62b)). -/
theorem rhonga_cl5_cl6_stacked :
    derivePlural rhongaPrefixes 5 6 = some (.stacked "ma" "rhi") := by decide

/-- Rhonga gender E: class 9 nouns stack — *ti-yi-n-dlu* 'houses' ((62c)). -/
theorem rhonga_cl9_cl10_stacked :
    derivePlural rhongaPrefixes 9 10 = some (.stacked "ti" "yi") := by decide

/-- Rhonga gender A pluralizes directly: *va* ↔ [# N₁] shares N₁. -/
theorem rhonga_cl1_cl2_direct :
    derivePlural rhongaPrefixes 1 1 = some (.direct "va") := by decide

/-- Rhonga gender D pluralizes directly: *swi* ↔ [# N₇] shares N₇. -/
theorem rhonga_cl7_cl8_direct :
    derivePlural rhongaPrefixes 7 7 = some (.direct "swi") := by decide

/-- Xhosa first-merges the plural N, so even the distinct-N gender B
    pluralizes directly: the plural of a class-3 noun is built on N₄ from
    the start and *mi* spells it out — no stacking. -/
theorem xhosa_cl3_cl4_direct :
    derivePluralFirstMerge xhosaPrefixes 4 = some (.direct "mi") := by decide

/-- Xhosa gender C: direct *ma*, same first-merge route. -/
theorem xhosa_cl5_cl6_direct :
    derivePluralFirstMerge xhosaPrefixes 6 = some (.direct "ma") := by decide

/-- Xhosa gender A: direct *ba*. -/
theorem xhosa_cl1_cl2_direct :
    derivePluralFirstMerge xhosaPrefixes 1 = some (.direct "ba") := by decide

/-- The cross-linguistic contrast in one statement: the same gender (3/4),
    direct in Xhosa, stacked in Changana/Rhonga — the paper's central
    prediction ((82)–(83) vs (62)). -/
theorem xhosa_rhonga_contrast :
    derivePluralFirstMerge xhosaPrefixes 4 = some (.direct "mi") ∧
    derivePlural rhongaPrefixes 3 4 = some (.stacked "mi" "mu") :=
  ⟨xhosa_cl3_cl4_direct, rhonga_cl3_cl4_stacked⟩

/-! ### Stacking iff distinct Ns -/

private theorem isStacked_iff_spellout_eq_none
    {entries : List (TreeLexEntry NCFeature)} {baseN plN : Nat}
    {r : PluralizationResult}
    (hr : derivePlural entries baseN plN = some r) :
    r.IsStacked ↔
      treeSpellout entries (.node .num [.leaf (.cls baseN)]) = none := by
  unfold derivePlural at hr
  split at hr
  next pfx heq =>
    cases hr
    rw [heq]
    exact iff_of_false id nofun
  next heq =>
    split at hr
    next outer inner h2 h3 =>
      cases hr
      exact iff_of_true trivial heq
    next => exact absurd hr nofun

/-- The paper's central correlation, derived rather than stipulated: for any
    lexicon where direct spellout of [# N_baseN] fails exactly when the
    singular/plural pair has distinct Ns (`hDirect`), a successful derivation
    stacks iff the Ns are distinct. Instantiated per gender below with
    `hDirect` discharged by `decide`. -/
theorem isStacked_iff_not_sharesClassifierN
    {entries : List (TreeLexEntry NCFeature)} {sg pl : TreeLexEntry NCFeature}
    {baseN plN : Nat} {r : PluralizationResult}
    (hDirect : treeSpellout entries (.node .num [.leaf (.cls baseN)]) = none ↔
      ¬ SharesClassifierN sg pl)
    (hr : derivePlural entries baseN plN = some r) :
    (r.IsStacked ↔ ¬ SharesClassifierN sg pl) :=
  (isStacked_iff_spellout_eq_none hr).trans hDirect

/-- With the first-merge option the built structure and the backtrack target
    coincide, so a failed direct spellout leaves nothing for backtracking to
    lexicalize either: stacking is underivable. This is the paper's account
    of why Xhosa never stacks. -/
theorem not_isStacked_of_firstMerge
    {entries : List (TreeLexEntry NCFeature)} {plN : Nat}
    {r : PluralizationResult}
    (hr : derivePluralFirstMerge entries plN = some r) : ¬ r.IsStacked := by
  unfold derivePluralFirstMerge derivePlural at hr
  split at hr
  next pfx _ => cases hr; exact id
  next heq =>
    split at hr
    next outer inner h2 _ => exact absurd h2 (heq ▸ nofun)
    next => exact absurd hr nofun

/-- For every Changana/Rhonga gender, a successful derivation stacks iff the
    pair's classifier Ns are distinct — §4.5's stacking-agreement correlation
    as a per-language theorem. -/
theorem rhonga_stacking_iff_not_sharesClassifierN (g : RhongaGender)
    {r : PluralizationResult}
    (hr : derivePlural rhongaPrefixes (rhongaBaseN g) (rhongaPlN g) = some r) :
    r.IsStacked ↔ ¬ SharesClassifierN (rhongaSg g) (rhongaPl g) := by
  cases g <;> exact isStacked_iff_not_sharesClassifierN (by decide) hr

/-! ### Prefix–concord identity

The paper's entries for nominal class prefixes and subject concords are
identical: (60)–(61) (p. 1360) repeat the nominal entries (48)–(49) as the SC
entries (the SC's gender head G having been dropped). The paper's own
exceptions: SC1 is *u*, not *m* (fn. 30), and SC6 is *a*, not *ma* ((53c)). -/

/-- The class-prefix lexicon yields the Fragment's subject-concord forms for
    classes 5, 7, 2, 8 — one set of entries spells out both nominal prefixes
    and SCs ((60)–(61)). -/
theorem xhosa_prefix_sc_identity :
    treeSpellout xhosaPrefixes (.leaf (.cls 5)) =
      some Xhosa.NounClass.cl5.subjPrefix ∧
    treeSpellout xhosaPrefixes (.leaf (.cls 7)) =
      some Xhosa.NounClass.cl7.subjPrefix ∧
    treeSpellout xhosaPrefixes (.node .num [.leaf (.cls 1)]) =
      some Xhosa.NounClass.cl2.subjPrefix ∧
    treeSpellout xhosaPrefixes (.node .num [.leaf (.cls 7)]) =
      some Xhosa.NounClass.cl8.subjPrefix := by decide

end TaraldsenEtAl2018
