import Linglib.Morphology.Nanosyntax.TreeSpellout
import Linglib.Fragments.Xhosa.Basic

/-!
# Taraldsen, Taraldsen Medová, and Langa (2018): Class Prefixes as Specifiers in Southern Bantu

This file formalizes [taraldsen-et-al-2018]'s analysis of Southern Bantu noun-class prefixes as
morphemes lexicalizing phrasal Specifiers built on a silent classifier-like noun Nₓ: a singular
prefix lexicalizes `[Nₓ]` and a plural prefix `[# Nₓ]` (41), (48)–(50), `sgTree`, `plTree`,
under the phrasal spellout of the substrate, matching by containment (35)–(36) and the Foot
Condition (39). Agreement with conjoined singular subjects (section 2) shows which
singular/plural pairs share one N, in Xhosa 1/2, 7/8 and 9/10, and which pair distinct Ns, 3/4
and 5/6, `SharesClassifierN`, the lexica `xhosaSg`, `xhosaPl`, `rhongaSg`, `rhongaPl`.

A plural is derived by cyclic spellout with last-resort backtracking (section 4.2, (65)–(75)),
`derivePlural`: the plural head merges above the classifier first merged with the root; if some
entry spells out `[# N]` the prefix is direct, and otherwise a second Specifier `[# N']` is built
inside the first and spelled out on top of the singular prefix, a stack. Over a class-prefix
lexicon, one whose entries all have the singular or plural shape, `IsClassEntry`, direct spellout
of `[# N]` fails exactly when no entry stores that tree, `treeSpellout_plTree_eq_none_iff`, so a
successful derivation stacks exactly when the lexicon has no plural entry on the singular's
classifier, `isStacked_iff_forall_ne`, and the outer prefix of a stack always lexicalizes a
plural Specifier, `stacked_outer`, which is why no singular prefix stacks on a plural one
(section 4.5). Per gender this is the paper's correlation: Changana and Rhonga stack in classes
3, 5 and 9, whose plural prefixes contain a distinct N, and not in 1 and 7 (62), (76)–(81),
`rhonga_stacking_iff_not_sharesClassifierN`, `rhonga_cl3_cl4_stacked`; and Xhosa, which may
first-merge the plural entry's N (82)–(83), `derivePluralFirstMerge`, never stacks, since the
built structure and the backtrack target then coincide, `not_isStacked_of_firstMerge`. The Shona
double plural *ma-mi-sha* (84) is derivable exactly when *mi* lexicalizes the bare `[N₄]` (89)
rather than `[# N₄]` (87), `shona_double_plural`. The class-prefix entries also spell out the
Fragment's subject concords (60)–(61), `xhosa_prefix_sc_identity`.

## Implementation notes

The exponents are the post-augment prefixes, which the paper takes as the prefix proper. The
classifier the backtracking Specifier targets is a parameter of `derivePlural`: the paper leaves
the pairing of prefixes with nouns to the meaning of the silent N or to idiom listing (section
5.3). The phonological elision of stacked class-5 prefixes (63)–(64), the portmanteau comparison
with Distributed Morphology (section 3.4), and the secondary prefixes of section 5 are not
formalized. The comparison with [carstens-2026]'s interpretability diagnostic lives in that
later study.

## References

* [taraldsen-et-al-2018]
* [bachetti-2006]
* [carstens-2026]
-/

namespace TaraldsenEtAl2018

open Morphology.Nanosyntax Morphology.Exponence

/-! ### Features and entry shapes -/

/-- The nominal features: the number head `#` and the classifier-like silent noun `Nₙ`. -/
inductive NCFeature where
  | num : NCFeature
  | cls : ℕ → NCFeature
  deriving DecidableEq, Repr

/-- The structure a singular prefix lexicalizes, the bare classifier `[Nₙ]` (41), (48a). -/
def sgTree (n : ℕ) : NanoTree NCFeature := .leaf (.cls n)

/-- The structure a plural prefix lexicalizes, the Specifier `[# Nₙ]` (41), (48b). -/
def plTree (n : ℕ) : NanoTree NCFeature := .node .num [.leaf (.cls n)]

/-- A class-prefix entry stores a singular or a plural tree. -/
def IsClassEntry (e : TreeLexEntry NCFeature String) : Prop :=
  match e.tree with
  | .leaf (.cls _) => True
  | .node .num [.leaf (.cls _)] => True
  | _ => False

instance (e : TreeLexEntry NCFeature String) : Decidable (IsClassEntry e) := by
  unfold IsClassEntry; split <;> infer_instance

/-- A class-prefix entry matches the plural Specifier `[# Nₙ]` exactly when it stores it: no
singular tree contains it, and a plural tree contains it only by equality. -/
theorem matches_plTree_iff {e : TreeLexEntry NCFeature String} (he : IsClassEntry e) (n : ℕ) :
    e.Matches (plTree n) ↔ e.tree = plTree n := by
  unfold TreeLexEntry.Matches plTree
  revert he
  unfold IsClassEntry
  split
  · rename_i heq
    rw [heq]
    simp
  · rename_i heq
    rw [heq]
    simp [NanoTree.contains_node_iff]
  · exact λ h => h.elim

/-- Over a class-prefix lexicon, spellout of `[# Nₙ]` fails exactly when no entry stores it. -/
theorem treeSpellout_plTree_eq_none_iff {L : List (TreeLexEntry NCFeature String)}
    (hL : ∀ e ∈ L, IsClassEntry e) (n : ℕ) :
    treeSpellout L (plTree n) = none ↔ ∀ e ∈ L, e.tree ≠ plTree n := by
  rw [treeSpellout, Option.map_eq_none_iff, treeSelect, selectBy_eq_none_iff, applicable,
    List.filter_eq_nil_iff]
  have happ : ∀ e : TreeLexEntry NCFeature String, Applies e (plTree n) ↔ e.Matches (plTree n) :=
    λ _ => Iff.rfl
  simp only [decide_eq_true_eq, happ]
  exact ⟨λ h e he hn => h e he ((matches_plTree_iff (hL e he) n).2 hn),
    λ h e he hm => h e he ((matches_plTree_iff (hL e he) n).1 hm)⟩

/-- A spelled-out exponent comes from a matching entry of the lexicon. -/
theorem exists_of_treeSpellout_eq_some {L : List (TreeLexEntry NCFeature String)}
    {t : NanoTree NCFeature} {x : String} (h : treeSpellout L t = some x) :
    ∃ e ∈ L, e.Matches t ∧ e.exponent = x := by
  rw [treeSpellout, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  exact ⟨e, selectBy_mem he, selectBy_applies he, rfl⟩

/-- Whether a singular and a plural entry contain the same classifier N, the foot of each stored
tree: the conjoined-subject diagnostic of section 2. -/
def SharesClassifierN (sg pl : TreeLexEntry NCFeature String) : Prop :=
  sg.tree.foot = pl.tree.foot

instance : DecidableRel SharesClassifierN := λ _ _ => inferInstanceAs (Decidable (_ = _))

/-! ### Pluralization: direct spellout and stacking (section 4.2) -/

/-- The result of pluralizing a noun: one plural prefix forming the sole Specifier, or the plural
prefix stacked on top of the singular prefix (75). -/
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

/-- Cyclic spellout with last-resort backtracking (65)–(75): the plural head merges above the
classifier `baseN` first merged with the root; if some entry spells out `[# N_baseN]` the prefix
is direct, and otherwise a Specifier `[# N_plN]` is built inside the first and spelled out on top
of the singular prefix `[N_baseN]`. -/
def derivePlural (L : List (TreeLexEntry NCFeature String)) (baseN plN : ℕ) :
    Option PluralizationResult :=
  match treeSpellout L (plTree baseN) with
  | some pfx => some (.direct pfx)
  | none =>
    match treeSpellout L (plTree plN), treeSpellout L (sgTree baseN) with
    | some outer, some inner => some (.stacked outer inner)
    | _, _ => none

/-- The first-merge option (82)–(83): the plural entry's N merges with the root directly, so the
built structure and the backtrack target coincide. -/
def derivePluralFirstMerge (L : List (TreeLexEntry NCFeature String)) (plN : ℕ) :
    Option PluralizationResult :=
  derivePlural L plN plN

private theorem isStacked_iff_spellout_eq_none {L : List (TreeLexEntry NCFeature String)}
    {baseN plN : ℕ} {r : PluralizationResult} (hr : derivePlural L baseN plN = some r) :
    r.IsStacked ↔ treeSpellout L (plTree baseN) = none := by
  unfold derivePlural at hr
  split at hr
  next pfx heq =>
    cases hr
    rw [heq]
    exact iff_of_false id nofun
  next heq =>
    split at hr
    next outer inner _ _ =>
      cases hr
      exact iff_of_true trivial heq
    next => exact absurd hr nofun

/-- The correlation of section 4.5, derived: over a class-prefix lexicon a successful derivation
stacks exactly when no entry stores the plural Specifier on the singular's classifier. -/
theorem isStacked_iff_forall_ne {L : List (TreeLexEntry NCFeature String)}
    (hL : ∀ e ∈ L, IsClassEntry e) {baseN plN : ℕ} {r : PluralizationResult}
    (hr : derivePlural L baseN plN = some r) :
    r.IsStacked ↔ ∀ e ∈ L, e.tree ≠ plTree baseN :=
  (isStacked_iff_spellout_eq_none hr).trans (treeSpellout_plTree_eq_none_iff hL baseN)

/-- The outer prefix of a stack lexicalizes the plural Specifier: a singular prefix never stacks
on top of a plural one (section 4.5). -/
theorem stacked_outer {L : List (TreeLexEntry NCFeature String)} {baseN plN : ℕ}
    {outer inner : String} (hr : derivePlural L baseN plN = some (.stacked outer inner)) :
    ∃ e ∈ L, e.Matches (plTree plN) ∧ e.exponent = outer := by
  unfold derivePlural at hr
  split at hr
  next => exact absurd hr nofun
  next =>
    split at hr
    next o i ho _ =>
      cases hr
      exact exists_of_treeSpellout_eq_some ho
    next => exact absurd hr nofun

/-- With the first-merge option the built structure and the backtrack target coincide, so a
failed direct spellout leaves nothing for backtracking to lexicalize: stacking is underivable,
which is why Xhosa never stacks. -/
theorem not_isStacked_of_firstMerge {L : List (TreeLexEntry NCFeature String)} {plN : ℕ}
    {r : PluralizationResult} (hr : derivePluralFirstMerge L plN = some r) : ¬ r.IsStacked := by
  unfold derivePluralFirstMerge derivePlural at hr
  split at hr
  next pfx _ => cases hr; exact id
  next heq =>
    split at hr
    next outer inner h2 _ => exact absurd h2 (heq ▸ nofun)
    next => exact absurd hr nofun

/-! ### The Xhosa lexicon

The entries by gender pair, with the paper's locators: gender A (1/2) *m* `[N₁]` (48a) and *ba*
`[# N₁]` (48b); B (3/4) *m* `[N₃]`, cf. (25a), and *mi* `[# N₄]` (41a); C (5/6) *li* `[N₅]` (50a)
and *ma* `[# N₆]` (50b); D (7/8) *si* `[N₇]` (49a) and *zi* `[# N₇]` (49b); E (9/10) the homorganic
nasal `[N₉]`, set aside in footnote 39, and *zi* `[# N₉]`, syncretic with class 8 (footnote 11)
and containing N₉ because conjoined class-9 singulars allow class-10 agreement (section 2.3). -/

/-- The Xhosa singular entries: bare classifiers. -/
def xhosaSg : Xhosa.Gender → TreeLexEntry NCFeature String
  | .genderA => ⟨sgTree 1, "m", .before⟩
  | .genderB => ⟨sgTree 3, "m", .before⟩
  | .genderC => ⟨sgTree 5, "li", .before⟩
  | .genderD => ⟨sgTree 7, "si", .before⟩
  | .genderE => ⟨sgTree 9, "n", .before⟩

/-- The Xhosa plural entries: genders A, D and E share their N with the singular, B and C contain
distinct Ns, the finding of section 2. -/
def xhosaPl : Xhosa.Gender → TreeLexEntry NCFeature String
  | .genderA => ⟨plTree 1, "ba", .before⟩
  | .genderB => ⟨plTree 4, "mi", .before⟩
  | .genderC => ⟨plTree 6, "ma", .before⟩
  | .genderD => ⟨plTree 7, "zi", .before⟩
  | .genderE => ⟨plTree 9, "zi", .before⟩

/-- The five Xhosa genders. -/
def xhosaGenders : List Xhosa.Gender := [.genderA, .genderB, .genderC, .genderD, .genderE]

/-- The Xhosa class-prefix lexicon. -/
def xhosaPrefixes : List (TreeLexEntry NCFeature String) :=
  xhosaGenders.map xhosaSg ++ xhosaGenders.map xhosaPl

/-- `[N₁]` spells out as *m*: the singular entry wins over *ba* by the smallest match, and `[# N₁]`
as *ba* (48). -/
theorem xhosa_spellout_genderA :
    treeSpellout xhosaPrefixes (sgTree 1) = some "m" ∧
      treeSpellout xhosaPrefixes (plTree 1) = some "ba" := by
  decide

/-- Genders A, D and E share their classifier; B and C do not (section 2). -/
theorem xhosa_sharesClassifierN (g : Xhosa.Gender) :
    SharesClassifierN (xhosaSg g) (xhosaPl g) ↔ g ∈ [.genderA, .genderD, .genderE] := by
  cases g <;> decide

/-! ### The Changana and Rhonga lexicon

The stacking languages (76)–(80): the plural classifiers N₄, N₆ and N₁₀ are distinct from every
singular's N, and cannot be first-merged with the root, so classes 3, 5 and 9 stack (62), from
[bachetti-2006]. Gender A (1/2) *mu* (79a) and *va* (79b); B (3/4) *mu* (76a) and *mi* (77a); C
(5/6) *rhi* (76b) and *ma* (77b); D (7/8) *xi* (80a) and *swi* (80b); E (9/10) *yi* (76c) and
*ti* (77c). -/

/-- The five Changana and Rhonga gender pairs, indexed like Xhosa's. -/
inductive RhongaGender where
  | gA | gB | gC | gD | gE
  deriving DecidableEq, Repr

/-- The singular entries (76), (79a), (80a). -/
def rhongaSg : RhongaGender → TreeLexEntry NCFeature String
  | .gA => ⟨sgTree 1, "mu", .before⟩
  | .gB => ⟨sgTree 3, "mu", .before⟩
  | .gC => ⟨sgTree 5, "rhi", .before⟩
  | .gD => ⟨sgTree 7, "xi", .before⟩
  | .gE => ⟨sgTree 9, "yi", .before⟩

/-- The plural entries (77), (79b), (80b). -/
def rhongaPl : RhongaGender → TreeLexEntry NCFeature String
  | .gA => ⟨plTree 1, "va", .before⟩
  | .gB => ⟨plTree 4, "mi", .before⟩
  | .gC => ⟨plTree 6, "ma", .before⟩
  | .gD => ⟨plTree 7, "swi", .before⟩
  | .gE => ⟨plTree 10, "ti", .before⟩

/-- The singular's classifier, first merged with the root. -/
def rhongaBaseN : RhongaGender → ℕ
  | .gA => 1 | .gB => 3 | .gC => 5 | .gD => 7 | .gE => 9

/-- The plural entry's classifier, the backtrack target. -/
def rhongaPlN : RhongaGender → ℕ
  | .gA => 1 | .gB => 4 | .gC => 6 | .gD => 7 | .gE => 10

/-- The five Changana and Rhonga genders. -/
def rhongaGenders : List RhongaGender := [.gA, .gB, .gC, .gD, .gE]

/-- The Changana and Rhonga class-prefix lexicon. -/
def rhongaPrefixes : List (TreeLexEntry NCFeature String) :=
  rhongaGenders.map rhongaSg ++ rhongaGenders.map rhongaPl

theorem rhongaPrefixes_isClassEntry : ∀ e ∈ rhongaPrefixes, IsClassEntry e := by decide

/-- *mi* on `[# N₄]` cannot spell out `[# N₃]`, its foot being absent, while *va* on `[# N₁]` can
spell out `[# N₁]`: the Foot Condition (68). -/
theorem rhonga_footCondition :
    ¬ FootConditionMet (rhongaPl .gB) (plTree 3) ∧ FootConditionMet (rhongaPl .gA) (plTree 1) := by
  decide

/-- Classes 3, 5 and 9 stack, *mi-mu-twa* 'thorns', *ma-rhi-tu* 'words', *ti-yi-n-dlu* 'houses'
(62), (78); classes 1 and 7 pluralize directly, *va-nhu*, *swi-fambu*. -/
theorem rhonga_derivations :
    derivePlural rhongaPrefixes 3 4 = some (.stacked "mi" "mu") ∧
      derivePlural rhongaPrefixes 5 6 = some (.stacked "ma" "rhi") ∧
      derivePlural rhongaPrefixes 9 10 = some (.stacked "ti" "yi") ∧
      derivePlural rhongaPrefixes 1 1 = some (.direct "va") ∧
      derivePlural rhongaPrefixes 7 7 = some (.direct "swi") := by
  decide

theorem rhonga_cl3_cl4_stacked : derivePlural rhongaPrefixes 3 4 = some (.stacked "mi" "mu") :=
  rhonga_derivations.1

/-- For every Changana and Rhonga gender, a successful derivation stacks exactly when the pair's
classifiers are distinct: the correlation of section 4.5 per language. -/
theorem rhonga_stacking_iff_not_sharesClassifierN (g : RhongaGender) {r : PluralizationResult}
    (hr : derivePlural rhongaPrefixes (rhongaBaseN g) (rhongaPlN g) = some r) :
    r.IsStacked ↔ ¬ SharesClassifierN (rhongaSg g) (rhongaPl g) := by
  rw [isStacked_iff_forall_ne rhongaPrefixes_isClassEntry hr]
  cases g <;> decide

/-- Xhosa first-merges the plural N, so even the distinct-N genders B and C pluralize directly,
*mi* and *ma*, as does gender A, *ba* (82)–(83). -/
theorem xhosa_direct :
    derivePluralFirstMerge xhosaPrefixes 4 = some (.direct "mi") ∧
      derivePluralFirstMerge xhosaPrefixes 6 = some (.direct "ma") ∧
      derivePluralFirstMerge xhosaPrefixes 1 = some (.direct "ba") := by
  decide

/-- The cross-linguistic contrast: gender 3/4, direct in Xhosa and stacked in Changana and
Rhonga. -/
theorem xhosa_rhonga_contrast :
    derivePluralFirstMerge xhosaPrefixes 4 = some (.direct "mi") ∧
      derivePlural rhongaPrefixes 3 4 = some (.stacked "mi" "mu") :=
  ⟨xhosa_direct.1, rhonga_cl3_cl4_stacked⟩

/-! ### Shona double plurals (section 4.3) -/

/-- Shona *mi* on the bare `[N₄]` (89) and *ma* on `[# N₆]`. -/
def shonaPrefixes : List (TreeLexEntry NCFeature String) :=
  [⟨sgTree 4, "mi", .before⟩, ⟨plTree 6, "ma", .before⟩]

/-- The double plural *ma-mi-sha* 'groups of villages' (84), (88) is derived from the entry (89),
and would be underivable, *mi* spelling out `[# N₄]` directly, from the entry (87). -/
theorem shona_double_plural :
    derivePlural shonaPrefixes 4 6 = some (.stacked "ma" "mi") ∧
      derivePlural [⟨plTree 4, "mi", .before⟩, ⟨plTree 6, "ma", .before⟩] 4 6 =
        some (.direct "mi") := by
  decide

/-! ### Prefix and concord identity (60)–(61) -/

/-- The class-prefix lexicon spells out the Fragment's subject concords for classes 5, 7, 2 and
8: one set of entries serves nominal prefixes and concords (60)–(61); the paper's own exceptions
are the class-1 concord *u* (footnote 30) and the class-6 concord *a* (53c). -/
theorem xhosa_prefix_sc_identity :
    treeSpellout xhosaPrefixes (sgTree 5) = some Xhosa.NounClass.cl5.subjPrefix ∧
      treeSpellout xhosaPrefixes (sgTree 7) = some Xhosa.NounClass.cl7.subjPrefix ∧
      treeSpellout xhosaPrefixes (plTree 1) = some Xhosa.NounClass.cl2.subjPrefix ∧
      treeSpellout xhosaPrefixes (plTree 7) = some Xhosa.NounClass.cl8.subjPrefix := by
  decide

end TaraldsenEtAl2018
