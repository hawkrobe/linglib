import Linglib.Data.Examples.Istratkova2004
import Linglib.Studies.Svenonius2004

/-!
# Istratkova (2004): On Multiple Prefixation in Bulgarian

This file formalizes [istratkova-2004], the account of Bulgarian verbs carrying up to seven
prefixes. Prefixes quantize rather than perfectivize: the simplex homogeneous verbs of (2) are
aspectless, and a prefix or the semelfactive suffix quantizes them so that the aspectual head can
project (`homogeneous`). In a stack only the innermost prefix is lexical and the rest are
superlexical, [svenonius-2004]'s generalization (`Svenonius2004.WellStacked`), and the
superlexical prefixes are merged above AspP in the fixed order of the hierarchy (32),
attenuative *po-* over inceptive *za-* over terminative *do-* over completive *iz-* over
distributive *po-* over cumulative *na-* over excessive *raz-* over repetitive *pre-*
(`hierarchy`, `Ordered`), with distributive *po-* occurring only under completive *iz-*, (29),
and delimitative *po-* attaching to simplex atelic verbs alone, (26). The attested stacks of
Sections 1, 4 and 5 conform (`attested_wellFormed`), the starred stacks that reverse two heads
of the hierarchy are excluded (`starred_not_wellFormed`), and attenuative *po-* is always
outermost.

## Implementation notes

* The surface prefix *po-* is classified as distributive under completive *iz-* and attenuative
  otherwise, following the paper's glosses; a starred stack with *po-* below another head is
  excluded on either classification, the distributive one for want of *iz-*.
* The hierarchy places excessive *raz-* above repetitive *pre-*, but the paper accepts the
  flipped order in (25c) and (30b) with a different scope reading; the flipped forms are rows,
  not analyses. The starred stacks the paper attributes to meaning incompatibility, (18d),
  (20e), (20f) and the *na-pre-* cells of Table 2, conform to the hierarchy and are not derived.
* The selection of high inceptive *za-* for an imperfective output, (24a), is recorded in the
  rows; the analyses carry no outer aspect.

## References

* [istratkova-2004]
* [svenonius-2004]
-/

namespace Istratkova2004

open Morphology (Morph)
open Verb (Stem)
open Svenonius2004
open Bulgarian.Verbs

/-- The simplex homogeneous verbs of (2), analysed as aspectless: the fragment records the
dictionary-imperfective value they show by default. -/
def homogeneous : List Stem := [misla, obicham, znam, blesta, pisha, cheta, peja]

/-! ### The hierarchy -/

/-- The hierarchy (32) of superlexical heads above AspP, highest first; delimitative *po-*
merges low and does not stack. -/
def hierarchy : List SuperlexicalSubtype :=
  [.attenuative, .inceptive, .terminative, .completive, .distributive, .cumulative, .excessive,
   .repetitive]

/-- `s` is merged above `t`. -/
def Above (s t : SuperlexicalSubtype) : Prop := hierarchy.idxOf s < hierarchy.idxOf t

instance (s t : SuperlexicalSubtype) : Decidable (Above s t) := inferInstanceAs (Decidable (_ < _))

/-- The superlexical heads of a classified prefix sequence, outermost first. -/
def superlexicals (ps : List (Morph × PrefixClass)) : List SuperlexicalSubtype :=
  ps.filterMap λ p => match p.2 with
    | .superlexical s => some s
    | .lexical => none

/-- The stack conforms to the hierarchy: every superlexical prefix is merged above the ones
inside it. -/
def Ordered (ps : List (Morph × PrefixClass)) : Prop := (superlexicals ps).Pairwise Above

/-- Distributive *po-* occurs only with completive *iz-* outside, (21) and (29). -/
def DistributiveLicensed (ps : List (Morph × PrefixClass)) : Prop :=
  .distributive ∈ superlexicals ps → .completive ∈ superlexicals ps

/-- Delimitative *po-* does not stack, (26). -/
def DelimitativeAlone (ps : List (Morph × PrefixClass)) : Prop :=
  .delimitative ∈ superlexicals ps → superlexicals ps = [.delimitative]

/-- A well-formed stack: superlexicals outside lexicals, in hierarchy order, with distributive
*po-* licensed and delimitative *po-* alone. -/
def WellFormed (ps : List (Morph × PrefixClass)) : Prop :=
  WellStacked ps ∧ Ordered ps ∧ DistributiveLicensed ps ∧ DelimitativeAlone ps

instance (ps : List (Morph × PrefixClass)) : Decidable (WellFormed ps) := by
  unfold WellFormed Ordered DistributiveLicensed DelimitativeAlone; infer_instance

/-- Nothing stacks on top of attenuative *po-*: in an ordered stack it is outermost. -/
theorem attenuative_outermost {l : List SuperlexicalSubtype} (h : l.Pairwise Above)
    (hm : .attenuative ∈ l) : l.head? = some .attenuative := by
  cases l with
  | nil => simp at hm
  | cons a t =>
    rcases List.mem_cons.1 hm with rfl | hm
    · rfl
    · have ha := (List.pairwise_cons.1 h).1 _ hm
      have h0 : hierarchy.idxOf SuperlexicalSubtype.attenuative = 0 := rfl
      simp [Above, h0] at ha

/-! ### The attested stacks -/

/-- (1a) *za-piša* 'put down in writing': lexical *za-* on *piša*. -/
def a1a : Analysis := ⟨Examples.ex_1a, pisha, [(za, .lexical)]⟩

/-- (3a) *iz-misl'a* 'make up (a story)': lexical *iz-*. -/
def a3a : Analysis := ⟨Examples.ex_3a, misla, [(iz, .lexical)]⟩

/-- (3b) *za-običam* 'start to love': low inceptive *za-* on a homogeneous verb. -/
def a3b : Analysis := ⟨Examples.ex_3b, obicham, [(za, .superlexical .inceptive)]⟩

/-- (3c) *po-znam* 'guess': lexical *po-*. -/
def a3c : Analysis := ⟨Examples.ex_3c, znam, [(po, .lexical)]⟩

/-- (3d) *za-blest'a* 'start to glitter': low inceptive *za-*. -/
def a3d : Analysis := ⟨Examples.ex_3d, blesta, [(za, .superlexical .inceptive)]⟩

/-- (3i) *pro-četa* 'read completely': lexical *pro-*. -/
def a3i : Analysis := ⟨Examples.ex_3i, cheta, [(pro, .lexical)]⟩

/-- (11) *iz-po-na-raz-pro-dam* 'sell completely many things in excess one by one'. -/
def a11 : Analysis :=
  ⟨Examples.ex_11, dam, [(iz, .superlexical .completive), (po, .superlexical .distributive),
    (na, .superlexical .cumulative), (raz, .superlexical .excessive), (pro, .lexical)]⟩

/-- (13a) *iz-raz-kaža* 'narrate completely': completive *iz-* outside lexical *raz-*. -/
def a13a : Analysis :=
  ⟨Examples.ex_13a, kazha, [(iz, .superlexical .completive), (raz, .lexical)]⟩

/-- (15) *iz-po-na-kaža*: the innermost prefix read as lexical out of context. -/
def a15 : Analysis :=
  ⟨Examples.ex_15, kazha,
    [(iz, .superlexical .completive), (po, .superlexical .distributive), (na, .lexical)]⟩

/-- (18a) *raz-pre-pro-dam* 'sell again in excess'. -/
def a18a : Analysis :=
  ⟨Examples.ex_18a, dam,
    [(raz, .superlexical .excessive), (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (18b) *po-pre-pro-dam* 'sell again a little bit'. -/
def a18b : Analysis :=
  ⟨Examples.ex_18b, dam,
    [(po, .superlexical .attenuative), (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (19a) *po-raz-pre-pro-dam*: attenuative *po-* lowering the intensity of *raz-*. -/
def a19a : Analysis :=
  ⟨Examples.ex_19a, dam, [(po, .superlexical .attenuative), (raz, .superlexical .excessive),
    (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (19b) *iz-raz-pre-pro-dam* 'completely sell again to the very end'. -/
def a19b : Analysis :=
  ⟨Examples.ex_19b, dam, [(iz, .superlexical .completive), (raz, .superlexical .excessive),
    (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (20b) *na-pre-pro-dam* 'sell again a lot of things'. -/
def a20b : Analysis :=
  ⟨Examples.ex_20b, dam,
    [(na, .superlexical .cumulative), (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (20c) *na-pro-dam* 'sell a lot'. -/
def a20c : Analysis := ⟨Examples.ex_20c, dam, [(na, .superlexical .cumulative), (pro, .lexical)]⟩

/-- (20d) *po-na-pro-dam* 'sell a little': attenuative *po-* modifying cumulative *na-*. -/
def a20d : Analysis :=
  ⟨Examples.ex_20d, dam,
    [(po, .superlexical .attenuative), (na, .superlexical .cumulative), (pro, .lexical)]⟩

/-- (21a) *iz-po-na-pro-dam*: distributive *po-* under completive *iz-*. -/
def a21a : Analysis :=
  ⟨Examples.ex_21a, dam, [(iz, .superlexical .completive), (po, .superlexical .distributive),
    (na, .superlexical .cumulative), (pro, .lexical)]⟩

/-- (21b) *iz-po-raz-pro-dam*. -/
def a21b : Analysis :=
  ⟨Examples.ex_21b, dam, [(iz, .superlexical .completive), (po, .superlexical .distributive),
    (raz, .superlexical .excessive), (pro, .lexical)]⟩

/-- (21c) *iz-po-pre-pro-dam*. -/
def a21c : Analysis :=
  ⟨Examples.ex_21c, dam, [(iz, .superlexical .completive), (po, .superlexical .distributive),
    (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (23b) *po-raz-pro-dam* 'sell almost everything'. -/
def a23b : Analysis :=
  ⟨Examples.ex_23b, dam,
    [(po, .superlexical .attenuative), (raz, .superlexical .excessive), (pro, .lexical)]⟩

/-- (23d) *po-iz-pro-dam* 'sell almost completely'. -/
def a23d : Analysis :=
  ⟨Examples.ex_23d, dam,
    [(po, .superlexical .attenuative), (iz, .superlexical .completive), (pro, .lexical)]⟩

/-- (23e) *po-pro-dam* 'sell a little bit'. -/
def a23e : Analysis := ⟨Examples.ex_23e, dam, [(po, .superlexical .attenuative), (pro, .lexical)]⟩

/-- (25a) *do-pro-dam* 'finish selling'. -/
def a25a : Analysis := ⟨Examples.ex_25a, dam, [(do_, .superlexical .terminative), (pro, .lexical)]⟩

/-- (25b) *do-pre-pro-dam* 'finish selling again'. -/
def a25b : Analysis :=
  ⟨Examples.ex_25b, dam,
    [(do_, .superlexical .terminative), (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (25c) *do-raz-pre-pro-dam* 'finish selling again to the very end'. -/
def a25c : Analysis :=
  ⟨Examples.ex_25c1, dam, [(do_, .superlexical .terminative), (raz, .superlexical .excessive),
    (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (25d) *do-iz-po-raz-pre-pro-dam* 'finish re-selling everything to the end'. -/
def a25d : Analysis :=
  ⟨Examples.ex_25d, dam, [(do_, .superlexical .terminative), (iz, .superlexical .completive),
    (po, .superlexical .distributive), (raz, .superlexical .excessive),
    (pre, .superlexical .repetitive), (pro, .lexical)]⟩

/-- (25e) *po-do-iz-raz-pro-dam* 'almost finish reselling to the end'. -/
def a25e : Analysis :=
  ⟨Examples.ex_25e, dam, [(po, .superlexical .attenuative), (do_, .superlexical .terminative),
    (iz, .superlexical .completive), (raz, .superlexical .excessive), (pro, .lexical)]⟩

/-- (25g) *do-peja* 'finish singing': low terminative *do-* on a homogeneous verb. -/
def a25g : Analysis := ⟨Examples.ex_25g, peja, [(do_, .superlexical .terminative)]⟩

/-- (26a) *po-peja* 'sing for a while': delimitative *po-* on a simplex atelic verb. -/
def a26a : Analysis := ⟨Examples.ex_26a, peja, [(po, .superlexical .delimitative)]⟩

/-- (27c) *iz-po-pro-dam* 'sell completely one by one'. -/
def a27c : Analysis :=
  ⟨Examples.ex_27c, dam,
    [(iz, .superlexical .completive), (po, .superlexical .distributive), (pro, .lexical)]⟩

/-- (28c) *iz-po-raz-kaža* 'narrate completely one by one'. -/
def a28c : Analysis :=
  ⟨Examples.ex_28c, kazha,
    [(iz, .superlexical .completive), (po, .superlexical .distributive), (raz, .lexical)]⟩

/-- (28d) *iz-po-na-raz-kaža* 'narrate completely many stories one by one'. -/
def a28d : Analysis :=
  ⟨Examples.ex_28d, kazha, [(iz, .superlexical .completive), (po, .superlexical .distributive),
    (na, .superlexical .cumulative), (raz, .lexical)]⟩

/-- (29) *za-iz-po-na-raz-kaža* 'start narrating many stories one by one'. -/
def a29 : Analysis :=
  ⟨Examples.ex_29, kazha, [(za, .superlexical .inceptive), (iz, .superlexical .completive),
    (po, .superlexical .distributive), (na, .superlexical .cumulative), (raz, .lexical)]⟩

/-- (33a) *iz-po-pro-četa* 'read through completely little by little'. -/
def a33a : Analysis :=
  ⟨Examples.ex_33a, cheta,
    [(iz, .superlexical .completive), (po, .superlexical .distributive), (pro, .lexical)]⟩

/-- (34a) *po-za-peja* 'start singing a bit': attenuative *po-* over low inceptive *za-*. -/
def a34a : Analysis :=
  ⟨Examples.ex_34a, peja, [(po, .superlexical .attenuative), (za, .superlexical .inceptive)]⟩

/-- (35a) *iz-po-na-reža* 'cut completely into many pieces little by little'. -/
def a35a : Analysis :=
  ⟨Examples.ex_35a, rezha, [(iz, .superlexical .completive), (po, .superlexical .distributive),
    (na, .superlexical .cumulative)]⟩

/-- The attested stacks. -/
def attested : List Analysis :=
  [a1a, a3a, a3b, a3c, a3d, a3i, a11, a13a, a15, a18a, a18b, a19a, a19b, a20b, a20c, a20d,
   a21a, a21b, a21c, a23b, a23d, a23e, a25a, a25b, a25c, a25d, a25e, a25g, a26a, a27c, a28c,
   a28d, a29, a33a, a34a, a35a]

/-! ### The starred stacks -/

/-- (25b) *pre-do-pro-dam*: repetitive *pre-* above terminative *do-*. -/
def s25b : Analysis :=
  ⟨Examples.ex_25b, dam,
    [(pre, .superlexical .repetitive), (do_, .superlexical .terminative), (pro, .lexical)]⟩

/-- Table 3 *na-po-pro-dam*: cumulative *na-* above *po-*. -/
def sNaPo : Analysis :=
  ⟨Examples.t3_na_po_pro_dam, dam,
    [(na, .superlexical .cumulative), (po, .superlexical .attenuative), (pro, .lexical)]⟩

/-- Table 3 *raz-po-pro-dam*: excessive *raz-* above *po-*. -/
def sRazPo : Analysis :=
  ⟨Examples.t3_raz_po_pro_dam, dam,
    [(raz, .superlexical .excessive), (po, .superlexical .attenuative), (pro, .lexical)]⟩

/-- (29) without *iz-*, *za-po-na-raz-kaža*: inceptive *za-* above *po-*. -/
def s29 : Analysis :=
  ⟨Examples.ex_29, kazha, [(za, .superlexical .inceptive), (po, .superlexical .attenuative),
    (na, .superlexical .cumulative), (raz, .lexical)]⟩

/-- Table 2 *pre-na-raz-dam*: repetitive *pre-* above cumulative *na-*. -/
def sPreNa : Analysis :=
  ⟨Examples.t2_pre_na_raz_dam, dam,
    [(pre, .superlexical .repetitive), (na, .superlexical .cumulative), (raz, .lexical)]⟩

/-- Table 2 *po-pre-na-raz-dam*. -/
def sPoPreNa : Analysis :=
  ⟨Examples.t2_po_pre_na_raz_dam, dam, [(po, .superlexical .attenuative),
    (pre, .superlexical .repetitive), (na, .superlexical .cumulative), (raz, .lexical)]⟩

/-- The starred stacks that reverse two heads of the hierarchy, or place *po-* below another
head without *iz-* above. -/
def starred : List Analysis := [s25b, sNaPo, sRazPo, s29, sPreNa, sPoPreNa]

/-- Every attested stack is well-formed. -/
theorem attested_wellFormed : ∀ a ∈ attested, WellFormed a.prefixes := by decide

/-- The starred stacks are ill-formed. -/
theorem starred_not_wellFormed : ∀ a ∈ starred, ¬ WellFormed a.prefixes := by decide

/-- The starred stacks with *po-* below another head are ill-formed on the distributive
classification too, for want of *iz-*. -/
theorem starred_distributive_not_wellFormed :
    ¬ WellFormed [(na, .superlexical .cumulative), (po, .superlexical .distributive),
      (pro, .lexical)] ∧
    ¬ WellFormed [(raz, .superlexical .excessive), (po, .superlexical .distributive),
      (pro, .lexical)] ∧
    ¬ WellFormed [(za, .superlexical .inceptive), (po, .superlexical .distributive),
      (na, .superlexical .cumulative), (raz, .lexical)] := by
  decide

/-- The paper's hyphenation equals each analysis' decomposition, the rows being citation
forms. -/
example : ∀ a ∈ attested, a.MatchesSegmentation := by decide

end Istratkova2004
