import Linglib.Phonology.Autosegmental.Melody
import Linglib.Fragments.Hungarian.VowelHarmony
import Linglib.Data.Forms.SiptarTorkenczy2000

/-!
# Siptár and Törkenczy (2000): The Phonology of Hungarian

This file formalizes the analysis of vowel harmony in chapter 6 of [siptar-torkenczy-2000] and
runs it on the derivations the chapter gives. A stem is a sequence of vocalic nodes with the
unary place features COR, LAB and DOR of [clements-hume-1995] either prelinked to nodes or
floating on the morpheme, and a suffix vowel is a node carrying a linked LAB or placeless, with
its aperture. Four rules apply in order: Link DOR and Link Place associate a floating feature,
unboundedly, to every node it may reach; Spread DOR and Spread Place extend an anchored feature
to the adjacent node, iterating left to right; and a node still placeless is coronal by
default. Throughout, DOR may join any node without COR, COR only a placeless node, and LAB any
node without DOR that is not low (`MayLink`, `linkDor`, `linkPlace`, `spreadDor`,
`spreadPlace`, `derive`). The rules only add association lines and never put COR and DOR on
one node (`surfaceLinks_subset_derive`, `derive_sound`). The eleven stem representations of
the chapter's Table 18 with the four suffixes of its (2) yield the forty-four suffixed forms of
its (13) to (23) (`derivations`), transparency, antiharmony and opacity following from the
prelinking alone, and the vacillating stem of section 3.2.3.1 has two representations deriving
its two forms (`dzsungel_vacillates`). The surface generalization of section 3.2, that the
last harmonic vowel governs suffix backness through the transparent neutral vowels, is the
Fragment's `hungarianPalatalHarmony`; it agrees with the derivations on the regular stems and
is silent or wrong exactly on the neutral, antiharmonic and opaque stems the analysis handles
by prelinking (`sourceValue_agrees`, `sourceValue_viz`, `sourceValue_hid`,
`sourceValue_kodex`).

## Implementation notes

* Forms are the substrate's `FloatingForm` with vocalic nodes for the backbone, place features
  for the tier and the stem and suffix as sponsors; a rule inserts association lines, and the
  derivation composes the rules in the chapter's order. Default COR is read at the surface, a
  placeless node counting as coronal. Where the chapter has COR and LAB spread together onto
  one node, COR spreads first and LAB joins it.
* A word is a stem and one suffix; the chapter's stems have at most two vowels and its
  suffixes one, and a prelinked feature is one tier element per node it is linked to.
  Apertures are read from the vowel letters and matter only through the constraint against a
  low labial node; long vowels are not distinguished.
* The forms are rows of `Data/Forms/SiptarTorkenczy2000.json`; a derivation is compared with
  the suffixed form's segments after the stem's, since three of the chapter's forms shorten
  the stem vowel.

## References

* [siptar-torkenczy-2000]
* [clements-hume-1995]
* [rose-walker-2011]
-/

namespace SiptarTorkenczy2000

open Autosegmental Hungarian.VowelHarmony Phonology.Harmony

/-- The unary place features of the vowels, (1) of the chapter. -/
inductive Place
  | cor | lab | dor
  deriving DecidableEq, Fintype

/-- A vocalic node with its aperture features. -/
structure VNode where
  open1 : Bool
  open2 : Bool
  deriving DecidableEq

/-- The aperture of the vowel a letter writes: the high vowels closed on both, the mid vowels
and *é* open on the second, the low vowels and *e* open on both. -/
def VNode.ofLetter (l : String) : VNode :=
  if l ∈ ["i", "í", "ü", "ű", "u", "ú"] then ⟨false, false⟩
  else if l ∈ ["ö", "ő", "o", "ó", "é"] then ⟨false, true⟩
  else ⟨true, true⟩

/-- The sponsors of a word's material. -/
inductive Morph
  | stem | suffix
  deriving DecidableEq

/-- A phonological word as an autosegmental form over vocalic nodes and place features. -/
abbrev Word := FloatingForm VNode Place Morph

/-! ### The rules -/

variable (f : Word)

/-- The place features linked to the `i`-th node. -/
def places (i : ℕ) : List Place := f.tierValues i

/-- Whether the `i`-th node is low. -/
def isLow (i : ℕ) : Bool := ((f.lower.get? i).map (·.value.open1)).getD false

/-- The value of the `k`-th tier element. -/
def valueAt (k : ℕ) : Option Place := (f.upper.get? k).map (·.value)

/-- Where a place feature may associate, principles (7c) and (7d) under constraints (6a) and
(6b): DOR to any node without COR, COR to a placeless node, LAB to a node without DOR that is
not low. -/
def MayLink (p : Place) (i : ℕ) : Prop :=
  i < f.lower.len ∧ (p = .dor → .cor ∉ places f i) ∧ (p = .cor → places f i = []) ∧
    (p = .lab → .dor ∉ places f i ∧ isLow f i = false)

instance (p : Place) (i : ℕ) : Decidable (MayLink f p i) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Associate tier element `k`, bearing `p`, to every node it may link to. -/
def linkAll (k : ℕ) (p : Place) : Word :=
  (List.range f.lower.len).foldl (λ g i => if MayLink g p i then g.insertLink k i else g) f

/-- The floating tier elements bearing `p`. -/
def floating (p : Place) : List ℕ :=
  (List.range f.upper.len).filter λ k => decide (f.IsFloating k ∧ valueAt f k = some p)

/-- Link DOR (3b): every floating DOR associates to every node without COR. -/
def linkDor : Word := (floating f .dor).foldl (λ g k => linkAll g k .dor) f

/-- Link Place (3a): every floating place feature associates to every node it may link to. -/
def linkPlace : Word :=
  (List.range f.upper.len).foldl (λ g k =>
    match valueAt g k with
    | some p => if g.IsFloating k then linkAll g k p else g
    | none => g) f

/-- The tier element bearing `p` anchored on node `i`. -/
def anchored (p : Place) (i : ℕ) : Option ℕ := (f.linksTo i).find? λ k => valueAt f k = some p

/-- Spread `p` from node `i` to the next node when it is anchored on `i` and may link there. -/
def spreadAt (p : Place) (i : ℕ) : Word :=
  match anchored f p i with
  | some k => if MayLink f p (i + 1) then f.insertLink k (i + 1) else f
  | none => f

/-- Spread DOR (4b): iterating left to right, an anchored DOR extends to the next node. -/
def spreadDor : Word := (List.range f.lower.len).foldl (λ g i => spreadAt g .dor i) f

/-- Spread Place (4a): iterating left to right, an anchored COR extends to the next node when
it is placeless, and an anchored LAB when it bears no DOR and is not low. -/
def spreadPlace : Word :=
  (List.range f.lower.len).foldl (λ g i => spreadAt (spreadAt g .cor i) .lab i) f

/-- The derivation: the linking rules, the DOR rule first, then the spreading rules. -/
def derive : Word := spreadPlace (spreadDor (linkPlace (linkDor f)))

/-- The harmonic quality a node surfaces with: back with DOR, front rounded with LAB alone,
and front unrounded with COR or, by Default COR (5), placeless. -/
inductive Quality
  | back | frontRounded | frontUnrounded
  deriving DecidableEq

/-- The quality of a place specification. -/
def quality (ps : List Place) : Quality :=
  if .dor ∈ ps then .back else if .lab ∈ ps then .frontRounded else .frontUnrounded

/-! ### Structural properties -/

variable {f}

/-- Constraint (6a): no node bears both COR and DOR. -/
def Sound (g : Word) : Prop := ∀ i, ¬ (.cor ∈ places g i ∧ .dor ∈ places g i)

theorem mem_places_insertLink {p : Place} {k i j : ℕ} :
    p ∈ places (f.insertLink k i) j ↔ p ∈ places f j ∨ (j = i ∧ valueAt f k = some p) := by
  simp only [places, valueAt, FloatingForm.mem_tierValues, FloatingForm.insertLink_surfaceLinks,
    FloatingForm.insertLink_upper, Finset.mem_insert, Prod.mk.injEq]
  aesop

/-- Inserting a line admitted by `MayLink` keeps the form sound. -/
theorem Sound.insertLink {p : Place} {k i : ℕ} (hs : Sound f) (hv : valueAt f k = some p)
    (hm : MayLink f p i) : Sound (f.insertLink k i) := by
  intro j ⟨hc, hd⟩
  rw [mem_places_insertLink] at hc hd
  rcases hc with hc | ⟨hji, hc⟩ <;> rcases hd with hd | ⟨hji', hd⟩
  · exact hs j ⟨hc, hd⟩
  · exact hm.2.1 (Option.some.inj (hv.symm.trans hd)) (hji' ▸ hc)
  · exact List.ne_nil_of_mem (hji ▸ hd) (hm.2.2.1 (Option.some.inj (hv.symm.trans hc)))
  · exact Place.noConfusion (Option.some.inj (hc.symm.trans hd))

/-- What every rule preserves: the association lines, the tier, and soundness. -/
structure Preserves (f g : Word) : Prop where
  subset : f.surfaceLinks ⊆ g.surfaceLinks
  upper : g.upper = f.upper
  sound : Sound f → Sound g

theorem Preserves.refl : Preserves f f := ⟨subset_rfl, rfl, id⟩

theorem Preserves.trans {g h : Word} (h₁ : Preserves f g) (h₂ : Preserves g h) : Preserves f h :=
  ⟨h₁.subset.trans h₂.subset, h₂.upper.trans h₁.upper, h₂.sound ∘ h₁.sound⟩

theorem Preserves.insertLink {p : Place} {k i : ℕ} (hv : valueAt f k = some p)
    (hm : MayLink f p i) : Preserves f (f.insertLink k i) :=
  ⟨Finset.subset_insert _ _, rfl, λ hs => hs.insertLink hv hm⟩

theorem Preserves.valueAt {g : Word} (h : Preserves f g) (k : ℕ) : valueAt g k = valueAt f k := by
  simp [SiptarTorkenczy2000.valueAt, h.upper]

private theorem foldl_preserves {α : Type*} {step : Word → α → Word} (l : List α)
    (h : ∀ a ∈ l, ∀ g, Preserves f g → Preserves g (step g a)) :
    ∀ g, Preserves f g → Preserves f (l.foldl step g) := by
  induction l with
  | nil => exact λ _ hg => hg
  | cons a l ih =>
    exact λ g hg => ih (λ b hb => h b (List.mem_cons_of_mem a hb)) _
      (hg.trans (h a (List.mem_cons_self ..) g hg))

theorem preserves_linkAll {k : ℕ} {p : Place} (hv : valueAt f k = some p) :
    Preserves f (linkAll f k p) :=
  foldl_preserves _ (λ i _ g hg => by
    split_ifs with hm
    · exact Preserves.insertLink ((hg.valueAt k).trans hv) hm
    · exact .refl) f .refl

theorem preserves_linkDor : Preserves f (linkDor f) :=
  foldl_preserves _ (λ k hk g hg => by
    have hv : valueAt f k = some .dor := (of_decide_eq_true (List.mem_filter.1 hk).2).2
    exact preserves_linkAll ((hg.valueAt k).trans hv)) f .refl

theorem preserves_linkPlace : Preserves f (linkPlace f) :=
  foldl_preserves _ (λ k _ g _ => by
    split
    · split_ifs
      · exact preserves_linkAll ‹_›
      · exact .refl
    · exact .refl) f .refl

theorem preserves_spreadAt (p : Place) (i : ℕ) : Preserves f (spreadAt f p i) := by
  unfold spreadAt
  split
  · next k hk =>
    split_ifs with hm
    · simp only [anchored] at hk
      have := List.find?_some hk
      exact Preserves.insertLink (of_decide_eq_true this) hm
    · exact .refl
  · exact .refl

theorem preserves_spreadDor : Preserves f (spreadDor f) :=
  foldl_preserves _ (λ i _ _ _ => preserves_spreadAt .dor i) f .refl

theorem preserves_spreadPlace : Preserves f (spreadPlace f) :=
  foldl_preserves _ (λ i _ _ _ => (preserves_spreadAt .cor i).trans (preserves_spreadAt .lab i))
    f .refl

theorem preserves_derive : Preserves f (derive f) :=
  preserves_linkDor.trans (preserves_linkPlace.trans
    (preserves_spreadDor.trans preserves_spreadPlace))

/-- The rules only add association lines. -/
theorem surfaceLinks_subset_derive : f.surfaceLinks ⊆ (derive f).surfaceLinks :=
  preserves_derive.subset

/-- The rules never put COR and DOR on one node. -/
theorem derive_sound (hs : Sound f) : Sound (derive f) := preserves_derive.sound hs

/-! ### Stems and suffixes -/

/-- A stem's underlying representation, Table 18: for each vowel its aperture and the place
features prelinked to it, and the floating place features of the morpheme. -/
structure Stem where
  nodes : List (VNode × List Place)
  floating : List Place

/-- The representation of a stem row whose vowels bear the given prelinked features. -/
def Stem.ofRow (row : Data.Forms.Form) (linked : List (List Place)) (floating : List Place) :
    Stem :=
  ⟨((row.segments.filter λ l => (ofLetter l).isSome).map VNode.ofLetter).zip linked, floating⟩

/-- The suffixes of the derivations, (2): the possessive ü/u and the ablative ö/o carry a
linked LAB; the dative e/a, the allative ö/o/e and the inessive e/a are placeless. -/
inductive Suffix
  | poss | abl | dat | all | iness
  deriving DecidableEq

/-- The suffix vowel's aperture. -/
def Suffix.node : Suffix → VNode
  | .poss => ⟨false, false⟩
  | .abl | .all => ⟨false, true⟩
  | .dat | .iness => ⟨true, true⟩

/-- Whether the suffix vowel carries a linked LAB. -/
def Suffix.hasLab : Suffix → Bool
  | .poss | .abl => true
  | .dat | .all | .iness => false

/-- The segments of a suffix at a harmonic quality, none where that quality cannot arise. -/
def Suffix.segments : Suffix → Quality → Option (List String)
  | .poss, .back => some ["u", "n", "k"]
  | .poss, .frontRounded => some ["ü", "n", "k"]
  | .abl, .back => some ["t", "ó", "l"]
  | .abl, .frontRounded => some ["t", "ő", "l"]
  | .dat, .back => some ["n", "a", "k"]
  | .dat, .frontUnrounded => some ["n", "e", "k"]
  | .all, .back => some ["h", "o", "z"]
  | .all, .frontRounded => some ["h", "ö", "z"]
  | .all, .frontUnrounded => some ["h", "e", "z"]
  | .iness, .back => some ["b", "a", "n"]
  | .iness, .frontUnrounded => some ["b", "e", "n"]
  | _, _ => none

/-- The word of a stem and a suffix concatenates the stem's melody, its floating features and
then its prelinked features over its nodes, with the suffix's melody, a LAB over the suffix
node when the suffix has one. -/
def word (s : Stem) (x : Suffix) : Word :=
  let prelinked : List (Place × ℕ) := s.nodes.zipIdx.flatMap fun (v, i) ↦ v.2.map (·, i)
  let n := s.floating.length
  (FloatingForm.melody .stem (s.floating ++ prelinked.map (·.1)) (s.nodes.map (·.1))
      (prelinked.zipIdx.map fun ((q, j) : (Place × ℕ) × ℕ) ↦ (n + j, q.2)).toFinset).concat
    (.melody .suffix (if x.hasLab then [.lab] else []) [x.node]
      (if x.hasLab then {(0, 0)} else ∅))

/-- The suffix segments the derivation yields. -/
def derived (s : Stem) (x : Suffix) : Option (List String) :=
  x.segments (quality (places (derive (word s x)) s.nodes.length))

/-- Whether the derivation gives a stem back suffixes. -/
def Stem.isBack (s : Stem) : Bool :=
  decide (quality (places (derive (word s .dat)) s.nodes.length) = .back)

/-! ### The representations of Table 18 -/

namespace Stem

/-- The pure DOR stem *ház* 'house': a floating DOR (8a). -/
def haz : Stem := ofRow Forms.haz [[]] [.dor]

/-- The pure LAB stem *tűz* 'fire': a floating LAB (8b). -/
def tuz : Stem := ofRow Forms.tuz [[]] [.lab]

/-- The pure COR stem *víz* 'water': a floating COR (8c). -/
def viz : Stem := ofRow Forms.viz [[]] [.cor]

/-- The COR + DOR stem *piros* 'red': a linked COR and a floating DOR (9a). -/
def piros : Stem := ofRow Forms.piros [[.cor], []] [.dor]

/-- The LAB + DOR stem *nüansz* 'nuance': both features linked (10a). -/
def nuansz : Stem := ofRow Forms.nuansz [[.lab], [.dor]] []

/-- The LAB + COR stem *öreg* 'old': both features linked (10b). -/
def oreg : Stem := ofRow Forms.oreg [[.lab], [.cor]] []

/-- The COR + LAB stem *szemölcs* 'wart': a floating COR and a linked LAB (11a). -/
def szemolcs : Stem := ofRow Forms.szemolcs [[], [.lab]] [.cor]

/-- The DOR + LAB stem *sofőr* 'driver': a linked DOR and a labial vowel exceptionally also
coronal, which keeps DOR from spreading onto it (11b). -/
def sofor : Stem := ofRow Forms.sofor [[.dor], [.cor, .lab]] []

/-- The transparent DOR + COR stem *papír* 'paper': a floating DOR and a linked COR (12a). -/
def papir : Stem := ofRow Forms.papir [[], [.cor]] [.dor]

/-- The antiharmonic DOR + COR stem *híd* 'bridge': a linked COR and a floating DOR with no
node in the stem to link to (12b). -/
def hid : Stem := ofRow Forms.hid [[.cor]] [.dor]

/-- The opaque DOR + COR stem *kódex* 'codex': both features linked (12c). -/
def kodex : Stem := ofRow Forms.kodex [[.dor], [.cor]] []

/-- The vacillating stem *dzsungel* 'jungle' represented like *papír*. -/
def dzsungelTransparent : Stem := ofRow Forms.dzsungel [[], [.cor]] [.dor]

/-- The vacillating stem *dzsungel* 'jungle' represented like *kódex*. -/
def dzsungelOpaque : Stem := ofRow Forms.dzsungel [[.dor], [.cor]] []

end Stem

/-- A stem with its four suffixed forms of the derivations. -/
def paradigm (stem : Data.Forms.Form) (s : Stem) (poss abl dat all : Data.Forms.Form) :
    List (Data.Forms.Form × Stem × Suffix × Data.Forms.Form) :=
  [(stem, s, .poss, poss), (stem, s, .abl, abl), (stem, s, .dat, dat), (stem, s, .all, all)]

/-- The derivations (13) to (23): the eleven stems of Table 18, each with the possessive,
ablative, dative and allative. -/
def derivationTable : List (Data.Forms.Form × Stem × Suffix × Data.Forms.Form) :=
  paradigm Forms.haz .haz Forms.hazunk Forms.haztol Forms.haznak Forms.hazhoz ++
    paradigm Forms.tuz .tuz Forms.tuzunk Forms.tuztol Forms.tuznek Forms.tuzhoz ++
    paradigm Forms.viz .viz Forms.vizunk Forms.viztol Forms.viznek Forms.vizhez ++
    paradigm Forms.piros .piros Forms.pirosunk Forms.pirostol Forms.pirosnak Forms.piroshoz ++
    paradigm Forms.nuansz .nuansz Forms.nuanszunk Forms.nuansztol Forms.nuansznak
      Forms.nuanszhoz ++
    paradigm Forms.oreg .oreg Forms.oregunk Forms.oregtol Forms.oregnek Forms.oreghez ++
    paradigm Forms.szemolcs .szemolcs Forms.szemolcsunk Forms.szemolcstol Forms.szemolcsnek
      Forms.szemolcshoz ++
    paradigm Forms.sofor .sofor Forms.soforunk Forms.sofortol Forms.sofornek Forms.soforhoz ++
    paradigm Forms.papir .papir Forms.papirunk Forms.papirtol Forms.papirnak Forms.papirhoz ++
    paradigm Forms.hid .hid Forms.hidunk Forms.hidtol Forms.hidnak Forms.hidhoz ++
    paradigm Forms.kodex .kodex Forms.kodexunk Forms.kodextol Forms.kodexnek Forms.kodexhez

/-- Every derivation of (13) to (23) yields the attested suffix: transparency, antiharmony and
opacity follow from the prelinking of Table 18 by the same rules. -/
theorem derivations : ∀ t ∈ derivationTable,
    derived t.2.1 t.2.2.1 = some (t.2.2.2.segments.drop t.1.segments.length) := by
  decide

/-- The vacillating stem of section 3.2.3.1 derives its back form from the transparent
representation and its front form from the opaque one. -/
theorem dzsungel_vacillates :
    derived .dzsungelTransparent .iness =
        some (Forms.dzsungelban.segments.drop Forms.dzsungel.segments.length) ∧
      derived .dzsungelOpaque .iness =
        some (Forms.dzsungelben.segments.drop Forms.dzsungel.segments.length) := by
  decide

/-! ### The surface generalization of section 3.2

The Fragment's palatal harmony system reads the backness of the last harmonic vowel through
the transparent neutral vowels. -/

/-- The stems whose harmonic vowels govern their suffixes as section 3.2 describes. -/
def regular : List (Data.Forms.Form × Stem) :=
  [(Forms.haz, .haz), (Forms.tuz, .tuz), (Forms.piros, .piros), (Forms.nuansz, .nuansz),
    (Forms.oreg, .oreg), (Forms.szemolcs, .szemolcs), (Forms.sofor, .sofor),
    (Forms.papir, .papir)]

/-- On the regular stems the surface generalization and the derivations agree. -/
theorem sourceValue_agrees : ∀ t ∈ regular,
    hungarianPalatalHarmony.searchCopy.sourceValue (vowelsOf t.1.segments) = some t.2.isBack := by
  decide

/-- A pure COR stem has no harmonic vowel to read, and its floating COR derives front
suffixes. -/
theorem sourceValue_viz :
    hungarianPalatalHarmony.searchCopy.sourceValue (vowelsOf Forms.viz.segments) = none ∧
      Stem.viz.isBack = false := by
  decide

/-- An antiharmonic stem has no harmonic vowel to read either; its floating DOR derives back
suffixes. -/
theorem sourceValue_hid :
    hungarianPalatalHarmony.searchCopy.sourceValue (vowelsOf Forms.hid.segments) = none ∧
      Stem.hid.isBack = true := by
  decide

/-- An opaque stem's last harmonic vowel is back, yet its linked DOR cannot reach the suffix
and its linked COR derives front suffixes. -/
theorem sourceValue_kodex :
    hungarianPalatalHarmony.searchCopy.sourceValue (vowelsOf Forms.kodex.segments) = some true ∧
      Stem.kodex.isBack = false := by
  decide

end SiptarTorkenczy2000
