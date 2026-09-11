import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Union
import Linglib.Phonology.Autosegmental.NonCrossing

/-!
# Hayes (1989): Compensatory Lengthening in Moraic Phonology

This file formalizes the moraic theory of compensatory lengthening (CL) of [hayes-1989]: a
syllabification that gives vowels their moras underlyingly and coda consonants theirs by the
language-particular rule of Weight by Position, deletion on the segmental tier only, Parasitic
Delinking, and CL as the filling of a stranded mora by a language-particular convention, all
under the ban on crossing association lines. The typological argument of the paper's §5 is
derived from the representations: `cl_delete_of_onset` is the onset-deletion asymmetry (an
onset projects no mora, so its loss strands nothing, and Moraic Conservation holds by
construction), and `not_isPlanar_link_of_onset` is the vowel-loss asymmetry (a stranded mora
cannot lengthen the vowel to its right across that syllable's onset). The seven CL types of
the typology, the weight prerequisite of §6, and the two-mora limit and trimoraic syllables of
§7 are run as derivations on the paper's forms.

## Implementation notes

A `Form` places every prosodic node at the timeline slot of the segment that projected it, so
the syllable, mora, and segmental tiers share one order and the lines a syllable node draws
directly to its onset consonants can cross the lines of a mora; `Autosegmental.IsNonCrossing`
on the node-to-segment lines is then the ban on crossing association lines as (66) and (68)
use it. The melody alphabet `Seg` is schematic, as the paper's forms are: segment features play
no role in the argument. Intervocalic clusters divide after their first consonant; every form
below has a one-consonant onset, so the language-particular division principles of §2.1 are
not needed. A CL convention takes the nearest linked segment on its side; the vowel-only
restriction of (17b) and the sonority-graded Degemination (41) of Ilokano are not modelled.

## TODO

* The cluster cases of (27d), where Stray Erasure removes the unsyllabifiable half of the
  geminate, and Degemination (41).
* The X-theory derivations of §3.1, §4, and §5.3 that the moraic account is compared against.

## References

* [hayes-1989]
* [hyman-1985]
* [ito-1986]
* [steriade-1982]
-/

namespace Hayes1989

open Autosegmental

/-! ### Prosodic nodes -/

/-- The prosodic tiers above the melody. -/
inductive Tier
  | syl
  | mora
  deriving DecidableEq, Repr

/-- A prosodic node: its tier and the timeline slot of the segment that projected it, the
    nucleus for a syllable node and the mora-bearing segment for a mora; `idx` tells apart
    the two morae of one long vowel ((3a)). -/
structure Node where
  tier : Tier
  slot : ℕ
  idx : ℕ := 0
  deriving DecidableEq, Repr

namespace Node

/-- The syllable node over the nucleus at slot `v`. -/
abbrev σ (v : ℕ) : Node := ⟨.syl, v, 0⟩

/-- The `k`-th mora projected from slot `i`. -/
abbrev μ (i : ℕ) (k : ℕ := 0) : Node := ⟨.mora, i, k⟩

/-- Nodes are ordered by slot: the order in which association lines are drawn. -/
instance : Preorder Node := Preorder.lift Node.slot

instance : DecidableLT Node := λ a b => inferInstanceAs (Decidable (a.slot < b.slot))
instance : DecidableLE Node := λ a b => inferInstanceAs (Decidable (a.slot ≤ b.slot))

end Node

open Node

/-! ### Forms -/

/-- A moraic representation over a melody: segment `i` occupies timeline slot `i`. -/
structure Form (α : Type*) where
  /-- The segmental tier. -/
  melody : List α
  /-- The prosodic nodes present: a syllable deleted by Parasitic Delinking is gone, a stranded
      mora survives. -/
  nodes : Finset Node
  /-- Domination of morae by syllable nodes. -/
  dom : Finset (Node × Node)
  /-- Association lines to the melody: a syllable node to its onset consonants, a mora to the
      segments it dominates. -/
  links : Finset (Node × ℕ)

namespace Form

variable {α : Type*} (f : Form α)

/-- The ban on crossing association lines, on both layers. -/
def IsPlanar : Prop := IsNonCrossing f.links ∧ IsNonCrossing f.dom

instance : Decidable f.IsPlanar := by unfold IsPlanar; infer_instance

/-- The slots node `n` is associated to. -/
def span (n : Node) : Finset ℕ := (f.links.filter (·.1 = n)).image (·.2)

/-- The morae of syllable node `s`. -/
def morae (s : Node) : Finset Node := (f.dom.filter (·.1 = s)).image (·.2)

/-- Syllable weight: the number of morae. -/
def weight (s : Node) : ℕ := (f.morae s).card

/-- The nuclear segments of syllable node `s`: the slots its morae dominate. -/
def nuclear (s : Node) : Finset ℕ := (f.morae s).biUnion f.span

/-- The number of association lines at slot `i`: one for a short segment, two for a long vowel
    ((3a)) or a geminate ((9a)). -/
def length (i : ℕ) : ℕ := (f.links.filter (·.2 = i)).card

/-- Morae stranded by a deletion on the segmental tier: they dominate nothing. -/
def stranded : Finset Node := f.nodes.filter λ n => n.tier = .mora ∧ f.span n = ∅

/-- Morae no syllable node dominates. -/
def free : Finset Node := f.nodes.filter λ n => n.tier = .mora ∧ ∀ p ∈ f.dom, p.2 ≠ n

/-- The mora count of the form. -/
def moraCount : ℕ := (f.nodes.filter (·.tier = .mora)).card

/-- The surface string after Stray Erasure: each linked segment with its number of lines. -/
def surface : List (α × ℕ) :=
  f.melody.zipIdx.filterMap λ p => if 0 < f.length p.2 then some (p.1, f.length p.2) else none

/-! #### Operations -/

/-- Deletion on the segmental tier only ((17a)): slot `i` loses every association line, and
    a mora that dominated it alone is stranded. -/
def delete (i : ℕ) : Form α := { f with links := f.links.filter (·.2 ≠ i) }

/-- Erase one association line: Glide Formation (37) disassociates a vowel from its mora. -/
def delink (n : Node) (i : ℕ) : Form α := { f with links := f.links.erase (n, i) }

/-- Draw one association line: spreading onto a stranded mora, or adjunction of a stray
    segment. -/
def link (n : Node) (i : ℕ) : Form α := { f with links := insert (n, i) f.links }

/-- Parasitic Delinking (23): a syllable node with no nuclear segment is deleted with its
    lines; its morae survive, now free. -/
def parasitic : Form α :=
  let dead := f.nodes.filter λ n => n.tier = .syl ∧ f.nuclear n = ∅
  { f with nodes := f.nodes \ dead, dom := f.dom.filter (·.1 ∉ dead),
           links := f.links.filter (·.1 ∉ dead) }

/-- Prosodic Licensing ([ito-1986]): a free mora adjoins the nearest syllable node to its
    left. -/
def adjoin : Form α :=
  { f with dom := f.dom ∪ f.free.biUnion λ m =>
      (((List.range (m.slot + 1)).filter λ v => σ v ∈ f.nodes).getLast?).elim ∅ λ v =>
        {(σ v, m)} }

/-- A language's CL convention ((17b), (25a), (40a)): fill a stranded mora from the nearest
    segment linked to a node on its left, or on its right. -/
inductive Convention
  | fromLeft
  | fromRight
  deriving DecidableEq, Repr

/-- The segment the convention spreads onto stranded mora `m`, if any. -/
def filler (m : Node) : Convention → Option ℕ
  | .fromLeft =>
    ((List.range f.melody.length).filter (· ∈ (f.links.filter (·.1 < m)).image (·.2))).getLast?
  | .fromRight =>
    ((List.range f.melody.length).filter (· ∈ (f.links.filter (m < ·.1)).image (·.2))).head?

/-- Compensatory lengthening: every stranded mora is filled by the convention's segment; a
    mora with none stays stranded, for Stray Erasure. -/
def cl (c : Convention) : Form α :=
  { f with
    links := f.links ∪ f.stranded.biUnion λ m => (f.filler m c).elim ∅ λ i => {(m, i)} }

/-! #### Moraic Conservation (64)

No operation but Stray Erasure touches the mora tier, so CL conserves mora count by
construction. -/

@[simp] theorem moraCount_delete (i : ℕ) : (f.delete i).moraCount = f.moraCount := rfl

@[simp] theorem moraCount_delink (n : Node) (i : ℕ) :
    (f.delink n i).moraCount = f.moraCount := rfl

@[simp] theorem moraCount_link (n : Node) (i : ℕ) : (f.link n i).moraCount = f.moraCount := rfl

@[simp] theorem moraCount_adjoin : f.adjoin.moraCount = f.moraCount := rfl

@[simp] theorem moraCount_cl (c : Convention) : (f.cl c).moraCount = f.moraCount := rfl

@[simp] theorem moraCount_parasitic : f.parasitic.moraCount = f.moraCount := by
  unfold moraCount parasitic
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_sdiff, not_and]
  constructor
  · exact λ h => ⟨h.1.1, h.2⟩
  · refine λ h => ⟨⟨h.1, λ _ h' => ?_⟩, h.2⟩
    rw [h.2] at h'
    exact absurd h' (by decide)

@[simp] theorem nodes_delete (i : ℕ) : (f.delete i).nodes = f.nodes := rfl

/-! #### Stranding -/

theorem span_delete (n : Node) (i : ℕ) : (f.delete i).span n = (f.span n).erase i := by
  ext j
  simp only [span, delete, Finset.mem_image, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨p, ⟨⟨hp, hpi⟩, hn⟩, rfl⟩
    exact ⟨hpi, p, ⟨hp, hn⟩, rfl⟩
  · rintro ⟨hji, p, ⟨hp, hn⟩, rfl⟩
    exact ⟨p, ⟨⟨hp, hji⟩, hn⟩, rfl⟩

/-- Deleting slot `i` strands exactly the morae whose only segment was at `i`. -/
theorem stranded_delete (i : ℕ) :
    (f.delete i).stranded =
      f.stranded ∪ f.nodes.filter (λ n => n.tier = .mora ∧ f.span n = {i}) := by
  ext n
  simp only [stranded, span_delete, nodes_delete, Finset.mem_union, Finset.mem_filter,
    Finset.erase_eq_empty_iff]
  tauto

/-- **The onset-deletion asymmetry** (§5.3.1): a slot linked only from syllable nodes bears
    no mora, so deleting it strands nothing. -/
theorem stranded_delete_of_onset {i : ℕ} (h : ∀ p ∈ f.links, p.2 = i → p.1.tier = .syl) :
    (f.delete i).stranded = f.stranded := by
  rw [stranded_delete, Finset.union_eq_left, Finset.subset_iff]
  intro n hn
  simp only [Finset.mem_filter] at hn
  have hi : i ∈ f.span n := by rw [hn.2.2]; exact Finset.mem_singleton_self i
  simp only [span, Finset.mem_image, Finset.mem_filter] at hi
  obtain ⟨p, ⟨hp, rfl⟩, rfl⟩ := hi
  have := h p hp rfl
  rw [hn.2.1] at this
  exact absurd this (by decide)

/-- A form with no stranded mora is untouched by CL. -/
theorem cl_eq_self (h : f.stranded = ∅) (c : Convention) : f.cl c = f := by
  simp [cl, h]

/-- CL from onset deletion is impossible ((57), (63)): with nothing stranded, the convention
    finds nothing to fill, and the mora count could only grow by a mora the representation
    does not provide. -/
theorem cl_delete_of_onset {i : ℕ} (h : ∀ p ∈ f.links, p.2 = i → p.1.tier = .syl)
    (h₀ : f.stranded = ∅) (c : Convention) : (f.delete i).cl c = f.delete i :=
  (f.delete i).cl_eq_self (by rw [stranded_delete_of_onset f h, h₀]) c

/-! #### Crossing -/

/-- A new line from `m` to `v` crosses an existing line from a node to the left of `m` to a
    slot to the right of `v`. -/
theorem not_isPlanar_link_of_left {n m : Node} {x v : ℕ} (h : (n, x) ∈ f.links) (hn : n < m)
    (hx : v < x) : ¬ (f.link m v).IsPlanar := λ ⟨hl, _⟩ =>
  absurd (isNonCrossing_iff.1 hl (n, x) (Finset.mem_insert_of_mem h) (m, v)
    (Finset.mem_insert_self _ _) hn) (not_le.2 hx)

/-- A new line from `m` to `v` crosses an existing line from a node to the right of `m` to a
    slot to the left of `v`. -/
theorem not_isPlanar_link_of_right {n m : Node} {x v : ℕ} (h : (n, x) ∈ f.links) (hn : m < n)
    (hx : x < v) : ¬ (f.link m v).IsPlanar := λ ⟨hl, _⟩ =>
  absurd (isNonCrossing_iff.1 hl (m, v) (Finset.mem_insert_self _ _) (n, x)
    (Finset.mem_insert_of_mem h) hn) (not_le.2 hx)

/-- **The vowel-loss asymmetry** (§5.3.2, (61) and (66)): a stranded mora to the left of a
    syllable cannot lengthen its nucleus `v` across an onset consonant `c`, whose line from the
    syllable node it would cross. Rightward CL through vowel loss is unattested. -/
theorem not_isPlanar_link_of_onset {m : Node} {v c : ℕ} (hc : (σ v, c) ∈ f.links)
    (hm : m.slot < v) (hcv : c < v) : ¬ (f.link m v).IsPlanar :=
  f.not_isPlanar_link_of_right hc hm hcv

/-- (68): a moraic coda `c` between the nucleus `v` and a stranded mora to its right blocks
    the vowel's lengthening, so vowel-loss CL favours open syllables. -/
theorem not_isPlanar_link_of_coda {m : Node} {v c : ℕ} (hc : (μ c, c) ∈ f.links) (hv : v < c)
    (hm : c < m.slot) : ¬ (f.link m v).IsPlanar :=
  f.not_isPlanar_link_of_left hc hm hv

end Form

/-! ### Syllabification (§2.1)

An underlying form lists each segment with its mora count ((3)–(7)): none for a consonant or
glide, one for a short vowel, two for a long vowel. Moraic segments are nuclei; a consonant
adjoins as onset to the following nucleus when prevocalic and otherwise as coda to the
preceding one; Weight by Position (10) gives a coda its own mora while the syllable is below
the language's mora limit, and a later coda rides the syllable's last mora ((11d)). -/

/-- An underlying form: segments with their mora counts. -/
abbrev Underlying (α : Type*) := List (α × ℕ)

namespace Underlying

variable {α : Type*} (u : Underlying α)

/-- The underlying mora count at slot `i`. -/
def morae (i : ℕ) : ℕ := (u[i]?.map Prod.snd).getD 0

/-- The nucleus slots. -/
def nuclei : List ℕ := (List.range u.length).filter λ i => 0 < u.morae i

/-- The nucleus whose syllable slot `i` belongs to: its own if moraic; the following one if
    the slot is the consonant right before it; else the preceding one. -/
def host (i : ℕ) : Option ℕ :=
  if 0 < u.morae i then some i else
  match (u.nuclei.filter (· < i)).getLast?, (u.nuclei.filter (i < ·)).head? with
  | none, none => none
  | none, some v => some v
  | some v, none => some v
  | some v₁, some v₂ => if i + 1 = v₂ then some v₂ else some v₁

/-- The nucleus slot `c` is an onset consonant of, if any. -/
def onsetHost (c : ℕ) : Option ℕ := (u.host c).bind λ v => if c < v then some v else none

/-- The nucleus slot `c` is a coda consonant of, if any. -/
def codaHost (c : ℕ) : Option ℕ := (u.host c).bind λ v => if v < c then some v else none

/-- The number of coda consonants of the same syllable before `c`. -/
def codaRank (c : ℕ) : ℕ := ((List.range c).filter λ c' => u.codaHost c' = u.codaHost c).length

/-- Weight by Position (10) gives coda `c` of the syllable at `v` its own mora: the language
    has the rule and the syllable is still below its mora limit. -/
def Projects (wbp : Bool) (limit v c : ℕ) : Prop := wbp ∧ u.morae v + u.codaRank c < limit

instance (wbp : Bool) (limit v c : ℕ) : Decidable (u.Projects wbp limit v c) := by
  unfold Projects; infer_instance

/-- The mora dominating coda `c` of the syllable at `v`: its own under Weight by Position,
    else the syllable's last mora so far. -/
def codaMora (wbp : Bool) (limit v c : ℕ) : Node :=
  if u.Projects wbp limit v c then μ c else
  match ((List.range c).filter λ c' =>
      u.codaHost c' = some v ∧ u.Projects wbp limit v c').getLast? with
  | some c' => μ c'
  | none => μ v (u.morae v - 1)

/-- The onset lines. -/
def onsets : List (Node × ℕ) :=
  (List.range u.length).filterMap λ c => (u.onsetHost c).map λ v => (σ v, c)

/-- The coda consonants with their syllables. -/
def codas : List (ℕ × ℕ) :=
  (List.range u.length).filterMap λ c => (u.codaHost c).map λ v => (v, c)

/-- Syllabify: nuclei project syllable nodes over their morae, onsets adjoin to the syllable
    node, codas to a mora, with Weight by Position for a language that has it (`wbp`) up to its
    mora limit (two, by default: §7). -/
def syllabify (wbp : Bool) (limit : ℕ := 2) : Form α :=
  let vMorae := u.nuclei.flatMap λ v => (List.range (u.morae v)).map λ k => (σ v, μ v k)
  let cMorae := u.codas.filterMap λ p =>
    if u.Projects wbp limit p.1 p.2 then some (σ p.1, μ p.2) else none
  { melody := u.map Prod.fst
    nodes := (u.nuclei.map σ ++ (vMorae ++ cMorae).map Prod.snd).toFinset
    dom := (vMorae ++ cMorae).toFinset
    links := (u.onsets ++ vMorae.map (λ p => (p.2, p.2.slot)) ++
      u.codas.map (λ p => (u.codaMora wbp limit p.1 p.2, p.2))).toFinset }

end Underlying

/-! ### The forms of the paper -/

/-- The schematic melody alphabet of the paper's forms. -/
inductive Seg
  | a | e | i | o | u | schwa
  | b | d | g | k | l | m | n | p | r | s | t | v | w | x | θ | ng
  deriving DecidableEq, Repr

open Seg Form.Convention

/-- A short vowel. -/
abbrev V (seg : Seg) : Seg × ℕ := (seg, 1)

/-- A long vowel ((3a)). -/
abbrev VV (seg : Seg) : Seg × ℕ := (seg, 2)

/-- A consonant or glide ((4), (5)). -/
abbrev C (seg : Seg) : Seg × ℕ := (seg, 0)

/-! #### Classical CL: Latin (12), (17) -/

/-- Latin *kasnus* 'gray' ((12b)), CVC heavy. -/
def kasnus : Form Seg := Underlying.syllabify [C k, V a, C s, C n, V u, C s] true

/-- *s* deletes before an anterior sonorant on the segmental tier only ((17a)), stranding the
    coda mora. -/
theorem kasnus_stranded : (kasnus.delete 2).stranded = {μ 2} := by decide

/-- (17c): the stranded mora is filled by spreading from the left. -/
def kaanus : Form Seg := (kasnus.delete 2).cl fromLeft

theorem kaanus_planar : kaanus.IsPlanar := by decide

theorem kaanus_surface : kaanus.surface = [(k, 1), (a, 2), (n, 1), (u, 1), (s, 1)] := by decide

/-- Moraic Conservation (64) on the derivation. -/
theorem kaanus_moraCount : kaanus.moraCount = kasnus.moraCount := by simp [kaanus]

/-! #### Onset deletion: Latin (14), (18) and Turkish -/

/-- Latin *smereō* 'deserve' ((14)): word-initial *s* is an onset. -/
def smereo : Form Seg := Underlying.syllabify [C s, C m, V e, C r, V e, VV o] true

/-- (18): deleting the onset *s* strands nothing, so the convention has nothing to fill. -/
theorem mereo_no_cl : (smereo.delete 0).cl fromLeft = smereo.delete 0 :=
  smereo.cl_delete_of_onset (by decide) (by decide) _

/-- Turkish *savmak* 'to get rid of' (§5.2.1, after Sezer 1986): coda *v* deletes with CL. -/
def savmak : Form Seg := Underlying.syllabify [C s, V a, C v, C m, V a, C k] true

theorem saamak_surface :
    ((savmak.delete 2).cl fromLeft).surface = [(s, 1), (a, 2), (m, 1), (a, 1), (k, 1)] := by
  decide

/-- Turkish *davul* 'drum': onset *v* deletes without CL, [daul] and not *[daːul]. -/
def davul : Form Seg := Underlying.syllabify [C d, V a, C v, V u, C l] true

theorem daul_no_cl : (davul.delete 2).cl fromLeft = davul.delete 2 :=
  davul.cl_delete_of_onset (by decide) (by decide) _

/-! #### Double flop: Ancient Greek (19), (21) -/

/-- East Ionic *odwos* 'threshold' ((19)): *d* is a moraic coda, *w* the next onset. -/
def odwos : Form Seg := Underlying.syllabify [V o, C d, C w, V o, C s] true

/-- Deleting the onset *w* strands nothing; the *d* then resyllabifies as the onset of the
    following syllable, and only that strands its mora ((21)). -/
def odwos_flop : Form Seg := ((odwos.delete 2).delink (μ 1) 1).link (σ 3) 1

theorem odwos_delete_stranded : (odwos.delete 2).stranded = ∅ :=
  odwos.stranded_delete_of_onset (by decide)

theorem odwos_flop_stranded : odwos_flop.stranded = {μ 1} := by decide

/-- Nonlocal CL: the vowel that lengthens is not adjacent to the consonant that deleted. -/
theorem oodos_surface :
    (odwos_flop.cl fromLeft).surface = [(o, 2), (d, 1), (o, 1), (s, 1)] := by decide

theorem oodos_planar : (odwos_flop.cl fromLeft).IsPlanar := by decide

/-! #### Vowel loss: Middle English (24)–(26) and the asymmetry (61), (66), (68) -/

/-- Middle English *tale* 'tale' (Minkova 1982). -/
def tale : Form Seg := Underlying.syllabify [C t, V a, C l, V schwa] true

/-- Schwa Drop and Parasitic Delinking (24): the second syllable goes, its mora is free. -/
def tal_free : Form Seg := (tale.delete 3).parasitic

theorem tal_free_nodes : tal_free.nodes = {σ 1, μ 1, μ 3} := by decide

/-- (25)–(26): CL from the left, then the stray *l* adjoins to the migrated mora, which the
    first syllable adopts. -/
def taal : Form Seg := ((tal_free.cl fromLeft).link (μ 3) 2).adjoin

theorem taal_planar : taal.IsPlanar := by decide

theorem taal_surface : taal.surface = [(t, 1), (a, 2), (l, 1)] := by decide

theorem taal_weight : taal.weight (σ 1) = 2 := by decide

theorem taal_moraCount : taal.moraCount = tale.moraCount := by simp [taal, tal_free]

/-- The mirror image (61), (66): *#ala* with the first vowel deleted. -/
def ala : Form Seg := Underlying.syllabify [V a, C l, V a] true

/-- After Parasitic Delinking the first mora is free, but the *l* remains the second
    syllable's onset. -/
def la_free : Form Seg := (ala.delete 0).parasitic

theorem la_free_stranded : la_free.stranded = {μ 0} := by decide

/-- Rightward vowel lengthening crosses the onset line: *#laː* cannot arise. -/
theorem no_rightward_vowel_loss : ¬ (la_free.link (μ 0) 2).IsPlanar :=
  la_free.not_isPlanar_link_of_onset (c := 1) (by decide) (by decide) (by decide)

/-- The remaining planar option is (56): the *l* geminates, the first half in its own
    syllable. -/
theorem lla_surface : ((la_free.cl fromRight).surface) = [(l, 2), (a, 1)] := by decide

theorem lla_planar : (la_free.cl fromRight).IsPlanar := by decide

/-- (68): *talpa* with the final vowel deleted; the first syllable is closed by a moraic
    *l*. -/
def talpa : Form Seg := Underlying.syllabify [C t, V a, C l, C p, V a] true

def talp_free : Form Seg := (talpa.delete 4).parasitic

/-- The vowel cannot lengthen across its coda's line. -/
theorem talp_no_vowel_lengthening : ¬ (talp_free.link (μ 4) 1).IsPlanar :=
  talp_free.not_isPlanar_link_of_coda (c := 2) (by decide) (by decide) (by decide)

/-- The *l* could, at the price of a consonant linked to two morae of one syllable ((7)), the
    configuration Estonian permits. -/
theorem talp_consonant_lengthening : (talp_free.link (μ 4) 2).IsPlanar := by decide

theorem talp_consonant_length : (talp_free.link (μ 4) 2).length 2 = 2 := by decide

/-! #### Glide Formation: Ilokano (38)–(40) and Managerial Lengthening (44), (46) -/

/-- Ilokano *bagi + en* 'to have as one's own' ((27a)), CVC heavy. -/
def bagien : Form Seg := Underlying.syllabify [C b, V a, C g, V i, V e, C n] true

/-- Glide Formation (37) delinks the stem vowel from its mora, Parasitic Delinking removes its
    syllable, and the stray *g* and glide adjoin to the following syllable (39). -/
def bagien_gf : Form Seg := ((bagien.delink (μ 3) 3).parasitic.link (σ 4) 2).link (σ 4) 3

theorem bagien_gf_stranded : bagien_gf.stranded = {μ 3} := by decide

theorem bagien_gf_planar : bagien_gf.IsPlanar := by decide

/-- Ilokano fills from the right ((40a)): the *g*, now an onset of the following syllable,
    spreads onto the mora, which the first syllable adopts: *bag.gyen*. -/
def baggyen : Form Seg := (bagien_gf.cl fromRight).adjoin

theorem baggyen_filler : bagien_gf.filler (μ 3) fromRight = some 2 := by decide

theorem baggyen_surface :
    baggyen.surface = [(b, 1), (a, 1), (g, 2), (i, 1), (e, 1), (n, 1)] := by decide

theorem baggyen_planar : baggyen.IsPlanar := by decide

theorem baggyen_weight : baggyen.weight (σ 1) = 2 := by decide

/-- Nothing but the convention keeps the preceding vowel from filling the mora instead ((44)):
    *baagyen*, the Managerial Lengthening of English *patience* ((46)). -/
def baagyen : Form Seg := (bagien_gf.cl fromLeft).adjoin

theorem baagyen_filler : bagien_gf.filler (μ 3) fromLeft = some 1 := by decide

theorem baagyen_surface :
    baagyen.surface = [(b, 1), (a, 2), (g, 1), (i, 1), (e, 1), (n, 1)] := by decide

theorem baagyen_planar : baagyen.IsPlanar := by decide

/-! #### Total assimilation (49a) and prenasalization (52) -/

/-- Regressive total assimilation, *asta* → *atta*: the coda deletes and the following
    consonant fills its mora, the convention of Lesbian and Thessalian Greek (§3.3). -/
def asta : Form Seg := Underlying.syllabify [V a, C s, C t, V a] true

theorem atta_surface : ((asta.delete 1).cl fromRight).surface = [(a, 1), (t, 2), (a, 1)] := by
  decide

theorem atta_planar : ((asta.delete 1).cl fromRight).IsPlanar := by decide

/-- Bantu prenasalization, *amba* → *aːmba*: the nasal leaves its mora for the onset of the
    following syllable, and the vowel fills it. -/
def amba : Form Seg := Underlying.syllabify [V a, C m, C b, V a] true

def aamba : Form Seg := ((amba.delink (μ 1) 1).link (σ 3) 1).cl fromLeft

theorem aamba_surface : aamba.surface = [(a, 2), (m, 1), (b, 1), (a, 1)] := by decide

theorem aamba_planar : aamba.IsPlanar := by decide

/-! #### Inverse CL: Luganda (55a) -/

/-- Luganda *aika* → *akka*: the vowel deletes and the following consonant geminates. -/
def aika : Form Seg := Underlying.syllabify [V a, V i, C k, V a] true

def akka : Form Seg := ((aika.delete 1).parasitic.cl fromRight).adjoin

theorem akka_surface : akka.surface = [(a, 1), (k, 2), (a, 1)] := by decide

theorem akka_planar : akka.IsPlanar := by decide

/-! #### The weight prerequisite (§6, (71)) -/

/-- *pas* in a language without Weight by Position: the coda rides the nucleus mora. -/
def pas_light : Form Seg := Underlying.syllabify [C p, V a, C s] false

/-- *pas* in a language with Weight by Position. -/
def pas_heavy : Form Seg := Underlying.syllabify [C p, V a, C s] true

/-- Without a weight distinction, coda deletion strands no mora and CL cannot occur. -/
theorem pas_light_no_cl : (pas_light.delete 2).stranded = ∅ := by decide

theorem pas_heavy_cl : (pas_heavy.delete 2).stranded = {μ 2} := by decide

theorem pas_light_weight : pas_light.weight (σ 1) = 1 := by decide

theorem pas_heavy_weight : pas_heavy.weight (σ 1) = 2 := by decide

/-! #### The two-mora limit and trimoraic syllables (§7) -/

/-- Komi *sult.ni* 'to stand up' ((73)): in a doubly closed syllable under the two-mora limit
    the *t* shares the *l*'s mora. -/
def sultni : Form Seg := Underlying.syllabify [C s, V u, C l, C t, C n, V i] true

/-- Deleting the *l* strands nothing: [sutni], no CL. -/
theorem sutni_no_cl : (sultni.delete 2).stranded = ∅ := by decide

/-- Komi *sul.ta.li* 'I stood up': the *l* alone closes its syllable and bears a mora. -/
def sultali : Form Seg := Underlying.syllabify [C s, V u, C l, C t, V a, C l, V i] true

theorem suutali_surface :
    ((sultali.delete 2).cl fromLeft).surface =
      [(s, 1), (u, 2), (t, 1), (a, 1), (l, 1), (i, 1)] := by decide

/-- Proto-Germanic *θangxta* 'thought' ((74)): CL in a nonfinal doubly closed syllable needs a
    trimoraic syllable, a mora limit of three. -/
def θangxta : Form Seg := Underlying.syllabify [C θ, V a, C ng, C x, C t, V a] true 3

theorem θangxta_weight : θangxta.weight (σ 1) = 3 := by decide

theorem θaaxta_surface :
    ((θangxta.delete 2).cl fromLeft).surface =
      [(θ, 1), (a, 2), (x, 1), (t, 1), (a, 1)] := by decide

/-- Under the two-mora limit the same change is underivable. -/
theorem θangxta_limit_two_no_cl :
    ((Underlying.syllabify [C θ, V a, C ng, C x, C t, V a] true).delete 2).stranded = ∅ := by
  decide

/-- Dithmarschen German *spreeke* 'speak, 1sg' ((76c)): vowel loss with CL lengthens a long
    vowel to overlong, a trimoraic syllable ((77)). -/
def spreeke : Form Seg := Underlying.syllabify [C s, C p, C r, VV e, C k, V schwa] true

def spreeek : Form Seg := (((spreeke.delete 5).parasitic.cl fromLeft).link (μ 5) 4).adjoin

theorem spreeek_surface : spreeek.surface = [(s, 1), (p, 1), (r, 1), (e, 3), (k, 1)] := by
  decide

theorem spreeek_weight : spreeek.weight (σ 3) = 3 := by decide

theorem spreeek_planar : spreeek.IsPlanar := by decide

end Hayes1989
