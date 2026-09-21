import Linglib.Data.PHOIBLE.Inventories.Indonesian
import Linglib.Phonology.Segmental.PHOIBLE
import Linglib.Phonology.Segmental.FeatureClass
import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Indonesian phonology

This file defines the segments of Standard Indonesian and the alternation of the nasal that
ends the prefixes *meN-* and *peN-*.

The capital N of the grammars is a velar nasal /ŋ/, which surfaces unchanged before a vowel or
*h*, as in *mengajar* from *ajar*. Before an obstruent it takes the obstruent's place of
articulation, as in *membeli* from *beli* and *mendengar* from *dengar*. Before a nasal, a
liquid or a glide it is lost, as in *melihat* from *lihat*. A base-initial *p*, *t*, *k* or *s*
is not itself realized, so that *pakai* gives *memakai* and *tulis* gives *menulis*, the process
known as nasal substitution, which Indonesian shares with Tagalog and many other Malayo-Polynesian
languages (Donohue). Two facts are particular to the standard language
(McDonnell and colleagues). The affricate *c* is not substituted, as in *mencari*, although it
is in most other Malayic varieties, and the nasal that replaces *s* is the palatal *ny*, as in
*menyewa*, where assimilation gives an alveolar.

Assimilation and substitution differ in where they apply (Pater). A nasal is homorganic with a
following obstruent throughout the word, inside a root as in *tampar* and between two prefixes
as in *memperbesar*, so assimilation is a rewrite rule over the whole string. Substitution is
confined to the left edge of the root. The cluster of *tampar* and the *p* of the prefix *per-*
in *memperbesar* are not substituted, and Pater analyses substitution as the fusion of
the nasal with the root-initial obstruent. It is therefore defined here on the root-initial
segment alone and not as a rule that deletes an obstruent after a nasal. A base that keeps its
initial consonant, as recent loans do, shows assimilation without fusion, and there the nasal
before *s* is the alveolar, as in *mensukseskan* beside *menyukseskan* (Sneddon).

## Main definitions

* `p`, `t`, …, `a`: the phonemes, named by their spelling, with `ny`, `ng`, `sy` and `kh` for
  the digraphs. The spelling writes *e* for both the schwa and /e/, and as in the dictionaries
  `e` is the schwa and `é` is /e/. `consonants` and `vowels` are the sets of them.
* `nasalAssimilation`, `nasalStridency`, `assimilate`: the assimilation of a nasal to the place
  of a following obstruent and the redundancy rule that keeps nasals non-strident, as
  `Subregular.LocalRewrite.Rule`s, and their sequence.
* `substituting`, `fuse`: the root-initial consonants that fuse with the prefix nasal, and the
  nasal that results.
* `juncture`, `junctureRetained`: what the prefix nasal and the base-initial segment surface
  as, with fusion and for a base that keeps its initial consonant.
* `prefixN`, `meN`, `peN`: a prefix in N attached to a base.

## Main results

* `exists_mem_ind`: every phoneme but the palatal glide is the segment of a phoneme of
  PHOIBLE's Standard Indonesian inventory.
* `substituting_subset`, `voicelessObstruents_sdiff_substituting`: the substituting consonants
  are voiceless obstruents, and the voiceless obstruents that do not substitute are *c* and the
  loan fricatives.
* `juncture_of_mem_substituting`, `juncture_of_sonorant`, `juncture_of_vowel_or_h`,
  `juncture_of_obstruent`: the outcome at the juncture for each class of base-initial segment.
* `juncture_head_agrees`: before every obstruent but *s* the juncture begins with a nasal that
  agrees with the obstruent in every place feature but [strident].
* `assimilate_eq_fuse_cons`: but for *s*, the fused nasal is the assimilated one, which is
  Donohue's decomposition of substitution into assimilation and the loss of the obstruent.
* `nasalAssimilation_s`: the place class alone makes the nasal before *s* strident, and the
  redundancy rule restores *n*.

## Implementation notes

Hayes's notation for place assimilation copies every place feature, and he places [strident]
under the coronal articulator, where other textbooks make it a manner feature (see
`Phonology/Segmental/FeatureClass.lean`). The chart specifies [strident] on coronals alone, so
a velar nasal that becomes coronal must get a value for it from somewhere, and copying gives
[+strident] before *s*, *z*, *c*, *j* and *sy*. `nasalStridency` is the redundancy rule that a
nasal is [−strident]. The fusing stops are not strident, so `fuse` needs no such repair.
Before *c*, *j* and *sy* the assimilated nasal is the postalveolar [n̠] of the chart, and before
*f* it is the labiodental [ɱ]. Both are allophones, written *n* and *m*, and the descriptions
differ on whether the first is the palatal phoneme.

The inventory is PHOIBLE 1690, the standard language. It lists the palatal glide under the
glyph of a front rounded vowel, so `y` is outside it, and its /v/, /x/, /ʔ/ and /ɛ/ are left
out here except /x/, the *kh* of loans.

## TODO

A base of one syllable takes *menge-*, as in *mengebom* from *bom* (Sneddon), which needs a
syllable count on the base. The prefixes *ber-*, *per-* and *ter-* lose their *r* before a base
in *r* and before some first syllables in *er*.

## References

* [J. N. Sneddon, *Indonesian: A Comprehensive Grammar* (1996)][sneddon-1996]
* [B. McDonnell, J. Wu, T. McKinnon and A. Adelaar, *Malayic languages*
  (2024)][mcdonnell-wu-mckinnon-adelaar-2024]
* [M. Donohue, *Phonotactics and morphophonology* (2024)][donohue-2024]
* [J. Pater, *Austronesian nasal substitution revisited: what's wrong with \*NC (and what's
  not)* (2001)][pater-2001]
* [B. P. Hayes, *Introductory Phonology* (2009)][hayes-2009]
* [S. Moran and D. McCloy, *PHOIBLE 2.0*][moran-mccloy-2019]
-/

open Phonology Subregular.LocalRewrite Data.PHOIBLE

namespace Indonesian.Phonology

/-! ### Segments -/

/-- The voiceless bilabial stop `p`. -/
def p : Segment := .ofChart .«p»

/-- The voiced bilabial stop `b`. -/
def b : Segment := .ofChart .«b»

/-- The voiceless alveolar stop `t`. -/
def t : Segment := .ofChart .«t»

/-- The voiced alveolar stop `d`. -/
def d : Segment := .ofChart .«d»

/-- The voiceless postalveolar affricate `c`, /tʃ/. -/
def c : Segment := .ofChart .«t̠ʃ»

/-- The voiced postalveolar affricate `j`, /dʒ/. -/
def j : Segment := .ofChart .«d̠ʒ»

/-- The voiceless velar stop `k`. -/
def k : Segment := .ofChart .«k»

/-- The voiced velar stop `g`. -/
def g : Segment := .ofChart .«ɡ»

/-- The voiceless labiodental fricative `f`, in loans. -/
def f : Segment := .ofChart .«f»

/-- The voiceless alveolar fricative `s`. -/
def s : Segment := .ofChart .«s»

/-- The voiced alveolar fricative `z`, in loans. -/
def z : Segment := .ofChart .«z»

/-- The voiceless postalveolar fricative `sy`, /ʃ/, in loans. -/
def sy : Segment := .ofChart .«ʃ»

/-- The voiceless velar fricative `kh`, /x/, in loans. -/
def kh : Segment := .ofChart .«x»

/-- The glottal fricative `h`. -/
def h : Segment := .ofChart .«h»

/-- The bilabial nasal `m`. -/
def m : Segment := .ofChart .«m»

/-- The alveolar nasal `n`. -/
def n : Segment := .ofChart .«n»

/-- The palatal nasal `ny`, /ɲ/. -/
def ny : Segment := .ofChart .«ɲ»

/-- The velar nasal `ng`, /ŋ/. -/
def ng : Segment := .ofChart .«ŋ»

/-- The lateral `l`. -/
def l : Segment := .ofChart .«l»

/-- The trill `r`. -/
def r : Segment := .ofChart .«r»

/-- The labial-velar glide `w`. -/
def w : Segment := .ofChart .«w»

/-- The palatal glide `y`, /j/. -/
def y : Segment := .ofChart .«j»

/-- The high front vowel `i`. -/
def i : Segment := .ofChart .«i»

/-- The high back vowel `u`. -/
def u : Segment := .ofChart .«u»

/-- The mid front vowel `é`, /e/, spelled *e*. -/
def é : Segment := .ofChart .«e»

/-- The schwa `e`, /ə/. -/
def e : Segment := .ofChart .«ə»

/-- The mid back vowel `o`. -/
def o : Segment := .ofChart .«o»

/-- The low vowel `a`. -/
def a : Segment := .ofChart .«a»

/-- The consonants, pairwise distinct. -/
def consonants : Finset Segment :=
  ⟨↑[p, b, t, d, c, j, k, g, f, s, z, sy, kh, h, m, n, ny, ng, l, r, w, y], by decide⟩

/-- The vowels, pairwise distinct. -/
def vowels : Finset Segment := ⟨↑[i, u, é, e, o, a], by decide⟩

/-- Every phoneme but the palatal glide is the segment of a phoneme of PHOIBLE's Standard
Indonesian inventory. -/
theorem exists_mem_ind :
    ∀ x ∈ consonants ∪ vowels, x ≠ y →
      ∃ ph ∈ Inventories.Indonesian.ind.phonemes, x = .ofChart ph.features := by
  decide

/-! ### Natural classes -/

/-- The obstruents, [+consonantal, −sonorant]. The glottal `h` is [−consonantal]. -/
def obstruent : Segment := Segment.ofSpecs [(.consonantal, true), (.sonorant, false)]

/-- The voiceless obstruents. -/
def voicelessObstruent : Segment :=
  Segment.ofSpecs [(.consonantal, true), (.sonorant, false), (.voice, false)]

/-- The sonorant consonants, [+sonorant, −syllabic], which are the nasals, liquids and
glides. -/
def sonorantConsonant : Segment := Segment.ofSpecs [(.sonorant, true), (.syllabic, false)]

/-- The nasals. -/
def nasal : Segment := Segment.ofSpecs [(.nasal, true)]

/-! ### Nasal assimilation -/

/-- A nasal takes the place of a following obstruent, in any position of the word. -/
def nasalAssimilation : Rule where
  name := "nasal place assimilation"
  target := nasal
  effect := .copyRight FeatureClass.place
  rightContext := [.seg obstruent]

/-- A nasal is not strident. The place class includes [strident], which assimilation to a
sibilant therefore copies, and this redundancy rule removes. -/
def nasalStridency : Rule where
  name := "nasal stridency"
  target := Segment.ofSpecs [(.nasal, true), (.strident, true)]
  effect := .changeFeatures (Segment.ofSpecs [(.strident, false)])

/-- `assimilate w` is the word `w` with each nasal assimilated to a following obstruent. -/
def assimilate : List Segment → List Segment := derive [nasalAssimilation, nasalStridency]

/-! ### Nasal substitution -/

/-- The root-initial consonants that fuse with the prefix nasal. -/
def substituting : Finset Segment := {p, t, k, s}

/-- The nasal in which the prefix nasal and a root-initial `x` fuse, which has the place of `x`,
except that with `s` it is the palatal `ny`. -/
def fuse (x : Segment) : Segment := if x = s then ny else FeatureClass.place.piecewise x ng

/-- What the prefix nasal and the base-initial segment `x` surface as. A substituting
consonant fuses with the nasal, the nasal is lost before a sonorant consonant, and otherwise it
assimilates. -/
def juncture (x : Segment) : List Segment :=
  if x ∈ substituting then [fuse x]
  else if sonorantConsonant ≤ x then [x]
  else assimilate [ng, x]

/-- The juncture with a base that keeps its initial consonant, where there is no fusion. -/
def junctureRetained (x : Segment) : List Segment :=
  if sonorantConsonant ≤ x then [x] else assimilate [ng, x]

/-- `prefixN pre base` attaches to `base` the prefix that consists of `pre` and the nasal. -/
def prefixN (pre : List Segment) : List Segment → List Segment
  | [] => pre ++ [ng]
  | x :: rest => pre ++ juncture x ++ rest

/-- The verbal prefix *meN-*. -/
def meN : List Segment → List Segment := prefixN [m, e]

/-- The nominal prefix *peN-*. -/
def peN : List Segment → List Segment := prefixN [p, e]

/-! ### The juncture by class -/

/-- The substituting consonants are voiceless obstruents. -/
theorem substituting_subset :
    substituting ⊆ consonants.filter (voicelessObstruent ≤ ·) := by
  decide

/-- The voiceless obstruents that do not substitute are `c` and the fricatives of loans. -/
theorem voicelessObstruents_sdiff_substituting :
    consonants.filter (voicelessObstruent ≤ ·) \ substituting = {c, f, sy, kh} := by
  decide

/-- A substituting consonant is replaced by one nasal. -/
theorem juncture_of_mem_substituting {x : Segment} (hx : x ∈ substituting) :
    juncture x = [fuse x] := by
  simp only [juncture, hx, ↓reduceIte]

/-- The nasal is lost before a nasal, a liquid or a glide. -/
theorem juncture_of_sonorant : ∀ x ∈ consonants, sonorantConsonant ≤ x → juncture x = [x] := by
  decide

/-- The nasal is velar before a vowel and before `h`. -/
theorem juncture_of_vowel_or_h : ∀ x ∈ insert h vowels, juncture x = [ng, x] := by
  decide

/-- Before an obstruent that does not substitute, the nasal and the obstruent both surface. -/
theorem juncture_of_obstruent :
    ∀ x ∈ consonants, obstruent ≤ x → x ∉ substituting → juncture x = assimilate [ng, x] := by
  decide

/-- Before every obstruent but `s` the nasal at the juncture is a nasal that agrees with the
obstruent in every place feature but [strident]. -/
theorem juncture_head_agrees :
    ∀ x ∈ consonants, obstruent ≤ x → x ≠ s →
      ∀ N ∈ (juncture x).head?, nasal ≤ N ∧ ∀ ft ∈ FeatureClass.place.erase .strident,
        N ft = x ft := by
  decide

/-- But for `s`, the fused nasal is the one that assimilation gives, so substitution is
assimilation together with the loss of the obstruent. -/
theorem assimilate_eq_fuse_cons :
    ∀ x ∈ substituting, x ≠ s → assimilate [ng, x] = [fuse x, x] := by
  decide

/-- The fused nasals are phonemes, the nasal of the place of each stop and the palatal for
`s`. -/
theorem fuse_eq : fuse p = m ∧ fuse t = n ∧ fuse k = ng ∧ fuse s = ny := by
  decide

/-- Where `s` is kept the nasal before it is alveolar, as in *mensukseskan*. -/
theorem junctureRetained_s : junctureRetained s = [n, s] := by
  decide

/-- The place class alone makes the nasal before `s` strident, and the redundancy rule
restores `n`. -/
theorem nasalAssimilation_s :
    nasalAssimilation.apply [ng, s] = [n.setFeature .strident true, s] ∧
      assimilate [ng, s] = [n, s] := by
  decide

/-! ### Examples -/

/-- *mengajar* 'teach' from *ajar*, with the velar nasal before a vowel. -/
theorem mengajar : meN [a, j, a, r] = [m, e, ng, a, j, a, r] := by decide

/-- *memakai* 'use' from *pakai*, with substitution of `p`. -/
theorem memakai : meN [p, a, k, a, i] = [m, e, m, a, k, a, i] := by decide

/-- *membeli* 'buy' from *beli*, with assimilation alone before a voiced stop. -/
theorem membeli : meN [b, e, l, i] = [m, e, m, b, e, l, i] := by decide

/-- *menyewa* 'rent' from *sewa*, with the palatal nasal for `s`. -/
theorem menyewa : meN [s, é, w, a] = [m, e, ny, é, w, a] := by decide

/-- *melihat* 'see' from *lihat*, with loss of the nasal before a liquid. -/
theorem melihat : meN [l, i, h, a, t] = [m, e, l, i, h, a, t] := by decide

/-- *penulis* 'writer' from *tulis*, with the same alternation under *peN-*. -/
theorem penulis : peN [t, u, l, i, s] = [p, e, n, u, l, i, s] := by decide

/-- *meN-* on *tampar* 'slap'. Substitution takes the root-initial `t` and leaves the
cluster inside the root, which assimilation does not change either. -/
theorem menampar :
    meN [t, a, m, p, a, r] = [m, e, n, a, m, p, a, r] ∧
      assimilate [t, a, m, p, a, r] = [t, a, m, p, a, r] := by
  decide

/-- *memperbesar* 'enlarge' from *besar* with the prefix *per-*. Between the two prefixes the
nasal assimilates and the `p` of *per-* is kept. -/
theorem memperbesar :
    assimilate ([m, e, ng] ++ [p, e, r] ++ [b, e, s, a, r])
      = [m, e, m, p, e, r, b, e, s, a, r] := by
  decide

end Indonesian.Phonology
