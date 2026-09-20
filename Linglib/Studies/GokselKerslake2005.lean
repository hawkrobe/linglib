import Linglib.Fragments.Turkish.Predicates

/-!
# Göksel and Kerslake (2005): Turkish suffixation

This file checks the account of the form and order of Turkish suffixes in the reference
grammar of Göksel and Kerslake against the Turkish Fragment.

The vowel harmony of Chapter 3 is derived by the surface forms of `Turkish.Phonology` from the
exponent forms of `Turkish.Morphotactics`. The permissible vowel sequences of §3.1 are the
surface forms of the two suffix vowels. The last vowel of a disharmonic loan decides
(*otobüs-ler*), an invariant suffix vowel is skipped and triggers what follows (*görüyorum*,
§3.4), the palatal l of *gol* fronts its suffix (§3.4), and a stem-final vowel before -(I)yor
leaves one high vowel (§8.2.3.3), the vowel of the negative among them.

The suffix order of Chapter 8 is licensing by the position-class systems of the finite verb
and the nominal. The grammar's example words are licensed with their stacked voice suffixes,
reversed orders are not, and the rule that markers of one position cannot co-occur (§8.2.3)
holds because the position is not iterable.

## Main results

* `followers_table`: the §3.1 table of permissible vowel sequences.
* `retriggering`, `palatal_l`: the §3.4 exceptions to harmony, derived rather than listed.
* `imperfective_of_vowel_stems`, `negative_raised`: the vowel-final stems of §8.2.3.3 and the
  negative of §8.2.2 before -(I)yor.
* `causative_stems`, `spelled_stems`: the -DIr causatives of §8.2.1.1 and the Fragment's verbs.
* `finite_verb`: §8.2 (7), every slot of the finite verb.
* `same_position_excluded`: §8.2.3 (i) from `PositionClassSystem.not_licensesIn_pair`.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
-/

namespace GokselKerslake2005

open Turkish Phonology

/-! ### Vowel harmony (Chapter 3) -/

/-- `followers v` lists the vowels that may follow `v` in a suffix, the surface forms of `A`
and of `I` after it. -/
def followers (v : Segment) : List Segment :=
  [A, I].map fun x ↦ (surface [v, x]).getLastD x

/-- The permissible vowel sequences are those the grammar tabulates (§3.1). -/
theorem followers_table :
    followers a = [a, ı] ∧ followers ı = [a, ı] ∧ followers o = [a, u] ∧ followers u = [a, u] ∧
    followers e = [e, i] ∧ followers i = [e, i] ∧ followers ö = [e, ü] ∧ followers ü = [e, ü] := by
  decide

/-- The second-person possessive -(I)n on *kız*, *el*, *kol* and *göz* surfaces with each of the
four high vowels (§3.2.1). -/
theorem iType :
    surface ([k, ı, z] ++ (Nominal.Exponent.possessive (.pn .second .singular)).form) =
        [k, ı, z, ı, n] ∧
    surface ([e, l] ++ (Nominal.Exponent.possessive (.pn .second .singular)).form) =
        [e, l, i, n] ∧
    surface ([k, o, l] ++ (Nominal.Exponent.possessive (.pn .second .singular)).form) =
        [k, o, l, u, n] ∧
    surface ([g, ö, z] ++ (Nominal.Exponent.possessive (.pn .second .singular)).form) =
        [g, ö, z, ü, n] := by
  decide

/-- The last vowel of a stem decides, so the disharmonic loan *otobüs* takes *-ler*
(Chapter 3). -/
theorem last_vowel_decides :
    surface ([o, t, o, b, ü, s] ++ Nominal.Exponent.plural.form) =
      [o, t, o, b, ü, s, l, e, r] := by
  decide

/-- In *üz-ül-dü-nüz* 'you became sad' rounding is copied through three suffixes, and the `D`
of -DI is voiced after `l` (§3.2). -/
theorem iterated :
    surface ([ü, z] ++ Verb.Exponent.passive.form ++ Verb.Exponent.di.form ++
        (Verb.Exponent.person .one (.pn .second .plural)).form) =
      [ü, z, ü, l, d, ü, n, ü, z] := by
  decide

/-- The `o` of -(I)yor does not harmonize and triggers the person marker in *gör-üyor-um*, and
the converb -(y)ken is invariable in *bak-mış-ken* (§3.4 (vi)). -/
theorem retriggering :
    surface ([g, ö, r] ++ Verb.Exponent.iyor.form ++
        (Verb.Exponent.person .two (.pn .first .singular)).form) = [g, ö, r, ü, y, o, r, u, m] ∧
    surface ([b, a, k] ++ Verb.Exponent.miş.form ++ [k, e, n]) = [b, a, k, m, ı, ş, k, e, n] := by
  decide

/-- The palatal l of *gol* and *hal* fronts the suffix in *gol-ü* and *hal-im*, while rounding
still comes from the vowel (§3.4 (iv)). -/
theorem palatal_l :
    surface ([g, o, l'] ++ (Nominal.Exponent.possessive (.pn .third .singular)).form) =
      [g, o, l', ü] ∧
    surface ([h, a, l'] ++ (Nominal.Exponent.possessive (.pn .first .singular)).form) =
      [h, a, l', i, m] := by
  decide

/-- The `D` of -DI is `d` after a voiced segment and `t` after a voiceless one, as in *kal-dı*
and *düş-tü* (§6.1.2). -/
theorem voicing_of_D :
    surface ([k, a, l] ++ Verb.Exponent.di.form) = [k, a, l, d, ı] ∧
    surface ([d, ü, ş] ++ Verb.Exponent.di.form) = [d, ü, ş, t, ü] := by
  decide

/-- Before -(I)yor a stem-final `a` or `e` becomes high and harmonizes, as in *anlıyor*,
*okşuyor*, *bekliyor* and *özlüyor*, and a stem-final high vowel stands, as in *eriyor* and
*kuruyor* (§8.2.3.3). -/
theorem imperfective_of_vowel_stems :
    surface ([a, n, l, a] ++ Verb.Exponent.iyor.form) = [a, n, l, ı, y, o, r] ∧
    surface ([o, k, ş, a] ++ Verb.Exponent.iyor.form) = [o, k, ş, u, y, o, r] ∧
    surface ([b, e, k, l, e] ++ Verb.Exponent.iyor.form) = [b, e, k, l, i, y, o, r] ∧
    surface ([ö, z, l, e] ++ Verb.Exponent.iyor.form) = [ö, z, l, ü, y, o, r] ∧
    surface ([e, r, i] ++ Verb.Exponent.iyor.form) = [e, r, i, y, o, r] ∧
    surface ([k, u, r, u] ++ Verb.Exponent.iyor.form) = [k, u, r, u, y, o, r] := by
  decide

/-- The vowel of the negative is a stem-final vowel before -(I)yor like any other, as in
*anla-mı-yor*, *gör-mü-yor*, *sakla-mı-yor* and *söyle-mi-yor* (§8.2.2, §8.2.3.3). -/
theorem negative_raised :
    surface ([a, n, l, a] ++ Verb.Exponent.negative.form ++ Verb.Exponent.iyor.form) =
      [a, n, l, a, m, ı, y, o, r] ∧
    surface ([g, ö, r] ++ Verb.Exponent.negative.form ++ Verb.Exponent.iyor.form) =
      [g, ö, r, m, ü, y, o, r] ∧
    surface ([s, a, k, l, a] ++ Verb.Exponent.negative.form ++ Verb.Exponent.iyor.form) =
      [s, a, k, l, a, m, ı, y, o, r] ∧
    surface ([s, ö, y, l, e] ++ Verb.Exponent.negative.form ++ Verb.Exponent.iyor.form) =
      [s, ö, y, l, e, m, i, y, o, r] := by
  decide

/-- *Ev-ler-imiz-de-ymiş-ler* 'apparently they are at our homes' is the nominal string, the
evidential copula with its buffer `y`, and a group-2 person marker (§8.1 (2)). -/
theorem nominal_predicate :
    surface ([e, v] ++ Nominal.Exponent.plural.form ++
        (Nominal.Exponent.possessive (.pn .first .plural)).form ++ Nominal.Exponent.locative.form ++
        [y] ++ Verb.Exponent.evidentialCopula.form ++
        (Verb.Exponent.person .two (.pn .third .plural)).form) =
      [e, v, l, e, r, i, m, i, z, d, e, y, m, i, ş, l, e, r] := by
  decide

/-- The causative -DIr on *yap-*, *koy-*, *öl-* and *dol-* gives the stems *yaptır-*,
*koydur-*, *öldür-* and *doldur-* (§8.2.1.1). -/
theorem causative_stems :
    surface ([y, a, p] ++ Verb.Exponent.causative.form) = [y, a, p, t, ı, r] ∧
    surface ([k, o, y] ++ Verb.Exponent.causative.form) = [k, o, y, d, u, r] ∧
    surface ([ö, l] ++ Verb.Exponent.causative.form) = [ö, l, d, ü, r] ∧
    surface ([d, o, l] ++ Verb.Exponent.causative.form) = [d, o, l, d, u, r] := by
  decide

/-- The spelled stem of every verb of the Fragment writes the surface form of its root and
voice suffixes, the causatives *öldür-* and *yaptır-* among them. -/
theorem spelled_stems : ∀ v ∈ verbs, ofString? v.form = some (v.inflect []) := by
  decide

/-! ### The order of suffixes (Chapter 8) -/

/-- *çocuk-lar-ın-a* 'to your children' has the order number, possession, case (§8.1 (1)). -/
theorem nominal :
    Nominal.system.Licenses []
      [⟨_, .plural⟩, ⟨_, .possessive (.pn .second .singular)⟩, ⟨_, .dative⟩] := by
  decide

/-- *Döğ-üş-tür-t-ül-me-yebil-iyor-muş-sunuz-dur* fills every slot of the finite verb, the
voice slot with four stacked suffixes (§8.2 (7)). -/
theorem finite_verb :
    Verb.system.Licenses []
      [⟨_, .reciprocal⟩, ⟨_, .causative⟩, ⟨_, .causative⟩, ⟨_, .passive⟩, ⟨_, .negative⟩,
        ⟨_, .abil⟩, ⟨_, .iyor⟩, ⟨_, .evidentialCopula⟩, ⟨_, .person .two (.pn .second .plural)⟩,
        ⟨_, .dir⟩] := by
  decide

/-- *Bitir-e-me-miş-tir*, *Oku-yabil-ecek-miş* and *git-ti-ydi-n* fill positions 1-3-5, 2-3-4,
and 3-4 with a group-1 person marker (§8.2.3 (11), (12), §8.2.3.3). -/
theorem tam_positions :
    Verb.system.Licenses [] [⟨_, .possibility⟩, ⟨_, .negative⟩, ⟨_, .miş⟩, ⟨_, .dir⟩] ∧
    Verb.system.Licenses [] [⟨_, .abil⟩, ⟨_, .acak⟩, ⟨_, .evidentialCopula⟩] ∧
    Verb.system.Licenses []
      [⟨_, .di⟩, ⟨_, .pastCopula⟩, ⟨_, .person .one (.pn .second .singular)⟩] := by
  decide

/-- The negative follows voice and precedes the tense/aspect/modality marker (§8.2.2), and
the copular markers follow that marker (§8.2.3), so the reversed orders are unlicensed. -/
theorem reversed_orders :
    ¬ Verb.system.Licenses [] [⟨_, .negative⟩, ⟨_, .causative⟩] ∧
    ¬ Verb.system.Licenses [] [⟨_, .di⟩, ⟨_, .negative⟩] ∧
    ¬ Verb.system.Licenses [] [⟨_, .pastCopula⟩, ⟨_, .di⟩] := by
  decide

/-- Markers of position 3 cannot co-occur, since the position is not iterable (§8.2.3 (i)). -/
theorem same_position_excluded (m₁ m₂ : Verb.Exponent .tam) :
    ¬ Verb.system.Licenses [] [⟨_, m₁⟩, ⟨_, m₂⟩] :=
  fun h ↦ Verb.system.not_licensesIn_pair (by decide : Verb.Slot.tam ≠ .voice) _ m₁ m₂ h.2

end GokselKerslake2005
