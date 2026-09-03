import Linglib.Fragments.Turkish.Morphotactics

/-!
# Göksel and Kerslake (2005): Turkish suffixation

The reference grammar's account of the form and order of Turkish suffixes, checked
against the Turkish Fragment. Chapter 3's vowel harmony is derived by the alternations
of `Turkish.Phonology` from the exponent forms of `Turkish.Morphotactics`: the
permissible vowel sequences of §3.1 are the A-type and I-type resolutions, the last vowel
of a disharmonic loan decides (*otobüs-ler*), an invariant suffix vowel is skipped and
re-triggers (*görüyorum*, §3.4), and the palatal l of *gol* fronts its suffix (§3.4).
Chapter 8's suffix order is licensing by the finite-verb and nominal position-class
systems: the grammar's example words are licensed with their stacked voice suffixes,
reversed orders are not, and its rule that markers of one position cannot co-occur
(§8.2.3) is the position's not being iterable.

## Main results

* `followers_table`: the §3.1 table of permissible vowel sequences.
* `retriggering`, `palatal_l`: the §3.4 exceptions to harmony, derived rather than listed.
* `finite_verb`: §8.2 (7), every slot of the finite verb.
* `same_position_excluded`: §8.2.3 (i) from `PositionClassSystem.not_licensesIn_pair`.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
-/

namespace GokselKerslake2005

open Turkish Phonology

/-! ### Vowel harmony (Chapter 3) -/

/-- The vowels that may follow `v` in a suffix: its A-type and I-type resolutions. -/
def followers (v : Segment) : List Segment :=
  [A, I].map fun x => (surface [v, x]).getLastD x

/-- §3.1: the permissible vowel sequences, as the grammar tabulates them. -/
theorem followers_table :
    followers a = [a, ı] ∧ followers ı = [a, ı] ∧ followers o = [a, u] ∧ followers u = [a, u] ∧
    followers e = [e, i] ∧ followers i = [e, i] ∧ followers ö = [e, ü] ∧ followers ü = [e, ü] := by
  decide

/-- §3.2.1: the second-person possessive -(I)n on *kız*, *el*, *kol* and *göz*. -/
theorem iType :
    surface ([k, ı, z] ++ (Nominal.Exponent.possessive (.pn .second .Sing)).form) =
        [k, ı, z, ı, n] ∧
    surface ([e, l] ++ (Nominal.Exponent.possessive (.pn .second .Sing)).form) =
        [e, l, i, n] ∧
    surface ([k, o, l] ++ (Nominal.Exponent.possessive (.pn .second .Sing)).form) =
        [k, o, l, u, n] ∧
    surface ([g, ö, z] ++ (Nominal.Exponent.possessive (.pn .second .Sing)).form) =
        [g, ö, z, ü, n] := by
  decide

/-- Chapter 3: the last vowel of a stem decides, so the disharmonic loan *otobüs* takes
*-ler*. -/
theorem last_vowel_decides :
    surface ([o, t, o, b, ü, s] ++ Nominal.Exponent.plural.form) =
      [o, t, o, b, ü, s, l, e, r] := by
  decide

/-- §3.2: *üz-ül-dü-nüz* 'you became sad' — rounding copied through three suffixes, and
the `D` of -DI voiced after `l`. -/
theorem iterated :
    surface ([ü, z] ++ Verb.Exponent.passive.form ++ Verb.Exponent.di.form ++
        (Verb.Exponent.person .one (.pn .second .Plur)).form) =
      [ü, z, ü, l, d, ü, n, ü, z] := by
  decide

/-- §3.4 (vi): the `o` of -(I)yor does not harmonize and triggers the person marker,
*gör-üyor-um*; the invariable converb -(y)ken, *bak-mış-ken*. -/
theorem retriggering :
    surface ([g, ö, r] ++ Verb.Exponent.iyor.form ++
        (Verb.Exponent.person .two (.pn .first .Sing)).form) = [g, ö, r, ü, y, o, r, u, m] ∧
    surface ([b, a, k] ++ Verb.Exponent.miş.form ++ [k, e, n]) = [b, a, k, m, ı, ş, k, e, n] := by
  decide

/-- §3.4 (iv): the palatal l of *gol* and *hal* fronts the suffix, *gol-ü* and *hal-im*,
while rounding still comes from the vowel. -/
theorem palatal_l :
    surface ([g, o, l'] ++ (Nominal.Exponent.possessive (.pn .third .Sing)).form) =
      [g, o, l', ü] ∧
    surface ([h, a, l'] ++ (Nominal.Exponent.possessive (.pn .first .Sing)).form) =
      [h, a, l', i, m] := by
  decide

/-- §6.1.2: the `D` of -DI is `d` after a voiced segment and `t` after a voiceless one,
*kal-dı* and *düş-tü*. -/
theorem voicing_of_D :
    surface ([k, a, l] ++ Verb.Exponent.di.form) = [k, a, l, d, ı] ∧
    surface ([d, ü, ş] ++ Verb.Exponent.di.form) = [d, ü, ş, t, ü] := by
  decide

/-- §8.2.2: before -(I)yor the negative's vowel is raised and harmonizes as an I-type
suffix, *anla-m-ıyor* and *gör-m-üyor*. -/
theorem negative_raised :
    surface ([a, n, l, a] ++ [m, I] ++ [y, o, r]) = [a, n, l, a, m, ı, y, o, r] ∧
    surface ([g, ö, r] ++ [m, I] ++ [y, o, r]) = [g, ö, r, m, ü, y, o, r] := by
  decide

/-- §8.1 (2) *Ev-ler-imiz-de-ymiş-ler* 'apparently they are at our homes': the nominal
string, the evidential copula with its buffer `y`, and a group-2 person marker. -/
theorem nominal_predicate :
    surface ([e, v] ++ Nominal.Exponent.plural.form ++
        (Nominal.Exponent.possessive (.pn .first .Plur)).form ++ Nominal.Exponent.locative.form ++
        [y] ++ Verb.Exponent.evidentialCopula.form ++
        (Verb.Exponent.person .two (.pn .third .Plur)).form) =
      [e, v, l, e, r, i, m, i, z, d, e, y, m, i, ş, l, e, r] := by
  decide

/-! ### The order of suffixes (Chapter 8) -/

/-- §8.1 (1) *çocuk-lar-ın-a* 'to your children': number - possession - case. -/
theorem nominal :
    Nominal.system.Licenses []
      [⟨_, .plural⟩, ⟨_, .possessive (.pn .second .Sing)⟩, ⟨_, .dative⟩] := by
  decide

/-- §8.2 (7) *Döğ-üş-tür-t-ül-me-yebil-iyor-muş-sunuz-dur*: every slot of the finite verb,
the voice slot filled by four stacked suffixes. -/
theorem finite_verb :
    Verb.system.Licenses []
      [⟨_, .reciprocal⟩, ⟨_, .causative⟩, ⟨_, .causative⟩, ⟨_, .passive⟩, ⟨_, .negative⟩,
        ⟨_, .abil⟩, ⟨_, .iyor⟩, ⟨_, .evidentialCopula⟩, ⟨_, .person .two (.pn .second .Plur)⟩,
        ⟨_, .dir⟩] := by
  decide

/-- §8.2.3 (11) *Bitir-e-me-miş-tir*, (12) *Oku-yabil-ecek-miş* and §8.2.3.3 *git-ti-ydi-n*:
positions 1-3-5, 2-3-4 and 3-4 with a group-1 person marker. -/
theorem tam_positions :
    Verb.system.Licenses [] [⟨_, .possibility⟩, ⟨_, .negative⟩, ⟨_, .miş⟩, ⟨_, .dir⟩] ∧
    Verb.system.Licenses [] [⟨_, .abil⟩, ⟨_, .acak⟩, ⟨_, .evidentialCopula⟩] ∧
    Verb.system.Licenses []
      [⟨_, .di⟩, ⟨_, .pastCopula⟩, ⟨_, .person .one (.pn .second .Sing)⟩] := by
  decide

/-- The negative follows voice and precedes the tense/aspect/modality marker (§8.2.2), and
the copular markers follow it (§8.2.3): the reversed orders are unlicensed. -/
theorem reversed_orders :
    ¬ Verb.system.Licenses [] [⟨_, .negative⟩, ⟨_, .causative⟩] ∧
    ¬ Verb.system.Licenses [] [⟨_, .di⟩, ⟨_, .negative⟩] ∧
    ¬ Verb.system.Licenses [] [⟨_, .pastCopula⟩, ⟨_, .di⟩] := by
  decide

/-- §8.2.3 (i): markers of one position cannot co-occur — position 3 is not iterable. -/
theorem same_position_excluded (m₁ m₂ : Verb.Exponent .tam) :
    ¬ Verb.system.Licenses [] [⟨_, m₁⟩, ⟨_, m₂⟩] :=
  fun h => Verb.system.not_licensesIn_pair (by decide : Verb.Slot.tam ≠ .voice) _ m₁ m₂ h.2

end GokselKerslake2005
