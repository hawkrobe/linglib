import Linglib.Core.Lexical.UD
import Linglib.Core.PrivativePair

/-!
# Surface Gender
@cite{corbett-1991} @cite{kramer-2020}

Descriptive (atheoretical) classification of surface gender values attested
cross-linguistically. This type records the *observable* gender of a noun —
what agreement class it triggers — without committing to the mechanism of
gender assignment.

The distinction between **sex-based** systems (masculine/feminine/neuter) and
**animacy-based** systems (animate/inanimate) follows @cite{corbett-1991}'s
WALS Chapter 31. @cite{kramer-2020} argues that these surface categories
arise from a single underlying mechanism (phi-features on the nominalizing
head *n*), parameterized by feature dimension; that analysis lives in
`Morphology.DM.Categorizer`.

For languages with many noun classes (Bantu, Mixtec), the fragment retains
its own fine-grained `Gender` type and provides a bridge to `SurfaceGender`
via a `.primary` function.
-/

namespace Core

/-- Surface gender categories attested cross-linguistically.

    These are the descriptive labels a grammar assigns to nouns based on
    agreement patterns. For the structural analysis, see
    `Morphology.DM.GenderFeature`. -/
inductive SurfaceGender where
  /-- Masculine: male humans/higher animates; default in many sex-based systems. -/
  | masculine
  /-- Feminine: female humans/higher animates; marked in many sex-based systems. -/
  | feminine
  /-- Neuter: neither masculine nor feminine; inanimate default in 3-gender systems. -/
  | neuter
  /-- Common: merged masculine + feminine (Swedish, Danish). -/
  | common
  /-- Animate: animate referents in animacy-based systems (Teop, Algonquian). -/
  | animate
  /-- Inanimate: inanimate referents in animacy-based systems. -/
  | inanimate
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Map surface gender to Universal Dependencies gender where a natural
    correspondence exists. Animacy-based genders have no standard UD
    equivalent. -/
def SurfaceGender.toUDGender : SurfaceGender → Option UD.Gender
  | .masculine => some .Masc
  | .feminine  => some .Fem
  | .neuter    => some .Neut
  | .common    => some .Com
  | .animate   => none
  | .inanimate => none

/-- Inverse: map UD gender to surface gender. Total (every UD gender has
    a surface gender equivalent). -/
def SurfaceGender.ofUDGender : UD.Gender → SurfaceGender
  | .Masc => .masculine
  | .Fem  => .feminine
  | .Neut => .neuter
  | .Com  => .common

/-- Round-trip: UD → Surface → UD is the identity. -/
theorem SurfaceGender.roundtrip_ud (g : UD.Gender) :
    (SurfaceGender.ofUDGender g).toUDGender = some g := by
  cases g <;> rfl

-- ============================================================================
-- § 2: Gender Features
-- ============================================================================

/-! ### Gender Features (@cite{sauerland-2003})

Binary feature decomposition of sex-based gender:
- **[±feminine]**: whether the referent triggers feminine agreement.
  Feminine and neuter are [+feminine]; masculine is [−feminine].
- **[±neuter]**: whether the referent triggers neuter agreement.
  Only neuter is [+neuter]; feminine and masculine are [−neuter].

These features form a containment hierarchy: [+neuter] → [+feminine].
This is a feature-geometric claim from @cite{sauerland-2003} §6,
not a natural-kind claim: neuter is the *most specified* gender
(like singular for number, 1st for person), and masculine is the
*least specified* (like plural, 3rd).

The three well-formed combinations yield the three gender values:
- **neuter**: [+feminine, +neuter] — maximal (presupposes inanimate)
- **feminine**: [+feminine, −neuter] — intermediate (presupposes female)
- **masculine**: [−feminine, −neuter] — minimal (vacuous/default)

This parallels person [±author] ⊂ [±participant] and number
[±atomic] ⊂ [±minimal]. All three are instances of `PhiFeatures`.

For the morphosyntactic (DM) analysis, see
`Morphology.DM.Categorizer.GenderFeature`. -/

namespace Gender

/-- Binary gender features: [±feminine, ±neuter].

    These two features suffice for the three-way gender distinction:
    - neuter:    [+feminine, +neuter]
    - feminine:  [+feminine, −neuter]
    - masculine: [−feminine, −neuter]

    The fourth combination [−feminine, +neuter] is ill-formed:
    a neuter entity necessarily triggers feminine agreement
    ([+neuter] → [+feminine] in the feature geometry). -/
structure Features where
  /-- [+feminine]: referent triggers feminine (or neuter) agreement. -/
  isFeminine : Bool
  /-- [+neuter]: referent triggers neuter agreement. -/
  isNeuter : Bool
  deriving DecidableEq, Repr

/-- Well-formedness: [+neuter] → [+feminine].
    Neuter entails feminine in the feature geometry. -/
def Features.wellFormed (gf : Features) : Bool :=
  !gf.isNeuter || gf.isFeminine

/-- Neuter features: [+feminine, +neuter]. -/
def neuterF : Features := ⟨true, true⟩

/-- Feminine features: [+feminine, −neuter]. -/
def feminineF : Features := ⟨true, false⟩

/-- Masculine features: [−feminine, −neuter]. -/
def masculineF : Features := ⟨false, false⟩

/-- Gender features are a `PhiFeatures` instance:
    outer = isFeminine, inner = isNeuter.

    The containment [+neuter] → [+feminine] maps to PrivativePair's
    [+inner] → [+outer], unifying the structure with person and number.
    All shared properties are inherited by construction. -/
instance : Core.PhiFeatures Features where
  toPair f := ⟨f.isFeminine, f.isNeuter⟩
  ofPair p := ⟨p.outer, p.inner⟩
  roundtrip := fun ⟨_, _⟩ => rfl

/-- The three canonical gender values map to the three PrivativePair cells. -/
@[simp] theorem neuter_is_maximal : PhiFeatures.toPair neuterF = .maximal := rfl
@[simp] theorem feminine_is_intermediate : PhiFeatures.toPair feminineF = .intermediate := rfl
@[simp] theorem masculine_is_minimal : PhiFeatures.toPair masculineF = .minimal := rfl

/-- No 4-way gender distinction (inherited from `PhiFeatures`). -/
theorem no_fourth_gender :
    ∀ (a b c d : Features),
      a.wellFormed = true → b.wellFormed = true →
      c.wellFormed = true → d.wellFormed = true →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False :=
  fun a b c d ha hb hc hd =>
    Core.PhiFeatures.no_four_way a b c d ha hb hc hd

@[simp] theorem neuter_wellFormed : neuterF.wellFormed = true := rfl
@[simp] theorem feminine_wellFormed : feminineF.wellFormed = true := rfl
@[simp] theorem masculine_wellFormed : masculineF.wellFormed = true := rfl

/-- The ill-formed combination [−feminine, +neuter] is the only
    combination that violates well-formedness. -/
theorem illFormed_only : (⟨false, true⟩ : Features).wellFormed = false := rfl

/-- There are exactly 3 well-formed feature combinations (= 3 genders). -/
theorem exactly_three_wellFormed :
    ([⟨true, true⟩, ⟨true, false⟩, ⟨false, true⟩, ⟨false, false⟩].filter
      Features.wellFormed).length = 3 := by decide

/-- Containment: [+neuter] → [+feminine] for all well-formed features. -/
theorem neuter_implies_feminine (f : Features) (hw : f.wellFormed = true) :
    f.isNeuter = true → f.isFeminine = true := by
  intro hn
  simp [Features.wellFormed] at hw
  simp [hn] at hw
  exact hw

-- ── Bridge to SurfaceGender ──

/-- Map gender features to the descriptive `SurfaceGender` type. -/
def Features.toSurfaceGender : Features → Option SurfaceGender
  | ⟨true, true⟩   => some .neuter
  | ⟨true, false⟩  => some .feminine
  | ⟨false, false⟩ => some .masculine
  | ⟨false, true⟩  => none  -- ill-formed

/-- Map `SurfaceGender` to gender features (partial — only sex-based
    genders have feature equivalents). -/
def Features.fromSurfaceGender : SurfaceGender → Option Features
  | .neuter    => some neuterF
  | .feminine  => some feminineF
  | .masculine => some masculineF
  | _          => none

/-- Round-trip: fromSurfaceGender ∘ toSurfaceGender = some for
    all well-formed features. -/
theorem roundtrip_fromSG_toSG :
    [neuterF, feminineF, masculineF].all
      (λ f => f.toSurfaceGender.bind Features.fromSurfaceGender == some f) = true := by
  decide

end Gender

-- ============================================================================
-- § 3: Discourse-Level Gender Knowledge
-- ============================================================================

/-- Gender knowledge state for a discourse referent.

    Distinct from `SurfaceGender`, which describes the morphosyntactic
    agreement class a noun triggers. `GenderInfo` describes what the
    discourse participants know or assume about a referent's gender.

    Motivated by @cite{arnold-2026}'s observation that singular *they*
    is licensed by two inversely correlated pragmatic conditions:
    one requiring an underspecified discourse representation (where gender
    is unknown or irrelevant), the other requiring knowledge that the
    referent's personal pronouns are *they/them* (where gender information
    is highly specific).

    See also @cite{newman-1992} ("nonsolid" antecedents),
    @cite{newman-1998} (low individuation), and
    @cite{camilliere-etal-2021} (social distance as a proxy for
    discourse specificity). -/
inductive GenderInfo where
  /-- Gender is known to discourse participants and matches a
      morphosyntactic agreement class.
      Example: "my sister" → `.known .feminine` -/
  | known : SurfaceGender → GenderInfo
  /-- Gender is unknown, irrelevant, or not elaborated in the discourse.
      Example: "every student", "someone", "the clerk" (in passing). -/
  | unspecified : GenderInfo
  deriving DecidableEq, Repr, BEq

/-- Lift a surface gender to discourse-level knowledge. -/
def SurfaceGender.toGenderInfo (g : SurfaceGender) : GenderInfo := .known g

/-- Extract the surface gender, if known. -/
def GenderInfo.toSurfaceGender : GenderInfo → Option SurfaceGender
  | .known g => some g
  | .unspecified => none

/-- Round-trip: known surface gender survives the coarsening. -/
theorem GenderInfo.roundtrip_known (g : SurfaceGender) :
    (SurfaceGender.toGenderInfo g).toSurfaceGender = some g := rfl

end Core
