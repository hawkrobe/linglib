import Linglib.Features.Person
import Linglib.Features.Gender

/-!
# Hausa TAM and the Person-Aspect-Complex (PAC) — mathlib-style
@cite{newman-2000} @cite{jaggar-2001}

Hausa inflection is concentrated in a portmanteau preverbal element
called the **PAC** (person-aspect-complex), which fuses:

- the subject's **person, number and (in 2sg/3sg) gender**, and
- the **TAM** of the clause (completive, continuous, future,
  subjunctive, habitual, …).

(@cite{newman-2000} ch. 70.) Because the PAC is the only inflectional
locus, the verb stem itself is unmarked for tense or person agreement —
all of that information lives in the PAC.

## The General / Relative split

A second axis cross-cuts the TAM dimension: a **General** (matrix
declarative) vs **Relative** form. The Relative forms surface in three
syntactic environments (@cite{newman-2000} ch. 64–65):

1. relative clauses headed by *dà*;
2. *wh*-questions (in-situ or *ex*-situ); and
3. ex-situ focus constructions licensed by the stabilizer *nē/cē*.

The Relative form is morphologically distinct in only the completive
and continuous TAMs (others are syncretic with the General form). This
yields a four-way diagnostic that we encode here as a TAM × Mode pair.
The Focus fragment (`Hausa/Focus.lean`) consumes this split as the
licensing condition on ex-situ focus.

`PAC.WellFormed` is a propositional predicate (`Prop` with a
`Decidable` instance). It is *not* enforced as a `Subtype` invariant —
ill-formed PACs are constructible by direct field assignment. The
`mkGeneralPAC` and `mkRelativePAC` constructors are ergonomic helpers:
the relative one takes a proof obligation `tam.HasRelativeForm` so that
PACs built via it are well-formed by construction, but a downstream
file is free to construct a deliberately ill-formed PAC and prove it
ill-formed (see `Focus.lean`'s `exSitu_with_genCmp`, which is exactly
that pattern).
-/

namespace Fragments.Hausa.Inflection

open Features.Person
open Features (SurfaceGender)

-- ============================================================================
-- § 1: TAM Inventory (@cite{newman-2000} ch. 70)
-- ============================================================================

/-- The seven core TAM categories of the PAC. We follow Newman's labels;
    the modally-ambiguous "potential" TAM is included for completeness
    but rarely controls the General/Relative split. -/
inductive TAM where
  | completive   -- "perfect / aorist": yā tāfi 'he went'
  | continuous   -- "imperfective": yanā tāfiyā 'he is going'
  | future       -- prospective: zāi tāfi 'he will go'
  | subjunctive  -- volitive: yà tāfi 'let him go'
  | habitual     -- generic / habitual: yakàn tāfi 'he goes (habitually)'
  | rhetorical   -- "rhetorical neg": bā yā tāfi
  | potential    -- modal: yâ tāfi
  deriving DecidableEq, Repr, Inhabited

namespace TAM

/-- The seven TAMs in canonical order. -/
def all : List TAM :=
  [.completive, .continuous, .future, .subjunctive,
   .habitual, .rhetorical, .potential]

/-- The General/Relative split surfaces morphologically only for the
    completive and continuous TAMs (@cite{newman-2000} §64.2, Table 32).
    `HasRelativeForm` is the propositional predicate; downstream
    constructors take it as a proof obligation. -/
def HasRelativeForm : TAM → Prop
  | .completive => True
  | .continuous => True
  | _           => False

instance (t : TAM) : Decidable t.HasRelativeForm := by
  cases t <;> unfold HasRelativeForm <;> infer_instance

end TAM

/-- General vs Relative form. Most TAMs are syncretic between the two;
    completive and continuous are the empirically diagnostic cases. -/
inductive Mode where
  | general
  | relative
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- § 2: Subject Slot (Person × Number × Gender)
-- ============================================================================

/-- The subject slot of the PAC. Hausa makes a 2sg / 3sg gender
    distinction (M vs F), absent in the plural and 1st person.
    We use `Features.Person.Category` for the singular/group cut and add
    a `gender` field that is empty (`none`) outside the 2sg/3sg cells. -/
structure Subject where
  person : Category
  gender : Option SurfaceGender
  deriving DecidableEq, Repr

namespace Subject

/-- A subject **has a gender contrast** iff its gender field is non-empty.
    Propositional predicate (with `Decidable`), not Bool. -/
def HasGenderContrast (s : Subject) : Prop := s.gender ≠ none

instance (s : Subject) : Decidable s.HasGenderContrast :=
  inferInstanceAs (Decidable (_ ≠ _))

end Subject

/-- The subject inventory of Hausa. We restrict to the cells that
    actually appear in the PAC paradigm (`Person.Category` includes
    inclusive/exclusive distinctions that Hausa lacks). -/
def hausaSubjects : List Subject :=
  [ ⟨.s1, none⟩,                     -- 1sg (no gender)
    ⟨.s2, some .masculine⟩,          -- 2sg.M
    ⟨.s2, some .feminine⟩,           -- 2sg.F
    ⟨.s3, some .masculine⟩,          -- 3sg.M
    ⟨.s3, some .feminine⟩,           -- 3sg.F
    ⟨.excl, none⟩,                   -- 1pl  (Hausa has no incl/excl split)
    ⟨.secondGrp, none⟩,              -- 2pl
    ⟨.thirdGrp, none⟩ ]              -- 3pl

/-- **Gender contrast is restricted to the singular.** A Hausa subject
    has a gender contrast only in 2sg or 3sg cells. -/
theorem gender_contrast_only_in_singular :
    ∀ s ∈ hausaSubjects, s.HasGenderContrast →
      s.person = .s2 ∨ s.person = .s3 := by
  decide

-- ============================================================================
-- § 3: PAC Forms — smart constructors
-- ============================================================================

/-- A PAC: subject × TAM × mode → surface form. The `WellFormed`
    invariant (relative mode requires a TAM that admits the relative
    form) is enforced at construction time by `mkRelativePAC`; PACs
    built via `mkGeneralPAC` are well-formed unconditionally.
    The full paradigm is in @cite{newman-2000} §70 Table 38. -/
structure PAC where
  subj : Subject
  tam  : TAM
  mode : Mode
  /-- Surface form (graphic, with marked tones). -/
  form : String
  deriving Repr

/-- A PAC is **well-formed** iff the relative mode is licensed by the
    TAM. Propositional predicate (with `Decidable`). -/
def PAC.WellFormed (p : PAC) : Prop :=
  p.mode = .relative → p.tam.HasRelativeForm

instance (p : PAC) : Decidable p.WellFormed :=
  inferInstanceAs (Decidable (_ → _))

/-- Smart constructor for a General-mode PAC. Always well-formed. -/
def mkGeneralPAC (subj : Subject) (tam : TAM) (form : String) : PAC :=
  ⟨subj, tam, .general, form⟩

/-- Smart constructor for a Relative-mode PAC. Takes a proof that the
    TAM admits a relative form; well-formedness then follows
    immediately (see `mkRelativePAC_wellFormed`). -/
def mkRelativePAC (subj : Subject) (tam : TAM) (form : String)
    (_ : tam.HasRelativeForm) : PAC :=
  ⟨subj, tam, .relative, form⟩

/-- A PAC built by `mkRelativePAC` is well-formed: the proof obligation
    threaded through the smart constructor *is* the witness. -/
theorem mkRelativePAC_wellFormed (s : Subject) (t : TAM) (f : String)
    (h : t.HasRelativeForm) :
    (mkRelativePAC s t f h).WellFormed := fun _ => h

-- ============================================================================
-- § 4: Representative PACs (@cite{newman-2000} §70.2, §64 Table 32)
-- ============================================================================

/-- 3sg.M completive, General form *yā* (high tone). -/
def cmp_3sm_G : PAC :=
  mkGeneralPAC ⟨.s3, some .masculine⟩ .completive "yā"

/-- 3sg.M completive, Relative form *yà* (low tone). The G/R contrast
    here is purely tonal — a textbook minimal pair. -/
def cmp_3sm_R : PAC :=
  mkRelativePAC ⟨.s3, some .masculine⟩ .completive "yà" trivial

/-- 3sg.F completive, Relative form *ta* (@cite{newman-2000} §70.2,
    @cite{hartmann-zimmermann-2007} eq. 24). -/
def cmp_3sf_R : PAC :=
  mkRelativePAC ⟨.s3, some .feminine⟩ .completive "ta" trivial

/-- 3sg.M continuous, General form *yanā*. -/
def cont_3sm_G : PAC :=
  mkGeneralPAC ⟨.s3, some .masculine⟩ .continuous "yanā"

/-- 3sg.M continuous, Relative form *yake* — a stem alternation, not
    just a tone change (@cite{newman-2000} §70.2). -/
def cont_3sm_R : PAC :=
  mkRelativePAC ⟨.s3, some .masculine⟩ .continuous "yake" trivial

/-- 3sg.F continuous, Relative form *takèe*
    (@cite{hartmann-zimmermann-2007} eq. 22). -/
def cont_3sf_R : PAC :=
  mkRelativePAC ⟨.s3, some .feminine⟩ .continuous "takèe" trivial

/-- 1sg completive, General form *naa*
    (@cite{hartmann-zimmermann-2007} eq. 23). -/
def cmp_1sg_G : PAC :=
  mkGeneralPAC ⟨.s1, none⟩ .completive "naa"

/-- 1sg continuous, Relative form *nakèe*
    (@cite{hartmann-zimmermann-2007} eq. 29). -/
def cont_1sg_R : PAC :=
  mkRelativePAC ⟨.s1, none⟩ .continuous "nakèe" trivial

/-- 1sg future *zân* (@cite{hartmann-zimmermann-2007} eqs. 25, 30).
    No General/Relative contrast in the future TAM. -/
def fut_1sg : PAC :=
  mkGeneralPAC ⟨.s1, none⟩ .future "zân"

/-- 3sg.M subjunctive *yà*. No General/Relative contrast in this TAM. -/
def subj_3sm : PAC :=
  mkGeneralPAC ⟨.s3, some .masculine⟩ .subjunctive "yà"

/-- The PAC registry: representative cells used by downstream fragments
    (notably `Hausa/Focus.lean`). Every entry is well-formed by
    construction (see `all_representative_PACs_wellFormed`). -/
def representativePACs : List PAC :=
  [cmp_3sm_G, cmp_3sm_R, cmp_3sf_R, cont_3sm_G, cont_3sm_R, cont_3sf_R,
   cmp_1sg_G, cont_1sg_R, fut_1sg, subj_3sm]

-- ============================================================================
-- § 5: Universal Theorems
-- ============================================================================

/-- **The G/R contrast is morphologically distinct only in completive
    and continuous.** In our representative TAM list, exactly the
    completive and continuous admit a Relative form. -/
theorem only_cmp_cont_split (t : TAM) :
    t.HasRelativeForm ↔ t = .completive ∨ t = .continuous := by
  cases t <;> simp [TAM.HasRelativeForm]

/-- **The completive G/R minimal pair.** The 3sg.M completive surfaces
    as *yā* (G) vs *yà* (R) — a tonal minimal pair. -/
theorem completive_3sm_G_R_contrast :
    cmp_3sm_G.form = "yā" ∧ cmp_3sm_R.form = "yà" := ⟨rfl, rfl⟩

/-- **Every PAC built by the smart constructors is well-formed.** The
    representative registry is well-formed because every entry is built
    via `mkGeneralPAC` or `mkRelativePAC`. -/
theorem all_representative_PACs_wellFormed :
    ∀ p ∈ representativePACs, p.WellFormed := by
  intro p hp
  simp only [representativePACs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **The registry covers both modes for every TAM that admits the
    split.** This is what makes the registry a genuine empirical
    sample of the G/R contrast rather than a one-sided collection. -/
theorem registry_covers_relative_TAMs :
    ∀ t : TAM, t.HasRelativeForm →
      (∃ p ∈ representativePACs, p.tam = t ∧ p.mode = .general) ∧
      (∃ p ∈ representativePACs, p.tam = t ∧ p.mode = .relative) := by
  intro t ht
  cases t <;> simp [TAM.HasRelativeForm] at ht <;>
    first
    | exact ⟨⟨cmp_3sm_G, by simp [representativePACs], rfl, rfl⟩,
            ⟨cmp_3sm_R, by simp [representativePACs], rfl, rfl⟩⟩
    | exact ⟨⟨cont_3sm_G, by simp [representativePACs], rfl, rfl⟩,
            ⟨cont_3sm_R, by simp [representativePACs], rfl, rfl⟩⟩

end Fragments.Hausa.Inflection
