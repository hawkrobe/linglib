import Linglib.Theories.Syntax.Minimalism.Basic
import Linglib.Theories.Syntax.Minimalism.SmallClause
import Linglib.Phenomena.ArgumentStructure.Studies.Dendikken1995

/-!
# Transitive causatives — den Dikken's affixal-particle analysis
@cite{dendikken-1995} @cite{baker-1988}

@cite{dendikken-1995} chapter 5 extends the SC-in-SC template from
triadic constructions (book chs. 3-4) to transitive causative
constructions. Central thesis: so-called "applicative" and "causative"
morphemes (Bantu *-il-*, Dutch *ver-*, Sanuma *-ma*, Indonesian *-kan*,
French *en-*, *a-*, *dé-*) are **affixal particles** — the same syntactic SC
heads as English particles, just morphologically bound to the verb.

## The affixal-particle thesis (book p. 235 ex. 25)

    ver- = -ma = -kan = PARTICLE

The cross-linguistic homophony of "applicative" and "causative" affixes
is dissolved: they are all affixal particles occupying the X position
in the SC-in-SC template. The verb supplies the lexical content; the
particle supplies the structural slot for SC3.

## Causative D-structure template (book p. 239 ex. 32; p. 246 ex. 48)

    [VP V_caus [SC1 Spec_θ' [VP V_emb [SC2 Spec_θ' [XP X [SC3 NP_obj [PP P NP_causee]]]]]]]

- V_caus = matrix causative verb (French *faire*; often empty for
  affixal causatives like Dutch *ver-* where the matrix CAUSE is
  non-overt — book p. 238).
- V_emb = the embedded causativised verb (e.g. *porter*, *manger*,
  *dormir*) — supplies the lexical content of the causation target.
- X = affixal particle slot (∅ in French *faire*; *ver-* in Dutch;
  *-ma* in Sanuma; *-kan* in Indonesian).
- NP_obj = embedded direct object (the patient of V_emb).
- PP = dative phrase whose object is the embedded subject (the *causee*).

## Triadic ↔ causative parallel (book p. 246 ex. 47/48)

    Triadic:   [VP V_triadic [SC1 Spec_θ' [VP "BE"  [SC2 Spec_θ' [XP X [SC3 Theme  [PP P Goal]]]]]]]
    Causative: [VP V_caus    [SC1 Spec_θ' [VP V_emb [SC2 Spec_θ' [XP X [SC3 EmbObj [PP P Causee]]]]]]]

Identical template. The only difference: the V slot in the lower VP
holds the empty copula BE in triadics but the lexical embedded verb
in causatives.

## Two cross-linguistic correlations (book p. 241 ex. 35; p. 243 ex. 41)

Both fall out of the structural assimilation:

    I.  Case of *causee* in transitive causatives = Case of *Goal* in PD.
    II. Case of *embedded direct object* in transitive causatives =
        Case of *Theme* in PD.

The causee occupies the PP-position SC3 has for the Goal in triadics;
the embedded direct object occupies the SC3-subject position SC3 has
for the Theme.

## Cross-linguistic data anchored in this file

- **French**: *Marie a fait manger des bonbons à ses enfants* —
  matrix V is *faire*, X = ∅, V_emb = *manger*, dative à-PP holds
  the causee *ses enfants*. (Book p. 248 ex. 49.)
- **Dutch**: *Jan verschafte de kinderen eten* — matrix V is empty,
  X = *ver-* (the affixal particle), V_emb = *schaffen* (provide).
  (Book p. 234 ex. 19b.)
- **Sanuma** (Yanomami, Borgman 1989): *kamisa-nö setenapi te niha
  manasi sa ta-ma-na-ni ke* 'I made the non-Indian see the guan bird'
  — X = *-ma*, embedded V = *ta* (see), causee = *setenapi*. (Book
  p. 240 ex. 34b.)
- **Indonesian** (Voskuil 1990): *Parto menidurkan Ratna* 'Parto made
  Ratna sleep' — X = *-kan*, embedded V = *tidur* (sleep), causee =
  *Ratna*. (Book p. 232 ex. 13b.)

## Cross-references

- `Phenomena/ArgumentStructure/Studies/Dendikken1995` — the triadic
  formalisation (book ch. 3). Same SC-in-SC template, V-slot filled
  with abstract BE rather than V_emb.
- `Phenomena/Constructions/ParticleVerbs/Studies/Dendikken1995` — the
  simplex PVC formalisation (book ch. 2.4). Particles in PVCs
  ≡ affixal particles in causatives at the syntactic level
  (book p. 235 ex. 25).
- `Theories/Syntax/Minimalism/Applicative.lean` — Pylkkänen's
  high/low applicative typology. Per chronological dependency, this
  1995 file does not import `Phenomena/ArgumentStructure/Studies/Pylkkanen2008`;
  the reverse direction is appropriate.

## Scope (and what's deferred)

Formalises the structural template (32)/(48) and verifies it satisfies
`IsSmallClause` at every nested SC layer for both the French and the
Dutch instantiations. The cross-linguistic affixal-particle thesis
(eq. 25) is recorded as a structural identity claim about the X
position's category.

NOT formalised (each pending substrate work):
- Predicate Inversion + LF P-incorporation for causative DOC analogues
  (parallel to triadic; needs LF-reanalysis substrate, see SC/particles
  architectural target memo).
- "Ergativisation" of V_emb (book §5.3.6) — den Dikken's claim that the
  embedded verb loses its external θ-role when embedded under V_caus.
- Case-licensing chains for causee + embedded direct object across
  languages (would need a Case-feature substrate).
- Clitic-climbing data (book §5.3.7) — requires a clitic-movement
  primitive in addition to Predicate Inversion.

-/

namespace Phenomena.Constructions.Causatives.Studies.Dendikken1995

open Minimalism

/-! ## §1. Lexical items for the causative template -/

/-- Matrix causative verb. French *faire* in `Marie a fait manger des
    bonbons à ses enfants`. -/
def V_faire : SyntacticObject := mkLeafPhon .V [.D] "faire" 500

/-- Empty matrix causative head. Per book p. 238: when no overt matrix
    causative verb is present (Dutch *ver-* causatives, Sanuma *-ma*
    causatives), the causation semantics is supplied by an empty
    causative matrix predicate. -/
def V_caus_empty : SyntacticObject := mkLeafPhon .V [] "∅_CAUS" 501

/-- Embedded causativised verbs. Lexical content preserved; only the
    external θ-role is lost ("ergativisation", book §5.3.6). -/
def V_manger   : SyntacticObject := mkLeafPhon .V [.D] "manger" 503
def V_schaffen : SyntacticObject := mkLeafPhon .V [.D] "schaffen" 505

/-! ## §2. The X position: affixal particles across languages

Each "affixal causativiser/applicativiser" morpheme is realised here
as a category-P leaf with no selectional features — the canonical
shape for a particle (compare `Phenomena/Constructions/ParticleVerbs/Studies/Dendikken1995`'s
particle leaves like `mkLeafPhon .P [] "up"`). -/

/-- French causative X is empty (*faire* construction). -/
def X_empty : SyntacticObject := mkLeafPhon .P [] "∅_X" 510

/-- Dutch *ver-*. -/
def X_dutch_ver : SyntacticObject := mkLeafPhon .P [] "ver-" 511

/-- Sanuma *-ma*. -/
def X_sanuma_ma : SyntacticObject := mkLeafPhon .P [] "-ma" 512

/-- Indonesian *-kan*. -/
def X_indonesian_kan : SyntacticObject := mkLeafPhon .P [] "-kan" 513

/-! ## §3. PP and Spec primitives (parallel to the triadic file) -/

/-- Dative preposition: French *à*, Bantu *kwa*, Sanuma postposition. -/
def P_a : SyntacticObject := mkLeafPhon .P [.D] "à" 520

/-- Empty θ'-Spec position. Same hack as the triadic file:
    `mkLeafPhon .D` with arbitrary category D, since linglib has no
    first-class empty-Spec primitive. -/
def Spec_theta_prime : SyntacticObject := mkLeafPhon .D [] "θ'" 530

/-! ## §4. French causative example: *faire manger des bonbons à ses enfants*

Building bottom-up: SC3 → XP → SC2 → lower VP → SC1 → matrix VP. -/

def DP_bonbons : SyntacticObject := mkLeafPhon .D [] "des bonbons" 540
def DP_enfants : SyntacticObject := mkLeafPhon .D [] "ses enfants" 541

/-- The dative PP holding the causee: `[PP à ses-enfants]`. -/
def pp_a_enfants : SyntacticObject := merge P_a DP_enfants

/-- SC3: `[SC3 des-bonbons [PP à ses-enfants]]` — the embedded direct
    object is the SC subject; the dative PP (causee) is the SC predicate. -/
def sc3_faire_manger : SyntacticObject := merge DP_bonbons pp_a_enfants

/-- XP: `[XP ∅_X SC3]`. -/
def xp_faire_manger : SyntacticObject := merge X_empty sc3_faire_manger

/-- SC2: `[SC2 Spec_θ' XP]`. -/
def sc2_faire_manger : SyntacticObject :=
  merge Spec_theta_prime xp_faire_manger

/-- Lower VP: `[VP V_emb SC2]` — the embedded causativised verb
    (manger) takes SC2 as its complement. -/
def vp_emb_manger : SyntacticObject := merge V_manger sc2_faire_manger

/-- SC1: `[SC1 Spec_θ' VP_emb]`. -/
def sc1_faire_manger : SyntacticObject :=
  merge Spec_theta_prime vp_emb_manger

/-- The full French causative D-structure for *faire manger des bonbons
    à ses enfants*. -/
def causativeStructure_faire_manger : SyntacticObject :=
  merge V_faire sc1_faire_manger

/-! ## §5. Dutch *ver-*-causative example: *Jan verschafte de kinderen eten*

The matrix causative V is empty (book p. 238). The affixal particle
*ver-* occupies the X slot. The embedded V is *schaffen* 'provide'. -/

def DP_kinderen : SyntacticObject := mkLeafPhon .D [] "de kinderen" 542
def DP_eten     : SyntacticObject := mkLeafPhon .D [] "eten" 543

def pp_a_kinderen : SyntacticObject := merge P_a DP_kinderen

def sc3_ver_schaffen : SyntacticObject :=
  merge DP_eten pp_a_kinderen

def xp_ver_schaffen : SyntacticObject :=
  merge X_dutch_ver sc3_ver_schaffen

def sc2_ver_schaffen : SyntacticObject :=
  merge Spec_theta_prime xp_ver_schaffen

def vp_emb_schaffen : SyntacticObject :=
  merge V_schaffen sc2_ver_schaffen

def sc1_ver_schaffen : SyntacticObject :=
  merge Spec_theta_prime vp_emb_schaffen

/-- The Dutch *ver-*-causative D-structure. Matrix V is empty per book
    p. 238 (the empty causative matrix predicate). -/
def causativeStructure_ver_schaffen : SyntacticObject :=
  merge V_caus_empty sc1_ver_schaffen

/-! ## §6. Structural assimilation: French and Dutch share one shape -/

/-- The French *faire* causative and the Dutch *ver-* causative share
    the same tree shape — the affixal-particle thesis at the geometric
    level. -/
theorem faire_ver_same_shape :
    causativeStructure_faire_manger.shape =
      causativeStructure_ver_schaffen.shape := rfl

/-- Both causative D-structures have the 7-level binary right-branching
    SC-in-SC depth predicted by book ex. 32 / ex. 48. -/
theorem causativeStructure_faire_manger_shape :
    causativeStructure_faire_manger.shape =
      .node .leaf
        (.node .leaf
          (.node .leaf
            (.node .leaf
              (.node .leaf
                (.node .leaf
                  (.node .leaf .leaf)))))) := rfl

/-! ## §7. IsSmallClause witnesses

Each of the three nested SCs in the causative D-structure satisfies the
`IsSmallClause` companion predicate. Same demonstration as in the
triadic file — confirming the structural assimilation claim *at the
substrate level*. SC3 has predicate-head P (dative preposition), SC2
has predicate-head P (the affixal particle X), SC1 has predicate-head
V (the embedded causativised verb). -/

theorem sc3_faire_manger_isSmallClause : IsSmallClause sc3_faire_manger := by decide
theorem sc2_faire_manger_isSmallClause : IsSmallClause sc2_faire_manger := by decide
theorem sc1_faire_manger_isSmallClause : IsSmallClause sc1_faire_manger := by decide

theorem sc3_ver_schaffen_isSmallClause : IsSmallClause sc3_ver_schaffen := by decide
theorem sc2_ver_schaffen_isSmallClause : IsSmallClause sc2_ver_schaffen := by decide
theorem sc1_ver_schaffen_isSmallClause : IsSmallClause sc1_ver_schaffen := by decide

/-! ## §8. The affixal-particle thesis as a categorial identity (book ex. 25)

`ver- = -ma = -kan = PARTICLE`

The three overt affixal-particle morphemes share head category P (the
canonical particle category). The unifying analytic claim is that the
language-specific surface differences between Dutch *ver-*, Sanuma
*-ma*, Indonesian *-kan*, and English particles like *up* / *out* /
*off* are morphological, not syntactic — at the X position they are
indistinguishable. -/

/-- Faithful to book ex. 25 (`ver- = -ma = -kan = PARTICLE`): the three
    overt affixal-particle morphemes from §5.2 share head category P.
    Note: French *faire*'s null X is NOT part of the ex. 25 claim and is
    intentionally omitted; book §5.2.5 covers French separately via
    *en-*, *a-*, *dé-* prefixes (which would have head category P too,
    but as distinct lexical particles, not via the *faire* X-slot). -/
theorem affixal_particles_share_category :
    X_dutch_ver.headCat = .P ∧
    X_sanuma_ma.headCat = .P ∧
    X_indonesian_kan.headCat = .P := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## §9. Structural assimilation theorem (book ex. 47/48)

The book's central ch. 5 claim is that triadic and transitive
causative constructions share the SC-in-SC structural backbone.
Now that both are formalised as sibling Dendikken1995 study files,
the parallel can be witnessed as a Lean theorem rather than a
docstring assertion. -/

/-- The French causative SC1 and the triadic SC1 share tree shape —
    the structural assimilation thesis at the geometric level. Both
    instantiate the same 7-level right-branching SC-in-SC template;
    they differ only in lexical content (V_emb vs BE in the lower-VP
    V slot, X = ∅ vs Prt_off, dative à vs to, etc.). -/
theorem causative_triadic_same_shape :
    sc1_faire_manger.shape =
      (Phenomena.ArgumentStructure.Studies.Dendikken1995.sc1_send).shape := rfl

/-- The Dutch *ver-* causative also matches the triadic shape — the
    affixal particle X position is structurally the same as the
    triadic particle X position. -/
theorem dutch_ver_triadic_same_shape :
    sc1_ver_schaffen.shape =
      (Phenomena.ArgumentStructure.Studies.Dendikken1995.sc1_send).shape := rfl

/-! ## §10. Bridge to Pylkkänen's applicative typology

Den Dikken's affixal-particle X position is the structural slot
Pylkkänen (2008) reanalyses as a low Applicative head — the two
analyses agree on category P, despite different theoretical framings
(particle vs. applicative). The bridge theorems below witness this
categorial coincidence using the existing `ApplType.toSCPredCategory`
API in `Theories/Syntax/Minimalism/SmallClause.lean`.

Per chronological dependency (this is a 1995 file; Pylkkänen 2008 is
later), the `ApplType` enum is referenced via the substrate, not via
direct import of the Pylkkanen2008 study file. -/

/-- The Dutch *ver-* affixal particle and a Pylkkänen low-recipient
    applicative head share SC predicate category P. -/
theorem dutch_ver_matches_low_recipient_appl :
    X_dutch_ver.headCat = .P ∧
    ApplType.toSCPredCategory .lowRecipient = some .P := by
  refine ⟨rfl, rfl⟩

/-- The Sanuma *-ma* affixal particle and a Pylkkänen low-source
    applicative head share SC predicate category P. -/
theorem sanuma_ma_matches_low_source_appl :
    X_sanuma_ma.headCat = .P ∧
    ApplType.toSCPredCategory .lowSource = some .P := by
  refine ⟨rfl, rfl⟩

/-- High applicatives DO NOT match the affixal-particle X — they project
    no SC at all in den Dikken's framework. The substrate's
    `high_appl_no_SC` theorem (in `SmallClause.lean`) records this. -/
theorem high_appl_not_affixal_particle :
    ApplType.toSCPredCategory .high = none ∧
    X_indonesian_kan.headCat = .P := by
  refine ⟨rfl, rfl⟩

end Phenomena.Constructions.Causatives.Studies.Dendikken1995
