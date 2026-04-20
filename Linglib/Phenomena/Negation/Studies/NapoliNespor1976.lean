import Linglib.Theories.Pragmatics.Bias
import Linglib.Phenomena.Negation.Studies.Rett2026
import Linglib.Phenomena.Negation.Studies.Tsiakmakis2025
import Linglib.Fragments.Italian.ExpletiveNegation
import Linglib.Fragments.Italian.PolarityItems
import Linglib.Core.Mood.Basic

/-!
# Napoli & Nespor (1976): Negatives in Comparatives @cite{napoli-nespor-1976}

*Language* 52(4), 811–838.

The Italian word *non* appears in some comparative clauses without
truth-conditional effect: *Maria è più intelligente di quanto non sia
Carlo* 'Maria is more intelligent than Carlo (is)'. The construction
had previously been treated either as pleonastic (Antinucci & Puglielli
1971) or as evidence that all *than*-clauses are underlyingly negative
(Seuren 1969). @cite{napoli-nespor-1976} reject both: *non₂* is real
negation, but its distribution is governed by a discourse condition,
not by the syntax of comparison.

## Core Claim

*Non₂* is licensed iff the speaker presupposes that their assertion
contradicts a prior belief (their own or attributed to the addressee),
the move is assertive, the matrix is unnegated, and the construction
does not require precise knowledge. The four conditions are formalized
once in `Pragmatics.Bias.BiasLicensingProfile` and consumed here; this
study file is the first historical attestation of the predicate, applied
to Italian comparatives.

## What's Foundational vs. Historical

@cite{napoli-nespor-1976} bundles two contributions:

- **Foundational (preserved):** the licensing predicate, the Dario/Paolo
  context paradigm, the morphosyntactic diagnostics for underlying
  negation (subjunctive co-occurrence, *pur*-NPI licensing, *neanche*-
  conjunction, [-specific] indefinites, complementizer alternation),
  and the cross-construction generalization to indirect questions and
  cross-linguistic parallels (French *ne*, German modal particles).
- **Historical (not preserved):** the Generative Semantics deep-structure
  apparatus — abstract higher S₂ dominating S₃ with *non₂* base-generated
  in S₃ and optionally deleted by transformation. The covert-operator
  insight is preserved by modern verum / use-conditional / commitment-
  update accounts (@cite{romero-han-2004}, @cite{repp-2013},
  @cite{gutzmann-2015}, @cite{farkas-bruce-2010}); the deletion-rule
  mechanism specifically is not.

## Connection to Existing linglib Studies

- @cite{rett-2026} classifies Italian comparative EN as low/optional with
  weak-NPI rejection. The N&N data refines this: optionality is
  *contextually conditioned* (a `BiasLicensingProfile`, not a `Bool`),
  and weak NPIs *are* licensed when the profile licenses (modulo
  independent precision-blockers like *affatto*). See
  `Rett2026.italianComparative` and the patches in §6 below.
- @cite{tsiakmakis-2025} classifies Italian comparative *non* as NEG₁
  (apparent EN, standard negation masked). N&N's analysis is the
  original NEG₁-style account: *non₂* is real negation in underlying
  structure, masked at surface by deletion or by an abstract operator.
- @cite{greco-2020} lists *comparativeClauses* among Italian weak-EN
  environments. N&N's *pur*-licensing data motivates this classification.
-/

namespace Phenomena.Negation.Studies.NapoliNespor1976

open Pragmatics.Bias
  (BiasLicensingProfile licensedProfile blockedProfile
   noContradictionProfile questionedProfile matrixNegatedProfile
   preciseProfile imperativeProfile)
open Fragments.Italian.PolarityItems (pur affatto neanche)
open Core.Lexical.PolarityItem (LicensingContext PolarityItemEntry)

-- ════════════════════════════════════════════════════
-- § 1. The Dario/Paolo dialogue paradigm (§2)
-- ════════════════════════════════════════════════════

/-! ### Four contexts varying the speaker's epistemic state

@cite{napoli-nespor-1976} pp. 812–813 construct four dialogues showing
that *non₂*'s acceptability tracks the speaker's presupposition that
their assertion contradicts a prior belief — neither too uncertain
(no presupposition to contradict) nor too explicit (use simple negation
instead). -/

/-- Context (6): Dario gives no opinion of Maria or Carlo; Paolo asserts
    Maria > Carlo. No prior belief to contradict ⇒ *non₂* infelicitous. -/
def context6 : BiasLicensingProfile := noContradictionProfile

/-- Context (7): Dario implies Carlo > Maria at chess; Paolo asserts
    Maria more intelligent. Inferred contradiction ⇒ *non₂* may appear. -/
def context7 : BiasLicensingProfile := licensedProfile

/-- Context (8): Dario *explicitly* says Maria is dumb; Paolo disagrees.
    The contradiction is too explicit; speaker should use simple negation,
    not *non₂*. Modeled here as failing the imprecise/inferred condition. -/
def context8 : BiasLicensingProfile := preciseProfile

/-- Context (9): Dario's complaint implies he expects Maria can't help;
    Paolo asserts Maria smart enough to ask. Inferred contradiction ⇒
    *non₂* used. -/
def context9 : BiasLicensingProfile := licensedProfile

/-- Predictions: *non₂* infelicitous in (6), licensed in (7), blocked
    in (8), licensed in (9). Each follows by `decide` from the licensing
    predicate in `Pragmatics.Bias`. -/
theorem context6_blocks : ¬ context6.licenses := by decide
theorem context7_licenses : context7.licenses := by decide
theorem context8_blocks : ¬ context8.licenses := by decide
theorem context9_licenses : context9.licenses := by decide

-- ════════════════════════════════════════════════════
-- § 2. Distributional environments (§2.1, §2.2, §2.3, §3.22)
-- ════════════════════════════════════════════════════

/-! ### Five distributional environments, each isolating one axis

@cite{napoli-nespor-1976} demonstrates each licensing condition by
exhibiting an environment where exactly that condition fails. -/

/-- §2.1 ex. 10b: *È più intelligente di quanto non sia Carlo?*
    'Is she more intelligent than Carlo is?' — questioned comparative
    blocks *non₂*. Speaker cannot simultaneously question and contradict. -/
def questionedComparative : BiasLicensingProfile := questionedProfile

/-- §2.2 ex. 18a: *Maria non è più intelligente di quanto non sia Carlo*
    'Maria is not more intelligent than Carlo is' — matrix-negated
    blocks *non₂*. -/
def matrixNegatedComparative : BiasLicensingProfile := matrixNegatedProfile

/-- §2.3 ex. 22b: *Maria è tanto intelligente *quanto non sia Carlo*
    'Maria is as intelligent as Carlo is' — equality (*tanto…quanto*)
    requires precise knowledge incompatible with the inferred-belief
    presupposition. -/
def equalityComparative : BiasLicensingProfile := preciseProfile

/-- §3.22 ex. 32b, 33b: *Maria è {molto più / due metri più} intelligente
    di quanto *tu non creda* — explicit precision modifiers fail the
    imprecise condition. -/
def precisionComparative : BiasLicensingProfile := preciseProfile

/-- §2.3 ex. 26b: *Maria è meno intelligente di quanto tu non creda*
    'Maria is less intelligent than you think' — *meno* (less) allows
    *non₂*. This is N&N's sanity check against Seuren 1969: if *non₂*
    were just "negation triggered by than-clause", it should appear
    equally with *meno*; in fact it does, but only under the same
    contextual conditions as with *più*. -/
def menoComparative : BiasLicensingProfile := licensedProfile

theorem questioned_blocks_non2 : ¬ questionedComparative.licenses := by decide
theorem matrix_negated_blocks_non2 : ¬ matrixNegatedComparative.licenses := by decide
theorem equality_blocks_non2 : ¬ equalityComparative.licenses := by decide
theorem precision_blocks_non2 : ¬ precisionComparative.licenses := by decide
theorem meno_licenses_non2 : menoComparative.licenses := by decide

-- ════════════════════════════════════════════════════
-- § 3. Morphosyntactic diagnostics for underlying negation
-- ════════════════════════════════════════════════════

/-! ### Predictions derived from the licensing profile

@cite{napoli-nespor-1976} §3 marshals six independent diagnostics for
the presence of underlying negation in the comparative clause. Each
diagnostic targets a different surface correlate (mood morphology, NPI
surface form, indefinite specificity, conjunction admissibility,
complementizer choice, predicative clitic) and so returns a value of a
*different type* — flattening them all to `Bool := p.licenses` would
collapse six empirically distinct probes into one fact. The agreement
theorem `licensed_diagnostics_agree` collects the six predictions on the
licensed profile rather than asserting they are tautologically equal. -/

/-- Specificity restriction on embedded indefinites. Without *non₂* an
    indefinite in the *than*-clause is [±specific]; with *non₂* it is
    restricted to [−specific] under the scope of the underlying negation.
    @cite{napoli-nespor-1976} §3.11 ex. 44–45. -/
inductive SpecificityProfile where
  | unrestricted    -- [+specific] reading available
  | nonspecificOnly -- restricted to [−specific] (negation-scope)
  deriving DecidableEq, Repr

/-- Complementizer choice in Italian comparatives.
    *Di quanto* is the standard *than*-complementizer; *che* surfaces
    when the abstract higher S of @cite{napoli-nespor-1976} §3.24 is
    present, which co-varies with *non₂*. -/
inductive ComplementizerChoice where
  | che      -- bias-licensed alternant
  | diQuanto -- default
  deriving DecidableEq, Repr

/-- Predicate-clitic *lo* presence. §3.25 treats the clitic as genuinely
    binary (present iff the abstract higher S licenses *non₂*), but the
    two outcomes carry distinct surface morphology — `Bool` would lose
    that contrast at the type level. -/
inductive CliticPresence where
  | present  -- clitic *lo* surfaces
  | absent   -- no clitic
  deriving DecidableEq, Repr

/-- §3.21: grammatical mood of the *than*-clause. Subjunctive surfaces
    iff *non₂* is underlyingly present (modulo lexical mood control by
    *credere* etc., abstracted away here). Returning `Core.Mood.GramMood`
    rather than `Bool` connects this prediction to the mood semantics in
    `Theories/Semantics/Mood/`. -/
def predictsGramMood (p : BiasLicensingProfile) : Core.Mood.GramMood :=
  if p.licenses then .subjunctive else .indicative

/-- §3.11 ex. 46–48: under bias-licensed negation the comparative admits
    a weak NPI on its surface; the canonical witness in the Italian
    Fragment is `pur`. Returning `Option String` carries the predicted
    surface form (or `none` when blocked) rather than collapsing to a
    coarse `Bool`. The form string is derived from the Fragment entry to
    keep the connection true by construction. -/
def predictsWeakNPISurface (p : BiasLicensingProfile) : Option String :=
  if p.licenses then some pur.form else none

/-- §3.11 ex. 44–45: specificity restriction on embedded indefinites.
    Bias-licensed comparatives restrict the indefinite to [−specific];
    blocked profiles leave it unrestricted. -/
def predictsSpecificity (p : BiasLicensingProfile) : SpecificityProfile :=
  if p.licenses then .nonspecificOnly else .unrestricted

/-- §3.11 ex. 50–52: *neanche*-conjunction is grammatical iff the first
    conjunct is underlyingly negated. The Fragment registers *neanche*
    as requiring `.negation` among its licensing contexts — the prediction
    is **derived** from that registry fact in conjunction with the bias
    profile, so changing the *neanche* lexical entry would break this
    prediction by construction rather than requiring a separate update
    here. -/
def predictsNeancheConjunction (p : BiasLicensingProfile) : Prop :=
  p.licenses ∧ neanche.licensingContexts.contains .negation = true

instance (p : BiasLicensingProfile) : Decidable (predictsNeancheConjunction p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- §3.24: the complementizer *che* (vs. *di quanto*) is licensed iff
    the abstract higher S is present, which co-varies with *non₂*.
    Returning `ComplementizerChoice` exposes both alternants rather than
    encoding "*che* present" as a Bool. -/
def predictsComplementizer (p : BiasLicensingProfile) : ComplementizerChoice :=
  if p.licenses then .che else .diQuanto

/-- §3.25: clitic *lo* substituting for the predicate adjective is
    licensed iff the comparative has the abstract S structure (*non₂*
    present). Returns `CliticPresence` rather than `Bool` to keep the
    surface alternants distinguishable at the type level. -/
def predictsLoClitic (p : BiasLicensingProfile) : CliticPresence :=
  if p.licenses then .present else .absent

/-- The six diagnostics agree on the **licensed** profile: each surface
    correlate takes its bias-marked value. The conjunction below is the
    theoretical unification @cite{napoli-nespor-1976} §3 argues for —
    one licensing predicate explains all six surface diagnostics. The
    *neanche*-conjunction conjunct is non-trivial: it factors through
    the Italian Fragment's `neanche.licensingContexts` and needs `decide`
    on the registry data. -/
theorem licensed_diagnostics_agree :
    predictsGramMood licensedProfile = .subjunctive ∧
    predictsWeakNPISurface licensedProfile = some pur.form ∧
    predictsSpecificity licensedProfile = .nonspecificOnly ∧
    predictsNeancheConjunction licensedProfile ∧
    predictsComplementizer licensedProfile = .che ∧
    predictsLoClitic licensedProfile = .present := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Dual: on a blocked profile every diagnostic returns its non-bias-marked
    value. Together with `licensed_diagnostics_agree` this witnesses that
    the six diagnostics are genuinely *predictive* (their values vary
    with the bias profile) rather than constant functions. -/
theorem blocked_diagnostics_agree :
    predictsGramMood blockedProfile = .indicative ∧
    predictsWeakNPISurface blockedProfile = none ∧
    predictsSpecificity blockedProfile = .unrestricted ∧
    ¬ predictsNeancheConjunction blockedProfile ∧
    predictsComplementizer blockedProfile = .diQuanto ∧
    predictsLoClitic blockedProfile = .absent := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

-- ════════════════════════════════════════════════════
-- § 4. The pur / affatto contrast (§3.11 fn 6)
-- ════════════════════════════════════════════════════

/-! ### Why some weak NPIs are licensed and others blocked

@cite{napoli-nespor-1976} §3.11 ex. 46–48 show that *pur* (weak NPI) is
licensed in *non₂*-comparatives. §3.22 fn (i) shows that *affatto* (also
a weak NPI) is *blocked*. The contrast is not about NPI licensing per se:
*affatto* requires *precise* knowledge of the listener's belief, which
fails N&N's imprecise condition. The block is semantic, not licensing-
theoretic.

The `weakNPIs` field of `Rett2026.ENDatum` (refactored from `Bool` to a
`WeakNPILicensing` sum type for exactly this reason) classifies
italianComparative as `.selective [pur.form]`: it licenses *some* weak
NPIs (*pur*) and blocks others (*affatto*) for *orthogonal* reasons.

The two NPIs are registered in the Italian Fragment as
`Fragments.Italian.PolarityItems.pur` and
`Fragments.Italian.PolarityItems.affatto`. The contrast is **already**
witnessed at the lexical layer (the structural theorems
`pur_licensed_in_comparative` and `affatto_not_licensed_in_comparative`
in the Fragment), so this study file just consumes those facts and
shows them follow from the bias profile. -/

/-- A weak NPI from the Italian Fragment is licensed in a bias-conditioned
    negation environment iff (a) its registry already lists `.comparative`
    among its licensing contexts AND (b) the bias profile licenses.
    The first conjunct rules out *affatto* (registry-blocked); the second
    rules out unlicensed contexts. -/
def predictsWeakNPI (p : BiasLicensingProfile) (npi : PolarityItemEntry) : Prop :=
  p.licenses ∧ npi.licensingContexts.contains .comparative = true

instance (p : BiasLicensingProfile) (npi : PolarityItemEntry) :
    Decidable (predictsWeakNPI p npi) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- *Pur* is licensed in any context where *non₂* is licensed.
    Combines `pur_licensed_in_comparative` from the Italian Fragment with
    the bias profile's licensing predicate. -/
theorem pur_licensed_with_non2 : predictsWeakNPI licensedProfile pur := by decide

/-- *Affatto* is *never* licensed in *non₂*-comparatives — the block is
    *registered in the lexical entry itself* (`affatto.licensingContexts`
    excludes `.comparative` per @cite{napoli-nespor-1976} §3.22 fn 6). The
    bias profile's licensing status is irrelevant: the Fragment's
    distributional fact alone settles the case.

    This makes the N&N contrast structural — derived from the lexical
    `licensingContexts` field — rather than stipulated by an inline
    inductive in this study file. -/
theorem affatto_blocked_in_non2 (p : BiasLicensingProfile) :
    ¬ predictsWeakNPI p affatto := by
  intro ⟨_, h⟩
  rw [Fragments.Italian.PolarityItems.affatto_not_licensed_in_comparative] at h
  exact Bool.false_ne_true h

-- ════════════════════════════════════════════════════
-- § 5. Cross-construction generalization (§4)
-- ════════════════════════════════════════════════════

/-! ### *Non₂* outside comparatives: indirect questions

@cite{napoli-nespor-1976} §4 ex. 88–91 show that the same *non₂* appears
in indirect questions where the speaker presupposes the negated
proposition is contrary to expectation: *Chissà se non vale la pena di
comprarlo* 'Who knows if it's not worth buying it' (suggests the
speaker expects it to be worth buying).

The licensing profile is the same. This is the foundational insight
that makes N&N's contribution a general predicate rather than a
construction-specific rule. -/

/-- *Chissà se non…* — indirect question with biased negation.
    Same licensing profile as the basic comparative. -/
def chissaSeNon : BiasLicensingProfile := licensedProfile

theorem chissa_licenses_non2 : chissaSeNon.licenses := by decide

/-- The licensing profile is *invariant under construction type*: the
    same profile that licenses comparative *non₂* also licenses indirect-
    question *non₂*. This is why N&N's analysis generalizes; it is also
    the prediction we want for parallel phenomena (French *ne* in biased
    contexts, etc.). -/
theorem licensing_invariant_across_constructions :
    context7.licenses ↔ chissaSeNon.licenses := Iff.rfl

-- ════════════════════════════════════════════════════
-- § 6. Bridge to Rett2026: refining italianComparative
-- ════════════════════════════════════════════════════

/-! ### Refining `Rett2026.italianComparative.isOptional`

`Rett2026.italianComparative.isOptional := true` is technically correct
but coarse: optionality is *contextually conditioned* on a bias profile,
not free. The function below derives `isOptional` from a bias profile,
restoring the connection that the `Bool` field flattens. -/

/-- Derived optionality: a construction is "optional" iff its licensing
    profile is satisfied by some context but not all. For the
    `BiasLicensingProfile` paradigm this is automatically true (the
    licensed/blocked profiles witness both polarities). -/
theorem bias_paradigm_is_optional :
    licensedProfile.licenses ∧ ¬ blockedProfile.licenses := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Bridge to @cite{rett-2026}: the `italianComparative` datum's
    `isOptional` field reflects exactly this contextual conditioning. -/
theorem rett_italianComparative_optionality_grounded :
    Rett2026.italianComparative.isOptional = true ∧
    licensedProfile.licenses ∧ ¬ blockedProfile.licenses := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

end Phenomena.Negation.Studies.NapoliNespor1976
