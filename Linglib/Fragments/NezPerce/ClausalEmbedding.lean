import Linglib.Features.Complementation
import Linglib.Data.UD.Basic
import Linglib.Features.Number.Capabilities

/-!
# Nez Perce Clausal Embedding Inventory

[deal-2010] [deal-2016a] [deal-2026]

Nez Perce (Sahaptian, ISO 639-3 `nez`) inventory of notional-complement-taking
predicates plus the relative-pronoun paradigm. Theory-light: each predicate
carries only consensus-typological metadata (CTP class per [noonan-2007],
factivity per [tonhauser-beaver-roberts-simons-2013]-style projection trials,
[deal-2026] §3/§6) and one morphological observable — the grammaticality
status of *yox̂ ke* on the complement edge. The analytical RE-vs-simplex split,
selectional features, and projection-site claims are Deal-specific apparatus
and live in the co-located `Studies/Deal2026.lean`.

The relative-pronoun paradigm is from [deal-2016a] as reproduced at
[deal-2026] (22); case and number values reuse `Core.UD` substrate.
-/

namespace NezPerce.ClausalEmbedding

/-! ### Predicate schema -/

/-- Grammaticality status of the *yox̂ ke* morpheme pair on a predicate's
    notional-complement edge — a morphological observable, recording what
    the morphology does, not what it means.

    [deal-2026]: obligatory for the RE-takers ((28)); prohibited for
    *neki* and *hi* ((65)); marginal for *cuukwe* — (66b) is `%`-marked,
    and consultants "did on rare occasions accept" and once produced it,
    so *cuukwe* *permits* a bare complement rather than rejecting the
    marked one. -/
inductive EdgeRequirement where
  | obligatory
  /-- Rarely/marginally accepted (`%`-marked). -/
  | marginal
  | prohibited
  deriving DecidableEq, Repr

/-- A Nez Perce notional-complement-taking predicate.

    - `ctpClass`: [noonan-2007] category. Emotive factives are
      `commentative`; cognitive factives are `knowledge`; *think* is
      `propAttitude`; *say* is `utterance`.
    - `factive`: by projection trials in entailment-canceling
      environments ([deal-2026] §3 (33)–(36), §6 (68)). Deal notes the
      trials assess only the projection dimension of the
      [tonhauser-beaver-roberts-simons-2013] taxonomy.
    - `yoxKeEdge`: the *yox̂ ke* edge observable ([deal-2026] (28), (65),
      (66)). -/
structure NezPerceEmbedder where
  form : String
  gloss : String
  ctpClass : CTPClass
  factive : Bool
  yoxKeEdge : EdgeRequirement
  deriving DecidableEq, Repr

/-! ### RE-taking predicates ([deal-2026] §3)

Emotive factives (commentative per [noonan-2007]) plus one cognitive
factive; all require *yox̂ ke* on the complement edge ((28)), with
factivity established by projection trials ((33)–(34)). -/

/-- *lilooy* 'be happy'. [deal-2026] (27a). -/
def liloy : NezPerceEmbedder where
  form := "lilooy"; gloss := "be happy"
  ctpClass := .commentative
  factive := true
  yoxKeEdge := .obligatory

/-- *'etqew* 'be sad'. [deal-2026] (27b). -/
def etqew : NezPerceEmbedder where
  form := "'etqew"; gloss := "be sad"
  ctpClass := .commentative
  factive := true
  yoxKeEdge := .obligatory

/-- *cicwaay* 'be surprised'. [deal-2026] (27c). -/
def cicwaay : NezPerceEmbedder where
  form := "cicwaay"; gloss := "be surprised"
  ctpClass := .commentative
  factive := true
  yoxKeEdge := .obligatory

/-- *'eey's* 'be joyful'. [deal-2026] (27e). -/
def eeys : NezPerceEmbedder where
  form := "'eey's"; gloss := "be joyful"
  ctpClass := .commentative
  factive := true
  yoxKeEdge := .obligatory

/-- *q'eese'* 'be bothered, unhappy'. [deal-2026] (27e). -/
def qeese : NezPerceEmbedder where
  form := "q'eese'"; gloss := "be bothered"
  ctpClass := .commentative
  factive := true
  yoxKeEdge := .obligatory

/-- *tim'neeneki* 'be worried'. [deal-2026] (27e). -/
def timneneki : NezPerceEmbedder where
  form := "tim'neeneki"; gloss := "be worried"
  ctpClass := .commentative
  factive := true
  yoxKeEdge := .obligatory

/-- *timiipni* 'remember'. [deal-2026] (27d). Classed by Noonan as
    `knowledge` (cognitive factive) but with the same RE morphosyntax as
    the emotive factives — whether `knowledge` predicates are RE-takers
    is a per-language property (contrast English *remember*). -/
def timiipni : NezPerceEmbedder where
  form := "timiipni"; gloss := "remember"
  ctpClass := .knowledge
  factive := true
  yoxKeEdge := .obligatory

/-- *qe'ciyeew'yew'* 'thank you' — an unanalyzable particle, not a verb,
    taking notional complements with RE morphosyntax while disallowing
    all nominal complements ([deal-2026] §4 (42); fn. 16). Its factivity
    follows [deal-2026] §7's generalization that all REs are factive (no
    per-item projection trial is reported). -/
def qeciyeewyew : NezPerceEmbedder where
  form := "qe'ciyeew'yew'"; gloss := "thank you"
  ctpClass := .commentative
  factive := true
  yoxKeEdge := .obligatory

/-! ### Simplex-taking predicates ([deal-2026] §6) -/

/-- *neki* 'think'. [deal-2026] (48), (65a). Non-factive; rejects
    *yox̂ ke* on the complement edge. -/
def neki : NezPerceEmbedder where
  form := "neki"; gloss := "think"
  ctpClass := .propAttitude
  factive := false
  yoxKeEdge := .prohibited

/-- *hi* 'say, tell'. [deal-2026] (47), (65b). Non-factive; rejects
    *yox̂ ke*. Unlike the RE-takers, *hi* is transitive: it takes an
    accusative addressee and triggers object agreement ((47a)). -/
def hi : NezPerceEmbedder where
  form := "hi"; gloss := "say, tell"
  ctpClass := .utterance
  factive := false
  yoxKeEdge := .prohibited

/-- *cuukwe* 'know'. [deal-2026] (66), (68). Factive (projection
    survives a conditional antecedent, (68)) but canonically
    simplex-embedding — the RE-marked variant is only marginally
    accepted ((66b), `%`-marked). The factive-but-simplex combination is
    [deal-2026]'s central dissociation: factivity does not force RE
    morphology. -/
def cuukwe : NezPerceEmbedder where
  form := "cuukwe"; gloss := "know"
  ctpClass := .knowledge
  factive := true
  yoxKeEdge := .marginal

/-! ### Inventories -/

/-- All embedders surveyed in [deal-2026]: 8 RE-canonical + 3
    simplex-canonical. Source-of-truth list; `reCanonical` and
    `simplexCanonical` are derived views via the `yoxKeEdge` observable. -/
def allEmbedders : List NezPerceEmbedder :=
  [liloy, etqew, cicwaay, eeys, qeese, timneneki, timiipni, qeciyeewyew,
   neki, hi, cuukwe]

/-- The RE-canonical predicates: *yox̂ ke* obligatory on the complement
    edge. -/
def reCanonical : List NezPerceEmbedder :=
  allEmbedders.filter (·.yoxKeEdge == .obligatory)

/-- The simplex-canonical predicates: those permitting a bare complement
    (*yox̂ ke* prohibited or merely marginal) — [deal-2026] §6's
    "conservative generalization". -/
def simplexCanonical : List NezPerceEmbedder :=
  allEmbedders.filter (·.yoxKeEdge != .obligatory)

/-- Drift sentry: `reCanonical` contains exactly the eight predicates
    [deal-2026] lists at (27a–e), (27d), (42). -/
theorem reCanonical_membership :
    reCanonical = [liloy, etqew, cicwaay, eeys, qeese, timneneki,
                   timiipni, qeciyeewyew] := by decide

/-- Drift sentry: `simplexCanonical` contains exactly *neki*, *hi*,
    *cuukwe*. -/
theorem simplexCanonical_membership :
    simplexCanonical = [neki, hi, cuukwe] := by decide

/-- Partition: every embedder is either RE-canonical or
    simplex-canonical (no third category in [deal-2026]'s survey). -/
theorem allEmbedders_partitioned :
    allEmbedders = reCanonical ++ simplexCanonical := by decide

/-! ### Factivity generalisations (observation-level) -/

/-- All RE-canonical predicates are factive. [deal-2026] §3, §7. -/
theorem reCanonical_all_factive :
    reCanonical.all (·.factive) = true := by decide

/-- The factive simplex-canonical predicates: exactly *cuukwe* 'know'. -/
theorem factive_simplex_membership :
    simplexCanonical.filter (·.factive) = [cuukwe] := by decide

/-- The non-factive simplex-canonical predicates: exactly *neki* and
    *hi*. -/
theorem nonfactive_simplex_membership :
    simplexCanonical.filter (! ·.factive) = [neki, hi] := by decide

/-- Factivity does not predict RE-canonical status: *cuukwe* 'know' is
    factive but simplex-canonical ([deal-2026]'s central dissociation —
    in Nez Perce factivity is necessary but not sufficient for RE
    morphosyntax). -/
theorem cuukwe_factive_but_simplex :
    cuukwe.factive = true ∧ cuukwe ∈ simplexCanonical := by
  refine ⟨rfl, ?_⟩
  decide

/-! ### Relative-pronoun paradigm

The *yox̂/ko* paradigm from [deal-2016a], reproduced at [deal-2026] (22).
Cells are indexed by `Core.UD.Case` (Nom/Erg/Acc) × `Core.UD.Number`. -/

/-- A relative-pronoun cell from [deal-2026] (22). -/
structure RelativePronoun where
  case : UD.Case
  number : UD.Number
  forms : List String  -- multiple if idiolectal variation
  deriving Repr

/-- A relative pronoun bears its number slot (`HasNumber`). -/
instance : HasNumber RelativePronoun := ⟨fun rp => Number.fromUD rp.number⟩

def rp_nom_sg : RelativePronoun := ⟨.Nom, .Sing, ["yox̂"]⟩
def rp_nom_pl : RelativePronoun := ⟨.Nom, .Plur, ["yox̂me"]⟩
def rp_erg_sg : RelativePronoun := ⟨.Erg, .Sing, ["konim"]⟩
def rp_erg_pl : RelativePronoun := ⟨.Erg, .Plur, ["konmam"]⟩
def rp_acc_sg : RelativePronoun := ⟨.Acc, .Sing, ["konya"]⟩
def rp_acc_pl : RelativePronoun := ⟨.Acc, .Plur, ["konmana", "yox̂mene"]⟩

/-- The full paradigm: three cases × two numbers, six cells. -/
def relativePronounParadigm : List RelativePronoun :=
  [rp_nom_sg, rp_nom_pl, rp_erg_sg, rp_erg_pl, rp_acc_sg, rp_acc_pl]

/-- Drift sentry: the paradigm covers exactly the Nom/Erg/Acc ×
    Sing/Plur cells. -/
theorem paradigm_membership :
    (relativePronounParadigm.map (λ p => (p.case, p.number))) =
      [(.Nom, .Sing), (.Nom, .Plur), (.Erg, .Sing), (.Erg, .Plur),
       (.Acc, .Sing), (.Acc, .Plur)] := by decide

/-- The accusative-plural cell shows idiolectal variation: two attested
    forms. -/
theorem acc_pl_variants : rp_acc_pl.forms = ["konmana", "yox̂mene"] := rfl

end NezPerce.ClausalEmbedding
