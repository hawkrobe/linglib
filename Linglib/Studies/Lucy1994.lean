import Linglib.Semantics.Verb.Root.Defs
import Linglib.Semantics.Verb.Root.Arity
import Linglib.Semantics.ArgumentStructure.SalienceClass
import Linglib.Morphology.Exponence.Select

/-!
# Lucy 1994: The role of semantic value in lexical comparison

[lucy-1994] argues that lexical classes must be identified
*morpho-distributionally*, not denotationally: the notional class "motion
verbs", assembled by English intuition, coincides with no morphologically
defined Yucatec class. The diagnostic is which derivation a root requires
to form a transitive stem:

| Derivation | Predicate root class (p. 630) | Size (p. 629) |
|------------|-------------------------------|----------------|
| `=t` (affective) | agent salient          | well over 100  |
| `=∅` (zero)      | agent-patient salient  | some 500       |
| `=s` (causative) | patient salient        | fewer than 75  |

Positional roots (over 100) fall outside this three-way cut: they take the
positional derivation `=lah` (incompletive `=tal`) and are formally
interstitial — *čin* 'bend' also zero-derives a transitive (ex. (6)).
Notional motion roots land in the *smallest* predicate class, patient
salient (ex. (4)); at best the five `#`-marked roots lacking the `-Vl`
imperfective form "a formal class of 'motion verbs'" (p. 641), a
distinction invisible to the entailment grid.

## Main results

* `predicted_matches_attested`: applicability derived from
  (kind signature × arity) reproduces every derivation Lucy attests.
* `motion_roots_not_separate_class`: motion roots share their predicted
  class with plain state-change roots like *kíim* 'die'.
* `positional_crosscuts_transitiviser_classes`: the positional diagnostic
  overlaps `=∅` (*čin*) and the diagnostic gap (*kul*) — Lucy's classes
  are not a partition.
* `hash_not_signature_definable`: the `#` motion subclass is not a
  function of the entailment grid.

## Implementation notes

The reconstruction is two-dimensional — B&K-G kind signature × Coon root
arity ([beavers-koontz-garboden-2020]; [coon-2019]; both postdate Lucy and
serve as project-canonical substrate). Arity carries the agent-patient
class: Lucy's `=∅` roots "require two arguments" (p. 629) and are not
signature-homogeneous (*p'is* 'measure' is manner-only, *k'os* 'cut'
manner+result), so no feature configuration could carry the class. The
signature separates the two intransitive classes, matching the Sapir 1917
~ Fillmore 1968 ~ Perlmutter 1978 unaccusativity lineage Lucy cites
(p. 630). "Salience" is Lucy's term for "a set of default semantic values
in a root or stem that influence an overt case marking" (p. 628). Root
name strings follow Lucy's orthography. The `=t` class is inflated by
denominal and loanword verbalization (p. 629), so `=t` applicability is a
weaker signal of manner entailments than `=∅` or `=s` are of theirs.

The salience classes and the pair-level classifier
(`ArgumentStructure.SalienceClass.ofKinds`) are substrate
(`Semantics/ArgumentStructure/SalienceClass.lean`); this file supplies the
Yucatec roots, diagnostic operators, and attested derivations.
-/

namespace Lucy1994

open Verb ArgumentStructure Morphology

/-! ### Agent-salient roots (p. 629, ex. (1a)) -/

/-- síit' 'jump' (ex. (1a)). -/
def siit : Root := ⟨"síit'", {.hasManner "jumping"}, none, {}⟩

/-- ¢'iib' 'write' (p. 629). -/
def tziib : Root := ⟨"¢'iib'", {.hasManner "writing"}, none, {}⟩

/-- mìis 'sweep' (p. 629); denominal from 'broom'. -/
def miis : Root := ⟨"mìis", {.hasManner "sweeping"}, none, {}⟩

/-- čé'eh 'smile' (p. 629). -/
def cheh : Root := ⟨"čé'eh", {.hasManner "smiling"}, none, {}⟩

/-- páak 'weed' (p. 629). -/
def paak : Root := ⟨"páak", {.hasManner "weeding"}, none, {}⟩

/-! ### Agent-patient salient roots (p. 629, ex. (1b))

Root transitives. They carry no uniform signature: *kuč*, *p'is*, *ha¢*,
*loš* are manner-only (surface contact without entailed result, B&K-G's
*hit* type), while *k'os* 'cut' is manner+result (their *cut* type). -/

/-- kuč 'carry' (ex. (1b)). -/
def kuc : Root := ⟨"kuč", {.hasManner "carrying"}, none, {}⟩

/-- k'os 'cut' (p. 629); manner+result. -/
def kos : Root :=
  ⟨"k'os", {.hasManner "cutting", .becomesState "cut"}, none, {}⟩

/-- p'is 'measure' (p. 629); no entailed change of state. -/
def pis : Root := ⟨"p'is", {.hasManner "measuring"}, none, {}⟩

/-- ha¢ 'whip' (p. 629). -/
def hats : Root := ⟨"ha¢", {.hasManner "whipping"}, none, {}⟩

/-- loš 'punch' (p. 629); surface contact without entailed result. -/
def los : Root := ⟨"loš", {.hasManner "striking"}, none, {}⟩

/-! ### Patient-salient roots (ex. (2), pp. 629–630)

Lucy's list (2) is arranged in antonym pairs "listed in vertical
adjacency" (fn. 7): 'ah ~ wen, siih ~ kíim, tú'ub' ~ k'a'ah, ču'un ~
č'en, hó'op' ~ háaw. The order below is the list's. -/

/-- 'ah '(a)wake(n)' ('ah=s 'wake (someone)'). -/
def ah : Root := ⟨"'ah", {.becomesState "awake"}, none, {}⟩

/-- wen '(fall a)sleep' (ween=s 'put to sleep'); fn. 7 flags it as also
    denoting continuation in the state. -/
def wen : Root := ⟨"wen", {.becomesState "asleep"}, none, {}⟩

/-- siih 'be born' (siih=s 'give birth, bear'). -/
def siih : Root := ⟨"siih", {.becomesState "born"}, none, {}⟩

/-- kíim 'die' (ex. (1c); kíim=s 'kill'). -/
def kiim : Root := ⟨"kíim", {.becomesState "dead"}, none, {}⟩

/-- tú'ub' 'forget' (tú'ub'=s 'distract, cause to forget'). -/
def tuub : Root := ⟨"tú'ub'", {.becomesState "forgotten"}, none, {}⟩

/-- k'a'ah 'remember' (k'á'ah=s 'remind, mention, invoke'). -/
def kaah : Root := ⟨"k'a'ah", {.becomesState "remembered"}, none, {}⟩

/-- ču'un 'begin activity' (ču'un=s 'cause to begin'). -/
def chuun : Root := ⟨"ču'un", {.becomesState "begun"}, none, {}⟩

/-- č'en 'stop, cease' (č'en=s 'cause to stop, suspend'). -/
def chen : Root := ⟨"č'en", {.becomesState "ceased"}, none, {}⟩

/-- hó'op' 'begin, start' (hó'op'=s 'cause to begin'). -/
def hoop : Root := ⟨"hó'op'", {.becomesState "started"}, none, {}⟩

/-- háaw 'stop, cease, heal' (háaw=s 'stop, revoke, medicate'). -/
def haaw : Root := ⟨"háaw", {.becomesState "stopped"}, none, {}⟩

/-- hé'el 'rest, stop at' (hé'e(l)=s 'rest'). -/
def heel : Root := ⟨"hé'el", {.becomesState "rested"}, none, {}⟩

/-- p'át 'remain' (p'át=s 'abandon'). -/
def paat : Root := ⟨"p'át", {.becomesState "remaining"}, none, {}⟩

/-! ### Motion roots (ex. (4), p. 640)

"Locational-spatial state-change predicates": notionally motion, formally
plain members of the patient-salient class. The five `#`-marked roots
"do not — and CANNOT — take the `-Vl` suffix in the imperfective"; fn. 17
adds that *péek* and *'ú'ul* are also irregular in their agent-focused
perfective forms, "where they pattern like agent-salient roots". -/

/-- máan 'pass by' (`#`; máan=s 'pass, transfer, transport'). -/
def maan : Root := ⟨"máan", {.becomesState "past"}, none, {}⟩

/-- péek 'move, vibrate' (`#`; pek=s 'cause to move, vibrate'). -/
def peek : Root := ⟨"péek", {.becomesState "in-motion"}, none, {}⟩

/-- b'in 'go' (`#`; bi(n)=s 'take'). -/
def bin : Root := ⟨"b'in", {.becomesState "gone"}, none, {}⟩

/-- tàal 'come (here)' (`#`; tàa(l)=s 'bring'). -/
def taal : Root := ⟨"tàal", {.becomesState "come"}, none, {}⟩

/-- 'ú'ul 'arrive (here)' (`#`; 'ú'uh=s 'bring it to here'). -/
def uul : Root := ⟨"'ú'ul", {.becomesState "arrived"}, none, {}⟩

/-- 'ok 'enter, intrude' ('òok=s 'move it in(to)'). -/
def ok : Root := ⟨"'ok", {.becomesState "inside"}, none, {}⟩

/-- lúub' 'fall' (lúub'=s 'fell'). -/
def luub : Root := ⟨"lúub'", {.becomesState "fallen"}, none, {}⟩

/-- líik' '(a)rise, ascend' (lii(k)'=s 'raise, lift, put away'). -/
def liik : Root := ⟨"líik'", {.becomesState "risen"}, none, {}⟩

/-- ná'ak '(a)rise, ascend' (ná'ak=s 'raise'); distinct from náak
    'arrive, reach, hit', not sampled here. -/
def naak : Root := ⟨"ná'ak", {.becomesState "ascended"}, none, {}⟩

/-! ### Positional roots (ex. (7), p. 643) -/

/-- čin 'bow, bend down, bend over' (ex. (5)–(7)); zero-derives a
    transitive, ex. (6) 'I bent it'. -/
def cin : Root := ⟨"čin", {.hasState "bent"}, none, {}⟩

/-- kul 'sit' (p. 645, fn. 24: relational 'x is-seated [on y]'). -/
def kul : Root := ⟨"kul", {.hasState "seated"}, none, {}⟩

/-! ### Arity and class lists -/

/-- Roots attested forming a transitive stem by zero derivation: the
    sampled `=∅` predicate roots (p. 629) plus the positional *čin*
    (ex. (6)). -/
def rootTransitives : List Root := [kuc, kos, pis, hats, los, cin]

/-- Coon arity for the sample: zero-derivers select a theme (√TV);
    every other sampled root is intransitive. Sample-local — the
    assignment defaults to `noTheme` off the sample. -/
def arity (r : Root) : Root.Arity :=
  if r ∈ rootTransitives then .selectsTheme else .noTheme

/-- The sampled agent-salient roots. -/
def agentSalientRoots : List Root := [siit, tziib, miis, cheh, paak]

/-- The sampled agent-patient salient (`=∅` predicate) roots. -/
def agentPatientSalientRoots : List Root := [kuc, kos, pis, hats, los]

/-- The sampled patient-salient roots of list (2), in Lucy's order. -/
def patientSalientRoots : List Root :=
  [ah, wen, siih, kiim, tuub, kaah, chuun, chen, hoop, haaw, heel, paat]

/-- The sampled motion roots of ex. (4). -/
def motionRoots : List Root :=
  [maan, peek, bin, taal, uul, ok, luub, liik, naak]

/-- The `#`-marked subset of ex. (4): the roots lacking the `-Vl`
    imperfective — for Lucy, the only candidate "formal class of 'motion
    verbs'" (p. 641). -/
def hashMarked : List Root := [maan, peek, bin, taal, uul]

/-- The sampled positional roots. -/
def positionalRoots : List Root := [cin, kul]

/-- Every sampled root. -/
def sampledRoots : List Root :=
  agentSalientRoots ++ agentPatientSalientRoots ++ patientSalientRoots ++
    motionRoots ++ positionalRoots

/-! ### Diagnostic operators -/

/-- A diagnostic derivational operator: exponent plus structural
    applicability condition, with bundled decidability so profiles
    compute (the inventory holds heterogeneous conditions, so a
    per-operator instance cannot serve). Selection machinery comes from
    the `Morphology.Exponence.Rule` instance. -/
structure DiagOp where
  /-- The suffix, in Lucy's orthography. -/
  exponent : String
  /-- The structural condition on the root. -/
  Applies : Root → Prop
  /-- Bundled decidability of the condition. -/
  decApplies : DecidablePred Applies

instance : Exponence.Rule DiagOp Root String where
  exponent := DiagOp.exponent
  Applies := DiagOp.Applies

instance : DecidableRel (Exponence.Applies : DiagOp → Root → Prop) :=
  fun op r => op.decApplies r

@[simp] theorem applies_iff (op : DiagOp) (r : Root) :
    Exponence.Applies op r ↔ op.Applies r := Iff.rfl

/-- Affective `=t`: transitivises an agent-salient root by adding a
    patient argument. -/
def affectiveT : DiagOp :=
  ⟨"=t", fun r => IsAgentSalient r.kinds (arity r), inferInstance⟩

/-- Zero derivation `=∅`: the root alone supports a transitive stem. -/
def zeroDeriv : DiagOp :=
  ⟨"=∅", fun r => arity r = .selectsTheme, inferInstance⟩

/-- Causative `=s`: transitivises a patient-salient root by adding an
    agent argument. -/
def causativeS : DiagOp :=
  ⟨"=s", fun r => IsPatientSalient r.kinds (arity r), inferInstance⟩

/-- Positional derivation, realized `=lah` ~ `=tal` by status (the
    `=tal` incompletive is the anomalous member, apparently compounding
    with *tàal* 'come'). -/
def positionalLah : DiagOp :=
  ⟨"=lah", fun r => IsPositional r.kinds, inferInstance⟩

/-- The diagnostic inventory, in the order of Lucy's presentation:
    the three transitivisers of ex. (1), then the positional. -/
def inventory : List DiagOp :=
  [affectiveT, zeroDeriv, causativeS, positionalLah]

/-- The exponents of the inventory's applicable operators at `r`, in
    inventory order — the root's predicted derivational behaviour. -/
def predictedExponents (r : Root) : List String :=
  (Exponence.applicable inventory r).map DiagOp.exponent

/-! ### Predicted vs attested derivations -/

/-- The derivations Lucy attests per sampled root: `=t` for the p. 629
    activity roots, `=∅` for the root transitives, `=s` for lists (2)
    and (4), `=lah` for positionals — with *čin* attested for both `=∅`
    (ex. (6)) and `=lah` (ex. (5)). -/
def attestations : List (Root × List String) :=
  [ (siit, ["=t"]), (tziib, ["=t"]), (miis, ["=t"]), (cheh, ["=t"]),
    (paak, ["=t"]),
    (kuc, ["=∅"]), (kos, ["=∅"]), (pis, ["=∅"]), (hats, ["=∅"]),
    (los, ["=∅"]),
    (ah, ["=s"]), (wen, ["=s"]), (siih, ["=s"]), (kiim, ["=s"]),
    (tuub, ["=s"]), (kaah, ["=s"]), (chuun, ["=s"]), (chen, ["=s"]),
    (hoop, ["=s"]), (haaw, ["=s"]), (heel, ["=s"]), (paat, ["=s"]),
    (maan, ["=s"]), (peek, ["=s"]), (bin, ["=s"]), (taal, ["=s"]),
    (uul, ["=s"]), (ok, ["=s"]), (luub, ["=s"]), (liik, ["=s"]),
    (naak, ["=s"]),
    (cin, ["=∅", "=lah"]), (kul, ["=lah"]) ]

/-- The derivations predicted from (signature × arity) reproduce every
    derivation Lucy attests. Unlike the classifier theorems below, this
    check is against a column transcribed from the paper, independent of
    the encoding. -/
theorem predicted_matches_attested :
    ∀ p ∈ attestations, predictedExponents p.1 = p.2 := by decide

/-! ### The derived classification -/

/-- A root's predicted salience class. -/
def predictedClass (r : Root) : Option SalienceClass :=
  SalienceClass.ofKinds r.kinds (arity r)

/-- The transitiviser each salience class requires. -/
def exponentOf : SalienceClass → String
  | .agent => "=t"
  | .agentPatient => "=∅"
  | .patient => "=s"

/-- Predicted derivational behaviour decomposes as the class's
    transitiviser followed by the positional derivation when the
    signature licenses it — the applicability profile *is* the
    classification, plus the cross-cutting positional diagnostic. -/
theorem predictedExponents_eq (r : Root) :
    predictedExponents r =
      (predictedClass r).toList.map exponentOf ++
        (if IsPositional r.kinds then ["=lah"] else []) := by
  simp only [predictedExponents, predictedClass, Exponence.applicable,
    applies_iff, inventory, affectiveT, zeroDeriv, causativeS,
    positionalLah, List.filter_cons, List.filter_nil, decide_eq_true_eq,
    SalienceClass.ofKinds]
  generalize r.kinds = s
  generalize arity r = a
  revert s a
  decide

theorem agentSalient_class :
    ∀ r ∈ agentSalientRoots, predictedClass r = some .agent := by decide

theorem agentPatientSalient_class :
    ∀ r ∈ agentPatientSalientRoots,
      predictedClass r = some .agentPatient := by decide

theorem patientSalient_class :
    ∀ r ∈ patientSalientRoots, predictedClass r = some .patient := by decide

/-- The `=∅` class is not signature-homogeneous (*p'is* manner-only vs
    *k'os* manner+result) — root transitivity is carried by arity, not
    by any feature configuration. -/
theorem rootTransitives_not_signature_uniform :
    ∃ r ∈ agentPatientSalientRoots, ∃ r' ∈ agentPatientSalientRoots,
      r.kinds ≠ r'.kinds := by decide

/-! ### The "motion verbs" non-class -/

/-- Lucy's central typological point: notional motion roots do not form
    their own salience class — each is classified exactly as the plain
    state-change root *kíim* 'die'. -/
theorem motion_roots_not_separate_class :
    ∀ r ∈ motionRoots, predictedClass r = predictedClass kiim := by decide

/-- The `#` subclass — Lucy's only candidate formal motion class — is
    not a function of the entailment grid: *péek* (`#`) and *lúub'*
    (plain) agree in signature and arity. The class is carried by an
    idiosyncratic morphological gap, not by lexical semantics. -/
theorem hash_not_signature_definable :
    ∃ r ∈ hashMarked, ∃ r' ∈ motionRoots,
      r' ∉ hashMarked ∧ r.kinds = r'.kinds ∧ arity r = arity r' := by
  decide

/-! ### Positional interstitiality -/

/-- The positional diagnostic cross-cuts the transitiviser cut: *čin* is
    positional yet zero-derives a transitive (agent-patient salient),
    while *kul* is positional and outside the cut altogether. Lucy's
    classes are diagnostics, not a partition. -/
theorem positional_crosscuts_transitiviser_classes :
    IsPositional cin.kinds ∧ predictedClass cin = some .agentPatient ∧
    IsPositional kul.kinds ∧ predictedClass kul = none := by decide

/-! ### Closure robustness -/

/-- For cause-free roots — every root in this sample — collocational
    closure does not change the predicted class. -/
theorem predictedClass_closure_invariant (r : Root) (h : ¬ r.HasCause) :
    SalienceClass.ofKinds r.closedKinds (arity r) = predictedClass r :=
  SalienceClass.ofKinds_close r.kinds (arity r) h

end Lucy1994
