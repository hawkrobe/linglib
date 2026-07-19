import Linglib.Morphology.Realization
import Mathlib.Tactic.DeriveFintype

/-!
# Arad 2005: root-derived vs word-derived, and the locality of root
interpretation
[arad-2005]

The √sgr family (her (5) in Ch. 7): one root, six listed formations across
verbal and nominal patterns — *sagar* 'close', *hisgir* 'extradite',
*histager* 'cocoon oneself', *seger* 'closure', *sograyim* 'parentheses',
*misgeret* 'frame'. Multiple Contextualized Meaning is allosemy of the root
across patterns (`sgr_mcm`); the √qlt nominal table (her (28) in Ch. 3) is
the second witness (`qlt_mcm`).

The lexeme grain and the root grain are related by arrows, not identity: no
strict hom merges any two of the lexemes into any target — their contextwise
interpretations clash (`no_strict_merger`) — but the six root-derived
lexemes lax-merge into the root's Encyclopedia entry
(`direct_lax_merger`): family, not identity.

**The denominal verb *misger*** 'to frame' (her (6)) is derived from the
noun *misgeret*, not from the root: no lax hom carries the full lexicon into
the root's entry, because *misger* is not among the root's own realizations
in any pattern (`misger_blocked`) — her interference argument. Its meaning
is instead the compositional image of the noun's (`misger_locality`), while
the root-derived lexemes' meanings are unanalyzable atoms
(`root_derived_atomic`) — her locality constraint (8) in Ch. 7: roots are
assigned an interpretation at the first category-assigning head, and the
interpretation is carried along thereafter.

## Main results

* `sgr_mcm`, `qlt_mcm` — Multiple Contextualized Meaning as root allosemy.
* `no_strict_merger` — no two sgr-lexemes strict-merge into any target.
* `direct_lax_merger` — the root-derived lexemes lax-merge into the root.
* `misger_blocked` — the denominal verb blocks a lax merger of the full
  lexicon: it is not a realization of the root.
* `misger_locality`, `root_derived_atomic` — word-derived meaning is the
  compositional image of the base noun's; root-derived meanings are atoms.
-/

namespace Arad2005

open Morphology Morphology.Realization

/-! ### The √sgr family -/

/-- The patterns of the √sgr family ((5)), plus the denominal verb pattern
CiCCeC of (6). -/
inductive Pattern
  | caCaC | hiCCiC | hitCaCCeC | ceCeC | coCCayim | miCCeCet | ciCCeC
  deriving DecidableEq, Fintype, Repr

/-- Meanings: the root-derived listed atoms of (5), plus the compositional
layer `vOf m` — 'to do something with an m' — for word-derived verbs. -/
inductive Meaning
  | close | extradite | cocoonOneself | closure | parentheses | frame
  | vOf (m : Meaning)
  deriving DecidableEq, Repr

/-- The seven lexemes: the six root-derived formations of (5) and the
noun-derived *misger* of (6). -/
inductive SgrLex
  | sagar | hisgir | histager | seger | sograyim | misgeret | misger
  deriving DecidableEq, Fintype, Repr

/-- The single root. -/
inductive Sqrt | sgr
  deriving DecidableEq, Fintype, Repr

/-- Each lexeme's home pattern. -/
def SgrLex.pattern : SgrLex → Pattern
  | .sagar => .caCaC | .hisgir => .hiCCiC | .histager => .hitCaCCeC
  | .seger => .ceCeC | .sograyim => .coCCayim | .misgeret => .miCCeCet
  | .misger => .ciCCeC

/-- Each lexeme's form. -/
def SgrLex.form : SgrLex → String
  | .sagar => "sagar" | .hisgir => "hisgir" | .histager => "histager"
  | .seger => "seger" | .sograyim => "sograyim" | .misgeret => "misgeret"
  | .misger => "misger"

/-- Each lexeme's meaning: listed atoms for the root-derived six, the
compositional 'to frame' for the noun-derived verb. -/
def SgrLex.meaning : SgrLex → Meaning
  | .sagar => .close | .hisgir => .extradite | .histager => .cocoonOneself
  | .seger => .closure | .sograyim => .parentheses | .misgeret => .frame
  | .misger => .vOf .frame

/-- The lexeme-grain system: each lexeme licensed in its home pattern
only. -/
def sgrLexemes : Realization.Interpreted SgrLex Pattern String Meaning where
  realize := fun l c => if c = l.pattern then {l.form} else ∅
  interp := fun l c => if c = l.pattern then {l.meaning} else ∅

/-- The root-grain system: √sgr's own Encyclopedia entry ((5)) — the six
direct cells. The denominal pattern CiCCeC is empty: the root has no
root-derived formation there. -/
def sgrRoot : Realization.Interpreted Sqrt Pattern String Meaning where
  realize := fun _ c =>
    match c with
    | .caCaC => {"sagar"} | .hiCCiC => {"hisgir"}
    | .hitCaCCeC => {"histager"} | .ceCeC => {"seger"}
    | .coCCayim => {"sograyim"} | .miCCeCet => {"misgeret"}
    | .ciCCeC => ∅
  interp := fun _ c =>
    match c with
    | .caCaC => {.close} | .hiCCiC => {.extradite}
    | .hitCaCCeC => {.cocoonOneself} | .ceCeC => {.closure}
    | .coCCayim => {.parentheses} | .miCCeCet => {.frame}
    | .ciCCeC => ∅

/-- Multiple Contextualized Meaning is root allosemy: √sgr's interpretation
varies across patterns. -/
theorem sgr_mcm : sgrRoot.IsAllosemous .sgr := by decide

/-! ### Grain arrows -/

private theorem interp_clash :
    ∀ l l' : SgrLex, l ≠ l' →
      sgrLexemes.interp l l.pattern ≠ sgrLexemes.interp l' l.pattern := by
  decide

/-- No strict hom into any target merges two distinct sgr-lexemes: their
contextwise interpretations clash at the home cell
(`Interpreted.Hom.interp_eq_of_onRoot_eq`). At the lexeme grain, all seven
are genuinely distinct indices. -/
theorem no_strict_merger {R₂ C₂ : Type*}
    {T : Realization.Interpreted R₂ C₂ String Meaning}
    (φ : Realization.Interpreted.Hom sgrLexemes T) {l l' : SgrLex}
    (h : l ≠ l') : φ.onRoot l ≠ φ.onRoot l' :=
  fun he => interp_clash l l' h (φ.interp_eq_of_onRoot_eq he l.pattern)

/-- The root-derived sublexicon of (5). -/
inductive Direct | sagar | hisgir | histager | seger | sograyim | misgeret
  deriving DecidableEq, Fintype, Repr

/-- The inclusion into the full lexicon. -/
def Direct.toSgr : Direct → SgrLex
  | .sagar => .sagar | .hisgir => .hisgir | .histager => .histager
  | .seger => .seger | .sograyim => .sograyim | .misgeret => .misgeret

/-- The lexeme grain restricted to the root-derived six. -/
def sgrDirect : Realization.Interpreted Direct Pattern String Meaning where
  realize := fun l c => sgrLexemes.realize l.toSgr c
  interp := fun l c => sgrLexemes.interp l.toSgr c

/-- The six root-derived lexemes lax-merge into the root's Encyclopedia
entry: each one's form and meaning are among the root's, at its own pattern.
Family membership without identity — the lexeme→√ coarsening arrow. -/
theorem direct_lax_merger :
    Nonempty (Realization.Interpreted.LaxHom sgrDirect sgrRoot) :=
  ⟨⟨fun _ => .sgr, id, by decide, by decide⟩⟩

/-- **The denominal verb blocks the merger** (her interference argument): no
lax hom carries the full lexicon into the root's entry, because *misger* is
not among √sgr's realizations in any pattern — it enters the family only
through the noun *misgeret*. -/
theorem misger_blocked
    (φ : Realization.Interpreted.LaxHom sgrLexemes sgrRoot) : False := by
  have h := φ.realize_sub .misger .ciCCeC
  cases hr : φ.onRoot .misger
  cases hc : φ.onCtx .ciCCeC <;> rw [hr, hc] at h <;>
    revert h <;> decide

/-! ### Locality ((8)): assigned at first categorization, carried along -/

/-- *misger*'s meaning is the compositional image of *misgeret*'s — 'to X'
applied to the noun's fixed interpretation, per the locality constraint: the
interpretation assigned at the noun's categorization is carried along into
the denominal verb. -/
theorem misger_locality :
    sgrLexemes.interp .misger Pattern.ciCCeC
      = (sgrLexemes.interp .misgeret Pattern.miCCeCet).image Meaning.vOf := by
  decide

private def Meaning.isDerived : Meaning → Bool
  | .vOf _ => true
  | _ => false

/-- Root-derived meanings are unanalyzable atoms: none is the compositional
image of another formation's meaning — they are listed against the root,
fixed at first categorization. -/
theorem root_derived_atomic :
    ∀ l : SgrLex, l ≠ .misger → ∀ c,
      ∀ m ∈ sgrLexemes.interp l c, m.isDerived = false := by
  decide

/-! ### The √qlt witness ((28), (61b)) -/

/-- √qlt's nominal patterns ((28)) and its two verbal patterns ((61b)). -/
inductive QPattern
  | ceCeC | maCCeC | miCCaC | taCCiC | caCeCet | p1 | p5
  deriving DecidableEq, Fintype, Repr

/-- √qlt's listed meanings: *qelet* 'input', *maqlet* 'receiver', *miqlat*
'shelter, asylum', *taqlit* '(vinyl) record', *qaletet* 'cassette', *qalat*
'absorb', *hiqlit* 'record'. -/
inductive QMeaning
  | input | receiver | shelter | vinylRecord | cassette | absorb | recordV
  deriving DecidableEq, Fintype, Repr

/-- The single root. -/
inductive QSqrt | qlt
  deriving DecidableEq, Fintype, Repr

/-- √qlt's Encyclopedia entry across its seven attested patterns. -/
def qltRoot : Realization.Interpreted QSqrt QPattern String QMeaning where
  realize := fun _ c =>
    match c with
    | .ceCeC => {"qelet"} | .maCCeC => {"maqlet"} | .miCCaC => {"miqlat"}
    | .taCCiC => {"taqlit"} | .caCeCet => {"qaletet"}
    | .p1 => {"qalat"} | .p5 => {"hiqlit"}
  interp := fun _ c =>
    match c with
    | .ceCeC => {.input} | .maCCeC => {.receiver} | .miCCaC => {.shelter}
    | .taCCiC => {.vinylRecord} | .caCeCet => {.cassette}
    | .p1 => {.absorb} | .p5 => {.recordV}

/-- The √qlt table is a second MCM witness: seven patterns, seven listed
meanings — root allosemy at scale. -/
theorem qlt_mcm : qltRoot.IsAllosemous .qlt := by decide

end Arad2005
