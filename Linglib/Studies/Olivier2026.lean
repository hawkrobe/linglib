import Linglib.Syntax.Minimalist.Phase.Basic
import Linglib.Semantics.ArgumentStructure.AuxiliarySelection

/-!
# Auxiliary Switch as person-identity matching: [olivier-2026]

[olivier-2026] analyses *Auxiliary Switch* (AS) — BE in place of HAVE on a modal in a
compound tense whose infinitive is unaccusative or reflexive (2b), (3b) — as ordinary
auxiliary selection across a transparent restructuring domain. Auxiliary selection
itself ([olivier-2025b], §6.2) is not driven by argument structure: a person value
carries the referential identity of its bearer (54), Voice's valued φ-set is
redistributed by head splitting onto `vAux[uPers]` and `VoicePrt[uGen, uNum]` (57),
and the Vocabulary Items (55) insert BE when `[vAux + T]` carry the same identity,
HAVE elsewhere — so unaccusatives (59) and bound reflexives (60) take BE and
transitives (61) HAVE. In a restructuring clause (40) the auxiliary belongs to the
modal, and whether Voice(*) KEEPs its φ-features or SHAREs them with vMOD
([ouali-2008]'s operations, (45), the substrate's `TransferStyle`) decides both clitic
climbing and AS at once: KEEP leaves vAux featureless, HAVE (69), (74); SHARE brings
the bound reflexive's identity — the subject's — to vAux, BE (71), (76).

`compound` is the simple compound tense and `matrixAux` the restructuring one; the
theorems derive the intro's conditions 3 and α (`share_switch_iff_selectsBe`,
`reflexive_switch_iff_climbs`), Table 1's absence of AS without climbing, the
optionality of AS with unaccusatives (§7.2), the prepositional clitics that climb
without triggering AS (§7.3: *y/ci*, *en/ne*, *lui/gli* introduce no coreferential
person value; a "rich" vAux also probing the internal argument gives the Italian and
Sardinian speakers' BE), and the varieties of §7.1 as the transfers they admit. Out of
scope: conditions 1–2, which the structure (40) presupposes; gender/number on the
participle; impersonal *si* (fn. 53); the corpus counts of §3 (Tables 1–3) beyond the
qualitative generalisations stated there.
-/

namespace Olivier2026

open Minimalist (TransferStyle)
open ArgumentStructure.AuxiliarySelection

/-! ### Person values with identity -/

/-- `[Person: X [ID: α]]` (54): a person value with the referential index of its bearer;
two values match for the Vocabulary Items (55) when their indices agree. -/
structure IndexedPerson where
  person : Person
  id : ℕ
  deriving DecidableEq, Repr

/-- The clitics the paper distinguishes: the reflexive *se/si*, bound by the external
argument through Voice* and so sharing its identity (54b), (60); the accusative *le/lo*
and dative *lui/gli*, with identities of their own; the locative *y/ci* and partitive
*en/ne*, which value a P-feature and carry no coreferential person (§7.3); and (65)'s
*je ne m'aurais pas foutu dehors*, a reflexive whose identity is not its binder's
(§6.2.3). -/
inductive Clitic
  | reflexive | detachedReflexive | accusative | dative | locative | partitive
  deriving DecidableEq, Repr, Fintype

/-- The "prepositional" clitics of §3.2.2 — locative, partitive and non-reflexive dative —
which pronominalise PP-constituents and never introduce the subject's identity. -/
def Clitic.prepositional : Clitic → Bool
  | .locative | .partitive | .dative => true
  | _ => false

/-- A clause by the class of its verb and its clitic, if any. -/
structure Clause where
  verb : TransitivityClass
  clitic : Option Clitic := none
  deriving DecidableEq, Repr

/-- The external argument's value carries index `0`, the internal argument's `1`, and any
other bearer's — a cognate object (fn. 26), a detached reflexive — `2`. -/
def externalArg (ea : Person) : IndexedPerson := ⟨ea, 0⟩

/-- The internal argument's value. -/
def internalArg (ia : Person) : IndexedPerson := ⟨ia, 1⟩

/-- The person/identity Voice(*) comes to bear after probing (58)–(61): the internal
argument's for unaccusatives and transitives (a DP or an accusative clitic), the bound
reflexive's — the external argument's identity — for reflexive verbs (60), the identity
of its own for a detached reflexive (65), and a default value for the cognate object of
unergatives (fn. 26). -/
def voicePerson (ea ia : Person) : Clause → IndexedPerson
  | ⟨.unaccusative, _⟩ | ⟨.transitive, _⟩ => internalArg ia
  | ⟨.reflexive, some .detachedReflexive⟩ => ⟨ea, 2⟩
  | ⟨.reflexive, _⟩ => externalArg ea
  | ⟨.unergative, _⟩ => ⟨.third, 2⟩

/-- T's person/identity: the external argument's, or the raised internal argument's for
unaccusatives (59). -/
def tPerson (ea ia : Person) : TransitivityClass → IndexedPerson
  | .unaccusative => internalArg ia
  | _ => externalArg ea

/-- Vocabulary Items (55): BE when `vAux` and `T` carry the same identity, HAVE elsewhere —
HAVE is the default auxiliary. -/
def insert (vAux : Option IndexedPerson) (t : IndexedPerson) : PerfectAux :=
  if vAux.map (·.id) = some t.id then .be else .have

/-! ### Simple compound tenses (§6.2.2) -/

/-- The auxiliary of a simple compound tense (58): Voice splits, so vAux carries Voice's
person/identity, and T carries the subject's. -/
def compound (ea ia : Person) (cl : Clause) : PerfectAux :=
  insert (some (voicePerson ea ia cl)) (tPerson ea ia cl.verb)

/-- (59)–(61): identity matching yields the canonical distribution — BE with unaccusatives
and reflexives, HAVE with transitives and unergatives — for every pair of persons. -/
theorem compound_eq_canonical (ea ia : Person) (c : TransitivityClass) :
    compound ea ia ⟨c, none⟩ = canonicalSelection c := by
  revert ea ia c; decide

/-- (52): *Jean s'est regardé* against *Jean l'a regardé* — the same third-person value,
identities matching only under binding. -/
example : compound .third .third ⟨.reflexive, some .reflexive⟩ = .be ∧
    compound .third .third ⟨.transitive, some .accusative⟩ = .have := by decide

/-- (65): a reflexive whose identity is not its binder's takes HAVE. -/
example : compound .first .first ⟨.reflexive, some .detachedReflexive⟩ = .have := by decide

/-! ### Restructuring clauses (§5, §7) -/

/-- A modal in a compound tense over an infinitive (40): the embedded clause, whether
Voice(*) KEEPs its φ-features or SHAREs them with vMOD (45), and whether a vAux that
receives a prepositional clitic's P-feature also receives the internal argument's person
(§7.3's "rich" vAux; DONATE plays no role in the paper). -/
structure Restructuring where
  embedded : Clause
  transfer : TransferStyle
  richAux : Bool := true
  deriving DecidableEq, Repr

/-- A clitic climbs iff its φ-features are shared upwards — it spells out on the head that
bears them (45), clitic reduplication showing the copies (41)–(44). -/
def Restructuring.climbs (r : Restructuring) : Prop :=
  r.embedded.clitic.isSome ∧ r.transfer = .share

instance (r : Restructuring) : Decidable r.climbs := inferInstanceAs (Decidable (_ ∧ _))

/-- The person/identity vAux receives after splitting vMOD: nothing under KEEP (69), (74);
under SHARE, Voice's — unless a prepositional clitic climbed to a "poor" vAux, which then
carries only its P-feature (§7.3). -/
def Restructuring.vAuxPerson (ea ia : Person) (r : Restructuring) : Option IndexedPerson :=
  match r.transfer with
  | .share =>
    if (r.embedded.clitic.map Clitic.prepositional).getD false ∧ !r.richAux then none
    else some (voicePerson ea ia r.embedded)
  | _ => none

/-- The modal's auxiliary. -/
def Restructuring.matrixAux (ea ia : Person) (r : Restructuring) : PerfectAux :=
  insert (r.vAuxPerson ea ia) (tPerson ea ia r.embedded.verb)

/-- Auxiliary Switch: the modal surfaces with BE. -/
def Restructuring.Switch (ea ia : Person) (r : Restructuring) : Prop :=
  r.matrixAux ea ia = .be

instance (ea ia : Person) (r : Restructuring) : Decidable (r.Switch ea ia) :=
  inferInstanceAs (Decidable (_ = _))

/-- (69), (74): under KEEP vAux is featureless, so the modal takes HAVE and no clitic
climbs. -/
theorem keep_have (ea ia : Person) (r : Restructuring) (h : r.transfer = .keep) :
    r.matrixAux ea ia = .have ∧ ¬ r.climbs := by
  refine ⟨?_, λ hc => TransferStyle.noConfusion (h.symm.trans hc.2)⟩
  simp [Restructuring.matrixAux, Restructuring.vAuxPerson, h, insert]

/-- Condition 3 derived: under SHARE, with no prepositional clitic, the modal switches to BE
exactly when the infinitive is a BE-selecting predicate (71), (76) versus (61) — the
identity vAux inherits is T's iff Voice probed the subject's bearer. -/
theorem share_switch_iff_selectsBe (ea ia : Person) (c : TransitivityClass)
    (cl : Option Clitic) (hcl : cl ≠ some .detachedReflexive)
    (hp : (cl.map Clitic.prepositional).getD false = false) (rich : Bool) :
    Restructuring.Switch ea ia ⟨⟨c, cl⟩, .share, rich⟩ ↔ SelectsBe c := by
  rcases cl with _ | cl
  · revert ea ia c rich; decide
  · cases cl <;> first | exact absurd rfl hcl | (revert ea ia c rich; decide) | cases hp

/-- Condition α and Table 1: with a reflexive infinitive, AS obtains exactly when the
reflexive clitic climbs — (19b)/(20a) against (19a)/(20b) — so there is no AS without
climbing. -/
theorem reflexive_switch_iff_climbs (ea ia : Person) (t : TransferStyle) (rich : Bool) :
    Restructuring.Switch ea ia ⟨⟨.reflexive, some .reflexive⟩, t, rich⟩ ↔
      Restructuring.climbs ⟨⟨.reflexive, some .reflexive⟩, t, rich⟩ := by
  revert ea ia rich; cases t <;> decide

/-- §7.2: with an unaccusative infinitive and no clitic nothing but the auxiliary
distinguishes SHARE (75)/(76) from KEEP (73)/(74) — AS is optional. -/
theorem unaccusative_optional (ea ia : Person) (rich : Bool) :
    Restructuring.matrixAux ea ia ⟨⟨.unaccusative, none⟩, .share, rich⟩ = .be ∧
      Restructuring.matrixAux ea ia ⟨⟨.unaccusative, none⟩, .keep, rich⟩ = .have := by
  revert ea ia rich; decide

/-- §7.3: a prepositional clitic climbing out of an unaccusative leaves HAVE when vAux
carries only its P-feature ((25)–(27), (36)), BE when vAux also probes the internal
argument ((28)–(30), (37a)). -/
theorem prepositional_climbing (ea ia : Person) (cl : Clitic) (hcl : cl.prepositional = true)
    (rich : Bool) :
    Restructuring.climbs ⟨⟨.unaccusative, some cl⟩, .share, rich⟩ ∧
      (Restructuring.Switch ea ia ⟨⟨.unaccusative, some cl⟩, .share, rich⟩ ↔ rich = true) := by
  revert ea ia cl rich; decide

/-- (31), [cardinaletti-shlonsky-2004]'s *lo sarei voluto andare a trovare* aside: an
accusative clitic climbs out of a transitive infinitive without AS — its identity is
not the subject's. -/
theorem accusative_climbing (ea ia : Person) (rich : Bool) :
    Restructuring.climbs ⟨⟨.transitive, some .accusative⟩, .share, rich⟩ ∧
      Restructuring.matrixAux ea ia ⟨⟨.transitive, some .accusative⟩, .share, rich⟩ = .have := by
  revert ea ia rich; decide

/-! ### Varieties (§7.1) -/

/-- The grammars the paper compares by the transfers they admit: Modern French only KEEP,
earlier French and Standard Italian both, Sardinian only SHARE. -/
inductive Variety
  | modernFrench | earlierFrench | standardItalian | sardinian
  deriving DecidableEq, Repr, Fintype

/-- The transfer operations a variety admits. -/
def Variety.admits : Variety → TransferStyle → Prop
  | .modernFrench, t => t = .keep
  | .sardinian, t => t = .share
  | _, t => t = .keep ∨ t = .share

instance : (v : Variety) → (t : TransferStyle) → Decidable (v.admits t)
  | .modernFrench, _ | .sardinian, _ => inferInstanceAs (Decidable (_ = _))
  | .earlierFrench, _ | .standardItalian, _ => inferInstanceAs (Decidable (_ ∨ _))

/-- (38): in Sardinian the reflexive clitic climbs and the modal takes BE, obligatorily. -/
theorem sardinian_reflexive (ea ia : Person) (r : Restructuring)
    (hv : Variety.sardinian.admits r.transfer)
    (he : r.embedded = ⟨.reflexive, some .reflexive⟩) : r.climbs ∧ r.Switch ea ia := by
  obtain ⟨e, t, rich⟩ := r
  have ht : t = .share := hv
  have he' : e = ⟨.reflexive, some .reflexive⟩ := he
  subst ht he'; revert ea ia rich; decide

/-- Modern French: KEEP alone yields neither climbing nor AS — (2a), (3a); the attested AS
of §3.3 is the SHARE derivation (71) surfacing in a grammar that does not usually use it. -/
theorem modernFrench_no_switch (ea ia : Person) (r : Restructuring)
    (hv : Variety.modernFrench.admits r.transfer) : ¬ r.climbs ∧ ¬ r.Switch ea ia := by
  have hk : r.transfer = .keep := hv
  have := keep_have ea ia r hk
  exact ⟨this.2, λ h => by simp [Restructuring.Switch, this.1] at h⟩

end Olivier2026
