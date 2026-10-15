import Proof.Amplification.RecoveryRootIterationSemantics
import Proof.Amplification.RecoveryRootDigitInput

/-! The fixed outer digit-loop machine. Only the stream tape moves between
rounds; each arithmetic body receives and returns the same reset workspace. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRootLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev bodyStates := Fintype.card (RecoveryCalls.Control RecoveryRootRound.sizes)
def bodySlots (i : Fin 13) : Fin 15 := i.natAdd 2
def readerSlots : Fin 1 → Fin 15 := fun _ => 1

theorem bodySlots_injective : Function.Injective bodySlots := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  simpa [bodySlots] using hv

theorem readerSlots_injective : Function.Injective readerSlots := by decide

def tapes (original stream : List Bool) (s : Store) : Fin 15 → List Bool :=
  Fin.addCases (m := 2) (n := 13) (motive := fun _ => List Bool) ![original, stream] s.tapes

def heads (position : Nat) : Fin 15 → Nat :=
  Fin.addCases (m := 2) (n := 13) (motive := fun _ => Nat) ![0, position] (fun _ => 0)

def config {states : Nat} (q : Fin states) (original stream : List Bool) (s : Store)
    (position : Nat) : Configuration 15 states := ⟨q, heads position, tapes original stream s⟩

private theorem pick_none {t u : Nat} (slot : Fin t → Fin u) (i : Fin u) (h : ∀ j, slot j ≠ i) :
    RecoveryFocus.pick slot i = none := by
  classical
  have hn : ¬∃ j, slot j = i := by simpa using h
  simp [RecoveryFocus.pick, hn]

private theorem body_other (i : Fin 2) : RecoveryFocus.pick bodySlots (i.castAdd 13) = none := by
  apply pick_none
  intro j he
  have hv := congrArg Fin.val he
  simp only [bodySlots, Fin.val_natAdd, Fin.val_castAdd] at hv
  omega

private theorem reader_other_body (i : Fin 13) : RecoveryFocus.pick readerSlots (i.natAdd 2) = none := by
  apply pick_none
  intro j he
  have hv := congrArg Fin.val he
  simp only [readerSlots, Fin.val_one, Fin.val_natAdd] at hv
  omega

theorem body_config {states : Nat} (original stream : List Bool) (before after : Store) (position : Nat)
    (c : Configuration 13 states) (hh : ∀ i, c.heads i = 0) (ht : c.tapes = after.tapes) :
    RecoveryFocus.config bodySlots (heads position) (tapes original stream before) c =
      config c.control original stream after position := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m := 2) (n := 13) (motive := fun k : Fin 15 =>
      (RecoveryFocus.config bodySlots (heads position) (tapes original stream before) c).heads k =
        (config c.control original stream after position).heads k) ?_ ?_ i
    · intro j
      simp [RecoveryFocus.config, body_other, config]
    · intro j
      have hp : RecoveryFocus.pick bodySlots (j.natAdd 2) = some j :=
        RecoveryFocus.pick_slot bodySlots bodySlots_injective j
      simp [RecoveryFocus.config, hp, hh, config, heads]
  · funext i
    refine Fin.addCases (m := 2) (n := 13) (motive := fun k : Fin 15 =>
      (RecoveryFocus.config bodySlots (heads position) (tapes original stream before) c).tapes k =
        (config c.control original stream after position).tapes k) ?_ ?_ i
    · intro j
      simp [RecoveryFocus.config, body_other, config, tapes]
    · intro j
      have hp : RecoveryFocus.pick bodySlots (j.natAdd 2) = some j :=
        RecoveryFocus.pick_slot bodySlots bodySlots_injective j
      simp [RecoveryFocus.config, hp, ht, config, tapes]

theorem reader_config (original stream : List Bool) (s : Store) (oldPosition position : Nat) (q : Fin 11) :
    RecoveryFocus.config readerSlots (heads oldPosition) (tapes original stream s)
      (RecoveryRootDigitInput.config q stream position) = config q original stream s position := by
  have hzero : RecoveryFocus.pick readerSlots (0 : Fin 15) = none := by
    apply pick_none; intro j; fin_cases j; decide
  have hone : RecoveryFocus.pick readerSlots (1 : Fin 15) = some 0 :=
    RecoveryFocus.pick_slot readerSlots readerSlots_injective 0
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m := 2) (n := 13) (motive := fun k : Fin 15 =>
      (RecoveryFocus.config readerSlots (heads oldPosition) (tapes original stream s)
        (RecoveryRootDigitInput.config q stream position)).heads k =
        (config q original stream s position).heads k) ?_ ?_ i
    · intro j
      fin_cases j <;> simp [RecoveryFocus.config, hzero, hone, RecoveryRootDigitInput.config, config, heads, Fin.addCases]
    · intro j
      simp [RecoveryFocus.config, reader_other_body, RecoveryRootDigitInput.config, config, heads]
  · funext i
    refine Fin.addCases (m := 2) (n := 13) (motive := fun k : Fin 15 =>
      (RecoveryFocus.config readerSlots (heads oldPosition) (tapes original stream s)
        (RecoveryRootDigitInput.config q stream position)).tapes k =
        (config q original stream s position).tapes k) ?_ ?_ i
    · intro j
      fin_cases j <;> simp [RecoveryFocus.config, hzero, hone, RecoveryRootDigitInput.config, config, tapes, Fin.addCases]
    · intro j
      simp [RecoveryFocus.config, reader_other_body, RecoveryRootDigitInput.config, config, tapes]

def sizes : Fin 5 → Nat := ![11, bodyStates, bodyStates, bodyStates, bodyStates]
noncomputable def programs : (j : Fin 5) → Machine 15 (sizes j)
  | ⟨0, _⟩ => RecoveryFocus.machine readerSlots RecoveryRootDigitInput.machine
  | ⟨1, _⟩ => RecoveryFocus.machine bodySlots (roundMachine false false)
  | ⟨2, _⟩ => RecoveryFocus.machine bodySlots (roundMachine true false)
  | ⟨3, _⟩ => RecoveryFocus.machine bodySlots (roundMachine false true)
  | ⟨4, _⟩ => RecoveryFocus.machine bodySlots (roundMachine true true)
  | ⟨n + 5, h⟩ => False.elim (by omega)

def bodyLabel (lo hi : Bool) : Fin 5 := ⟨1 + lo.toNat + 2 * hi.toNat, by cases lo <;> cases hi <;> decide⟩

def next (j : Fin 5) (q : Fin (sizes j)) (_ : Fin 15 → Bool) : Option (Fin 5) :=
  if j.val = 0 then
    if q.val = 6 then some 1 else if q.val = 7 then some 2 else if q.val = 8 then some 3
    else if q.val = 9 then some 4 else none
  else some 0

noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

noncomputable def boundary (j : Fin 5) (original stream : List Bool) (s : Store) (position : Nat) :=
  controlConfig (RecoveryCalls.code sizes j) (config (programs j).start original stream s position)

end NearCubicWires.RepairOrdinary.RecoveryRootLoop
