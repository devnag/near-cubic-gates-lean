import Proof.MachineModel.OrdinaryOracleComposeReady
import Proof.PCP.PCPFieldMoves
import Proof.Amplification.RecoveryScratchErase

/-! Fixed five-phase wiring for arbitrary two ordinary-oracle programs.
The two source banks identify only their query tapes. All transfer logs and
the final exact framed output have separate fresh physical tapes. -/
namespace NearCubicWires.RepairSource.OrdinaryOracleCompose
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapeCount (p q : OrdinaryOracleProgram) :=
  (clocked p).base.tapeCount + (clocked q).base.tapeCount + 4

def firstSlot (p q : OrdinaryOracleProgram) (i : Fin (clocked p).base.tapeCount) :
    Fin (tapeCount p q) := ⟨i.val, by have hi := i.isLt; unfold tapeCount; omega⟩

def secondSlot (p q : OrdinaryOracleProgram) (i : Fin (clocked q).base.tapeCount) :
    Fin (tapeCount p q) :=
  if i = (clocked q).queryTape then firstSlot p q (clocked p).queryTape
  else ⟨(clocked p).base.tapeCount + i.val, by have hi := i.isLt; unfold tapeCount; omega⟩

def extraSlot (p q : OrdinaryOracleProgram) (i : Fin 4) : Fin (tapeCount p q) :=
  ⟨(clocked p).base.tapeCount + (clocked q).base.tapeCount + i.val,
    by have hi := i.isLt; unfold tapeCount; omega⟩

theorem first_injective (p q : OrdinaryOracleProgram) : Function.Injective (firstSlot p q) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin (tapeCount p q) => x.val) h)

theorem second_injective (p q : OrdinaryOracleProgram) : Function.Injective (secondSlot p q) := by
  intro i j h
  by_cases hi : i = (clocked q).queryTape
  · by_cases hj : j = (clocked q).queryTape
    · exact hi.trans hj.symm
    · have hv := congrArg (fun x : Fin (tapeCount p q) => x.val) h
      simp only [secondSlot, hi, hj, if_true, if_false, firstSlot] at hv
      have ht := (clocked p).queryTape.isLt
      omega
  · by_cases hj : j = (clocked q).queryTape
    · have hv := congrArg (fun x : Fin (tapeCount p q) => x.val) h
      simp only [secondSlot, hi, hj, if_true, if_false, firstSlot] at hv
      have ht := (clocked p).queryTape.isLt
      omega
    · apply Fin.ext
      have hv := congrArg (fun x : Fin (tapeCount p q) => x.val) h
      simp only [secondSlot, hi, hj, if_false] at hv
      omega

@[simp] theorem second_query (p q : OrdinaryOracleProgram) :
    secondSlot p q (clocked q).queryTape = firstSlot p q (clocked p).queryTape := by
  simp [secondSlot]

theorem banks_meet (p q : OrdinaryOracleProgram)
    (i : Fin (clocked p).base.tapeCount) (j : Fin (clocked q).base.tapeCount) :
    firstSlot p q i = secondSlot p q j ↔
      i = (clocked p).queryTape ∧ j = (clocked q).queryTape := by
  by_cases hj : j = (clocked q).queryTape
  · rw [hj, second_query]
    exact ⟨fun h => ⟨first_injective p q h, rfl⟩, fun h => congrArg (firstSlot p q) h.1⟩
  · constructor
    · intro h
      have hv := congrArg (fun x : Fin (tapeCount p q) => x.val) h
      simp only [firstSlot, secondSlot, hj, if_false] at hv
      have hi := i.isLt
      omega
    · rintro ⟨_, h⟩
      exact False.elim (hj h)

theorem extra_injective (p q : OrdinaryOracleProgram) : Function.Injective (extraSlot p q) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin (tapeCount p q) => x.val) h
  simp only [extraSlot] at hv
  omega

theorem first_ne_extra (p q : OrdinaryOracleProgram)
    (i : Fin (clocked p).base.tapeCount) (j : Fin 4) : firstSlot p q i ≠ extraSlot p q j := by
  intro h
  have hv := congrArg (fun x : Fin (tapeCount p q) => x.val) h
  simp only [firstSlot, extraSlot] at hv
  have hi := i.isLt
  omega

theorem second_ne_extra (p q : OrdinaryOracleProgram)
    (i : Fin (clocked q).base.tapeCount) (j : Fin 4) : secondSlot p q i ≠ extraSlot p q j := by
  by_cases hi : i = (clocked q).queryTape
  · simpa only [secondSlot, hi, if_true] using first_ne_extra p q (clocked p).queryTape j
  · intro h
    have hv := congrArg (fun x : Fin (tapeCount p q) => x.val) h
    simp only [secondSlot, hi, if_false, extraSlot] at hv
    have ht := i.isLt
    omega

def zeroTape (p : OrdinaryOracleProgram) : Fin (clocked p).base.tapeCount :=
  ⟨0, by have ht := (clocked p).base.twoTapes; omega⟩

theorem zero_ne_query (p : OrdinaryOracleProgram) : zeroTape p ≠ (clocked p).queryTape := by
  intro h
  exact (clocked p).queryFresh (congrArg Fin.val h).symm

theorem query_ne_clock (p : OrdinaryOracleProgram) : (clocked p).queryTape ≠ clockTape p := by
  intro h
  have hv := congrArg (fun x : Fin (clocked p).base.tapeCount => x.val) h
  change p.queryTape.val = p.base.tapeCount at hv
  have ht := p.queryTape.isLt
  omega

def copySlots (p q : OrdinaryOracleProgram) : Fin 3 → Fin (tapeCount p q) :=
  ![firstSlot p q (clocked p).base.outputTape, secondSlot p q (zeroTape q), extraSlot p q 0]

def clearSlots (p q : OrdinaryOracleProgram) : Fin 3 → Fin (tapeCount p q) :=
  ![firstSlot p q (clocked p).queryTape, firstSlot p q (clockTape p), extraSlot p q 1]

def outputSlots (p q : OrdinaryOracleProgram) : Fin 3 → Fin (tapeCount p q) :=
  ![secondSlot p q (clocked q).base.outputTape, extraSlot p q 3, extraSlot p q 2]

theorem copy_injective (p q : OrdinaryOracleProgram) : Function.Injective (copySlots p q) := by
  have h01 : firstSlot p q (clocked p).base.outputTape ≠ secondSlot p q (zeroTape q) := by
    intro h
    exact zero_ne_query q ((banks_meet p q _ _).mp h).2
  have h02 := first_ne_extra p q (clocked p).base.outputTape 0
  have h12 := second_ne_extra p q (zeroTape q) 0
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [copySlots]

theorem clear_injective (p q : OrdinaryOracleProgram) : Function.Injective (clearSlots p q) := by
  have h01 : firstSlot p q (clocked p).queryTape ≠ firstSlot p q (clockTape p) := by
    intro h
    exact query_ne_clock p (first_injective p q h)
  have h02 := first_ne_extra p q (clocked p).queryTape 1
  have h12 := first_ne_extra p q (clockTape p) 1
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [clearSlots]

theorem output_injective (p q : OrdinaryOracleProgram) : Function.Injective (outputSlots p q) := by
  have h01 := second_ne_extra p q (clocked q).base.outputTape 3
  have h02 := second_ne_extra p q (clocked q).base.outputTape 2
  have h12 : extraSlot p q 3 ≠ extraSlot p q 2 := by
    intro h
    have he := extra_injective p q h
    exact (by decide : (3 : Fin 4) ≠ 2) he
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [outputSlots]

def ports (p q : OrdinaryOracleProgram) : Ports (tapeCount p q) where
  twoTapes := by unfold tapeCount; omega
  outputTape := extraSlot p q 3
  outputFresh := by intro h; change (clocked p).base.tapeCount + (clocked q).base.tapeCount + 3 = 0 at h; omega
  queryTape := firstSlot p q (clocked p).queryTape
  queryFresh := (clocked p).queryFresh

noncomputable def pieces (p q : OrdinaryOracleProgram) (j : Fin 5) : Piece (tapeCount p q) :=
  match j.val with
  | 0 => focused (clocked p) (firstSlot p q)
  | 1 => ordinary (RecoveryFocus.machine (copySlots p q) PCPFieldMoves.readyMachine)
  | 2 => ordinary (RecoveryFocus.machine (clearSlots p q) (RecoveryScratchErase.resetMachine 1))
  | 3 => focused (clocked q) (secondSlot p q)
  | _ => ordinary (RecoveryFocus.machine (outputSlots p q) PCPFieldMoves.readyMachine)

def next (p q : OrdinaryOracleProgram) (j : Fin 5) (_ : Fin (pieces p q j).states)
    (_ : Fin (tapeCount p q) → Bool) : Option (Fin 5) :=
  if j.val = 4 then none else some ⟨(j.val + 1) % 5, Nat.mod_lt _ (by decide)⟩

noncomputable def compose (p q : OrdinaryOracleProgram) : OrdinaryOracleProgram :=
  (ports p q).program (graph (pieces p q) 0 (next p q))

end NearCubicWires.RepairSource.OrdinaryOracleCompose
