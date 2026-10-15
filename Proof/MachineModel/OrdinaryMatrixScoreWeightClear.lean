import Proof.MachineModel.OrdinaryMatrixScoreWeightEndpoint

/-! Physical reset between successive weight entries. This clears the ten
local work tapes and retains source cursors, width and both signed sums. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreWeightClear
open LocalBitMultitape RecoveryRootRound MatrixScoreWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scratchSlots : Fin 10 → Fin 17 := ![2,3,4,5,7,8,9,12,13,14]
def slots : Fin 12 → Fin 17 := ![2,3,4,5,7,8,9,12,13,14,15,16]
def heads (pos apos : ℕ) : Fin 17 → ℕ := ![pos,apos,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def tapes (source assignment : List Bool) (c w p n : ℕ) (scratch : Fin 10 → List Bool) : Fin 17 → List Bool :=
  ![source,assignment,scratch 0,scratch 1,scratch 2,scratch 3,List.replicate w true,
    scratch 4,scratch 5,scratch 6,scalar c w p,scalar c w n,scratch 7,scratch 8,scratch 9,
    List.replicate c true,zeros (c+1)]
noncomputable def machine : Machine 17 4 := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 10)

def pick : Fin 17 → Option (Fin 12) :=
  ![none,none,some 0,some 1,some 2,some 3,none,some 4,some 5,some 6,none,none,
    some 7,some 8,some 9,some 10,some 11]
theorem pick_slots (i : Fin 17) : RecoveryFocus.pick slots i=pick i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot slots (by decide) 0
    | exact RecoveryFocus.pick_slot slots (by decide) 1
    | exact RecoveryFocus.pick_slot slots (by decide) 2
    | exact RecoveryFocus.pick_slot slots (by decide) 3
    | exact RecoveryFocus.pick_slot slots (by decide) 4
    | exact RecoveryFocus.pick_slot slots (by decide) 5
    | exact RecoveryFocus.pick_slot slots (by decide) 6
    | exact RecoveryFocus.pick_slot slots (by decide) 7
    | exact RecoveryFocus.pick_slot slots (by decide) 8
    | exact RecoveryFocus.pick_slot slots (by decide) 9
    | exact RecoveryFocus.pick_slot slots (by decide) 10
    | exact RecoveryFocus.pick_slot slots (by decide) 11

theorem clear_run (source assignment : List Bool) (pos apos c w p n : ℕ) (scratch : Fin 10 → List Bool)
    (hb : ∀ i,(scratch i).length≤c) :
    ∃ actual : ExecutionReceipt 17 4,
      runFrom machine (2*c+4) (RecoveryCalls.restarted machine (heads pos apos)
        (tapes source assignment c w p n scratch))=some actual ∧
      actual.final.heads=heads pos apos ∧
      actual.final.tapes=tapes source assignment c w p n (fun _ => zeros c) ∧ actual.steps=2*c+4 := by
  have ready := RecoveryScratchErase.erase_ready c (c+1) scratch hb
  simp only [max_self] at ready
  have hh : ∀ j,heads pos apos (slots j)=0 := by intro j; fin_cases j <;> rfl
  have ht : ∀ j,tapes source assignment c w p n scratch (slots j)=
      (Fin.addCases (m := 11) (n := 1) (motive := fun _ => List Bool)
        (Fin.addCases (m := 10) (n := 1) (motive := fun _ => List Bool) scratch (fun _ : Fin 1 => List.replicate c true))
        (fun _ : Fin 1 => List.replicate (c+1) false)) j := by intro j; fin_cases j <;> rfl
  obtain ⟨actual,hr,hah,hat,has⟩ := HierarchyBinary.focused_run slots (by decide)
    (RecoveryScratchErase.resetMachine 10) _ _ ready (heads pos apos)
    (tapes source assignment c w p n scratch) hh ht
  refine ⟨actual,hr,hah,?_,has⟩
  rw [hat]
  funext i
  fin_cases i <;> simp [install,pick_slots,pick,tapes,Fin.addCases,zeros]

end NearCubicWires.RepairOrdinary.MatrixScoreWeightClear
