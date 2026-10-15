import Proof.Amplification.RecoveryTseitinFields

/-! Physical six-cell graph for the original three-literal clause code.
Only consumed operands share prior output slots. Five ambient tapes are retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryTseitinKernel
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryTseitin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bank (k : Fin 6) (i : Fin 39) : Fin 239 := ⟨5+39*k.val+i.val,by omega⟩
def leftPort : Fin 6→Fin 239 :=
  ![bank 0 2,bank 1 2,bank 2 2,bank 2 26,bank 1 26,bank 0 26]
def rightPort : Fin 6→Fin 239 :=
  ![bank 0 3,bank 1 3,bank 2 3,bank 3 3,bank 3 26,bank 4 26]
def cellSlots (k : Fin 6) (i : Fin 39) : Fin 239 :=
  if i.val=2 then leftPort k else if i.val=3 then rightPort k else bank k i

theorem bank_injective (k : Fin 6) : Function.Injective (bank k) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin 239 => x.val) h
  dsimp [bank] at hv
  omega

theorem cell_injective (k : Fin 6) : Function.Injective (cellSlots k) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun x : Fin 239 => x.val) h
  have hi := i.isLt
  have hj := j.isLt
  fin_cases k <;> dsimp [cellSlots,leftPort,rightPort,bank] at hv <;>
    (try split_ifs at hv) <;> (try dsimp at hv) <;> omega

theorem cell_range (k : Fin 6) (i : Fin 39) :
    5 ≤ (cellSlots k i).val ∧ (cellSlots k i).val < 5+39*(k.val+1) := by
  have hi := i.isLt
  fin_cases k <;> dsimp [cellSlots,leftPort,rightPort,bank] <;>
    (try split_ifs) <;> (try dsimp) <;> omega

theorem install_small (k : Fin 6) (ambient : Fin 239→List Bool) (out : Fin 39→List Bool)
    (i : Fin 239) (hi : i.val<5) : install (cellSlots k) ambient out i=ambient i := by
  apply install_other
  intro j he
  have h := (cell_range k j).1
  rw [he] at h
  omega

theorem install_above (k : Fin 6) (ambient : Fin 239→List Bool) (out : Fin 39→List Bool)
    (i : Fin 239) (hi : 5+39*(k.val+1) ≤ i.val) :
    install (cellSlots k) ambient out i=ambient i := by
  apply install_other
  intro j he
  have h := (cell_range k j).2
  rw [he] at h
  omega

@[simp] theorem cell_output (k : Fin 6) : cellSlots k 26=bank k 26 := by rfl

noncomputable def call (k : Fin 6) : Σ s,Machine 239 s :=
  ⟨_,RecoveryFocus.machine (cellSlots k) (RecoveryQueryCell.machine (operations k)).2⟩
noncomputable def sizes (k : Fin 6) := (call k).1
noncomputable def programs (k : Fin 6) : Machine 239 (sizes k) := (call k).2
def next (k : Fin 6) (_ : Fin (sizes k)) (_ : Fin 239→Bool) : Option (Fin 6) :=
  if k.val=5 then none else some ⟨(k.val+1)%6,Nat.mod_lt _ (by decide)⟩
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def Bounded (cap : Nat) (tapes : Fin 239→List Bool) : Prop :=
  ∀ i,5 ≤ i.val → (tapes i).length ≤ cap

theorem install_bounded (k : Fin 6) (cap : Nat) (ambient : Fin 239→List Bool)
    (out : Fin 39→List Bool) (ha : Bounded cap ambient) (hb : ∀ i,(out i).length ≤ cap) :
    Bounded cap (install (cellSlots k) ambient out) := by
  intro i hi
  by_cases he : ∃ j,cellSlots k j=i
  · obtain ⟨j,rfl⟩ := he
    rw [install_slot _ (cell_injective k)]
    exact hb j
  · rw [install_other _ _ _ _ (by intro j hj; exact he ⟨j,hj⟩)]
    exact ha i hi

theorem cell_run (k : Fin 6) (cap a b : Nat) (ambient : Fin 239→List Bool)
    (hin : ∀ i,ambient (cellSlots k i)=RecoveryQueryCell.paddedInput cap a b i)
    (hcap : RecoveryQueryCell.budget (operations k) a b+1 ≤ cap)
    (ha : 2*a.bits.length+1 ≤ cap) (hb : 2*b.bits.length+1 ≤ cap) :
    ∃ out : Fin 39→List Bool,
      ClockJoin.ReadyRun (programs k) (RecoveryQueryCell.budget (operations k) a b)
        ambient (install (cellSlots k) ambient out) ∧
      out 26=ZeroPadding.pad cap (frame (RecoveryQueryCell.result (operations k) a b).bits) ∧
      ∀ i,(out i).length ≤ cap := by
  obtain ⟨out,hr,hf,hbound⟩ := RecoveryQueryCell.padded_run (operations k) cap a b hcap ha hb
  exact ⟨out,hr.focus (cellSlots k) (cell_injective k) ambient hin,hf,hbound⟩

end NearCubicWires.RepairOrdinary.RecoveryTseitinKernel
