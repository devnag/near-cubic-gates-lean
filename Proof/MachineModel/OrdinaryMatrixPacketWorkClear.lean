import Proof.MachineModel.OrdinaryMatrixPacketCapacityNative

/-! The scheduler clears only the packet workspace. The live offset, global
packet stream, one-time capacity work and retained original request are
outside the executed erase focus. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketWorkClear
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
open MatrixWilliamsProduct (source)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def count (a : WilliamsAlgorithm) := MatrixVariableProduct.tapes a+16
noncomputable def tapes (a : WilliamsAlgorithm) (E : ℕ) := MatrixPacketCapacityNative.tapes a E+2
noncomputable def work (a : WilliamsAlgorithm) (E : ℕ) (i : Fin (count a)) : Fin (tapes a E) :=
  ⟨if i.val<424 then i.val else if i.val<MatrixVariableProduct.tapes a+15 then i.val+1 else i.val+2,
    by have h:=i.isLt
       unfold count at h
       unfold tapes MatrixPacketCapacityNative.tapes MatrixVariablePacketWorkspace.tapes MatrixVariableCount.tapes
       split_ifs <;> omega⟩
noncomputable def capTape (a : WilliamsAlgorithm) (E : ℕ) := (MatrixPacketCapacityNative.outputTape a E).castAdd 2
noncomputable def logTape (a : WilliamsAlgorithm) (E : ℕ) := (0 : Fin 2).natAdd (MatrixPacketCapacityNative.tapes a E)
noncomputable def original (a : WilliamsAlgorithm) (E : ℕ) := (1 : Fin 2).natAdd (MatrixPacketCapacityNative.tapes a E)
noncomputable def slots (a : WilliamsAlgorithm) (E : ℕ) : Fin (count a+2) → Fin (tapes a E) :=
  Fin.addCases (m := count a+1) (n := 1) (motive := fun _ => Fin (tapes a E))
    (Fin.addCases (m := count a) (n := 1) (motive := fun _ => Fin (tapes a E)) (work a E) (fun _ => capTape a E))
    (fun _ => logTape a E)

theorem work_val (a : WilliamsAlgorithm) (E : ℕ) (i : Fin (count a)) :
    (work a E i).val=if i.val<424 then i.val else if i.val<MatrixVariableProduct.tapes a+15 then i.val+1 else i.val+2 := rfl

theorem work_bound (a : WilliamsAlgorithm) (E : ℕ) (i : Fin (count a)) :
    (work a E i).val<MatrixVariablePacketWorkspace.tapes a := by
  have h:=i.isLt
  unfold count at h
  rw [work_val]
  unfold MatrixVariablePacketWorkspace.tapes MatrixVariableCount.tapes
  split_ifs <;> omega

theorem cap_bound (a : WilliamsAlgorithm) (E : ℕ) :
    MatrixVariablePacketWorkspace.tapes a≤(capTape a E).val := by
  have hv : (MatrixPacketCapacityEntry.outputTape E).val=21+(RepairSource.ProjectionNormalization.DimensionPower.tapes E+3) := by
    unfold MatrixPacketCapacityEntry.outputTape MatrixPacketCapacityEntry.slots
    simp only [Fin.val_natAdd]
    rw [if_neg (by omega),if_neg (by omega)]
    rfl
  unfold capTape MatrixPacketCapacityNative.outputTape MatrixPacketCapacityNative.slots
  simp only [Fin.val_castAdd,hv]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  change MatrixVariablePacketWorkspace.tapes a≤MatrixVariablePacketWorkspace.tapes a+(MatrixPacketCapacityEntry.outputTape E).val
  omega

theorem work_injective (a : WilliamsAlgorithm) (E : ℕ) : Function.Injective (work a E) := by
  intro i j h
  have hi:=i.isLt
  have hj:=j.isLt
  unfold count at hi hj
  have hK : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
  have hv:=congrArg Fin.val h
  rw [work_val,work_val] at hv
  repeat' split at hv
  all_goals exact Fin.ext (by omega)

theorem slots_cases (a : WilliamsAlgorithm) (E : ℕ) (j : Fin (count a+2)) :
    slots a E j=if h : j.val<count a then work a E ⟨j.val,h⟩
      else if j.val=count a then capTape a E else logTape a E := by
  refine Fin.addCases (m := count a+1) (n := 1) (fun i => ?_) (fun i => ?_) j
  · refine Fin.addCases (m := count a) (n := 1) (fun k => ?_) (fun k => ?_) i
    · simp [slots,k.isLt]
    · fin_cases k; simp [slots]
  · fin_cases i; simp [slots]

theorem slots_injective (a : WilliamsAlgorithm) (E : ℕ) : Function.Injective (slots a E) := by
  have wc (i : Fin (count a)) : work a E i≠capTape a E := by
    intro he
    have hv:=congrArg Fin.val he
    have h0:=work_bound a E i
    have h1:=cap_bound a E
    omega
  have wl (i : Fin (count a)) : work a E i≠logTape a E := by
    intro he
    have hv:=congrArg Fin.val he
    have h0:=work_bound a E i
    change (work a E i).val=MatrixPacketCapacityNative.tapes a E at hv
    unfold MatrixPacketCapacityNative.tapes at hv
    omega
  have cl : capTape a E≠logTape a E := by
    intro he
    have hv:=congrArg Fin.val he
    have h0:=(MatrixPacketCapacityNative.outputTape a E).isLt
    change (MatrixPacketCapacityNative.outputTape a E).val=MatrixPacketCapacityNative.tapes a E at hv
    omega
  intro i j he
  rw [slots_cases,slots_cases] at he
  split_ifs at he
  · exact Fin.ext (congrArg (fun k : Fin (count a) => k.val) (work_injective a E he))
  · exact False.elim (wc _ he)
  · exact False.elim (wl _ he)
  · exact False.elim (wc _ he.symm)
  · exact Fin.ext (by omega)
  · exact False.elim (cl he)
  · exact False.elim (wl _ he.symm)
  · exact False.elim (cl he.symm)
  · exact Fin.ext (by omega)

noncomputable def machine (a : WilliamsAlgorithm) (E : ℕ) :=
  RecoveryFocus.machine (slots a E) (RecoveryScratchErase.resetMachine (count a))
def eraseData {n : ℕ} (cap log : ℕ) (backing : Fin n → List Bool) : Fin (n+2) → List Bool :=
  Fin.addCases (m := n+1) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := n) (n := 1) (motive := fun _ => List Bool) backing (fun _ => List.replicate cap true))
    (fun _ => List.replicate log false)

theorem clear_run (a : WilliamsAlgorithm) (E cap log : ℕ)
    (heads : Fin (tapes a E) → ℕ) (ambient : Fin (tapes a E) → List Bool)
    (hd : ambient (capTape a E)=List.replicate cap true)
    (hl : ambient (logTape a E)=List.replicate log false)
    (hb : ∀ j,(ambient (work a E j)).length≤cap)
    (hh : ∀ j,heads (slots a E j)=0) : ∃ actual,
    runFrom (machine a E) (2*cap+4) (RecoveryCalls.restarted (machine a E) heads ambient)=some actual ∧
    actual.final.heads=heads ∧
    actual.final.tapes=install (slots a E) ambient
      (eraseData cap (max log (cap+1)) (fun _ : Fin (count a) => List.replicate cap false)) ∧
    actual.steps=2*cap+4 := by
  have ready : ReadyRun (RecoveryScratchErase.resetMachine (count a)) (2*cap+4)
      (eraseData cap log (fun j => ambient (work a E j)))
      (eraseData cap (max log (cap+1)) (fun _ => List.replicate cap false)) :=
    RecoveryScratchErase.erase_ready cap log _ hb
  have ht : ∀ j,ambient (slots a E j)=eraseData cap log (fun j => ambient (work a E j)) j := by
    intro j
    refine Fin.addCases (m := count a+1) (n := 1) (fun i => ?_) (fun i => ?_) j
    · refine Fin.addCases (m := count a) (n := 1) (fun k => ?_) (fun k => ?_) i
      · simp [slots,eraseData]
      · fin_cases k; simpa [slots,eraseData] using hd
    · fin_cases i; simpa [slots,eraseData] using hl
  exact HierarchyBinary.focused_run (slots a E) (slots_injective a E) _ _ _ ready heads ambient hh ht

end NearCubicWires.RepairOrdinary.MatrixPacketWorkClear
