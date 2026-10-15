import Proof.Amplification.RecoveryQueryPrepareLayout

/-! Physically clear every query work tape, retaining all three original
fields and the actual unary capacity. The reset log is also paid and retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryQueryKernel.Prepare
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem erase_range (j : Fin 354) : 3 ≤ (eraseSlots j).val := by
  refine Fin.addCases (m := 353) (n := 1) (fun a=>?_) (fun a=>?_) j
  · refine Fin.addCases (m := 352) (n := 1) (fun b=>?_) (fun b=>?_) a
    · simp only [eraseSlots,Fin.addCases_left]
      dsimp [workSlot]
      omega
    · simp [eraseSlots]
  · simp [eraseSlots]

theorem clear_run (cap log : Nat) (ambient : Fin 357→List Bool)
    (hb : Bounded cap ambient) (hd : ambient 3=List.replicate cap true)
    (hl : ambient 4=List.replicate log false) (hz : log ≤ cap+1) :
    ReadyRun clearMachine (2*cap+4) ambient (cleared cap ambient) := by
  have h := (RecoveryScratchErase.erase_ready cap log (fun i=>ambient (workSlot i))
    (fun i=>hb (workSlot i) (by simp [workSlot]))).focus eraseSlots erase_injective ambient (by
      intro j
      refine Fin.addCases (m := 353) (n := 1) (fun a=>?_) (fun a=>?_) j
      · refine Fin.addCases (m := 352) (n := 1) (fun b=>?_) (fun b=>?_) a
        · simp [eraseSlots]
        · simpa [eraseSlots] using hd
      · simpa [eraseSlots] using hl)
  let result : Fin 354→List Bool := Fin.addCases (m := 353) (n := 1)
    (motive := fun _=>List Bool)
    (Fin.addCases (m := 352) (n := 1) (motive := fun _=>List Bool)
      (fun _=>List.replicate cap false) (fun _=>List.replicate cap true))
    (fun _=>List.replicate (max log (cap+1)) false)
  have hout : install eraseSlots ambient result=cleared cap ambient := by
    funext i
    match i with
    | ⟨0,_⟩ =>
      exact install_other _ _ _ _ (by intro j he; have hv := erase_range j; rw [he] at hv; contradiction)
    | ⟨1,_⟩ =>
      exact install_other _ _ _ _ (by intro j he; have hv := erase_range j; rw [he] at hv; contradiction)
    | ⟨2,_⟩ =>
      exact install_other _ _ _ _ (by intro j he; have hv := erase_range j; rw [he] at hv; contradiction)
    | ⟨3,_⟩ =>
      have he := install_slot eraseSlots erase_injective ambient result
        (((0 : Fin 1).natAdd 352).castAdd 1)
      simp only [eraseSlots,result,Fin.addCases_left,Fin.addCases_right] at he
      exact he
    | ⟨4,_⟩ =>
      have he := install_slot eraseSlots erase_injective ambient result ((0 : Fin 1).natAdd 353)
      simp only [eraseSlots,result,Fin.addCases_right] at he
      exact he.trans (by rw [max_eq_right hz]; rfl)
    | ⟨n+5,hn⟩ =>
      let j : Fin 352 := ⟨n,by omega⟩
      have he := install_slot eraseSlots erase_injective ambient result ((j.castAdd 1).castAdd 1)
      have hi : eraseSlots ((j.castAdd 1).castAdd 1)=(⟨n+5,hn⟩ : Fin 357) := by
        apply Fin.ext
        simp only [eraseSlots,Fin.addCases_left]
        dsimp [workSlot,j]
        omega
      rw [hi] at he
      simpa [result,cleared,show ¬n+5<3 by omega,show n+5≠3 by omega,show n+5≠4 by omega] using he
  change ReadyRun clearMachine (2*cap+4) ambient (install eraseSlots ambient result) at h
  rw [hout] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryQueryKernel.Prepare
