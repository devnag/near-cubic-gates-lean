import Proof.MachineModel.NativeReload

/-! Reloading writes back the same retained metadata and changes no tape
outside the native bank. This is the invariant needed by the family loop. -/
namespace NearCubicWires.ExtIncidence.NativeReload
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound NativeInitialize NativeInitializedPorts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ports_cases (j : Fin (15+(124+1)+1)) :
    (∃ a,ports j=sources a) ∨ (∃ b,ports j=bank b):=by
  refine Fin.addCases (m:=15+(124+1)) (n:=1) (fun i=>?_) (fun i=>?_) j
  · refine Fin.addCases (m:=15) (n:=124+1) (fun a=>?_) (fun a=>?_) i
    · exact Or.inl ⟨a,by simp only [ports,Fin.addCases_left]⟩
    · refine Fin.addCases (m:=124) (n:=1) (fun a=>?_) (fun a=>?_) a
      · exact Or.inr ⟨targets a,by simp only [ports,Fin.addCases_left,Fin.addCases_right]⟩
      · exact Or.inr ⟨104,by simp only [ports,Fin.addCases_left,Fin.addCases_right]⟩
  · exact Or.inr ⟨105,by simp only [ports,Fin.addCases_right]⟩

theorem reload_retained_run (data : Fin 15→List Bool) (C pos : ℕ) (source out : List Bool)
    (fit : ∀ j,(data j).length ≤ C) (H : Fin 277→ℕ) (A : Fin 277→List Bool)
    (sh : ∀ j,H (sources j)=0) (sa : ∀ j,A (sources j)=data j)
    (bh : ∀ i,H (bank i)=extraH pos out i)
    (ba : ∀ i,A (bank i)=word (fun _=>[]) C source out i) :
    ∃ B,Step NativeFanoutLayout.machine (2*C+4) H A H B ∧
      (∀ i,B (bank i)=word data C source out i) ∧
      (∀ j,B (sources j)=data j) ∧
      (∀ i,(∀ j,bank j≠i) → B i=A i):=by
  classical
  obtain ⟨B,run,bp,bs,keep⟩:=reload_run data C pos source out fit H A sh sa bh ba
  refine ⟨B,run,bp,bs,?_⟩
  intro i hi
  by_cases hit : ∃ j,ports j=i
  · obtain ⟨j,hj⟩:=hit
    rcases ports_cases j with ⟨a,ha⟩ | ⟨b,hb⟩
    · have eqi : i=sources a:=hj.symm.trans ha
      rw [eqi,bs,sa]
    · exact False.elim (hi b (hb.symm.trans hj))
  · exact keep i (by intro j hj;exact hit ⟨j,hj⟩)

end NearCubicWires.ExtIncidence.NativeReload
