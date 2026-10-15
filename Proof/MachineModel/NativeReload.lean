import Proof.MachineModel.NativeInitializedPorts
import Proof.MachineModel.NativeFanoutReusable

/-! The erased native bank reloads from the same fifteen retained words in
one linear pass. Its source and append cursors are outside that pass. -/
namespace NearCubicWires.ExtIncidence.NativeReload
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound NativeInitialize NativeInitializedPorts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem reload_run (data : Fin 15→List Bool) (C pos : ℕ) (source out : List Bool)
    (fit : ∀ j,(data j).length ≤ C) (H : Fin 277→ℕ) (A : Fin 277→List Bool)
    (sh : ∀ j,H (sources j)=0) (sa : ∀ j,A (sources j)=data j)
    (bh : ∀ i,H (bank i)=extraH pos out i)
    (ba : ∀ i,A (bank i)=word (fun _=>[]) C source out i) :
    ∃ B,Step NativeFanoutLayout.machine (2*C+4) H A H B ∧
      (∀ i,B (bank i)=word data C source out i) ∧
      (∀ j,B (sources j)=data j) ∧
      (∀ i,(∀ j,ports j≠i) → B i=A i):=by
  have dh (j : Fin 124) : H (bank (targets j))=0:=by
    rw [bh]
    have h31 : targets j≠31:=by revert j;decide
    have h113 : targets j≠113:=by revert j;decide
    simp only [extraH,if_neg h31,if_neg h113]
  have da (j : Fin 124) : A (bank (targets j))=List.replicate C false:=by
    rw [ba]
    have h31 : targets j≠31:=by revert j;decide
    have h104 : targets j≠104:=by revert j;decide
    have h105 : targets j≠105:=by revert j;decide
    have h113 : targets j≠113:=by revert j;decide
    simp only [word,if_neg h31,if_neg h104,if_neg h105,if_neg h113]
    cases selection (targets j).val <;> simp [ZeroPadding.pad]
  have hh : ∀ j,H (ports j)=0:=by
    intro j
    refine Fin.addCases (m:=15+(124+1)) (n:=1) (fun i=>?_) (fun i=>?_) j
    · refine Fin.addCases (m:=15) (n:=124+1) (fun a=>?_) (fun a=>?_) i
      · simpa only [ports,Fin.addCases_left] using sh a
      · refine Fin.addCases (m:=124) (n:=1) (fun a=>?_) (fun a=>?_) a
        · simpa only [ports,Fin.addCases_left,Fin.addCases_right] using dh a
        · simp only [ports,Fin.addCases_left,Fin.addCases_right];exact bh 104
    · simp only [ports,Fin.addCases_right];exact bh 105
  have ha : ∀ j,A (ports j)=NativeFanout.reusableInput data C j:=by
    intro j
    refine Fin.addCases (m:=15+(124+1)) (n:=1) (fun i=>?_) (fun i=>?_) j
    · refine Fin.addCases (m:=15) (n:=124+1) (fun a=>?_) (fun a=>?_) i
      · simpa only [ports,NativeFanout.reusableInput,Fin.addCases_left] using sa a
      · refine Fin.addCases (m:=124) (n:=1) (fun a=>?_) (fun a=>?_) a
        · simpa only [ports,NativeFanout.reusableInput,Fin.addCases_left,Fin.addCases_right] using da a
        · simp only [ports,NativeFanout.reusableInput,Fin.addCases_left,Fin.addCases_right];exact ba 104
    · simp only [ports,NativeFanout.reusableInput,Fin.addCases_right];exact ba 105
  have run:=(NativeFanout.reusable choice data C fit).dock ports ports_injective H A hh ha
  rw [dockH_existing ports H (fun _=>0) hh] at run
  let B:=install ports A (NativeFanout.output choice data C)
  have kept (i : Fin 277) (hi : ∀ j,ports j≠i) : B i=A i:=install_other ports A _ i hi
  have pb (j) : B (ports j)=NativeFanout.output choice data C j:=
    install_slot ports ports_injective A _ j
  refine ⟨B,run,?_,?_,kept⟩
  · intro i
    exact (fields H B data C pos source out hh pb (bh 31)
      ((kept (bank 31) (by decide)).trans (ba 31)) (bh 113)
      ((kept (bank 113) (by decide)).trans (ba 113)) i).2
  · intro j
    simpa only [ports,NativeFanout.output,Fin.addCases_left] using
      pb ((j.castAdd (124+1)).castAdd 1)

end NearCubicWires.ExtIncidence.NativeReload
