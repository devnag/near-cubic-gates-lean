import Proof.CaseAnalysis.WitnessInputGuard

/-! The actual produced native width is compared to the retained original
input length before oracle parsing. Both raw fields survive the existing
paid comparator, including on the rejecting R>N branch. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeGuard
open LocalBitMultitape RecoveryRootRound RepairSource.CloseoutSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def slots {t : ℕ} (fields : Fin 2 → Fin t) : Fin 6 → Fin (t+4):=
  Fin.addCases (m:=2) (n:=4) (motive:=fun _=>Fin (t+4)) (fun i=>(fields i).castAdd 4) (Fin.natAdd t)
def input {t : ℕ} (base : Fin t → List Bool) : Fin (t+4) → List Bool:=
  Fin.addCases (m:=t) (n:=4) (motive:=fun _=>List Bool) base (fun _=>[])
def machine {t : ℕ} (fields : Fin 2 → Fin t):=RecoveryFocus.machine (slots fields) RawCompare.machine
def flagSlot (t : ℕ):=(2 : Fin 4).natAdd t

theorem injective {t : ℕ} (fields : Fin 2 → Fin t) (hf : Function.Injective fields) : Function.Injective (slots fields):=by
  intro i j h
  revert j h
  refine Fin.addCases (m:=2) (n:=4) ?_ ?_ i
  · intro a j
    refine Fin.addCases (m:=2) (n:=4) ?_ ?_ j
    · intro b h
      simp only [slots,Fin.addCases_left] at h
      have he:fields a=fields b:=Fin.ext (congrArg (fun z : Fin (t+4)=>z.val) h)
      exact congrArg (Fin.castAdd 4) (hf he)
    · intro b h
      simp only [slots,Fin.addCases_left,Fin.addCases_right] at h
      have hv:=congrArg (fun z : Fin (t+4)=>z.val) h
      change (fields a).val=t+b.val at hv
      omega
  · intro a j
    refine Fin.addCases (m:=2) (n:=4) ?_ ?_ j
    · intro b h
      simp only [slots,Fin.addCases_left,Fin.addCases_right] at h
      have hv:=congrArg (fun z : Fin (t+4)=>z.val) h
      change t+a.val=(fields b).val at hv
      omega
    · intro b h
      simp only [slots,Fin.addCases_right] at h
      have hv:=congrArg (fun z : Fin (t+4)=>z.val) h
      change t+a.val=t+b.val at hv
      have he:a=b:=Fin.ext (by omega)
      exact congrArg (Fin.natAdd 2) he

theorem guard_run {t : ℕ} (fields : Fin 2 → Fin t) (hf : Function.Injective fields)
    (R N : ℕ) (base : Fin t → List Bool)
    (hR : base (fields 0)=List.replicate R true) (hN : base (fields 1)=List.replicate N true) :
    ∃ out,ClockJoin.ReadyRun (machine fields) (RawCompare.budget R N) (input base) out ∧
      (∀ i,out (i.castAdd 4)=base i) ∧ out (flagSlot t)=[decide (R ≤ N)]:=by
  have hin (i : Fin 6):input base (slots fields i)=RawCompare.input R N i:=by
    refine Fin.addCases (m:=2) (n:=4) ?_ ?_ i
    · intro j
      simp only [slots,Fin.addCases_left,input]
      fin_cases j
      · exact hR
      · exact hN
    · intro j
      rw [slots,Fin.addCases_right,input,Fin.addCases_right]
      fin_cases j <;> rfl
  have h:=(RawCompare.compare_run R N).focus (slots fields) (injective fields hf) (input base) hin
  refine ⟨_,h,?_,?_⟩
  · intro i
    by_cases present:∃ j,fields j=i
    · obtain ⟨j,rfl⟩:=present
      have hs:slots fields (j.castAdd 4)=(fields j).castAdd 4:=by rw [slots,Fin.addCases_left]
      rw [←hs,install_slot _ (injective fields hf)]
      fin_cases j
      · exact hR.symm
      · exact hN.symm
    · rw [install_other _ _ _ _ (by
        intro j
        refine Fin.addCases (m:=2) (n:=4) ?_ ?_ j
        · intro a he
          rw [slots,Fin.addCases_left] at he
          exact present ⟨a,Fin.ext (congrArg (fun z : Fin (t+4)=>z.val) he)⟩
        · intro a he
          rw [slots,Fin.addCases_right] at he
          have hv:=congrArg (fun z : Fin (t+4)=>z.val) he
          change t+a.val=i.val at hv;omega),input,Fin.addCases_left]
  · have hs:slots fields ((2 : Fin 4).natAdd 2)=flagSlot t:=by rw [slots,Fin.addCases_right];rfl
    rw [←hs,install_slot _ (injective fields hf)]
    rfl

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeGuard
