import Proof.CaseAnalysis.RecoveryGrammarRefresh

/-! The original atom bank and the disjoint retained scalar bank share
one concrete grammar configuration. Packet replacement preserves every scalar. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape RecoveryRootRound
open RecoveryBoundedGrammarWorker (resultHeads)
open RecoveryBoundedGrammarContinue (bank)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def atomSlots (j : Fin 79) : Fin 112:=j.castAdd 33
def heads (out stack : List Bool) : Fin 112→ℕ:=
  Fin.addCases (m:=79) (n:=33) (resultHeads out.length stack.length) (fun _=>0)
def data (fields : Fin 78→List Bool) (node B P : ℕ) (out stack packet source : List Bool)
    (cold : Fin 33→List Bool) : Fin 112→List Bool:=
  Fin.addCases (m:=79) (n:=33)
    (bank (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) B P) cold
def entry {s : ℕ} (p : Machine 112 s) (fields : Fin 78→List Bool) (node B P : ℕ)
    (out stack packet source : List Bool) (cold : Fin 33→List Bool) : Configuration 112 s:=
  ⟨p.start,heads out stack,data fields node B P out stack packet source cold⟩

theorem heads_old (out stack : List Bool) (j : Fin 79) :
    heads out stack (atomSlots j)=resultHeads out.length stack.length j := by
  simp only [heads,atomSlots,Fin.addCases_left]
theorem data_old (fields : Fin 78→List Bool) (node B P : ℕ) (out stack packet source : List Bool)
    (cold : Fin 33→List Bool) (j : Fin 79) :
    data fields node B P out stack packet source cold (atomSlots j)=
      bank (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) B P j := by
  simp only [data,atomSlots,Fin.addCases_left]
theorem heads_high (out stack : List Bool) (i : Fin 112) (hi : 79 ≤ i.val) : heads out stack i=0 := by
  have hj : i=(⟨i.val-79,by omega⟩ : Fin 33).natAdd 79:=Fin.ext (by dsimp;omega)
  rw [hj]
  simp only [heads,Fin.addCases_right]

theorem packet_data (fields : Fin 78→List Bool) (node B P : ℕ) (out stack packet source bits : List Bool)
    (cold : Fin 33→List Bool) :
    Function.update (data fields node B P out stack packet source cold) 75 bits=
      data fields node B P out stack bits source cold := by
  funext i
  refine Fin.addCases (m:=79) (n:=33) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=78) (n:=1) (fun k=>?_) (fun k=>?_) j
    · fin_cases k <;>
        simp [data,bank,RecoveryBoundedGrammarContinue.stackCapacity,
          RecoveryBoundedGrammarWorker.resultData,Fin.addCases,
          RecoveryBoundedGrammarBank.ready,RecoveryBoundedRowReload.loaded_apply,
          RecoveryBoundedRowReload.ports,RecoveryBoundedGrammarBank.base]
    · fin_cases k
      simp [data,bank,RecoveryBoundedGrammarContinue.stackCapacity,
        RecoveryBoundedGrammarWorker.resultData,Fin.addCases]
  · have hj : (j.natAdd 79 : Fin 112)≠75 := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
    rw [Function.update_of_ne hj]
    simp only [data,Fin.addCases_right]

theorem data75 (fields : Fin 78→List Bool) (node B P : ℕ) (out stack packet source : List Bool)
    (cold : Fin 33→List Bool) : data fields node B P out stack packet source cold 75=packet := by
  change ZeroPadding.pad 0 (RecoveryBoundedGrammarBank.ready fields node B out stack packet source 75)=_
  rw [ZeroPadding.pad_zero,RecoveryBoundedGrammarBank.ready_kept _ _ _ _ _ _ _ _ (by decide)]
  rfl
theorem data73 (fields : Fin 78→List Bool) (node B P : ℕ) (out stack packet source : List Bool)
    (cold : Fin 33→List Bool) : data fields node B P out stack packet source cold 73=List.replicate B false := by
  change ZeroPadding.pad 0 (RecoveryBoundedGrammarBank.ready fields node B out stack packet source 73)=_
  rw [ZeroPadding.pad_zero,RecoveryBoundedGrammarBank.ready_kept _ _ _ _ _ _ _ _ (by decide)]
  rfl
theorem data76 (fields : Fin 78→List Bool) (node B P : ℕ) (out stack packet source : List Bool)
    (cold : Fin 33→List Bool) : data fields node B P out stack packet source cold 76=List.replicate B true := by
  change ZeroPadding.pad 0 (RecoveryBoundedGrammarBank.ready fields node B out stack packet source 76)=_
  rw [ZeroPadding.pad_zero,RecoveryBoundedGrammarBank.ready_kept _ _ _ _ _ _ _ _ (by decide)]
  rfl
theorem data77 (fields : Fin 78→List Bool) (node B P : ℕ) (out stack packet source : List Bool)
    (cold : Fin 33→List Bool) : data fields node B P out stack packet source cold 77=List.replicate (B+1) false := by
  change ZeroPadding.pad 0 (RecoveryBoundedGrammarBank.ready fields node B out stack packet source 77)=_
  rw [ZeroPadding.pad_zero,RecoveryBoundedGrammarBank.ready_kept _ _ _ _ _ _ _ _ (by decide)]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
