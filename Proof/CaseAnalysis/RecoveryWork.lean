import Proof.CaseAnalysis.RecoveryScalarMetadata
import Proof.CaseAnalysis.RecoveryRowErase

/-! One actual sweep allocates the initial original row work, empty outer
stack and two grammar drivers. The graph, clause source and metadata remain. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdWork
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def work : Fin 73→Fin 158:=Fin.addCases (m:=70) (n:=3)
  (fun j=>(RecoveryBoundedRowErase.work j).castAdd 80) ![74,150,151]
def slots : Fin 75→Fin 158:=Fin.addCases (m:=73) (n:=2) work ![76,77]
def data (B : ℕ) (word : List Bool) : Fin 75→List Bool:=
  Fin.addCases (m:=73) (n:=2) (fun _=>word) ![List.replicate B true,List.replicate (B+1) false]
noncomputable def machine:=RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 73)

theorem injective : Function.Injective slots := by decide

theorem ready (B : ℕ) :
    ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 73) (2*B+4)
      (data B []) (data B (List.replicate B false)) := by
  obtain ⟨r,hr,rt,rh,rs⟩:=RecoveryScratchErase.erase_ready B (B+1)
    (fun _ : Fin 73=>[]) (by intro i;exact Nat.zero_le B)
  have hi : (Fin.addCases (m:=74) (n:=1)
      (Fin.addCases (m:=73) (n:=1) (fun _=>[]) (fun _=>List.replicate B true))
      (fun _=>List.replicate (B+1) false))=data B [] := by
    funext i
    refine Fin.addCases (m:=73) (n:=2) (fun j=>?_) (fun j=>?_) i
    · simp only [data,Fin.addCases_left]
      change Fin.addCases (Fin.addCases (fun _ : Fin 73=>[]) (fun _ : Fin 1=>List.replicate B true))
        (fun _ : Fin 1=>List.replicate (B+1) false) ((j.castAdd 1).castAdd 1)=[]
      simp only [Fin.addCases_left]
    · fin_cases j <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,rh,rs.le⟩
  rw [rt,Nat.max_self]
  funext i
  refine Fin.addCases (m:=73) (n:=2) (fun j=>?_) (fun j=>?_) i
  · simp only [data,Fin.addCases_left]
    change Fin.addCases (Fin.addCases (fun _ : Fin 73=>List.replicate B false)
      (fun _ : Fin 1=>List.replicate B true)) (fun _ : Fin 1=>List.replicate (B+1) false)
      ((j.castAdd 1).castAdd 1)=List.replicate B false
    simp only [Fin.addCases_left]
  · fin_cases j <;> rfl

theorem work_run (B : ℕ) (A : Fin 158→List Bool) (H : Fin 158→ℕ)
    (hin : ∀ j,A (slots j)=data B [] j) (hh : ∀ j,H (slots j)=0) :
    ∃ r,runFrom machine (2*B+4) ⟨machine.start,H,A⟩=some r ∧
      r.final.heads=H ∧ r.final.tapes=install slots A (data B (List.replicate B false)) ∧
      r.steps≤2*B+4 :=
  (ready B).focus_at slots injective H A hin hh

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdWork
