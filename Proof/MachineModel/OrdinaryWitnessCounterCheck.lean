import Proof.MachineModel.OrdinaryVerifierInputFields
import Proof.MachineModel.OrdinaryFramedIncrement

/-! Bounded witness streaming uses a small counter, never a unary B-sized
driver. This paid comparison restores only its four local tapes. -/
namespace NearCubicWires.RepairOrdinary.WitnessCounterCheck
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (w counter bound cap : ℕ) (flag : Bool) : Configuration 4 s :=
  ⟨state,fun _ => 0,
    ![frame (binary w counter),frame (binary w bound),[flag],List.replicate cap false]⟩
def capacities : Fin 3 → ℕ := ![0,0,1]
def machine : Machine 4 7 := Rewind.machine Compare.machine

theorem compare_run (w counter bound cap : ℕ) (hn : counter<2^w) (hb : bound<2^w)
    (hcap : 2*w+1≤cap) :
    ∃ r : ExecutionReceipt 4 7,
      runFrom machine (4*w+4) (config machine.start w counter bound cap false) = some r ∧
      r.final = config 6 w counter bound cap (decide (counter≤bound)) := by
  obtain ⟨base,hbase,hf,hs,_⟩ := Compare.compare_run [] [] (binary w counter) (binary w bound) [] [] [] (by simp)
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add,binary_length,
    binary_value _ _ hn,binary_value _ _ hb] at hbase hf hs
  obtain ⟨padded,hp,hpf,hps,_⟩ := ZeroPadding.run_config Compare.machine capacities _ _ base hbase
  have hin : ZeroPadding.config capacities
      (Compare.config (Compare.scanState true) (frame (binary w counter)) (frame (binary w bound)) 0 0 []) =
      initialConfiguration Compare.machine
        (![frame (binary w counter),frame (binary w bound),[false]] : Fin 3 → List Bool) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,capacities,Compare.config,initialConfiguration,ZeroPadding.pad]
  rw [hin] at hp
  have hend : padded.final = Compare.config 4 (frame (binary w counter)) (frame (binary w bound))
      (2*w) (2*w) [decide (counter≤bound)] := by
    rw [hpf,hf]
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,capacities,Compare.config,ZeroPadding.pad]
  have hsteps : padded.steps = 2*w+1 := hps.trans hs
  obtain ⟨r,hr,ht,hcounter,hheads,_,_⟩ := Rewind.Workspace.reset_workspace Compare.machine (2*w+1)
    (![frame (binary w counter),frame (binary w bound),[false]] : Fin 3 → List Bool) padded hp cap
  rw [hsteps] at hr hcounter
  have htime : 2*(2*w+1)+2 = 4*w+4 := by omega
  rw [htime] at hr
  have hi : initialConfiguration machine
      (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
        (![frame (binary w counter),frame (binary w bound),[false]] : Fin 3 → List Bool)
        (fun _ : Fin 1 => List.replicate cap false)) = config machine.start w counter bound cap false := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [initialConfiguration,config,Fin.addCases]
  change runFrom machine (4*w+4) _ = some r at hr
  have hrun : runFrom machine (4*w+4) (config machine.start w counter bound cap false) = some r := by
    rw [← hi]
    exact hr
  refine ⟨r,hrun,?_⟩
  apply configuration_ext
  · have halted := (prefix_of_run machine (4*w+4) _ r hrun).2
    exact (by decide : ∀ q : Fin 7, machine.halted q = true → q = 6) _ halted
  · funext i
    exact hheads i
  · funext i
    fin_cases i
    · simpa [hend,Compare.config,config] using ht 0
    · simpa [hend,Compare.config,config] using ht 1
    · simpa [hend,Compare.config,config] using ht 2
    · simpa [config,max_eq_left hcap] using hcounter

end NearCubicWires.RepairOrdinary.WitnessCounterCheck
