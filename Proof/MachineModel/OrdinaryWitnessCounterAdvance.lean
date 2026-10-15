import Proof.MachineModel.OrdinaryWitnessCounterCheck

/-! Increment and compare the bounded witness cursor on the same four local
tapes. The long witness and output will be retained by the enclosing loop. -/
namespace NearCubicWires.RepairOrdinary.WitnessCounterAdvance
open LocalBitMultitape SignedSortKey
open WitnessCounterCheck (config)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 4 ≃ Fin 4 where
  toFun := ![0,3,1,2]
  invFun := ![0,2,3,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem inverse : (layout.symm : Fin 4 → Fin 4) = ![0,2,3,1] := rfl
def increment : Machine 4 5 := TapeRenaming.machine layout (TapeEmbedding.machine 2 FramedIncrement.machine)
def machine : Machine 4 12 := Composition.machine increment WitnessCounterCheck.machine

theorem increment_run (w counter bound cap : ℕ) (hn : counter+1<2^w) (hcap : 2*w≤cap) :
    ∃ r : ExecutionReceipt 4 5,
      runFrom increment (4*w+2) (config increment.start w counter bound cap false) = some r ∧
      r.final = config 4 w (counter+1) bound cap false := by
  obtain ⟨base,hb,ht,hc,hh,_,_⟩ := FramedIncrement.increment_run w counter cap hn hcap
  have hfinal : base.final =
      (⟨4,fun _ => 0,![frame (binary w (counter+1)),List.replicate cap false]⟩ : Configuration 2 5) := by
    apply configuration_ext
    · have halted := (prefix_of_run FramedIncrement.machine (4*w+2) _ base hb).2
      exact (by decide : ∀ q : Fin 5, FramedIncrement.machine.halted q = true → q = 4) _ halted
    · funext i
      exact hh i
    · funext i
      fin_cases i
      · exact ht
      · exact hc
  let extra : Fin 2 → List Bool := ![frame (binary w bound),[false]]
  have he := TapeEmbedding.run_embed FramedIncrement.machine (fun _ : Fin 2 => 0) extra _ _ base hb
  have hr := TapeRenaming.run_rename layout (TapeEmbedding.machine 2 FramedIncrement.machine) _ _ _ he
  have hi : TapeRenaming.config layout
      (TapeEmbedding.config (fun _ : Fin 2 => 0) extra
        (initialConfiguration FramedIncrement.machine
          (Fin.addCases (motive := fun _ : Fin (1+1) => List Bool)
            (fun _ : Fin 1 => frame (binary w counter)) (fun _ : Fin 1 => List.replicate cap false)))) =
      config increment.start w counter bound cap false := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,initialConfiguration,
        config,extra,Fin.addCases]
  have hrun : runFrom increment (4*w+2) (config increment.start w counter bound cap false) =
      some (TapeRenaming.receipt layout (TapeEmbedding.receipt (fun _ : Fin 2 => 0) extra base)) := by
    rw [← hi]
    exact hr
  refine ⟨_,hrun,?_⟩
  simp only [TapeRenaming.receipt,TapeEmbedding.receipt,hfinal]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,config,extra,Fin.addCases]

theorem check_run (w counter bound cap : ℕ) (hn : counter+1<2^w) (hb : bound<2^w)
    (hcap : 2*w+1≤cap) :
    ∃ r : ExecutionReceipt 4 12,
      runFrom machine (8*w+7) (config machine.start w counter bound cap false) = some r ∧
      r.final = config 11 w (counter+1) bound cap (decide (counter+1≤bound)) := by
  obtain ⟨first,hf,hff⟩ := increment_run w counter bound cap hn (by omega)
  obtain ⟨last,hl,hlf⟩ := WitnessCounterCheck.compare_run w (counter+1) bound cap hn hb hcap
  have hi : Composition.restart first.final WitnessCounterCheck.machine.start =
      config WitnessCounterCheck.machine.start w (counter+1) bound cap false := by rw [hff]; rfl
  rw [← hi] at hl
  have hr := Composition.run_join increment WitnessCounterCheck.machine (4*w+2) (4*w+4)
    (config increment.start w counter bound cap false) first last hf hl
  have ht : (4*w+2)+1+(4*w+4) = 8*w+7 := by omega
  rw [ht] at hr
  refine ⟨Composition.joinedReceipt first last,hr,?_⟩
  simp only [Composition.joinedReceipt,hlf]
  rfl

end NearCubicWires.RepairOrdinary.WitnessCounterAdvance
