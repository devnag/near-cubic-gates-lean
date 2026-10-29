import SourceAdapters.Machine.CappedLayoutSlots

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: identify every prepared input tape with its literal loader field. -/
namespace NearCubicGates.Adapters.Machine.Capped.Layout
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins
set_option autoImplicit false

theorem preparedInput_formula (p : Program) (cap : ℕ) (word : List Bool)
    (i : Fin (p.tapeCount+1+1+1+1)) :
    preparedInput p cap word i =
      if i.val=0 then frame word else if i.val=p.tapeCount then List.replicate cap true
      else if i.val=p.tapeCount+2 then [true] else [] := by
  have hp := p.twoTapes
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) k
      · refine Fin.addCases (fun a => ?_) (fun a => ?_) l
        · have ha := a.isLt
          have hc : a.val ≠ p.tapeCount := by omega
          have hs : a.val ≠ p.tapeCount+2 := by omega
          simp [preparedInput,cappedInputTapes,Program.inputTapes,ha,hc,hs]
        · fin_cases a
          have hn : p.tapeCount ≠ 0 := by omega
          simp [preparedInput,cappedInputTapes,hn]
      · fin_cases l
        simp [preparedInput]
    · fin_cases k
      simp [preparedInput]
      omega
  · fin_cases j
    simp [preparedInput]
    omega

end NearCubicGates.Adapters.Machine.Capped.Layout
