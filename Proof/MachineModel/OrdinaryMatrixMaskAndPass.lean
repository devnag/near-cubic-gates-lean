import Proof.MachineModel.OrdinaryMatrixMaskAndLoop

/-! Whole matrix-mask application with one paid source/output return.
All row and width loops execute on their physical sentinels. The mask is
reused per row without a log, and the retained left matrix is restored only
after the complete pass so the next coefficient bit can reuse it. -/
namespace NearCubicWires.RepairOrdinary.MatrixMaskAndPass
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 5) := decide (i=2 ∨ i=3)
noncomputable def machine := MaskedReset.machine MatrixMaskAndLoop.machine selected
def budget (width count : ℕ) := 2*MatrixMaskAndLoop.nativeBudget width count+2
noncomputable def input (mask : List Bool) (rows : List (List Bool)) :=
  Rewind.recording (MatrixMaskAndLoop.nativeCfg mask rows 0 0 []) 0

theorem pass_run (mask : List Bool) (rows : List (List Bool))
    (hwidth : ∀ row ∈ rows,row.length=mask.length) : ∃ actual,
    runFrom machine (budget mask.length rows.length) (input mask rows)=some actual ∧
    (∀ i : Fin 5,actual.final.tapes (i.castAdd 1)=
      (![UnaryTemplate.tape mask.length,mask,rows.flatten,MatrixMaskAndLoop.output mask rows,
        UnaryTemplate.tape rows.length] : Fin 5 → List Bool) i) ∧
    (∀ i : Fin 5,actual.final.heads (i.castAdd 1)=(![1,0,0,0,1] : Fin 5 → ℕ) i) ∧
    actual.final.heads 5=0 ∧ (∃ n,actual.final.tapes 5=List.replicate n false ∧ n≤MatrixMaskAndLoop.nativeBudget mask.length rows.length) ∧
    actual.steps≤budget mask.length rows.length := by
  obtain ⟨base,hb,bf,bs⟩ := MatrixMaskAndLoop.all_run mask rows [] hwidth
  simp only [List.nil_append] at bf
  have hh : ∀ i,selected i=true → base.final.heads i≤base.steps := by
    intro i hi
    have hi23 : i=2 ∨ i=3 := by simpa only [selected,decide_eq_true_eq] using hi
    obtain ⟨hp,_⟩ := prefix_of_run MatrixMaskAndLoop.machine (MatrixMaskAndLoop.nativeBudget mask.length rows.length)
      (MatrixMaskAndLoop.nativeCfg mask rows 0 0 []) base hb
    have h := SelectiveReset.prefix_head hp i
    rcases hi23 with rfl | rfl
    all_goals simpa [MatrixMaskAndLoop.native_heads] using h
  obtain ⟨actual,ha,af,as,_⟩ := MaskedReset.reset_run MatrixMaskAndLoop.machine selected _ _ base hb hh
  have hs : 2*base.steps+2≤budget mask.length rows.length := by unfold budget; omega
  have he := runFrom_moreFuel machine _ (budget mask.length rows.length-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hs] at he
  refine ⟨actual,he,?_,?_,?_,?_,as.trans_le hs⟩
  · intro i
    rw [af,bf]
    simp [SelectiveReset.finished,Rewind.config,Fin.addCases_left,MatrixMaskAndLoop.native_tapes]
  · intro i
    rw [af,bf]
    fin_cases i <;> simp [SelectiveReset.finished,Rewind.config,Fin.addCases,MatrixMaskAndLoop.native_heads,selected]
  · rw [af]
    rfl
  · exact ⟨base.steps,by rw [af]; rfl,bs⟩

end NearCubicWires.RepairOrdinary.MatrixMaskAndPass
