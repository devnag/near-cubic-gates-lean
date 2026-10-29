import SourceAdapters.Machine.CappedInputShape

/-! `app:sources`, "Uniform three-query PCPP and code interfaces", and the proof of `lem:multitape-refuter`: literal loader fields occupy the prepared machine's selected tapes. -/
namespace NearCubicGates.Adapters.Machine.Capped.Layout
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.Joins
set_option autoImplicit false

def extend (p : Program) (data : Fin 8 → List Bool) : Fin (tapes p) → List Bool :=
  Fin.addCases (motive := fun _ : Fin (8+(p.tapeCount+6)) => List Bool) data (fun _ => [])

theorem extend_prepared (p : Program) (cap : ℕ) (word : List Bool) (data : Fin 8 → List Bool)
    (h1 : data 1=frame word) (h2 : data 2=List.replicate cap true) (h3 : data 3=[true])
    (i : Fin (p.tapeCount+1+1+1+1)) :
    extend p data (preparedSlot p i)=preparedInput p cap word i := by
  rw [preparedInput_formula]
  by_cases h0 : i.val=0
  · have he : preparedSlot p i=(1 : Fin 8).castAdd (p.tapeCount+6) := by
      apply Fin.ext; simp [preparedSlot,h0]
    rw [he]
    simpa [extend,h0] using h1
  · by_cases hc : i.val=p.tapeCount
    · have he : preparedSlot p i=(2 : Fin 8).castAdd (p.tapeCount+6) := by
        apply Fin.ext; simp only [preparedSlot,if_neg h0,if_pos hc]
        rfl
      rw [he]
      simpa only [extend,Fin.addCases_left,if_neg h0,if_pos hc] using h2
    · by_cases hs : i.val=p.tapeCount+2
      · have he : preparedSlot p i=(3 : Fin 8).castAdd (p.tapeCount+6) := by
          apply Fin.ext; simp only [preparedSlot,if_neg h0,if_neg hc,if_pos hs]
          rfl
        rw [he]
        simpa only [extend,Fin.addCases_left,if_neg h0,if_neg hc,if_pos hs] using h3
      · let j : Fin (p.tapeCount+6) := ⟨i.val,by have := i.isLt; omega⟩
        have he : preparedSlot p i=j.natAdd 8 := by
          apply Fin.ext; simp [preparedSlot,h0,hc,hs,j]
        rw [he]
        simp [extend,h0,hc,hs]

theorem extend_output (p : Program) (data : Fin 8 → List Bool) :
    extend p data (outputSlot p)=[] := by
  change (Fin.addCases (motive := fun _ : Fin (8+(p.tapeCount+6)) => List Bool) data (fun _ : Fin (p.tapeCount+6) => []))
    ((⟨p.tapeCount+4,by omega⟩ : Fin (p.tapeCount+6)).natAdd 8)=[]
  simp only [Fin.addCases_right]

theorem extend_origin (p : Program) (data : Fin 8 → List Bool) :
    extend p data (originSlot p)=[] := by
  change (Fin.addCases (motive := fun _ : Fin (8+(p.tapeCount+6)) => List Bool) data (fun _ : Fin (p.tapeCount+6) => []))
    ((⟨p.tapeCount+5,by omega⟩ : Fin (p.tapeCount+6)).natAdd 8)=[]
  simp only [Fin.addCases_right]

end NearCubicGates.Adapters.Machine.Capped.Layout
