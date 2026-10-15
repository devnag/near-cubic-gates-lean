import Proof.CaseAnalysis.RowsSupportReturned
import Proof.CaseAnalysis.RowsCircuitBody

/-! The existing prepared circuit fields enter the support-retaining body
through unchanged old aliases and one independent support accumulator. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem oldIndex_covers (i : Fin 1061) (hi : i≠1059) : ∃ j,oldIndex j=i:=by
  by_cases h60:i.val=1060
  · refine ⟨1059,?_⟩
    exact Fin.ext h60.symm
  · have bound:i.val<1059:=by
      have hn:i.val≠1059:=fun h=>hi (Fin.ext h)
      omega
    let j : Fin 1059:=⟨i.val,bound⟩
    refine ⟨j.castAdd 1,?_⟩
    simp only [oldIndex,Fin.addCases_left]
    exact Fin.ext rfl

theorem lift_heads (p m : ℕ) (native supports : List Bool) (D W : ℕ) (H : Fin 1703 → ℕ)
    (hh : ∀ i,H (CloseoutRowsCircuit.bottomSlots i)=
      CloseoutRowsCircuitBottomDock.localHeads p m native D W i) :
    ∀ i,(Fin.addCases (m:=1703) (n:=1) (motive:=fun _=>ℕ) H (fun _=>supports.length)) (slots i)=
      localHeads p m native supports D W i:=by
  intro i
  by_cases hi:i=1059
  · subst i
    rfl
  · obtain ⟨j,rfl⟩:=oldIndex_covers i hi
    rw [old_slots,Fin.addCases_left,old_heads]
    exact hh j

theorem lift_tapes (C q n : ℕ) (native supports source members : List Bool) (D W : ℕ) (flag : Bool)
    (A : Fin 1703 → List Bool)
    (ht : ∀ i,A (CloseoutRowsCircuit.bottomSlots i)=
      CloseoutRowsCircuitBottomDock.localTapes C q n native source members D W flag i) :
    ∀ i,(Fin.addCases (m:=1703) (n:=1) (motive:=fun _=>List Bool) A (fun _=>supports)) (slots i)=
      localTapes C q n native supports source members D W flag i:=by
  intro i
  by_cases hi:i=1059
  · subst i
    rfl
  · obtain ⟨j,rfl⟩:=oldIndex_covers i hi
    rw [old_slots,Fin.addCases_left,old_tapes]
    exact ht j

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Dock
