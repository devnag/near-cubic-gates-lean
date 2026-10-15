import Proof.CaseAnalysis.RecoveryRowLoopBank

/-! Dock the entire original address batch directly onto row source58,
preserving the graph and reverse-result append cursors of the outer loop. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRows
open LocalBitMultitape RecoveryRootRound SourceInterfaces RepairSource
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def addressMachine:=RecoveryFocus.machine addressSlots RecoveryBoundedRowAddressBatch.machine

theorem address_input (A : Fin 78→List Bool) (P : Fin 37→List Bool) (out : List Bool)
    (ha : A 58=out) (i : Fin 38) :
    data A P (addressSlots i)=RecoveryBoundedRowAddressBatch.data P out i := by
  refine Fin.addCases (m:=37) (n:=1) (fun j=>?_) (fun j=>?_) i
  · rw [address_old,data_projection,RecoveryBoundedRowAddressBatch.data_old]
  · fin_cases j
    change data A P (addressSlots 37)=out
    rw [address_new,data_row]
    exact ha

theorem address_heads (H : Fin 78→ℕ) (hh : H 58=0) (i : Fin 38) :
    heads H (addressSlots i)=0 := by
  refine Fin.addCases (m:=37) (n:=1) (fun j=>?_) (fun j=>?_) i
  · rw [address_old,heads_projection]
  · fin_cases j
    change heads H (addressSlots 37)=0
    rw [address_new,heads_row]
    exact hh

theorem address_install (A : Fin 78→List Bool) (P Q : Fin 37→List Bool) (out : List Bool) :
    install addressSlots (data A P) (RecoveryBoundedRowAddressBatch.data Q out)=
      data (Function.update A 58 out) Q := by
  funext i
  refine Fin.addCases (m:=78) (n:=37) (fun j=>?_) (fun j=>?_) i
  · change install _ _ _ (rowSlots j)=data _ _ (rowSlots j)
    rw [data_row]
    by_cases hj : j=58
    · subst j
      rw [←address_new,install_slot _ address_injective]
      exact (Function.update_self 58 out A).symm
    · rw [install_other _ _ _ _ (by
        intro k he
        have hv:=congrArg (fun i : Fin 115=>i.val) he
        have hk:=k.isLt;have hlt:=j.isLt
        have hne : j.val≠58:=fun h=>hj (Fin.ext h)
        change (if k.val=37 then 58 else 78+k.val)=j.val at hv
        split_ifs at hv <;> omega),Function.update_of_ne hj]
      exact data_row A P j
  · change install _ _ _ (projectionSlots j)=data _ _ (projectionSlots j)
    rw [←address_old,install_slot _ address_injective,RecoveryBoundedRowAddressBatch.data_old]
    rw [address_old]
    exact (data_projection _ _ j).symm

theorem address_run (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (randomness : BitInput R) (B : ℕ)
    (H : Fin 78→ℕ) (A : Fin 78→List Bool) (hh : H 58=0) (ha : A 58=List.replicate B false)
    (hp : RecoveryProjectionRowsRewind.batchBudget R Q+2≤B)
    (hc : RecoveryBoundedRowAddress.budget (RecoveryProjectionRows.addressFields p R Q hr hq x randomness)+2≤B) :
    let fields:=RecoveryProjectionRows.addressFields p R Q hr hq x randomness
    ∃ r,runFrom addressMachine (RecoveryBoundedRowAddressBatch.budget R Q fields)
      ⟨addressMachine.start,heads H,data A (RecoveryBoundedRowProjection.bank p R Q randomness B)⟩=some r ∧
      r.steps≤RecoveryBoundedRowAddressBatch.budget R Q fields ∧ r.final.heads=heads H ∧
      r.final.tapes=data (Function.update A 58 (ZeroPadding.pad B fields.flatten))
        (Function.update (RecoveryBoundedRowProjection.bank p R Q randomness B) 31
          (ZeroPadding.pad B (FieldList.stream fields))) := by
  have base:=RecoveryBoundedRowAddressBatch.batch_ready p R Q hr hq x randomness B hp hc
  obtain ⟨r,rr,rh,rt,rs⟩:=base.focus_at addressSlots address_injective (heads H)
    (data A (RecoveryBoundedRowProjection.bank p R Q randomness B))
    (address_input A _ _ ha) (address_heads H hh)
  refine ⟨r,rr,rs,rh,?_⟩
  rw [rt,address_install]

end NearCubicWires.RepairOrdinary.RecoveryBoundedRows
