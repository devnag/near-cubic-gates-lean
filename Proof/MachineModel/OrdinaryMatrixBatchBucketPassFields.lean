import Proof.MachineModel.OrdinaryMatrixBucketPassInput

/-! Actual retained rank/Gates fields and the produced bucket bank belong
to the same original-request execution, ready for the whole bucket pass. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchBucketPassFields
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 37 → Fin 336 :=
  ![306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,
    130,295,291,299,222,329,330,331,332,333,334,162,89,335]
theorem slots_injective : Function.Injective slots := by decide

theorem source_fields (r : Request) :
    ∃ unused : Fin 3 → List Bool,∃ base,
      run MatrixBatchBucketBank.machine (MatrixBatchBucketBank.budget r) (MatrixBatchBucketBank.input r)=some base ∧
      (∀ j,(TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) base.final).tapes (slots j)=
        MatrixBucketGatePass.input r unused j) ∧
      (∀ j,(TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) base.final).heads (slots j)=0) ∧
      base.steps≤MatrixBatchBucketBank.budget r := by
  obtain ⟨ancestor,bankOut,base,hancestor,hbase,bt,bh,localT,localH,fields,counter,bs⟩ := MatrixBatchBucketBank.raw_run r
  obtain ⟨_,same,_,hsame,_,_,r162,h162,_,_,r89,h89,_,_,_,_,_,_,_⟩ := MatrixBatchRankReverse.raw_run r
  have heq : same=ancestor := Option.some.inj (hsame.symm.trans hancestor)
  subst same
  let unused : Fin 3 → List Bool := ![bankOut 28,bankOut 29,bankOut 30]
  have bankEq := MatrixBucketPassInput.bank_fields r bankOut fields counter
  have oldT (j : Fin 34) : base.final.tapes (MatrixBatchBucketBank.slots j)=MatrixBucketPassInput.bank r unused j :=
    (localT j).trans (congrFun bankEq j)
  refine ⟨unused,base,hbase,?_,?_,bs⟩
  · intro j
    rw [MatrixBucketPassInput.input_fields]
    fin_cases j
    all_goals first
      | exact (bt 162).trans r162
      | exact (bt 89).trans r89
      | rfl
      | exact oldT 0 | exact oldT 1 | exact oldT 2 | exact oldT 3 | exact oldT 4 | exact oldT 5
      | exact oldT 6 | exact oldT 7 | exact oldT 8 | exact oldT 9 | exact oldT 10 | exact oldT 11
      | exact oldT 12 | exact oldT 13 | exact oldT 14 | exact oldT 15 | exact oldT 16 | exact oldT 17
      | exact oldT 18 | exact oldT 19 | exact oldT 20 | exact oldT 21 | exact oldT 22 | exact oldT 23
      | exact oldT 24 | exact oldT 25 | exact oldT 26 | exact oldT 27 | exact oldT 28 | exact oldT 29
      | exact oldT 30 | exact oldT 31 | exact oldT 32 | exact oldT 33
  · intro j
    fin_cases j
    all_goals first
      | exact (bh 162).trans h162
      | exact (bh 89).trans h89
      | rfl
      | exact localH 0 | exact localH 1 | exact localH 2 | exact localH 3 | exact localH 4 | exact localH 5
      | exact localH 6 | exact localH 7 | exact localH 8 | exact localH 9 | exact localH 10 | exact localH 11
      | exact localH 12 | exact localH 13 | exact localH 14 | exact localH 15 | exact localH 16 | exact localH 17
      | exact localH 18 | exact localH 19 | exact localH 20 | exact localH 21 | exact localH 22 | exact localH 23
      | exact localH 24 | exact localH 25 | exact localH 26 | exact localH 27 | exact localH 28 | exact localH 29
      | exact localH 30 | exact localH 31 | exact localH 32 | exact localH 33

end NearCubicWires.RepairOrdinary.MatrixBatchBucketPassFields
