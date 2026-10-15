import Proof.MachineModel.OrdinaryMatrixRightBankEntry

/-! Literal right-bank entry fields from the actual retained native bank,
plus precisely three new blank tapes. No scratch or coordinate is assumed. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchRightBankFields
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 9 → Fin 347 := ![344,345,346,323,130,334,299,332,333]
theorem slots_injective : Function.Injective slots := by decide
def native : Fin 6 → Fin 36 := ![17,23,33,26,31,32]

theorem native_fields (r : Request) (unused : Fin 3 → List Bool) (store : MatrixBucketGateLoop.Store r) :
    ∀ j,(MatrixBucketGateFinish.final r unused store).tapes (native j)=
      MatrixRightBankEntry.input r r.Used ⟨j.val+3,by omega⟩ := by
  intro j
  fin_cases j
  all_goals simp [native,MatrixBucketGateFinish.final,MatrixBucketGateFinish.before,
    MatrixBucketGateNativeLoop.cfg_tapes,MatrixBucketGatePrepare.data,MatrixBucketGatePrepare.native_core,
    MatrixBucketGatePrepare.core,MatrixBucketGatePrepare.extra,Fin.addCases,
    MatrixRightBankEntry.input,MatrixScoreWeight.scalar,MatrixScoreWeight.zeros]
  all_goals rfl

theorem source_fields (r : Request) : ∃ base,
    run MatrixBatchRightReturn.machine (MatrixBatchRightReturn.budget r) (MatrixBatchRightReturn.input r)=some base ∧
    (∀ j,(TapeEmbedding.config (fun _ : Fin 3 => 0) (fun _ : Fin 3 => []) base.final).tapes (slots j)=
      MatrixRightBankEntry.input r r.Used j) ∧
    (∀ j,(TapeEmbedding.config (fun _ : Fin 3 => 0) (fun _ : Fin 3 => []) base.final).heads (slots j)=0) ∧
    base.steps≤MatrixBatchRightReturn.budget r := by
  obtain ⟨unused,store,left,base,hleft,hb,_,_,_,nt,_,old,bs⟩ := MatrixBatchRightReturn.raw_run r
  obtain ⟨_,_,same,hs,_,_,_,nh,_,_,_,_,_⟩ := MatrixBatchLeftRetained.retained_run r
  have he : same=left := Option.some.inj (hs.symm.trans hleft)
  subst same
  have fields (j : Fin 6) : base.final.tapes (MatrixBatchLeftRetained.nativeSlot (native j))=
      MatrixRightBankEntry.input r r.Used ⟨j.val+3,by omega⟩ :=
    (nt (native j) (by fin_cases j <;> decide)).trans (native_fields r unused store j)
  have heads (j : Fin 6) : base.final.heads (MatrixBatchLeftRetained.nativeSlot (native j))=0 := by
    have hn : ∀ k,MatrixBatchRightReturn.slots k≠MatrixBatchLeftRetained.nativeSlot (native j) := by
      fin_cases j <;> decide
    apply (old _ hn).trans
    apply (nh (native j) (by fin_cases j <;> decide)).trans
    fin_cases j <;> rfl
  refine ⟨base,hb,?_,?_,bs⟩
  · intro j
    fin_cases j
    all_goals first | rfl | exact fields 0 | exact fields 1 | exact fields 2 | exact fields 3 | exact fields 4 | exact fields 5
  · intro j
    fin_cases j
    all_goals first | rfl | exact heads 0 | exact heads 1 | exact heads 2 | exact heads 3 | exact heads 4 | exact heads 5

end NearCubicWires.RepairOrdinary.MatrixBatchRightBankFields
