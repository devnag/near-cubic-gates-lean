import Proof.MachineModel.OrdinaryMatrixRightPassEntry

/-! All physical right-pass fields are obtained from one actual original-
request run. The bank allocation/reset, retained left endpoint and rank
return are aligned by deterministic run equality; the only new tape is the
blank log recorded by the enclosing output rewind. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchRightPassFields
open LocalBitMultitape MatrixScoreBatch
open MatrixRightPassEntry (native)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 39 → Fin 348 :=
  ![306,307,308,309,310,311,312,313,344,315,316,317,318,319,320,321,322,323,324,325,326,327,328,
    130,295,291,299,222,329,330,331,332,333,334,162,345,346,89,347]
theorem slots_injective : Function.Injective slots := by decide

theorem native_slots (j : Fin 36) (h8 : j≠8) :
    slots ((native j).castAdd 1)=((MatrixBatchLeftRetained.nativeSlot j).castAdd 3).castAdd 1 := by
  fin_cases j <;> first | exact (h8 rfl).elim | rfl

theorem native_left (j : Fin 35) : (native (j.castAdd 1)).castAdd 1=j.castAdd 4 := by
  apply Fin.ext
  simp [native,j.isLt]

theorem new_tapes (r : Request) (unused : Fin 3 → List Bool) (store : MatrixBucketGateLoop.Store r)
    (j : Fin 4) : MatrixRightBankEntry.output r (![0,3,1,2] j)=
      (MatrixRightGatePass.input r unused store).tapes (![8,17,35,36] j) := by
  fin_cases j
  all_goals simp [MatrixRightBankEntry.output,MatrixRightBankEntry.cleared,MatrixRightGatePass.input,Rewind.recording,Rewind.config,
    MatrixRightGateBootstrap.input,MatrixRightGateBootstrap.target,MatrixRightGateNativeLoop.cfg_tapes,
    MatrixRightGateLayout.data,MatrixRightGateLoop.state,MatrixBucketGatePrepare.data,
    MatrixBucketGatePrepare.native_core,MatrixBucketGatePrepare.core,MatrixBucketGatePrepare.extra,
    Fin.addCases,MatrixScoreWeight.scalar,MatrixScoreWeight.zeros,ZeroPadding.pad]

theorem source_fields (r : Request) :
    ∃ unused : Fin 3 → List Bool,∃ store : MatrixBucketGateLoop.Store r,∃ base,
      run MatrixBatchRightBank.machine (MatrixBatchRightBank.budget r) (MatrixBatchRightBank.input r)=some base ∧
      (∀ j,(TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) base.final).tapes (slots j)=
        (MatrixRightGatePass.input r unused store).tapes j) ∧
      (∀ j,(TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) base.final).heads (slots j)=
        (MatrixRightGatePass.input r unused store).heads j) ∧
      base.final.tapes 342=MatrixBucketLeftPlane.plane r ∧ base.final.heads 342=0 ∧
      base.steps≤MatrixBatchRightBank.budget r := by
  obtain ⟨unused,store,left,ret,hleft,hret,_,planeT,planeH,nt,rh,oldR,_⟩ := MatrixBatchRightReturn.raw_run r
  obtain ⟨other,otherStore,same,hs,_,_,_,nh,_,_,_,_,_⟩ := MatrixBatchLeftRetained.retained_run r
  have he : same=left := Option.some.inj (hs.symm.trans hleft)
  subst same
  obtain ⟨ret',base,hret',hb,bt,bh,oldT,oldH,bs⟩ := MatrixBatchRightBank.raw_run r
  have he : ret'=ret := Option.some.inj (hret'.symm.trans hret)
  subst ret'
  let actual := TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => []) base.final
  have fields (j : Fin 36) (h8 : j≠8) (h17 : j≠17) :
      actual.tapes (slots ((native j).castAdd 1))=(MatrixRightGatePass.input r unused store).tapes ((native j).castAdd 1) := by
    rw [native_slots j h8]
    simp only [actual,TapeEmbedding.config,Fin.addCases_left]
    have hn : MatrixBatchLeftRetained.nativeSlot j≠323 := by
      fin_cases j <;> first | exact (h17 rfl).elim | decide
    rw [oldT _ hn]
    simpa only [MatrixRightGatePass.input,Rewind.recording,Rewind.config,Fin.addCases_left,MatrixRightGateBootstrap.input] using
      (nt j h8).trans (MatrixRightPassEntry.old_tapes r unused store j h8 h17)
  have heads (j : Fin 36) (h8 : j≠8) (h34 : j≠34) (h35 : j≠35) :
      actual.heads (slots ((native j).castAdd 1))=(MatrixRightGatePass.input r unused store).heads ((native j).castAdd 1) := by
    rw [native_slots j h8]
    simp only [actual,TapeEmbedding.config,Fin.addCases_left]
    rw [oldH]
    have hn : ∀ k,MatrixBatchRightReturn.slots k≠MatrixBatchLeftRetained.nativeSlot j := by
      fin_cases j <;> first | exact (h34 rfl).elim | exact (h35 rfl).elim | decide
    rw [oldR _ hn]
    simpa only [MatrixRightGatePass.input,Rewind.recording,Rewind.config,Fin.addCases_left,MatrixRightGateBootstrap.input] using
      (nh j h8).trans (MatrixRightPassEntry.old_heads r other unused otherStore store j h8 h34 h35)
  have rightT (j : Fin 4) : actual.tapes (![344,323,345,346] j)=
      (MatrixRightGatePass.input r unused store).tapes (![8,17,35,36] j) := by
    fin_cases j
    · exact (bt 0).trans (new_tapes r unused store 0)
    · exact (bt 3).trans (new_tapes r unused store 1)
    · exact (bt 1).trans (new_tapes r unused store 2)
    · exact (bt 2).trans (new_tapes r unused store 3)
  have rightH (j : Fin 3) : actual.heads (![344,345,346] j)=0 := by
    fin_cases j <;> first | exact bh 0 | exact bh 1 | exact bh 2
  have sourceH : actual.heads 162=0 := (oldH 162).trans (rh 0)
  have gatesH : actual.heads 89=0 := (oldH 89).trans (rh 3)
  refine ⟨unused,store,base,hb,?_,?_,(oldT 342 (by decide)).trans planeT,(oldH 342).trans planeH,bs⟩
  · intro j
    refine Fin.addCases (m := 35) (n := 4) (motive := fun k => actual.tapes (slots k)=
      (MatrixRightGatePass.input r unused store).tapes k) ?_ ?_ j
    · intro k
      by_cases h8 : k=8
      · subst k; exact rightT 0
      by_cases h17 : k=17
      · subst k; exact rightT 1
      have hh := fields (k.castAdd 1) (by exact fun h => h8 (Fin.ext (congrArg (fun x : Fin 36 => x.val) h)))
        (by exact fun h => h17 (Fin.ext (congrArg (fun x : Fin 36 => x.val) h)))
      simpa only [native_left] using hh
    · intro k
      fin_cases k
      · exact rightT 2
      · exact rightT 3
      · exact fields 35 (by decide) (by decide)
      · rfl
  · intro j
    refine Fin.addCases (m := 35) (n := 4) (motive := fun k => actual.heads (slots k)=
      (MatrixRightGatePass.input r unused store).heads k) ?_ ?_ j
    · intro k
      by_cases h8 : k=8
      · subst k; exact rightH 0
      by_cases h34 : k=34
      · subst k; exact sourceH
      have hh := heads (k.castAdd 1) (by exact fun h => h8 (Fin.ext (congrArg (fun x : Fin 36 => x.val) h)))
        (by exact fun h => h34 (Fin.ext (congrArg (fun x : Fin 36 => x.val) h))) (by
          intro h
          have hv := congrArg Fin.val h
          change k.val=35 at hv
          omega)
      simpa only [native_left] using hh
    · intro k
      fin_cases k
      · exact rightH 1
      · exact rightH 2
      · exact gatesH
      · rfl

end NearCubicWires.RepairOrdinary.MatrixBatchRightPassFields
