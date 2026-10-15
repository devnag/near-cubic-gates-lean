import Proof.MachineModel.OrdinaryMatrixScoreRight
import Proof.MachineModel.OrdinaryMatrixScoreRecordDock

/-! The whole actual right score and literal stable-id append, retaining
source/assignment and global output cursors in the same26-tape carrier. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreRightRecord
open LocalBitMultitape SignedSortKey MatrixScoreRecordDock
open MatrixScoreWeight (zeros scalar)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def compute := TapeEmbedding.machine 4 MatrixScoreRight.machine
noncomputable def machine := Composition.machine compute MatrixScoreRecordDock.machine
def budget (d p s c m : ℕ) := MatrixScoreRight.budget d p s c+1+(4*(m+(s+1))+7)

theorem right_record_run (left right : List ℤ) (pre suffix apre asuffix : List Bool)
    (p n s c cap m id template : ℕ) (work : Fin 12 → List Bool) (driver counter out : List Bool)
    (hlen : right.length=left.length) (hf : ∀ z ∈ right,z.natAbs<2^p)
    (hw : p≤ s+1) (hc : 4*(s+1)+5≤c) (hm : 2*m≤c) (hcap : cap≤c+1) (hs : ∀ i,(work i).length≤c)
    (hp : MatrixScoreBatch.part false right n<2^s) (hn : MatrixScoreBatch.part true right n<2^s) :
    ∃ finalWork : Fin 12 → List Bool,(∀ i,(finalWork i).length≤c) ∧
      finalWork 0=scalar c (s+1) (shifted s (MatrixScoreBatch.linearForm right n)) ∧
      ∃ actual,runFrom machine (budget left.length p s c m)
        (RecoveryCalls.restarted machine (heads pre.length apre.length out.length)
          (tapes (pre++MatrixScoreCanonical.fields p left++MatrixScoreCanonical.fields p right++suffix)
            (apre++frame (binary left.length n)++asuffix) left.length c cap (s+1) (2^s) m id template work driver counter out))=some actual ∧
        actual.final.heads=heads
          (pre.length+(MatrixScoreCanonical.fields p left).length+(MatrixScoreCanonical.fields p right).length)
          (apre.length+2*left.length)
          (out++StablePartition.recordBits (encode s m (MatrixScoreBatch.linearForm right n) id)).length ∧
        actual.final.tapes=tapes (pre++MatrixScoreCanonical.fields p left++MatrixScoreCanonical.fields p right++suffix)
          (apre++frame (binary left.length n)++asuffix) left.length c (c+1) (s+1) (2^s) m id template finalWork driver counter
          (out++StablePartition.recordBits (encode s m (MatrixScoreBatch.linearForm right n) id)) ∧
        actual.steps≤budget left.length p s c m := by
  let source := pre++MatrixScoreCanonical.fields p left++MatrixScoreCanonical.fields p right++suffix
  let assignment := apre++frame (binary left.length n)++asuffix
  let pos := pre.length+(MatrixScoreCanonical.fields p left).length+(MatrixScoreCanonical.fields p right).length
  let apos := apre.length+2*left.length
  obtain ⟨finalWork,hws,hw0,base,hb,bh,bt,bs⟩ := MatrixScoreRight.right_run left right pre suffix apre asuffix
    p n s c cap work driver counter hlen hf hw hc hcap hs hp hn
  have he := TapeEmbedding.run_embed MatrixScoreRight.machine ![0,0,out.length,0]
    ![frame (binary m id),frame (binary m template),out,zeros c] _ _ base hb
  let expanded := TapeEmbedding.receipt ![0,0,out.length,0]
    ![frame (binary m id),frame (binary m template),out,zeros c] base
  have eh : expanded.final.heads=heads pos apos out.length := by
    funext i; fin_cases i <;> simp [expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,bh,
      heads,MatrixScoreLeftFields.heads,MatrixScoreFoldEntry.heads,pos,apos]
  have et : expanded.final.tapes=tapes source assignment left.length c (c+1) (s+1) (2^s) m id template finalWork driver counter out := by
    funext i; fin_cases i <;> simp [expanded,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,bt,tapes,
      source,assignment]
  obtain ⟨appended,ha,ah,atapes,as⟩ := MatrixScoreRecordDock.append_run source assignment pos apos left.length c (c+1)
    s (2^s) m id template finalWork driver counter out (MatrixScoreBatch.linearForm right n) hw0 hm (by omega)
  have hi : Composition.restart expanded.final MatrixScoreRecordDock.machine.start=
      RecoveryCalls.restarted MatrixScoreRecordDock.machine (heads pos apos out.length)
        (tapes source assignment left.length c (c+1) (s+1) (2^s) m id template finalWork driver counter out) := by
    apply configuration_ext
    · rfl
    · exact eh
    · exact et
  rw [← hi] at ha
  have joined := Composition.run_join compute MatrixScoreRecordDock.machine _ _ _ expanded appended he ha
  have hin : Composition.leftConfig _ (TapeEmbedding.config ![0,0,out.length,0]
      ![frame (binary m id),frame (binary m template),out,zeros c]
      (RecoveryCalls.restarted MatrixScoreRight.machine (MatrixScoreLeftFields.heads pre.length apre.length)
        (MatrixScoreLeftFields.tapes source assignment left.length c cap (s+1) (2^s) 0 work driver counter)))=
      RecoveryCalls.restarted machine (heads pre.length apre.length out.length)
        (tapes source assignment left.length c cap (s+1) (2^s) m id template work driver counter out) := by rfl
  rw [hin] at joined
  refine ⟨finalWork,hws,hw0,Composition.joinedReceipt expanded appended,joined,ah,atapes,?_⟩
  change base.steps+1+appended.steps≤_
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.MatrixScoreRightRecord
