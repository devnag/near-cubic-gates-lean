import Proof.Amplification.RecoveryRowLookupTapes

/-! The shared prior-row lookup reads all four fixed-width fields before
using a code or count. Truncated rows halt false; success keeps the exact
streaming cursor and all arithmetic inputs for the next lookup cell. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowLookupStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem afterRead_width (d : Data) (bits : List Bool) : (d.afterRead bits).row.width=d.row.width :=
  RecoveryRowFields.afterReads_width d.row 0 4 bits

theorem afterRead_valid (d : Data) (bits : List Bool) (hd : d.Valid) : (d.afterRead bits).Valid := by
  refine ⟨RecoveryRowFields.afterReads_valid d.row 0 4 bits hd.1,?_,?_,?_,?_⟩
  · simpa only [Data.afterRead,RecoveryRowFields.afterReads_width] using hd.2.1
  · simpa only [Data.afterRead,RecoveryRowFields.afterReads_width] using hd.2.2.1
  · simpa only [Data.afterRead,RecoveryRowFields.afterReads_width] using hd.2.2.2.1
  · simpa only [Data.afterRead,RecoveryRowFields.afterReads_width] using hd.2.2.2.2

theorem read_run (d : Data) (pre bits : List Bool) (hd : d.Valid)
    (hs : d.row.source=pre++frame bits) (hp : d.row.pos=pre.length) :
    ∃ r,runFrom readMachine (RecoveryRowFields.budget d.row.width) (d.cfg readMachine.start)=some r ∧
      r.steps≤RecoveryRowFields.budget d.row.width ∧ r.final.heads 6=0 ∧
      r.final.tapes 6=[(readRow d.row.width bits).isSome] ∧
      ((readRow d.row.width bits).isSome=true →
        r.final=(d.afterRead bits).cfg (RecoveryCalls.controlCode RecoveryRowFields.sizes none)) := by
  obtain ⟨base,hr,hn,hh,ht,hf⟩ := RecoveryRowFields.row_run d.row pre bits hs hp hd.1
  have h := TapeEmbedding.run_embed RecoveryRowFields.machine (fun _ : Fin 7=>0) d.extra _ _ base hr
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 7=>0) d.extra base,h,hn,?_,?_,?_⟩
  · simpa [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using hh
  · simpa [TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using ht
  · intro ha
    rw [TapeEmbedding.receipt,hf ha]
    rfl

def Data.codeWord (d : Data) (bits : List Bool) := RecoveryRowFields.words d.row.width bits 1
def Data.countWord (d : Data) (bits : List Bool) := RecoveryRowFields.words d.row.width bits 2
def Data.done (d : Data) (bits : List Bool) : Data :=
  (d.afterRead bits).afterCell (d.codeWord bits) (d.countWord bits)

theorem read_cell_run (d : Data) (bits : List Bool) (hd : d.Valid)
    (hw : 4*d.row.width≤bits.length) :
    ∃ r,runFrom cellMachine (16*d.row.width+32) ((d.afterRead bits).cfg cellMachine.start)=some r ∧
      r.final=(d.done bits).cfg r.final.control ∧ r.steps≤16*d.row.width+32 := by
  have hc : (d.codeWord bits).length=(d.afterRead bits).row.width := by
    rw [afterRead_width]
    exact RecoveryRowStream.words_length d.row.width bits 1 hw
  have hn : (d.countWord bits).length=(d.afterRead bits).row.width := by
    rw [afterRead_width]
    exact RecoveryRowStream.words_length d.row.width bits 2 hw
  simpa only [afterRead_width,Data.done] using cell_run (d.afterRead bits) (d.codeWord bits) (d.countWord bits)
    (afterRead_valid d bits hd) hc hn (RecoveryRowFields.four_fields d.row bits 1)
    (RecoveryRowFields.four_fields d.row bits 2)

theorem done_valid (d : Data) (bits : List Bool) (hd : d.Valid)
    (hw : 4*d.row.width≤bits.length) : (d.done bits).Valid := by
  apply afterCell_valid _ _ _ (afterRead_valid d bits hd)
  · rw [afterRead_width]
    exact RecoveryRowStream.words_length d.row.width bits 1 hw
  · rw [afterRead_width]
    exact RecoveryRowStream.words_length d.row.width bits 2 hw

end NearCubicWires.RepairOrdinary.RecoveryRowLookupStream
