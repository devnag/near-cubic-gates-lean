import Proof.Amplification.RecoveryRowLookupGraph

/-! Actual capped scan of a checked prior-row prefix. Each row is physically
read and compared, the first matching count is retained, and a truncated row
stops the same repeat machine without a successful-workspace invariant. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowLookupTable
open LocalBitMultitape RecoveryRowLookupStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Cursor where
  data : Data
  rest : List Bool

def Inv (width : Nat) (x : Cursor) : Prop :=
  x.data.Valid ∧ x.data.row.width=width ∧
    ∃ pre,x.data.row.source=pre++frame x.rest ∧ x.data.row.pos=pre.length
def advance (x : Cursor) : Cursor :=
  ⟨x.data.done x.rest,x.rest.drop (4*x.data.row.width)⟩
def next (x : Cursor) : Bool×Cursor :=
  ((readRow x.data.row.width x.rest).isSome,advance x)
noncomputable def source (x : Cursor) := x.data.cfg RecoveryRowLookupStream.machine.start
def accepted (_ : Fin (Fintype.card (RecoveryCalls.Control RecoveryRowLookupStream.sizes)))
    (scanned : Fin 14→Bool) : Bool := scanned 6
noncomputable def machine := RepeatMachine.machine RecoveryRowLookupStream.machine accepted

theorem next_inv (width : Nat) (x : Cursor) (hx : Inv width x) (ha : (next x).1=true) :
    Inv width (next x).2 := by
  rcases hx with ⟨hd,hw,pre,hs,hp⟩
  have hlong : 4*x.data.row.width≤x.rest.length := by
    simpa only [next,RecoveryCertificateRow.row_isSome,decide_eq_true_eq] using ha
  refine ⟨done_valid x.data x.rest hd hlong,?_,pre++Streaming.marks (x.rest.take (4*x.data.row.width)),?_,?_⟩
  · exact (afterRead_width x.data x.rest).trans hw
  · change (RecoveryRowFields.afterReads x.data.row 0 4 x.rest).source=
      (pre++Streaming.marks (x.rest.take (4*x.data.row.width)))++frame (x.rest.drop (4*x.data.row.width))
    rw [RecoveryRowFields.afterReads_source,List.append_assoc,←Streaming.frame_append,List.take_append_drop]
    exact hs
  · change (RecoveryRowFields.afterReads x.data.row 0 4 x.rest).pos=
      (pre++Streaming.marks (x.rest.take (4*x.data.row.width))).length
    rw [RecoveryRowFields.afterReads_pos _ _ _ _ hlong]
    simp [hp,Streaming.marks_length,List.length_take,Nat.min_eq_left hlong]

theorem row_supplier (width : Nat) (x : Cursor) (hx : Inv width x) :
    ∃ r,runFrom RecoveryRowLookupStream.machine (budget width) (source x)=some r ∧
      r.steps≤budget width ∧ accepted r.final.control r.final.scanned=(next x).1 ∧
      ((next x).1=true → r.final.heads=(source (next x).2).heads ∧
        r.final.tapes=(source (next x).2).tapes ∧ Inv width (next x).2) := by
  rcases hx with ⟨hd,hw,pre,hs,hp⟩
  obtain ⟨r,hr,hn,hh,ht,hf⟩ := row_run x.data pre x.rest hd hs hp
  refine ⟨r,by simpa only [source,hw] using hr,by simpa only [hw] using hn,?_,?_⟩
  · simp only [accepted,Configuration.scanned,hh,ht,next]
    rfl
  · intro ha
    obtain ⟨he,_⟩ := hf ha
    refine ⟨?_,?_,next_inv width x ⟨hd,hw,pre,hs,hp⟩ ha⟩
    · rw [he]; rfl
    · rw [he]; rfl

theorem table_run (width total : Nat) (x : Cursor) (hx : Inv width x) :
    ∃ r,runFrom machine (total*(budget width+3)+3)
        (RepeatMachine.cfg 0 (source x) total 1)=some r ∧
      r.steps≤total*(budget width+3)+3 ∧
      RepeatMachine.Result source total (RepeatMachine.iterate next total x) r.final := by
  exact RepeatMachine.rejecting_repeat_run RecoveryRowLookupStream.machine accepted source next
    (Inv width) (budget width) (by intro x _; rfl) (row_supplier width) total x hx

end NearCubicWires.RepairOrdinary.RecoveryRowLookupTable
