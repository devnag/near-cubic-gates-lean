import Proof.Supplier.RowTupleCommonEquation

/-! The tuple equation caller accepts the binary frame emitted by the
actual enumerator. Its time is bounded using source dimensions and tuple
degree, without a separate supplied selected-occurrence count. -/
namespace NearCubicWires.RepairOrdinary.RowTupleEquationBounds
open LocalBitMultitape RepairRepresentation SignedSortKey RowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem count_le (N : ℕ) (rows : List (List Bool)) (ds : List ℕ)
    (hl : ∀ row∈rows,row.length=N) (hd : ∀ d∈ds,d<rows.length) :
    RowTupleMaskLoop.count rows ds≤N*ds.length := by
  induction ds with
  | nil => simp [RowTupleMaskLoop.count]
  | cons d ds ih =>
    have htail := ih (fun a ha=>hd a (List.mem_cons_of_mem d ha))
    have hm := mask_length N rows d hl (hd d (by simp))
    have hc : (RowTupleMaskLoop.mask rows d).count true≤N := by
      simpa only [hm] using (List.count_le_length (a:=true) (l:=RowTupleMaskLoop.mask rows d))
    simp only [RowTupleMaskLoop.count,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (p w M k : ℕ) :=
  RowTupleMaskReady.budget gs.length w M k (gs.length*k)+1+
    ((n+1)*(RowCommonBounds.bound gs (gs.length*k) p+2*n+13)+3)

theorem budget_le {n : ℕ} (gs : List (ExactThresholdGate n)) (p w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length) :
    RowTupleCommonEquation.budget gs p w M rows ds≤budget gs p w M ds.length := by
  have hc := count_le gs.length rows ds hl hd
  have hi := (index_fields gs.length rows ds hl hd).2
  have hm : RowCommonBounds.bound gs (indices gs.length rows ds).length p≤
      RowCommonBounds.bound gs (gs.length*ds.length) p := by
    rw [hi]
    have hmul := Nat.mul_le_mul_right (RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs))
      (Nat.mul_le_mul_left 65536 (Nat.add_le_add_right hc 1))
    unfold RowCommonBounds.bound
    omega
  unfold RowTupleCommonEquation.budget budget
  apply Nat.add_le_add
  · apply Nat.add_le_add_right
    unfold RowTupleMaskReady.budget
    omega
  · unfold RowCommonCoordinateLoop.budget RowCommonCoordinateLoop.bodyBudget
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    omega

theorem encoded_tuple (w : ℕ) (ds : List ℕ) (hd : ∀ d∈ds,d<2^w) :
    frame (binary (w*ds.length+1) (RowTupleDigits.encode w ds))=
      RowTupleFilterLoop.word w ds++frame [false] := by
  have h := RowTupleFilterReusable.counter_word w ds.length (RowTupleDigits.encode w ds)
    (RowTupleDigits.encode_bound w ds hd)
  rwa [RowTupleDigits.digits_encode w ds hd] at h

theorem input_tuple {n : ℕ} (gs : List (ExactThresholdGate n)) (p w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool) :
    (input gs p w M rows ds tail out).tapes 44=RowTupleFilterLoop.word w ds++tail := by
  change (RecoveryFocus.config tupleSlots (ambient gs p rows ds out).heads
    (ambient gs p rows ds out).tapes
    (Composition.restart (RowTupleMaskReady.input gs.length w M rows ds tail) RowTupleMaskReady.machine.start)).tapes
      (tupleSlots 10)=_
  simp only [RecoveryFocus.config,RecoveryFocus.pick_slot tupleSlots tuple_injective]
  simp [Composition.restart,RowTupleMaskReady.input,RowTupleMaskReady.before,
    RowTupleMaskLoop.cfg,RepairSource.VerifierDecoding.RepeatMachine.cfg,controlConfig,
    ZeroPadding.config,Rewind.Workspace.capacities,Rewind.recording,Rewind.config,TapeEmbedding.config,
    RowTupleMaskBody.cfg,RowMaskLookupReusable.cfg,Fin.addCases,ZeroPadding.pad]

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M)
    (hp : RowCoordinateLoop.width gs (indices gs.length rows ds)≤p) :
    (input gs p w M rows ds (frame [false]++tail) out).tapes 44=
      frame (binary (w*ds.length+1) (RowTupleDigits.encode w ds))++tail ∧
    ∃ r,runFrom machine (budget gs p w M ds.length)
      (input gs p w M rows ds (frame [false]++tail) out)=some r ∧
      r.final.tapes 31=out++RowCoordinateLoop.equationWord p
        (RowCoordinateLoop.equation gs (indices gs.length rows ds)) ∧
      r.final.heads 31=(out++RowCoordinateLoop.equationWord p
        (RowCoordinateLoop.equation gs (indices gs.length rows ds))).length ∧
      r.steps≤budget gs p w M ds.length := by
  constructor
  · rw [input_tuple,encoded_tuple w ds (fun d hh=>(hd d hh).trans hb),List.append_assoc]
  · obtain ⟨r,hr,rt,rh,rs⟩ := RowTupleCommonEquation.equation_run gs p w M rows ds (frame [false]++tail) out hl hd hb hM hp
    have hbound := budget_le gs p w M rows ds hl hd
    have hmore := runFrom_moreFuel machine _ (budget gs p w M ds.length-RowTupleCommonEquation.budget gs p w M rows ds)
      _ r hr
    rw [Nat.add_sub_of_le hbound] at hmore
    exact ⟨r,hmore,rt,rh,rs.trans hbound⟩

end NearCubicWires.RepairOrdinary.RowTupleEquationBounds
