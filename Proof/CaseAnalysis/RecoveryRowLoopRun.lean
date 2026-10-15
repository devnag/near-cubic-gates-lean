import Proof.CaseAnalysis.RecoveryRowLoopAddress

/-! One complete original randomness row starts with its actual source
projector, consumes the raw addresses, and restores its retained row bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRows
open LocalBitMultitape Composition SourceInterfaces RepairRepresentation RepairSource
open RepairSource.ProjectionNormalization BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Calls
variable {a b : ℕ}
def second (row : Machine 78 b):=TapeEmbedding.machine 37 row
def machine (first : Machine 115 a) (row : Machine 78 b):=Composition.machine first (second row)
theorem row_run (row : Machine 78 b) (H : Fin 78→ℕ) (A : Fin 78→List Bool) (P : Fin 37→List Bool)
    (u : ℕ) (base : ExecutionReceipt 78 b)
    (hr : runFrom row u ⟨row.start,H,A⟩=some base) :
    ∃ r,runFrom (second row) u ⟨(second row).start,heads H,data A P⟩=some r ∧
      r.steps=base.steps ∧ r.final.heads=heads base.final.heads ∧ r.final.tapes=data base.final.tapes P := by
  exact ⟨TapeEmbedding.receipt (fun _=>0) P base,TapeEmbedding.run_embed row (fun _=>0) P _ _ base hr,rfl,rfl,rfl⟩
theorem join (first : Machine 115 a) (row : Machine 78 b) (H : Fin 115→ℕ) (A : Fin 115→List Bool)
    (u v : ℕ) (p : ExecutionReceipt 115 a) (q : ExecutionReceipt 115 b)
    (hp : runFrom first u ⟨first.start,H,A⟩=some p)
    (hq : runFrom (second row) v (restart p.final (second row).start)=some q) :
    ∃ r,runFrom (machine first row) (u+1+v) ⟨(machine first row).start,H,A⟩=some r ∧
      r.steps=p.steps+1+q.steps ∧ r.final.heads=q.final.heads ∧ r.final.tapes=q.final.tapes := by
  exact ⟨joinedReceipt p q,Composition.run_join first (second row) _ _ _ p q hp hq,rfl,rfl,rfl⟩
end Calls

noncomputable def rowMachine:=Calls.machine addressMachine RecoveryBoundedRowReusable.machine
def rowBudget (B : ℕ):=128*(B+2)
def rowData (node C D F L B : ℕ) (out : List Bool) (R count Q clauses : ℕ)
    (addresses source stack packet : List Bool):=
  RecoveryBoundedRowAfter.data (RecoveryBoundedRowReuse.paddedData B
    (RecoveryBoundedRow.data node C D F L out R count addresses [] Q source [] clauses)) B stack packet

theorem rowData_address (node C D F L B : ℕ) (out : List Bool) (R count Q clauses : ℕ)
    (addresses source stack packet : List Bool) :
    rowData node C D F L B out R count Q clauses addresses source stack packet=
      Function.update (rowData node C D F L B out R count Q clauses [] source stack packet) 58 (ZeroPadding.pad B addresses) := by
  unfold rowData
  rw [row_address node C D F L out R count [] addresses [] Q source [] clauses,after_address]

theorem row_run (p : RawProjectionPCP) (R Q : ℕ) (hr : p.width≤R) (hq : p.queries≤Q)
    {n bound : ℕ} (x : BitInput n) (b : BooleanDAGBuilder (descriptionWidth R bound))
    (count : ℕ) (hc : count≤bound) (randomness : BitInput R)
    (W D L B S : ℕ) (out sourceTail stack packetTail : List Bool)
    (hfits : RecoveryBoundedQueries.Fits b count W hc
      (projectedAddresses (compactProjectionPCP (p.normalized R Q hr hq)) x randomness))
    (hR : R≤W) (hQ : Q≤W)
    (hFinal : (compileVerifierRow (compactProjectionPCP (p.normalized R Q hr hq)) x b count hc randomness).compiled.final.nodes.length≤W)
    (hD : 8388608*(W+1)^3≤D) (hL : RecoveryBoundedSelectorFinish.logCapacity W≤L)
    (hLC : capacity W+5*W+7≤L) (hCB : capacity W+1≤B) (hDB : D≤B) (hLB : L≤B)
    (hS : 1≤S) (ho : out.length≤S)
    (hp : RecoveryProjectionRowsRewind.batchBudget R Q+2≤B)
    (ha : RecoveryBoundedRowAddress.budget (RecoveryProjectionRows.addressFields p R Q hr hq x randomness)+2≤B) :
    let C:=capacity W
    let F:=OuterPCPRecovery.boundedCircuitFieldLimit R bound
    let clauses:=(Codec.clauses p).length
    let source:=DedupBytes.fields p++sourceTail
    let u:=RecoveryBoundedRow.budget Q clauses W
    let f:=RecoveryBoundedRowPrototype.fields C D F L R count Q clauses
    let packet:=RecoveryBoundedRowReload.word f++packetTail
    let pcp:=compactProjectionPCP (p.normalized R Q hr hq)
    let addresses:=RecoveryBoundedQueries.addressWord (projectedAddresses pcp x randomness)
    let A:=RecoveryBoundedRow.data b.nodes.length C D F L out R count addresses [] Q source [] clauses
    let compiled:=compileVerifierRow pcp x b count hc randomness
    let result:=out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let nextStack:=RecoveryBoundedClauseCollect.pushed compiled.compiled.output.val stack
    (∀ i,(A i).length≤S) → S+u+3≤B →
    (∀ j∈RecoveryBoundedRowReload.ports,(f j).length≤B) → (RecoveryBoundedRowReload.word f).length≤B →
    ∃ r,runFrom rowMachine (rowBudget B)
      ⟨rowMachine.start,heads (RecoveryBoundedRowAfter.heads out stack),
        data (rowData b.nodes.length C D F L B out R count Q clauses [] source stack packet)
          (RecoveryBoundedRowProjection.bank p R Q randomness B)⟩=some r ∧
      r.steps≤rowBudget B ∧
      r.final.heads=heads (RecoveryBoundedRowAfter.heads result nextStack) ∧
      r.final.tapes=data (rowData compiled.compiled.final.nodes.length C D F L B result R count Q clauses [] source nextStack packet)
        (Function.update (RecoveryBoundedRowProjection.bank p R Q randomness B) 31
          (ZeroPadding.pad B (FieldList.stream (RecoveryProjectionRows.addressFields p R Q hr hq x randomness)))) := by
  let C:=capacity W
  let F:=OuterPCPRecovery.boundedCircuitFieldLimit R bound
  let clauses:=(Codec.clauses p).length
  let source:=DedupBytes.fields p++sourceTail
  let u:=RecoveryBoundedRow.budget Q clauses W
  let f:=RecoveryBoundedRowPrototype.fields C D F L R count Q clauses
  let packet:=RecoveryBoundedRowReload.word f++packetTail
  let pcp:=compactProjectionPCP (p.normalized R Q hr hq)
  let addresses:=RecoveryBoundedQueries.addressWord (projectedAddresses pcp x randomness)
  let compiled:=compileVerifierRow pcp x b count hc randomness
  let result:=out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let fields:=RecoveryProjectionRows.addressFields p R Q hr hq x randomness
  let P:=RecoveryBoundedRowProjection.bank p R Q randomness B
  let nextP:=Function.update P 31 (ZeroPadding.pad B (FieldList.stream fields))
  let A0:=rowData b.nodes.length C D F L B out R count Q clauses [] source stack packet
  let A1:=rowData b.nodes.length C D F L B out R count Q clauses addresses source stack packet
  dsimp only
  intro hA hB hf hw
  have baseRun:=RecoveryBoundedRowReusable.row_run pcp x b count hc randomness W D L B S
    out [] sourceTail stack packetTail hfits hR hQ hFinal hD hL hLC hCB hDB hLB hS ho
  dsimp only at baseRun
  rw [RecoveryBoundedRow.original_clause_source,RecoveryBoundedRow.original_clause_count] at baseRun
  simp only [List.append_nil] at baseRun
  obtain ⟨base,br,bs,bh,bt⟩:=baseRun hA hB hf hw
  obtain ⟨a,ar,as,ah,aT⟩:=address_run p R Q hr hq x randomness B
    (RecoveryBoundedRowAfter.heads out stack) A0 (by rfl)
    (by change ZeroPadding.pad B []=List.replicate B false
        simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]) hp ha
  have inject : A1=Function.update A0 58 (ZeroPadding.pad B fields.flatten) := by
    rw [RecoveryBoundedRowAddress.flattened_original]
    exact rowData_address _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  change a.final.tapes=data (Function.update A0 58 (ZeroPadding.pad B fields.flatten)) nextP at aT
  rw [←inject] at aT
  let fuel:=RecoveryBoundedRowReusable.budget u compiled.compiled.output.val B f
  have br' : runFrom RecoveryBoundedRowReusable.machine fuel
      ⟨RecoveryBoundedRowReusable.machine.start,RecoveryBoundedRowAfter.heads out stack,A1⟩=some base := br
  obtain ⟨q,qr,qs,qh,qt⟩:=Calls.row_run RecoveryBoundedRowReusable.machine _ _ nextP fuel base br'
  have qr' : runFrom (Calls.second RecoveryBoundedRowReusable.machine) fuel
      (restart a.final (Calls.second RecoveryBoundedRowReusable.machine).start)=some q := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some q
    rw [ah,aT]
    exact qr
  obtain ⟨r,rr,rs,rh,rt⟩:=Calls.join addressMachine RecoveryBoundedRowReusable.machine
    (heads (RecoveryBoundedRowAfter.heads out stack)) (data A0 P)
    (RecoveryBoundedRowAddressBatch.budget R Q fields) fuel a q ar qr'
  have hW : W≤B := by
    have h:=hCB
    unfold capacity at h
    nlinarith only [h,Nat.zero_le (W^2)]
  have hu : u≤B := by
    change S+u+3≤B at hB
    omega
  have hrow : fuel≤64*(B+2):=RecoveryBoundedRowReusable.budget_backing u compiled.compiled.output.val B f
    hu (compiled.compiled.output.isLt.le.trans (hFinal.trans hW)) hf
  have haddr : RecoveryBoundedRowAddressBatch.budget R Q fields≤4*B+5 := by
    have ha' : RecoveryBoundedRowAddress.budget fields+2≤B:=ha
    unfold RecoveryBoundedRowAddressBatch.budget RecoveryProjectionRowsRewind.budget RecoveryBoundedRowAddress.readyBudget
    omega
  have hbound : RecoveryBoundedRowAddressBatch.budget R Q fields+1+fuel≤rowBudget B := by
    unfold rowBudget
    omega
  have more:=runFrom_moreFuel rowMachine _ (rowBudget B-(RecoveryBoundedRowAddressBatch.budget R Q fields+1+fuel)) _ r rr
  rw [Nat.add_sub_of_le hbound] at more
  refine ⟨r,more,?_,?_,?_⟩
  · rw [rs,qs]
    have hb : base.steps≤fuel:=bs
    have hab : a.steps≤RecoveryBoundedRowAddressBatch.budget R Q fields:=as
    omega
  · exact rh.trans (qh.trans (congrArg heads bh))
  · exact rt.trans (qt.trans (congrArg (fun A=>data A nextP) bt))

end NearCubicWires.RepairOrdinary.RecoveryBoundedRows
