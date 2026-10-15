import Proof.Amplification.RecoveryBoundedTableLoop

/-! Complete outer-table driver obtained from the abstract bounded-repeat
proof using the actual nested-row supplier and checked-prefix invariant. -/
namespace NearCubicWires.RepairOrdinary.RecoveryOuterTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure RecoveryOuterLeaf
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate RepairSource.VerifierDecoding
open RecoveryRowTable (localAnswer tableCheck)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev states {t s : Nat} (_ : Machine t s) := s
noncomputable abbrev bodySize := states bodyMachine
def accepted (_ : Fin bodySize) (scanned : Fin 84 → Bool) := scanned 50
noncomputable def source (x : Cursor) := x.data.cfg bodyMachine.start
noncomputable def machine := RepeatMachine.machine bodyMachine accepted

theorem iteration_supplier (width limit : Nat) (word outerBits innerBits : List Bool) (innerRows : List Row) (innerRest : List Bool)
    (x : Cursor) (hx : Inv width limit word outerBits innerBits innerRows innerRest x) (hj : x.data.outer.total<limit) :
    ∃ r : ExecutionReceipt 84 bodySize,runFrom bodyMachine (tableBudget width limit) (source x)=some r ∧
      r.steps ≤ tableBudget width limit ∧ r.final.heads 50=0 ∧ r.final.tapes 50=[readRowAnswer x.data outerBits innerBits x.input] ∧
      (readRowAnswer x.data outerBits innerBits x.input=true  → 
        r.final.heads=(source (advance x outerBits innerBits)).heads ∧
        r.final.tapes=(source (advance x outerBits innerBits)).tapes ∧
        Inv width limit word outerBits innerBits innerRows innerRest (advance x outerBits innerBits) ∧
        (advance x outerBits innerBits).data.outer.total=x.data.outer.total+1) := by
  have hb : x.data.outer.bank.row.width=width := hx.ready.1.2.1.2.1.trans hx.sameWidth
  have hp : readMany (readRow x.data.outer.bank.row.width) x.data.outer.total outerBits=some (x.prior,x.input) := by
    rw [hb]; exact hx.parsed
  have hib : x.data.inner.row.width=width := hx.ready.2.2.1.2.1.trans hx.sameWidth
  have hip : readMany (readRow x.data.inner.row.width) x.data.total innerBits=some (innerRows,innerRest) := by
    rw [hib]; exact hx.innerParsed
  have hcapacity : (x.data.outer.total+1)*(RecoveryRowLookupStream.budget x.data.outer.bank.row.width+3)+5 ≤ x.data.outer.lookupCapacity := by
    rw [hb]
    calc
      _ ≤ limit*(RecoveryRowLookupStream.budget width+3)+5 := by gcongr; omega
      _ ≤ _ := hx.capacity
  obtain ⟨r,hr,hrb,hrh,hrt,hgood⟩ := body_run x.data word outerBits innerBits x.pre x.input x.prior innerRows x.input innerRest
    limit hx.ready hx.source hx.sourcePos hp hx.checked hip hx.bounded hx.innerBound hcapacity
  rw [hx.sameWidth] at hr hrb
  refine ⟨r,hr,hrb,hrh,hrt,?_⟩
  intro ha
  obtain ⟨hout,hready⟩ := hgood ha
  have hlen : 4*x.data.outer.base.state.bits.length ≤ x.input.length := by
    have h:=ha
    simp only [readRowAnswer,Bool.and_eq_true,RecoveryCertificateRow.row_isSome,decide_eq_true_eq] at h
    exact h.1
  refine ⟨?_,?_,advance_inv width limit word outerBits innerBits innerRows innerRest x hx hready hj ha,?_⟩
  · rw [hout]; rfl
  · rw [hout]; rfl
  · change (readRowOutput x.data outerBits innerBits x.input).outer.total+1=x.data.outer.total+1
    rw [(read_output_retained x.data outerBits innerBits x.input hlen).2.2.1]

theorem recursive_check (width limit : Nat) (word outerBits innerBits : List Bool) (innerRows : List Row) (innerRest : List Bool)
    (n : Nat) (x : Cursor) (hx : Inv width limit word outerBits innerBits innerRows innerRest x) :
    tableCheck width (predicate innerRows) (n+1) x.prior x.input=
      (readRowAnswer x.data outerBits innerBits x.input &&
        tableCheck width (predicate innerRows) n (advance x outerBits innerBits).prior (advance x outerBits innerBits).input) := by
  cases ha : readRowAnswer x.data outerBits innerBits x.input
  · rw [Bool.false_and]
    exact RecoveryRowTable.table_check_reject width (predicate innerRows) n x.prior x.input
      ((body_answer width limit word outerBits innerBits innerRows innerRest x hx).symm.trans ha)
  · rw [Bool.true_and]
    exact table_advance width innerRows n x outerBits innerBits hx.sameWidth
      ((body_answer width limit word outerBits innerBits innerRows innerRest x hx).symm.trans ha)

theorem table_driver_run (width limit : Nat) (word outerBits innerBits : List Bool) (innerRows : List Row) (innerRest : List Bool)
    (n total pos : Nat) (x : Cursor) (hx : Inv width limit word outerBits innerBits innerRows innerRest x)
    (hn : pos+n=total) (hbound : x.data.outer.total+n ≤ limit) :
    ∃ r,runFrom machine (n*(tableBudget width limit+2)+total+3)
        (RepeatMachine.cfg 0 (source x) total (pos+1))=some r ∧
      r.steps ≤ n*(tableBudget width limit+2)+total+3 ∧
      r.final.control=RepeatMachine.phaseCode bodySize (if tableCheck width (predicate innerRows) n x.prior x.input then 3 else 4) ∧
      r.final.heads 50=0 ∧ (∃ bit,r.final.tapes 50=[bit]) ∧
      (tableCheck width (predicate innerRows) n x.prior x.input=true  →  ∃ out : Cursor,
        r.final=RepeatMachine.cfg 3 (source out) total 1 ∧ Inv width limit word outerBits innerBits innerRows innerRest out ∧
        out.data.outer.total=x.data.outer.total+n) := by
  exact RecoveryBoundedTableLoop.driver_run bodyMachine 50 source
    (fun x=>advance x outerBits innerBits) (fun x=>readRowAnswer x.data outerBits innerBits x.input)
    (fun x=>x.data.outer.total) (Inv width limit word outerBits innerBits innerRows innerRest)
    (fun n x=>tableCheck width (predicate innerRows) n x.prior x.input) (tableBudget width limit) limit
    (fun _ _=>rfl) (fun _ _=>rfl) (fun x _=>⟨x.data.outer.base.valid,rfl⟩) (fun _=>rfl)
    (fun n x hx _=>recursive_check width limit word outerBits innerBits innerRows innerRest n x hx)
    (iteration_supplier width limit word outerBits innerBits innerRows innerRest) n total pos x hx hn hbound

theorem table_run (width limit total : Nat) (word outerBits innerBits : List Bool) (innerRows : List Row) (innerRest : List Bool)
    (x : Cursor) (hx : Inv width limit word outerBits innerBits innerRows innerRest x) (hbound : x.data.outer.total+total ≤ limit) :
    ∃ r,runFrom machine (total*(tableBudget width limit+3)+3)
        (RepeatMachine.cfg 0 (source x) total 1)=some r ∧
      r.steps ≤ total*(tableBudget width limit+3)+3 ∧
      r.final.control=RepeatMachine.phaseCode bodySize (if tableCheck width (predicate innerRows) total x.prior x.input then 3 else 4) ∧
      r.final.heads 50=0 ∧ (∃ bit,r.final.tapes 50=[bit]) ∧
      (tableCheck width (predicate innerRows) total x.prior x.input=true  →  ∃ out : Cursor,
        r.final=RepeatMachine.cfg 3 (source out) total 1 ∧ Inv width limit word outerBits innerBits innerRows innerRest out ∧
        out.data.outer.total=x.data.outer.total+total) := by
  have h := table_driver_run width limit word outerBits innerBits innerRows innerRest total total 0 x hx (by omega) hbound
  have he : total*(tableBudget width limit+2)+total+3=total*(tableBudget width limit+3)+3 := by ring
  simpa only [he,Nat.zero_add] using h

end NearCubicWires.RepairOrdinary.RecoveryOuterTable
