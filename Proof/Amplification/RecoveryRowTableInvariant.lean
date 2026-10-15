import Proof.Amplification.RecoveryRowTableBody

/-! The table-loop invariant identifies the physical prior-count driver
with a parsed, structurally checked prefix of the same retained table. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Cursor where
  data : Children
  prior : List Row
  input : List Bool
  pre : List Bool

structure Inv (width limit : Nat) (word bits : List Bool) (P : Nat→Bool) (x : Cursor) : Prop where
  ready : x.data.Valid word bits
  sameWidth : x.data.base.state.bits.length=width
  priorLength : x.data.total=x.prior.length
  parsed : readMany (readRow width) x.data.total bits=some (x.prior,x.input)
  checked : checkFrom [] x.prior=true
  leaves : x.prior.all (leafCheck P)=true
  predicate : tableLeafPredicate x.data word=P
  source : x.data.base.source=x.pre++frame x.input
  sourcePos : x.data.base.pos=x.pre.length
  bounded : x.data.total ≤ limit
  capacity : limit*(RecoveryRowLookupStream.budget width+3)+5 ≤ x.data.lookupCapacity

theorem readMany_snoc {α : Type} (read : Parser α) (count : Nat) (bits : List Bool)
    (items : List α) (rest : List Bool) (item : α) (tail : List Bool)
    (hp : readMany read count bits=some (items,rest)) (hl : read rest=some (item,tail)) :
    readMany read (count+1) bits=some (items++[item],tail) := by
  induction count generalizing bits items rest with
  | zero =>
    have he : ([],bits)=(items,rest) := Option.some.inj hp
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    simp [readMany,hl]
  | succ count ih =>
    cases hh : read bits with
    | none => rw [RecoveryValuationTable.readMany_head_none read count bits hh] at hp; contradiction
    | some pair =>
      rcases pair with ⟨head,remaining⟩
      rw [RecoveryValuationTable.readMany_head_some read count bits head remaining hh] at hp
      cases hr : readMany read count remaining with
      | none => simp [hr] at hp
      | some pair =>
        rcases pair with ⟨middle,leftover⟩
        rw [hr] at hp
        have he : (head::middle,leftover)=(items,rest) := Option.some.inj hp
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
        rw [RecoveryValuationTable.readMany_head_some read (count+1) bits head remaining hh,
          ih remaining middle leftover hr hl]
        rfl

def advance (x : Cursor) (word bits : List Bool) (out : ReadLeafResult x.data word bits x.input) : Cursor :=
  ⟨rowAdvanced x.data word bits x.input out,
    x.prior++[RecoveryRowFields.parsed x.data.base.state.bits.length x.input],
    x.input.drop (4*x.data.base.state.bits.length),
    x.pre++Streaming.marks (x.input.take (4*x.data.base.state.bits.length))⟩

theorem advance_inv (width limit : Nat) (word bits : List Bool) (P : Nat→Bool) (x : Cursor)
    (hx : Inv width limit word bits P x) (out : ReadLeafResult x.data word bits x.input)
    (hready : (rowAdvanced x.data word bits x.input out).Valid word bits)
    (hj : x.data.total<limit) (ha : readWholeAnswer x.data word bits x.input=true) :
    Inv width limit word bits P (advance x word bits out) := by
  have hi : 4*x.data.base.state.bits.length ≤ x.input.length := by
    simp only [readWholeAnswer,Bool.and_eq_true,RecoveryCertificateRow.row_isSome,decide_eq_true_eq] at ha
    exact ha.1
  have h := read_finished_retained x.data word bits x.input out hi
  have hb : x.data.bank.row.width=width := hx.ready.2.1.2.1.trans hx.sameWidth
  have hparse : readMany (readRow x.data.bank.row.width) x.data.total bits=some (x.prior,x.input) := by
    rw [hb]; exact hx.parsed
  have hlocal := read_whole_answer x.data word bits x.input x.prior x.input hparse hx.checked hi
  rw [hlocal,hx.predicate] at ha
  simp only [Bool.and_eq_true] at ha
  refine ⟨hready,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact h.2.2.2.2.2.1.trans hx.sameWidth
  · change (readFinished x.data word bits x.input out).total+1=(x.prior++[_]).length
    rw [h.2.2.1,hx.priorLength]
    simp
  · change readMany (readRow width) ((readFinished x.data word bits x.input out).total+1) bits=some _
    rw [h.2.2.1]
    apply readMany_snoc _ _ _ _ _ _ _ hx.parsed
    rw [←hx.sameWidth]
    exact RecoveryRowFields.readRow_full _ _ hi
  · change checkFrom [] (x.prior++[_])=true
    rw [check_append]
    simp only [hx.checked,Bool.true_and,List.nil_append,checkFrom,Bool.and_true]
    exact ha.1
  · change (x.prior++[_]).all (leafCheck P)=true
    simp only [List.all_append,List.all_cons,List.all_nil,Bool.and_true,hx.leaves,Bool.true_and]
    exact ha.2
  · change tableLeafPredicate (rowAdvanced x.data word bits x.input out) word=P
    rw [←hx.predicate]
    unfold tableLeafPredicate
    change (fun code=>(readList out.extra.cap (readEntry out.state.bits.length) word).any
      (fun pair=>RepairSource.RecoveryOracle.CompactCertificate.clausePredicate
        (RadixSemantics.value out.extra.committed) (RadixSemantics.value out.extra.binaryCount) pair.1 code))=_
    have hwidth : out.state.bits.length=x.data.base.state.bits.length := h.2.2.2.2.2.1
    have hcount : out.extra.binaryCount=x.data.base.extra.binaryCount := h.2.2.2.2.2.2.1
    have hcommitted : out.extra.committed=x.data.base.extra.committed := h.2.2.2.2.2.2.2.1
    have hcap : out.extra.cap=x.data.base.extra.cap := h.2.2.2.2.2.2.2.2
    rw [hwidth,hcount,hcommitted,hcap]
  · change (readFinished x.data word bits x.input out).base.source=
      (x.pre++Streaming.marks (x.input.take (4*x.data.base.state.bits.length)))++frame (x.input.drop (4*x.data.base.state.bits.length))
    rw [h.1,List.append_assoc,←Streaming.frame_append,List.take_append_drop]
    exact hx.source
  · change (readFinished x.data word bits x.input out).base.pos=_
    rw [h.2.1,hx.sourcePos]
    simp only [advance,List.length_append,Streaming.marks_length,List.length_take,Nat.min_eq_left hi]
    omega
  · change (readFinished x.data word bits x.input out).total+1 ≤ limit
    rw [h.2.2.1]
    omega
  · change _ ≤ (readFinished x.data word bits x.input out).lookupCapacity
    rw [h.2.2.2.2.1]
    exact hx.capacity

end NearCubicWires.RepairOrdinary.RecoveryRowTable
