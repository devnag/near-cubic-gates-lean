import Proof.Amplification.RecoveryOuterTableBody

namespace NearCubicWires.RepairOrdinary.RecoveryOuterTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure RecoveryOuterLeaf
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
open RecoveryRowTable (localAnswer tableCheck)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Cursor where
  data : State
  prior : List Row
  input : List Bool
  pre : List Bool

structure Inv (width limit : Nat) (word outerBits innerBits : List Bool) (innerRows : List Row) (innerRest : List Bool)
    (x : Cursor) : Prop where
  ready : x.data.Valid word outerBits innerBits
  sameWidth : x.data.outer.base.state.bits.length=width
  priorLength : x.data.outer.total=x.prior.length
  parsed : readMany (readRow width) x.data.outer.total outerBits=some (x.prior,x.input)
  checked : checkFrom [] x.prior=true
  leaves : x.prior.all (leafCheck (predicate innerRows))=true
  innerParsed : readMany (readRow width) x.data.total innerBits=some (innerRows,innerRest)
  innerBound : x.data.total ≤ limit
  source : x.data.outer.base.source=x.pre++frame x.input
  sourcePos : x.data.outer.base.pos=x.pre.length
  bounded : x.data.outer.total ≤ limit
  capacity : limit*(RecoveryRowLookupStream.budget width+3)+5 ≤ x.data.outer.lookupCapacity

theorem body_answer (width limit : Nat) (word outerBits innerBits : List Bool) (innerRows : List Row) (innerRest : List Bool)
    (x : Cursor) (hx : Inv width limit word outerBits innerBits innerRows innerRest x) :
    readRowAnswer x.data outerBits innerBits x.input=localAnswer width (predicate innerRows) x.prior x.input := by
  cases hp : readRow width x.input with
  | none=>simp only [readRowAnswer,hx.sameWidth,hp,Option.isSome_none,Bool.false_and,localAnswer,Option.any_none]
  | some pair=>
    rcases pair with ⟨row,rest⟩
    have hb : x.data.outer.bank.row.width=width := hx.ready.1.2.1.2.1.trans hx.sameWidth
    have hi : x.data.inner.row.width=width := hx.ready.2.2.1.2.1.trans hx.sameWidth
    have hprefix : readMany (readRow x.data.outer.bank.row.width) x.data.outer.total outerBits=some (x.prior,x.input) := by
      rw [hb]; exact hx.parsed
    have hinner : readMany (readRow x.data.inner.row.width) x.data.total innerBits=some (innerRows,innerRest) := by
      rw [hi]; exact hx.innerParsed
    obtain ⟨_,_,_,_,_,hout⟩ := read_row_run x.data word outerBits innerBits x.pre x.input x.prior innerRows x.input innerRest
      hx.ready hx.source hx.sourcePos hprefix hx.checked hinner
    have hread : (readRow x.data.outer.base.state.bits.length x.input).isSome=true := by rw [hx.sameWidth,hp]; rfl
    obtain ⟨_,_,ha⟩ := hout hread
    have he := RecoveryRowLookupTable.readRow_some width x.input row rest hp
    simp only [readRowAnswer,Bool.true_and,ha,hx.sameWidth,localAnswer,hp,Option.any_some,Option.isSome_some,he.1]

def advance (x : Cursor) (outerBits innerBits : List Bool) : Cursor :=
  ⟨rowAdvanced x.data outerBits innerBits x.input,
    x.prior++[RecoveryRowFields.parsed x.data.outer.base.state.bits.length x.input],
    x.input.drop (4*x.data.outer.base.state.bits.length),
    x.pre++Streaming.marks (x.input.take (4*x.data.outer.base.state.bits.length))⟩

theorem advance_inv (width limit : Nat) (word outerBits innerBits : List Bool) (innerRows : List Row) (innerRest : List Bool)
    (x : Cursor) (hx : Inv width limit word outerBits innerBits innerRows innerRest x)
    (hready : (rowAdvanced x.data outerBits innerBits x.input).Valid word outerBits innerBits)
    (hj : x.data.outer.total<limit) (ha : readRowAnswer x.data outerBits innerBits x.input=true) :
    Inv width limit word outerBits innerBits innerRows innerRest (advance x outerBits innerBits) := by
  have hi : 4*x.data.outer.base.state.bits.length ≤ x.input.length := by
    have h:=ha
    simp only [readRowAnswer,Bool.and_eq_true,RecoveryCertificateRow.row_isSome,decide_eq_true_eq] at h
    exact h.1
  have h := read_output_retained x.data outerBits innerBits x.input hi
  have hlocal := (body_answer width limit word outerBits innerBits innerRows innerRest x hx).symm.trans ha
  have hparse := RecoveryRowFields.readRow_full x.data.outer.base.state.bits.length x.input hi
  rw [←hx.sameWidth] at hlocal
  simp only [localAnswer,hparse,Option.any_some,Bool.and_eq_true] at hlocal
  refine ⟨hready,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact h.2.2.2.2.2.1.trans hx.sameWidth
  · change (readRowOutput x.data outerBits innerBits x.input).outer.total+1=(x.prior++[_]).length
    rw [h.2.2.1,hx.priorLength]
    simp
  · change readMany (readRow width) ((readRowOutput x.data outerBits innerBits x.input).outer.total+1) outerBits=some _
    rw [h.2.2.1]
    apply RecoveryRowTable.readMany_snoc _ _ _ _ _ _ _ hx.parsed
    rw [←hx.sameWidth]
    exact hparse
  · change checkFrom [] (x.prior++[_])=true
    rw [check_append]
    simp only [hx.checked,Bool.true_and,List.nil_append,checkFrom,Bool.and_true]
    exact hlocal.1
  · change (x.prior++[_]).all (leafCheck (predicate innerRows))=true
    simp only [List.all_append,List.all_cons,List.all_nil,Bool.and_true,hx.leaves,Bool.true_and]
    exact hlocal.2
  · change readMany (readRow width) (readRowOutput x.data outerBits innerBits x.input).total innerBits=some _
    rw [h.2.2.2.2.2.2.2.1]
    exact hx.innerParsed
  · change (readRowOutput x.data outerBits innerBits x.input).total ≤ limit
    rw [h.2.2.2.2.2.2.2.1]
    exact hx.innerBound
  · change (readRowOutput x.data outerBits innerBits x.input).outer.base.source=
      (x.pre++Streaming.marks (x.input.take (4*x.data.outer.base.state.bits.length)))++frame (x.input.drop (4*x.data.outer.base.state.bits.length))
    rw [h.1,List.append_assoc,←Streaming.frame_append,List.take_append_drop]
    exact hx.source
  · change (readRowOutput x.data outerBits innerBits x.input).outer.base.pos=_
    rw [h.2.1,hx.sourcePos]
    simp only [advance,List.length_append,Streaming.marks_length,List.length_take,Nat.min_eq_left hi]
    omega
  · change (readRowOutput x.data outerBits innerBits x.input).outer.total+1 ≤ limit
    rw [h.2.2.1]
    omega
  · change _ ≤ (readRowOutput x.data outerBits innerBits x.input).outer.lookupCapacity
    rw [h.2.2.2.2.1]
    exact hx.capacity

end NearCubicWires.RepairOrdinary.RecoveryOuterTable
