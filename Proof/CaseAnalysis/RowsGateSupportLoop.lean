import Proof.CaseAnalysis.RowsGateSupportRun
import Proof.Amplification.RecoveryPaddedCopy

/-! The actual weight-count driver checks and filters all native weights.
It reads the same retained support bitmap, reuses one prefix scratch tape,
and never requests a body call after the last weight. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
open LocalBitMultitape RadixSemantics StablePartition.Workspace
open CloseoutRowsFamilyLoop
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fieldWord (field : Bool×List Bool):=weightWord field.1 field.2
def scratch (fields : List (Bool×List Bool)) (backing : List Bool) : ℕ→List Bool
  | 0=>backing
  | j+1=>overlay (UnaryTemplate.tape (fields.getD j (false,[])).2.length) (scratch fields backing j)
def validity (fields : List (Bool×List Bool)) (membership : List Bool) (flag : Bool) : ℕ→Bool
  | 0=>flag
  | j+1=>checked (membership.getD j false) (validity fields membership flag j) (fields.getD j (false,[])).2
def emission (compressed : Bool) (fields : List (Bool×List Bool)) (membership : List Bool) (j : ℕ):=
  selected compressed (membership.getD j false) (fieldWord (fields.getD j (false,[])))
def entry (fields : List (Bool×List Bool)) (membership backing pre tail : List Bool)
    (flag : Bool) (j : ℕ) (out : List Bool):=
  cfg 0 (pre++fields.flatMap fieldWord++tail) (pre.length+((fields.take j).flatMap fieldWord).length)
    (scratch fields backing j) 0 out (frame membership) (2*j) (validity fields membership flag j)
noncomputable def loop (compressed : Bool):=CloseoutRowsDegreeLoop.machine (machine compressed)
def loopBudget (w count : ℕ):=count*(2*w+7)+3

theorem loop_run (compressed : Bool) (fields : List (Bool×List Bool))
    (membership backing out pre tail : List Bool) (flag : Bool) (w : ℕ)
    (hw : ∀ field∈fields,field.2.length≤w) :
    ∃ actual,runFrom (loop compressed) (loopBudget w fields.length)
      (RepeatMachine.cfg 0 (entry fields membership backing pre tail flag 0 out) fields.length 1)=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (entry fields membership backing pre tail flag fields.length
          (out++(List.range fields.length).flatMap (emission compressed fields membership))) fields.length 1 ∧
      actual.steps≤loopBudget w fields.length:=by
  have supplier:∀ j<fields.length,∀ acc,∃ actual,
      runFrom (machine compressed) (2*w+4) (entry fields membership backing pre tail flag j acc)=some actual ∧
      actual.final.heads=(entry fields membership backing pre tail flag (j+1)
        (acc++emission compressed fields membership j)).heads ∧
      actual.final.tapes=(entry fields membership backing pre tail flag (j+1)
        (acc++emission compressed fields membership j)).tapes ∧ actual.steps≤2*w+4:=by
    intro j hj acc
    let field:=fields.getD j (false,[])
    let fieldPre:=pre++(fields.take j).flatMap fieldWord
    let fieldTail:=(fields.drop (j+1)).flatMap fieldWord++tail
    have hmem:field∈fields:=by
      dsimp only [field]
      rw [List.getD_eq_getElem fields (false,[]) hj]
      exact List.getElem_mem hj
    have hs:fieldPre++weightWord field.1 field.2++fieldTail=pre++fields.flatMap fieldWord++tail:=by
      rw [split_word fields (false,[]) fieldWord j hj]
      simp only [fieldPre,fieldTail,field,fieldWord,List.append_assoc]
    have hm:readTapeBit (frame membership) (2*j+1)=membership.getD j false:=
      RecoveryColdPaddedCopy.frame_data membership j
    obtain ⟨a,ha,af,as⟩:=field_run compressed field.1 (membership.getD j false) fieldPre field.2 fieldTail
      (scratch fields backing j) acc (frame membership) (2*j) (validity fields membership flag j) hm
    have hi:cfg 0 (fieldPre++weightWord field.1 field.2++fieldTail) fieldPre.length
        (scratch fields backing j) 0 acc (frame membership) (2*j) (validity fields membership flag j)=
        entry fields membership backing pre tail flag j acc:=by
      rw [hs]
      simp only [fieldPre,List.length_append,entry]
    rw [hi] at ha
    have hb:2*field.2.length+4≤2*w+4:=by have h:=hw field hmem;omega
    have more:=runFrom_moreFuel (machine compressed) _ (2*w+4-(2*field.2.length+4)) _ a ha
    rw [Nat.add_sub_of_le hb] at more
    refine ⟨a,more,?_,?_,as.le.trans hb⟩
    · rw [af]
      change ![fieldPre.length+(fieldWord field).length,0,
          (acc++emission compressed fields membership j).length,2*j+2,0]=
        ![pre.length+((fields.take (j+1)).flatMap fieldWord).length,0,
          (acc++emission compressed fields membership j).length,2*(j+1),0]
      rw [next_word fields (false,[]) fieldWord j hj]
      simp only [fieldPre,List.length_append,field,Nat.mul_add,Nat.mul_one,Nat.add_assoc]
    · rw [af]
      change ![fieldPre++weightWord field.1 field.2++fieldTail,
          overlay (UnaryTemplate.tape field.2.length) (scratch fields backing j),
          acc++emission compressed fields membership j,frame membership,
          [checked (membership.getD j false) (validity fields membership flag j) field.2]]=_
      rw [hs]
      rfl
  exact CloseoutRowsDegreeLoop.loop_run (machine compressed)
    (entry fields membership backing pre tail flag) (emission compressed fields membership) (2*w+4) fields.length
      (by intro j hj acc;rfl) supplier out

theorem validity_iff (fields : List (Bool×List Bool)) (membership : List Bool) (flag : Bool) (j : ℕ) :
    validity fields membership flag j=true ↔ flag=true ∧
      ∀ k<j,membership.getD k false=false → value (fields.getD k (false,[])).2=0:=by
  induction j with
  | zero=>simp [validity]
  | succ j ih=>
    rw [validity,checked_iff,ih]
    constructor
    · rintro ⟨⟨hf,earlier⟩,last⟩
      refine ⟨hf,?_⟩
      intro k hk hm
      by_cases he:k=j
      · subst k;exact last hm
      · exact earlier k (by omega) hm
    · rintro ⟨hf,all⟩
      exact ⟨⟨hf,fun k hk=>all k (by omega)⟩,all j (by omega)⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
