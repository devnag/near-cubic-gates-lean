import Proof.CaseAnalysis.CaseTwoXorBody

/-! The exact list fields of one fixed padded occurrence window. Out-of-range
reads are total notation only; the physical worker is used under window_fit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.AddressWindow
open SourceInterfaces RepairSource RepairRepresentation OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def read {N : ℕ} (point : BitInput N) (i : ℕ) : Bool:=if h : i<N then point ⟨i,h⟩ else false
def field {N : ℕ} (point : BitInput N) (offset width : ℕ) : BitInput width:=fun i=>read point (offset+i.val)
theorem full_field {N : ℕ} (point : BitInput N) : List.ofFn (field point 0 N)=List.ofFn point:=by
  congr 1
  funext i
  simp [field,read,i.isLt]
theorem field_split {N : ℕ} (point : BitInput N) (offset left right : ℕ) :
    List.ofFn (field point offset (left+right))=
      List.ofFn (field point offset left)++List.ofFn (field point (offset+left) right):=by
  rw [List.ofFn_add]
  congr 1
  congr 1
  funext i
  simp only [field,Fin.val_natAdd,Nat.add_assoc]
theorem field_one {N : ℕ} (point : BitInput N) (offset : ℕ) :
    List.ofFn (field point offset 1)=[read point offset]:=by
  simp [List.ofFn_succ,field]

def pre {N : ℕ} (point : BitInput N) (offset : ℕ):=List.ofFn (field point 0 offset)
def padding {N : ℕ} (point : BitInput N) (offset q cb cap : ℕ):=
  List.ofFn (field point (offset+q+cb) (cap-cb))
def tail {N : ℕ} (point : BitInput N) (offset width : ℕ):=
  List.ofFn (field point (offset+width) (N-(offset+width)))
theorem fields {N : ℕ} (point : BitInput N) (offset q cb cap : ℕ)
    (hcb : cb≤cap) (hfit : offset+(q+cap+1)≤N) :
    List.ofFn point=pre point offset++
      AddressFields.word (field point offset q) (field point (offset+q) cb)
        (padding point offset q cb cap) (read point (offset+q+cap))++tail point offset (q+cap+1):=by
  let rest:=N-(offset+(q+cap+1))
  let total:=offset+(q+(cb+((cap-cb)+(1+rest))))
  have htotal : N=total:=by dsimp only [total,rest];omega
  have hpos : offset+q+cb+(cap-cb)=offset+q+cap:=by omega
  have hafter : offset+q+cap+1=offset+(q+cap+1):=by omega
  calc
    List.ofFn point=List.ofFn (field point 0 N):=(full_field point).symm
    _=List.ofFn (field point 0 total):=
      congrArg (fun n=>List.ofFn (field point 0 n)) htotal
    _=_:=by
      dsimp only [total]
      rw [field_split,field_split,field_split,field_split,field_split,field_one]
      simp only [Nat.zero_add]
      rw [hpos,hafter]
      simp only [pre,AddressFields.word,padding,tail,rest,List.append_assoc]

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.AddressWindow
