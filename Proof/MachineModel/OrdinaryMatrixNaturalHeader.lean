import Proof.MachineModel.OrdinaryMatrixTemplateProduct

/-! The source's natWord header is physically serialized from the actual
framed binary value and raw width driver. This is the source header ABI,
including its unary prefix and one delimiter bit. -/
namespace NearCubicWires.RepairOrdinary.MatrixNaturalHeader
open LocalBitMultitape RecoveryExecution Streaming SignedSortKey RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then
    if bits 1 then some ⟨0,![none,none,some true],![.stay,.right,.right]⟩
    else some ⟨1,![none,none,some false],![.stay,.stay,.right]⟩
    else if q.val=1 then
      if bits 0 then some ⟨2,fun _ => none,![.right,.stay,.stay]⟩
      else some ⟨3,fun _ => none,fun _ => .stay⟩
    else if q.val=2 then some ⟨1,![none,none,some (bits 0)],![.right,.stay,.right]⟩
    else none
def input (bits : List Bool) : Fin 3 → List Bool := ![frame bits,List.replicate bits.length true,[]]
def unary (bits : List Bool) (k : ℕ) : Configuration 3 4 :=
  ⟨0,![0,k,k],![frame bits,List.replicate bits.length true,List.replicate k true]⟩
def cfg (q : Fin 4) (source : List Bool) (w pos : ℕ) (out : List Bool) : Configuration 3 4 :=
  ⟨q,![pos,w,out.length],![source,List.replicate w true,out]⟩
def header (bits : List Bool) := List.replicate bits.length true++[false]

theorem unary_step (bits : List Bool) (k : ℕ) (hk : k < bits.length) :
    step machine (unary bits k)=some (unary bits (k+1)) := by
  simp [step,machine,unary,Configuration.scanned,ClockUnaryProduct.read_unary,hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,List.replicate_add]

theorem delimiter_step (bits : List Bool) :
    step machine (unary bits bits.length)=some (cfg 1 (frame bits) bits.length 0 (header bits)) := by
  have hw : writeTapeBit (List.replicate bits.length true) bits.length false =
      List.replicate bits.length true++[false] := by simpa using write_append (List.replicate bits.length true) false
  simp [step,machine,unary,Configuration.scanned,ClockUnaryProduct.read_unary]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,cfg,header]
  · funext i; fin_cases i <;> simp [applyAction,cfg,header,hw]

theorem unary_timed (bits : List Bool) (k rem : ℕ) (he : k+rem=bits.length) :
    Timed machine (rem+1) (unary bits k) (cfg 1 (frame bits) bits.length 0 (header bits)) := by
  induction rem generalizing k with
  | zero =>
    have hk : k=bits.length := by omega
    subst k
    exact Timed.single (by rfl) (delimiter_step bits)
  | succ rem ih =>
    have ht := (Timed.single (by rfl) (unary_step bits k (by omega))).trans (ih (k+1) (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

theorem marker_step (pre : List Bool) (bit : Bool) (tail out : List Bool) (w : ℕ) :
    step machine (cfg 1 (pre++frame (bit::tail)) w pre.length out)=
      some (cfg 2 (pre++frame (bit::tail)) w (pre.length+1) out) := by
  simp [step,machine,cfg,Configuration.scanned,frame,read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem bit_step (pre : List Bool) (bit : Bool) (tail out : List Bool) (w : ℕ) :
    step machine (cfg 2 (pre++frame (bit::tail)) w (pre.length+1) out)=
      some (cfg 1 (pre++frame (bit::tail)) w (pre.length+2) (out++[bit])) := by
  have hs : pre++frame (bit::tail)=(pre++[true])++bit::frame tail := by simp [frame,List.append_assoc]
  have hp : (pre++[true]).length=pre.length+1 := by simp
  have hr : readTapeBit (pre++frame (bit::tail)) (pre.length+1)=bit := by rw [hs,←hp]; exact read_append _ _ _
  simp [step,machine,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.add_assoc]
  · funext i; fin_cases i <;> simp [applyAction,write_append]

theorem stop_step (pre out : List Bool) (w : ℕ) :
    step machine (cfg 1 (pre++frame []) w pre.length out)=
      some (cfg 3 (pre++frame []) w pre.length out) := by
  simp [step,machine,cfg,Configuration.scanned,frame,read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem binary_timed (pre bits out : List Bool) (w : ℕ) :
    Timed machine (2*bits.length+1) (cfg 1 (pre++frame bits) w pre.length out)
      (cfg 3 (pre++frame bits) w (pre.length+2*bits.length) (out++bits)) := by
  induction bits generalizing pre out with
  | nil => simpa using Timed.single (by rfl) (stop_step pre out w)
  | cons bit bits ih =>
    have ht := (Timed.single (by rfl) (marker_step pre bit bits out w)).trans
      (Timed.single (by rfl) (bit_step pre bit bits out w))
    have htail := ih (pre++[true,bit]) (out++[bit])
    have hsource : (pre++[true,bit])++frame bits=pre++frame (bit::bits) := by simp [frame,List.append_assoc]
    have hlen : (pre++[true,bit]).length=pre.length+2 := by simp
    rw [hsource,hlen] at htail
    have hall := ht.trans htail
    simpa [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add] using hall

theorem header_run (bits : List Bool) :
    ∃ r : ExecutionReceipt 3 4,
      run machine (3*bits.length+2) (input bits)=some r ∧
      r.final=cfg 3 (frame bits) bits.length (2*bits.length) (header bits++bits) ∧
      r.steps=3*bits.length+2 := by
  have hu := unary_timed bits 0 bits.length (by omega)
  have hb := binary_timed [] bits (header bits) bits.length
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hb
  have ht := hu.trans hb
  have htime : (bits.length+1)+(2*bits.length+1)=3*bits.length+2 := by omega
  rw [htime] at ht
  have hin : unary bits 0=initialConfiguration machine (input bits) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at ht
  exact ht.run (by rfl)

def resetMachine := Rewind.machine machine
def resetInput (bits : List Bool) : Fin 4 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (3+1) => List Bool) (input bits) (fun _ : Fin 1 => [])

theorem natural_run (n : ℕ) :
    ∃ r : ExecutionReceipt 4 6,
      run resetMachine (6*natBitLength n+6) (resetInput (binary (natBitLength n) n))=some r ∧
      r.final.tapes 0=frame (binary (natBitLength n) n) ∧
      r.final.tapes 1=List.replicate (natBitLength n) true ∧ r.final.tapes 2=natWord n ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=6*natBitLength n+6 := by
  obtain ⟨base,hb,hf,hs⟩ := header_run (binary (natBitLength n) n)
  obtain ⟨r,hr,ht,hh,hsteps,_⟩ := Rewind.reset_run machine _ _ base hb
  have htime : 2*base.steps+2=6*natBitLength n+6 := by simp only [binary_length] at hs; omega
  rw [htime] at hr hsteps
  refine ⟨r,hr,?_,?_,?_,hh,hsteps⟩
  · exact (ht 0).trans (by rw [hf]; rfl)
  · exact (ht 1).trans (by rw [hf]; simp [cfg])
  · exact (ht 2).trans (by rw [hf]; simp [cfg,header,WilliamsInputHeader.natWord_eq,List.append_assoc])

end NearCubicWires.RepairOrdinary.MatrixNaturalHeader
