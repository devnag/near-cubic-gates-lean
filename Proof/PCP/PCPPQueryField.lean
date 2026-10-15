import Proof.PCP.ProjectionNormalizationStreamBounds
import Proof.MachineModel.OrdinaryWilliamsInputHeader

/-! A reusable physical parser for the unary-length natural fields in the
explicit PCPP object. It copies or skips one complete field, retaining the
source and output endpoints. The width is read from the source and written
on reusable scratch; no width, address, or reset tape is supplied. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryField
open LocalBitMultitape RecoveryExecution Streaming StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (keep : Bool) (bits : List Bool) := if keep then bits else []
def machine (keep : Bool) : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q bits => if q.val=0 then
      some ⟨1,![none,some false,none],![.stay,.right,.stay]⟩
    else if q.val=1 then
      some ⟨if bits 0 then 1 else 2,
        ![none,some (bits 0),if keep then some (bits 0) else none],
        ![.right,if bits 0 then .right else .left,if keep then .right else .stay]⟩
    else if q.val=2 then
      if bits 1 then some ⟨2,![none,none,if keep then some (bits 0) else none],
        ![.right,.left,if keep then .right else .stay]⟩
      else some ⟨3,fun _ => none,fun _ => .stay⟩
    else none

def cfg (q : Fin 4) (source : List Bool) (pos : ℕ) (scratch : List Bool)
    (head : ℕ) (out : List Bool) : Configuration 3 4 :=
  ⟨q,![pos,head,out.length],![source,scratch,out]⟩
def scan (source : List Bool) (pos width : ℕ) (backing out : List Bool) :=
  cfg 1 source pos (overlay (false :: List.replicate width true) backing) (width+1) out
def payload (q : Fin 4) (source : List Bool) (pos width head : ℕ) (backing out : List Bool) :=
  cfg q source pos (overlay (UnaryTemplate.tape width) backing) head out

theorem overlay_read (pre backing : List Bool) (i : ℕ) (hi : i<pre.length) :
    readTapeBit (overlay pre backing) i=readTapeBit pre i := by
  simp only [overlay,readTapeBit,List.getD]
  rw [List.getElem?_append_left hi]

theorem start_step (keep : Bool) (source backing out : List Bool) (pos : ℕ) :
    step (machine keep) (cfg 0 source pos backing 0 out)=some (scan source pos 0 backing out) := by
  have hw : writeTapeBit backing 0 false=overlay [false] backing := by
    simpa [overlay] using overlay_write [] backing false
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,scan,cfg]
  · funext i; fin_cases i <;> simp [applyAction,scan,cfg,hw]

theorem mark_step (keep : Bool) (pre tail backing out : List Bool) (width : ℕ) :
    step (machine keep) (scan (pre++true::tail) pre.length width backing out)=
      some (scan (pre++true::tail) (pre.length+1) (width+1) backing
        (out++selected keep [true])) := by
  have hw := overlay_write (false::List.replicate width true) backing true
  simp only [List.length_cons,List.length_replicate] at hw
  simp [step,machine,scan,cfg,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i; cases keep <;> fin_cases i <;> simp [applyAction,HeadMove.apply,selected]
  · funext i; cases keep <;> fin_cases i <;>
      simp [applyAction,selected,hw,List.replicate_add,write_append]

theorem delimiter_step (keep : Bool) (pre tail backing out : List Bool) (width : ℕ) :
    step (machine keep) (scan (pre++false::tail) pre.length width backing out)=
      some (payload 2 (pre++false::tail) (pre.length+1) width width backing
        (out++selected keep [false])) := by
  have hw := overlay_write (false::List.replicate width true) backing false
  simp only [List.length_cons,List.length_replicate] at hw
  simp [step,machine,scan,cfg,Configuration.scanned,read_append]
  apply configuration_ext
  · rfl
  · funext i; cases keep <;> fin_cases i <;> simp [applyAction,HeadMove.apply,payload,cfg,selected]
  · funext i; cases keep <;> fin_cases i <;>
      simp [applyAction,payload,cfg,selected,hw,UnaryTemplate.tape,write_append]

theorem bit_step (keep bit : Bool) (pre tail backing out : List Bool) (width k : ℕ) (hk : k<width) :
    step (machine keep) (payload 2 (pre++bit::tail) pre.length width (k+1) backing out)=
      some (payload 2 (pre++bit::tail) (pre.length+1) width k backing
        (out++selected keep [bit])) := by
  have hm : readTapeBit (overlay (UnaryTemplate.tape width) backing) (k+1)=true := by
    rw [overlay_read _ _ _ (by simp; omega),UnaryTemplate.tape_mark width k hk]
  simp [step,machine,payload,cfg,Configuration.scanned,hm,read_append]
  apply configuration_ext
  · rfl
  · funext i; cases keep <;> fin_cases i <;> simp [applyAction,HeadMove.apply,selected]
  · funext i; cases keep <;> fin_cases i <;> simp [applyAction,selected,write_append]

theorem stop_step (keep : Bool) (source backing out : List Bool) (pos width : ℕ) :
    step (machine keep) (payload 2 source pos width 0 backing out)=
      some (payload 3 source pos width 0 backing out) := by
  have hz : readTapeBit (overlay (UnaryTemplate.tape width) backing) 0=false := by
    rw [overlay_read _ _ _ (by simp),UnaryTemplate.tape_zero]
  simp [step,machine,payload,cfg,Configuration.scanned,hz]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem header_timed (keep : Bool) (pre tail backing out : List Bool) (width remaining : ℕ) :
    Timed (machine keep) (remaining+1)
      (scan (pre++List.replicate remaining true++false::tail) pre.length width backing out)
      (payload 2 (pre++List.replicate remaining true++false::tail)
        (pre.length+remaining+1) (width+remaining) (width+remaining) backing
        (out++selected keep (List.replicate remaining true++[false]))) := by
  induction remaining generalizing pre width out with
  | zero => simpa [selected] using Timed.single (by rfl) (delimiter_step keep pre tail backing out width)
  | succ remaining ih =>
    have ht := ih (pre++[true]) (out++selected keep [true]) (width+1)
    have hs := Timed.single (by rfl)
      (mark_step keep pre (List.replicate remaining true++false::tail) backing out width)
    have hall := hs.trans (by
      simpa [List.replicate_succ,List.append_assoc,Nat.add_assoc] using ht)
    cases keep <;> simpa [selected,List.replicate_succ,List.append_assoc,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall

theorem payload_timed (keep : Bool) (pre bits tail backing out : List Bool)
    (width : ℕ) (hw : bits.length≤width) :
    Timed (machine keep) (bits.length+1)
      (payload 2 (pre++bits++tail) pre.length width bits.length backing out)
      (payload 3 (pre++bits++tail) (pre.length+bits.length) width 0 backing
        (out++selected keep bits)) := by
  induction bits generalizing pre out with
  | nil => simpa [selected] using Timed.single (by rfl) (stop_step keep (pre++tail) backing out pre.length width)
  | cons bit bits ih =>
    have ht := ih (pre++[bit]) (out++selected keep [bit]) (by simp only [List.length_cons] at hw; omega)
    have hs := Timed.single (by rfl)
      (bit_step keep bit pre (bits++tail) backing out width bits.length (by simp only [List.length_cons] at hw; omega))
    have hall := hs.trans (by simpa [List.append_assoc,Nat.add_assoc] using ht)
    cases keep <;> simpa [selected,List.append_assoc,Nat.add_assoc,Nat.add_comm] using hall

theorem field_run (keep : Bool) (pre bits tail backing out : List Bool) :
    let source := pre++List.replicate bits.length true++false::(bits++tail)
    ∃ r : ExecutionReceipt 3 4,
      runFrom (machine keep) (2*bits.length+3) (cfg 0 source pre.length backing 0 out)=some r ∧
      r.final=payload 3 source (pre.length+2*bits.length+1) bits.length 0 backing
        (out++selected keep (List.replicate bits.length true++false::bits)) ∧
      r.steps=2*bits.length+3 := by
  dsimp only
  let source := pre++List.replicate bits.length true++false::(bits++tail)
  let preHeader := pre++List.replicate bits.length true++[false]
  have hsource : preHeader++bits++tail=source := by simp [preHeader,source,List.append_assoc]
  have hlength : preHeader.length=pre.length+bits.length+1 := by simp [preHeader,Nat.add_assoc]
  have h0 := Timed.single (by rfl) (start_step keep source backing out pre.length)
  have h1 := header_timed keep pre (bits++tail) backing out 0 bits.length
  have h2 := payload_timed keep preHeader bits tail backing
    (out++selected keep (List.replicate bits.length true++[false])) bits.length (by rfl)
  rw [hsource,hlength] at h2
  have hall := (h0.trans (by simpa [source] using h1)).trans h2
  have htime : 1+(bits.length+1)+(bits.length+1)=2*bits.length+3 := by omega
  have hpos : pre.length+bits.length+1+bits.length=pre.length+2*bits.length+1 := by omega
  rw [htime,hpos] at hall
  have hout : (out++selected keep (List.replicate bits.length true++[false]))++selected keep bits=
      out++selected keep (List.replicate bits.length true++false::bits) := by
    cases keep <;> simp [selected,List.append_assoc]
  rw [hout] at hall
  obtain ⟨r,hr,hf,hs⟩ := hall.run (by rfl)
  exact ⟨r,hr,hf,hs⟩

theorem nat_run (keep : Bool) (pre tail backing out : List Bool) (n : ℕ) :
    ∃ r : ExecutionReceipt 3 4,
      runFrom (machine keep) (2*natBitLength n+3)
        (cfg 0 (pre++RepairRepresentation.natWord n++tail) pre.length backing 0 out)=some r ∧
      r.final=payload 3 (pre++RepairRepresentation.natWord n++tail)
        (pre.length+2*natBitLength n+1) (natBitLength n) 0 backing
        (out++selected keep (RepairRepresentation.natWord n)) ∧
      r.steps=2*natBitLength n+3 := by
  simpa [WilliamsInputHeader.natWord_eq,SignedSortKey.binary_length,List.append_assoc]
    using field_run keep pre (SignedSortKey.binary (natBitLength n) n) tail backing out

end NearCubicWires.RepairOrdinary.PCPPQueryField
