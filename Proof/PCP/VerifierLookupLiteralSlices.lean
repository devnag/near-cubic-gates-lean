import Proof.PCP.VerifierLookupRuntimeRun

/-! Exact canonical flag and record slices read by the runtime machine.
Both the flattened ordinal and its bounds are derived from the supplied code. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.LookupLiteral
open LocalBitMultitape VerifierEncoding RepairOrdinary SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def header (v : OrdinaryVerifier) : List Bool :=
  List.replicate v.tapeCount true++[false]++List.replicate v.stateCount true++[false]++
    fixedBits (natBitLength v.stateCount) v.machine.start.val

theorem header_length (v : OrdinaryVerifier) :
    (header v).length=v.tapeCount+v.stateCount+natBitLength v.stateCount+2 := by
  simp only [header,List.length_append,List.length_replicate,List.length_singleton,fixedBits,List.length_ofFn]
  omega

theorem split_code (v : OrdinaryVerifier) : code v=header v++flags v++table v := by
  simp only [code,header,flags,table,List.append_assoc]

theorem slice_middle (pre word tail : List Bool) (offset width : ℕ) (hw : offset+width≤word.length) :
    slice (pre++word++tail) (pre.length+offset) width=slice word offset width := by
  have hd : (pre++word++tail).drop (pre.length+offset)=(word++tail).drop offset := by
    rw [List.append_assoc,←List.drop_drop,List.drop_append_length]
  simp only [slice,hd]
  rw [List.drop_append_of_le_length (by omega : offset≤word.length)]
  rw [List.take_append_of_le_length (by simp only [List.length_drop]; omega : width≤(word.drop offset).length)]

theorem getD_slice (word : List Bool) (offset width i : ℕ) (hi : i<width) :
    (slice word offset width).getD i false=word.getD (offset+i) false := by
  simp [slice,List.getD,hi,List.getElem?_drop]

theorem flag_pair (v : OrdinaryVerifier) (q : Fin v.stateCount) :
    slice (code v) ((header v).length+2*q.val) 2=[v.machine.halted q,v.accepting q] := by
  rw [split_code,slice_middle]
  · have h := slice_flat (width:=2) (fun i : Fin v.stateCount=>[v.machine.halted i,v.accepting i])
      (by intro i; rfl) q
    simpa only [flags,Nat.mul_comm] using h
  · rw [flags_length]
    omega

def ordinal (v : OrdinaryVerifier) (q : Fin v.stateCount) (scanned : Fin v.tapeCount→Bool) : ℕ :=
  q.val*2^v.tapeCount+value (List.ofFn scanned)

theorem ordinal_lt (v : OrdinaryVerifier) (q : Fin v.stateCount) (scanned : Fin v.tapeCount→Bool) :
    ordinal v q scanned< v.stateCount*2^v.tapeCount := by
  have hm : value (List.ofFn scanned)<2^v.tapeCount := by simpa only [List.length_ofFn] using value_lt (List.ofFn scanned)
  have hq := Nat.mul_le_mul_right (2^v.tapeCount) (Nat.succ_le_of_lt q.isLt)
  rw [Nat.succ_mul] at hq
  unfold ordinal
  omega

theorem table_record (v : OrdinaryVerifier) (q : Fin v.stateCount) (scanned : Fin v.tapeCount→Bool) :
    slice (table v) (ordinal v q scanned*entryWidth v.tapeCount v.stateCount)
      (entryWidth v.tapeCount v.stateCount)=actionCode (natBitLength v.stateCount) (v.machine.rule q scanned) := by
  let w := entryWidth v.tapeCount v.stateCount
  have hm : value (List.ofFn scanned)<2^v.tapeCount := by simpa only [List.length_ofFn] using value_lt (List.ofFn scanned)
  let mask : Fin (2^v.tapeCount) := ⟨value (List.ofFn scanned),hm⟩
  have hr := slice_flat (fun i : Fin v.stateCount=>
    (List.ofFn fun m : Fin (2^v.tapeCount)=>actionCode (natBitLength v.stateCount)
      (v.machine.rule i (fun tape=>m.val.testBit tape.val))).flatten)
    (by intro i; exact flat_ofFn_length _ (fun _=>actionCode_length _ _)) q
  have he := slice_flat (fun m : Fin (2^v.tapeCount)=>actionCode (natBitLength v.stateCount)
    (v.machine.rule q (fun tape=>m.val.testBit tape.val))) (fun _=>actionCode_length _ _) mask
  have hfit : mask.val*w+w≤2^v.tapeCount*w := by
    have h := Nat.mul_le_mul_right w (Nat.succ_le_of_lt mask.isLt)
    rw [Nat.succ_mul] at h
    exact h
  have hf := Sequential.slice_slice (table v) (q.val*(2^v.tapeCount*w)) (2^v.tapeCount*w) (mask.val*w) w hfit
  have hoff : q.val*(2^v.tapeCount*w)+mask.val*w=ordinal v q scanned*w := by dsimp only [ordinal,mask]; ring
  rw [hoff] at hf
  rw [←hf]
  have hr' : slice (table v) (q.val*(2^v.tapeCount*w)) (2^v.tapeCount*w)=_ := hr
  change slice _ (mask.val*w) w=_ at he
  rw [hr',he]
  have hmask : (fun tape : Fin v.tapeCount=>mask.val.testBit tape.val)=scanned := mask_inverse scanned
  rw [hmask]

def recordOffset (v : OrdinaryVerifier) (q : Fin v.stateCount) (scanned : Fin v.tapeCount→Bool) : ℕ :=
  (header v++flags v).length+ordinal v q scanned*entryWidth v.tapeCount v.stateCount

theorem record_fit (v : OrdinaryVerifier) (q : Fin v.stateCount) (scanned : Fin v.tapeCount→Bool) :
    recordOffset v q scanned+entryWidth v.tapeCount v.stateCount≤(code v).length := by
  have h := Nat.mul_le_mul_right (entryWidth v.tapeCount v.stateCount)
    (Nat.succ_le_of_lt (ordinal_lt v q scanned))
  rw [Nat.succ_mul,←table_length] at h
  rw [recordOffset,split_code]
  simp only [List.length_append]
  omega

theorem code_record (v : OrdinaryVerifier) (q : Fin v.stateCount) (scanned : Fin v.tapeCount→Bool) :
    slice (code v) (recordOffset v q scanned) (entryWidth v.tapeCount v.stateCount)=
      actionCode (natBitLength v.stateCount) (v.machine.rule q scanned) := by
  have h := Nat.mul_le_mul_right (entryWidth v.tapeCount v.stateCount)
    (Nat.succ_le_of_lt (ordinal_lt v q scanned))
  rw [Nat.succ_mul,←table_length] at h
  have hs := slice_middle (header v++flags v) (table v) []
    (ordinal v q scanned*entryWidth v.tapeCount v.stateCount) (entryWidth v.tapeCount v.stateCount) h
  simp only [List.append_nil] at hs
  rw [split_code,recordOffset,hs]
  exact table_record v q scanned

end NearCubicWires.RepairSource.VerifierDecoding.LookupLiteral
