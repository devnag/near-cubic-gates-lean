import Proof.PCP.PCPPRequestTaggedBounds

/-! Actual finite tag classifier. Among tags0..4, exactly3/4 have canonical
natural codes at least eight bits long. The transition table reads at most
eight framed bits; its five finite cases are kernel checked. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestTagArity
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 2 19 where
  descriptionBits := 0
  start := 0
  halted := fun q => decide (17 ≤ q.val)
  rule := fun q bs => if h : q.val<16 then
      if q.val%2=0 ∧ bs 0=false then
        some ⟨18,![none,some false],fun _ => .stay⟩
      else some ⟨⟨q.val+1,by omega⟩,fun _ => none,![.right,.stay]⟩
    else some ⟨17,![none,some true],fun _ => .stay⟩

def code (tag : Fin 5) := (CanonicalBinary.encodeNat tag.val).bits
def input (tag : Fin 5) : Fin 2 → List Bool := ![frame (code tag),[]]
def outputFlag (tag : Fin 5) := decide (3 ≤ tag.val)
def steps (tag : Fin 5) := min (2*(code tag).length+1) 17
def observed (r : ExecutionReceipt 2 19) :=
  (r.final.tapes 0,r.final.tapes 1,r.final.heads 1,r.steps)

theorem tag_codes (tag : Fin 5) :
    CanonicalBinary.encodeNat tag.val=(![0,3,123,227,19580627] : Fin 5 → ℕ) tag := by
  have h2 : (2 : ℕ).bits=[false,true] := by
    rw [show (2 : ℕ)=2*1 from rfl,Nat.bit0_bits 1 (by decide),Nat.one_bits]
  have h3 : (3 : ℕ).bits=[true,true] := by
    rw [show (3 : ℕ)=2*1+1 from rfl,Nat.bit1_bits,Nat.one_bits]
  have h4 : (4 : ℕ).bits=[false,false,true] := by
    rw [show (4 : ℕ)=2*2 from rfl,Nat.bit0_bits 2 (by decide),h2]
  fin_cases tag <;> norm_num [CanonicalBinary.encodeNat,CanonicalBinary.encodeBits,
    CanonicalBinary.encodeBoolList,CanonicalBinary.encodeBalancedList,CanonicalBinary.boolCode,Nat.pair,h2,h3,h4]

theorem finite_cases (tag : Fin 5) :
    (run raw 17 (input tag)).map observed=
      some (frame (code tag),[outputFlag tag],0,steps tag) := by
  simp only [input,code,steps,tag_codes]
  fin_cases tag <;> decide

theorem raw_run (tag : Fin 5) :
    ∃ r,run raw 17 (input tag)=some r ∧ r.final.tapes 0=frame (code tag) ∧
      r.final.tapes 1=[outputFlag tag] ∧ r.final.heads 1=0 ∧ r.steps=steps tag := by
  have h := finite_cases tag
  cases hr : run raw 17 (input tag) with
  | none => simp [hr] at h
  | some r =>
    simp only [hr,Option.map_some,Option.some.injEq,Prod.mk.injEq,observed] at h
    exact ⟨r,rfl,h⟩

noncomputable def machine := Rewind.machine raw
def output (tag : Fin 5) : Fin 3 → List Bool :=
  ![frame (code tag),[outputFlag tag],List.replicate (steps tag) false]

theorem tag_run (tag : Fin 5) :
    ClockJoin.ReadyRun machine 36 (fun j => if j=0 then frame (code tag) else []) (output tag) := by
  obtain ⟨base,hb,b0,b1,bh1,bs⟩ := raw_run tag
  obtain ⟨r,hr,ht,hc,hh,hs,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have hbound : 2*base.steps+2 ≤ 36 := by rw [bs]; unfold steps; omega
  have more := run_moreFuel machine _ (36-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hbound] at more
  refine ⟨r,?_,?_,hh,hs.trans_le hbound⟩
  · convert more using 2
    funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · exact (ht 0).trans b0
    · exact (ht 1).trans b1
    · change r.final.tapes 2=List.replicate (steps tag) false
      have he : (Fin.natAdd 2 (0 : Fin 1) : Fin 3)=2 := by decide
      rw [he,bs,Nat.zero_max] at hc
      exact hc

end NearCubicWires.RepairOrdinary.PCPPRequestTagArity
