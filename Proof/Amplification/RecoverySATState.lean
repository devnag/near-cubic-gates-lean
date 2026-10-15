import Proof.Amplification.RecoveryViewRetained

/-! Exact RawSAT entry for the same original witness. The next cold copy
phase must produce its nonzero tapes; only false backing is virtual padding. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdSAT
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prefixCap (bits word : List Bool) := RecoveryColdPreliminary.prefixLimit (width bits) (limit bits) word
def clause (bits : List Bool) : RecoveryClauseState.State :=
  {RecoveryColdView.clause (RecoveryColdHeader.zeroWord bits) with capacity:=erase bits+1}
def valuation (bits word : List Bool) : RecoveryClauseEvaluation.Extra :=
  ⟨ZeroPadding.pad (2*prefixCap bits word+1) (frame word),[],[],
    RecoveryColdHeader.zeroWord bits,RecoveryColdHeader.zeroWord bits,
    false,false,false,false,false,limit bits,prefixCap bits word⟩
def state (bits word : List Bool) : RecoveryRawSAT.State :=
  ⟨clause bits,valuation bits word,RecoveryColdView.clause (RecoveryColdHeader.codeWord bits)⟩

theorem width_eq (bits word : List Bool) : (state bits word).width=width bits :=
  RecoveryColdHeader.zero_length bits
theorem valid (bits word : List Bool) : (state bits word).Valid word := by
  refine ⟨RecoveryColdView.clause_valid _,?_,RecoveryColdView.clause_valid _,?_⟩
  · constructor
    · change ZeroPadding.pad (2*prefixCap bits word+1) (frame word)=
        ZeroPadding.pad (2*prefixCap bits word+1) (frame (word.take (prefixCap bits word)))
      unfold prefixCap
      rw [RecoveryColdPreliminary.prefix_take]
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · rfl
    · exact Nat.le_refl _
    · change limit bits≤3*((RecoveryColdHeader.zeroWord bits).length+1)
      rw [RecoveryColdHeader.zero_length]
      change 3*(max 1 bits.length+1)≤3*(max 1 bits.length+2+1)
      omega
    · change limit bits*((RecoveryColdHeader.zeroWord bits).length+2)+1≤prefixCap bits word
      rw [RecoveryColdHeader.zero_length]
      exact RecoveryColdPreliminary.prefix_bound _ _ _
    · change RecoveryReusableUnpair.capacity (RecoveryColdHeader.zeroWord bits)+1≤erase bits+1
      simp only [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,
        RecoveryColdHeader.zero_length,erase,RecoveryColdValuation.capacity]
      exact Nat.le_refl _
  · exact (RecoveryColdHeader.code_length bits).trans (RecoveryColdHeader.zero_length bits).symm

theorem invariant (bits word : List Bool) :
    RecoveryRawSAT.Inv (width bits) (limit bits) 0 0 word (state bits word) := by
  refine ⟨valid bits word,width_eq bits word,rfl,?_,?_⟩
  · exact RecoveryColdHeader.zero_value bits
  · exact RecoveryColdHeader.zero_value bits

def tapes (bits word : List Bool) (i : Fin 70) : List Bool :=
  match i.val with
  | 0=>frame (RecoveryColdHeader.zeroWord bits)
  | 21=>List.replicate (erase bits) true
  | 28=>frame word
  | 30=>CompareMachine.word (width bits+1)
  | 36=>CompareMachine.word (limit bits)
  | 37=>frame (RecoveryColdHeader.zeroWord bits)
  | 38=>frame (RecoveryColdHeader.zeroWord bits)
  | 42=>frame (RecoveryColdHeader.codeWord bits)
  | 63=>List.replicate (erase bits) true
  | _=>[]
def caps (bits word : List Bool) (i : Fin 70) : Nat :=
  if i.val=22 then erase bits+1 else if i.val=28 then 2*prefixCap bits word+1
  else if i.val=33 ∨ i.val=40 then erase bits
  else if i.val=23 ∨ i.val=27 ∨ i.val=31 ∨ i.val=32 ∨ i.val=34 ∨
    i.val=39 ∨ i.val=41 ∨ i.val=65 ∨ i.val=69 then 1 else 0

theorem clause_reset_tapes (data : List Bool) (reset : Nat) :
    (⟨data,reset,fun _=>[],fun _=>[],false,false⟩ : RecoveryClauseState.State).tapes=
      ![frame data,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],
        List.replicate (RecoveryReusableUnpair.capacity data) true,List.replicate reset false,
        [false],[],[],[],[false]] := by
  funext i
  fin_cases i <;> rfl

theorem clause_tapes (bits : List Bool) : (clause bits).tapes=
    ![frame (RecoveryColdHeader.zeroWord bits),[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],
      List.replicate (erase bits) true,List.replicate (erase bits+1) false,[false],[],[],[],[false]] := by
  have h := clause_reset_tapes (RecoveryColdHeader.zeroWord bits) (erase bits+1)
  have he : RecoveryReusableUnpair.capacity (RecoveryColdHeader.zeroWord bits)=erase bits := by
    simp only [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,RecoveryColdHeader.zero_length]
    rfl
  rw [he] at h
  exact h

theorem native_layout {s : Nat} (bits word : List Bool) (q : Fin s) :
    ZeroPadding.config (caps bits word) ⟨q,(fun _=>0),tapes bits word⟩=(state bits word).cfg q := by
  apply configuration_ext
  · rfl
  · rfl
  · change (fun i=>ZeroPadding.pad (caps bits word i) (tapes bits word i))=
      Fin.addCases (m:=42) (n:=28) (motive:=fun _=>List Bool)
        (fun j=>Fin.addCases (m:=28) (n:=14) (motive:=fun _=>List Bool)
          (clause bits).tapes ((valuation bits word).tapes (clause bits)) j)
        (RecoveryColdView.clause (RecoveryColdHeader.codeWord bits)).tapes
    rw [clause_tapes,RecoveryColdView.clause_tapes]
    funext i
    fin_cases i <;> simp [tapes,caps,Fin.addCases,RecoveryClauseEvaluation.Extra.tapes,
      valuation,clause,RecoveryColdView.clause,RecoveryColdHeader.zero_length,RecoveryColdHeader.code_length,
      RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,erase,RecoveryColdValuation.capacity,
      width,ZeroPadding.pad]
    all_goals rfl

end NearCubicWires.RepairOrdinary.RecoveryColdSAT
