import Proof.Amplification.RecoveryViewEntry

/-! The raw-view parser's exact initial bank. Only the false-only inner
count backing is represented by the accepted per-tape padding bridge. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clause (bits : List Bool) : RecoveryClauseState.State :=
  ⟨bits,0,fun _=>[],fun _=>[],false,false⟩
def view (bits word : List Bool) (pos : Nat) : RecoveryRawView.State :=
  ⟨⟨⟨⟨clause (RecoveryColdHeader.zeroWord bits),false⟩,frame word,pos⟩,
    RecoveryColdHeader.boundWord bits,false,true,true⟩,
    clause (RecoveryColdHeader.codeWord bits),0,limit bits⟩
theorem clause_valid (bits : List Bool) : (clause bits).Valid := by
  constructor <;> intro i <;> simp [clause]
theorem view_width (bits word : List Bool) (pos : Nat) : (view bits word pos).width=width bits :=
  RecoveryColdHeader.zero_length bits
theorem view_valid (bits word : List Bool) (pos : Nat) : (view bits word pos).Valid := by
  refine ⟨⟨clause_valid _,?_⟩,clause_valid _,?_,Nat.zero_le _,?_⟩
  · exact (RecoveryColdHeader.bound_length bits).trans (RecoveryColdHeader.zero_length bits).symm
  · exact (RecoveryColdHeader.code_length bits).trans (RecoveryColdHeader.zero_length bits).symm
  · rw [view_width]
    change 3*(max 1 bits.length+1)≤3*(max 1 bits.length+2+1)
    omega

def nativeHeads (pos : Nat) (i : Fin 66) : Nat :=
  if i.val=29 then pos else if i.val=30 ∨ i.val=35 ∨ i.val=64 ∨ i.val=65 then 1 else 0
def nativeTapes (bits word : List Bool) (i : Fin 66) : List Bool :=
  match i.val with
  | 0=>frame (RecoveryColdHeader.zeroWord bits)
  | 21=>List.replicate (erase bits) true
  | 23=>[false]
  | 27=>[false]
  | 28=>[false]
  | 29=>frame word
  | 30=>CompareMachine.word (2*width bits)
  | 31=>frame (RecoveryColdHeader.boundWord bits)
  | 32=>[false]
  | 33=>[true]
  | 34=>[true]
  | 35=>[false]
  | 36=>frame (RecoveryColdHeader.codeWord bits)
  | 57=>List.replicate (erase bits) true
  | 59=>[false]
  | 63=>[false]
  | 64=>CompareMachine.word (limit bits)
  | 65=>[false]
  | _=>[]
def nativeCaps (bits : List Bool) (i : Fin 66) : Nat := if i.val=35 then erase bits else 0

theorem clause_tapes (bits : List Bool) : (clause bits).tapes=
    ![frame bits,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],
      List.replicate (RecoveryReusableUnpair.capacity bits) true,[],[false],[],[],[],[false]] := by
  funext i
  fin_cases i <;> rfl

theorem native_layout {s : Nat} (bits word : List Bool) (pos : Nat) (q : Fin s) :
    ZeroPadding.config (nativeCaps bits) ⟨q,nativeHeads pos,nativeTapes bits word⟩=
      RecoveryRawViewEnd.cfg (view bits word pos) 0 q := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · simp only [ZeroPadding.config,RecoveryRawViewEnd.cfg,
      RecoveryRawView.State.cfg,RecoveryRawView.State.innerCfg,RecoveryRawView.State.extra,
      RecoveryRawView.State.capacity,RecoveryRawLiteralBound.State.cfg,RecoveryRawLiteralBound.State.extra,
      RecoveryRawLiteralStream.State.cfg,RecoveryRawLiteralStream.State.extra,
      RecoveryRawLiteralStream.State.width,RecoveryRawLiteral.State.tapes,
      view,RecoveryBankPair.cfg,TapeEmbedding.config]
    rw [clause_tapes,clause_tapes]
    funext i
    fin_cases i <;> simp [nativeCaps,nativeTapes,Fin.addCases,RecoveryReusableUnpair.capacity,
      RecoveryTapeSupport.capacity,clause,RecoveryColdHeader.zero_length,RecoveryColdHeader.code_length,
      erase,RecoveryColdValuation.capacity,width,RecoveryColdValuation.width,CompareMachine.word]

end NearCubicWires.RepairOrdinary.RecoveryColdView
