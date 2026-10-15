import Proof.Amplification.RecoverySelectedCertificate

/-! Literal cold marker bank. The original code and both initially zero
metadata words are physical framed fields; only false scratch is padding. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdMarker
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def inner (bits : List Bool) : RecoveryClauseState.State :=
  ⟨RecoveryColdHeader.zeroWord bits,erase bits+1,fun _=>[],
    Function.update (fun _=>[]) 1 (frame (RecoveryColdHeader.zeroWord bits)),false,false⟩
def outer (bits : List Bool) : RecoveryClauseState.State :=
  ⟨RecoveryColdHeader.codeWord bits,0,fun _=>[],
    Function.update (fun _=>[]) 2 (frame (RecoveryColdHeader.zeroWord bits)),false,false⟩
def state (bits : List Bool) : RecoveryMarkerClause.State := ⟨⟨inner bits,false⟩,outer bits⟩

theorem valid (bits : List Bool) : (state bits).Valid := by
  have hz := RecoveryColdHeader.zero_length bits
  have hc := RecoveryColdHeader.code_length bits
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,hc.trans hz.symm⟩
  · intro i; exact Nat.zero_le _
  · intro i; fin_cases i <;> simp [state,inner,frame_length,hz]
  · intro i; exact Nat.zero_le _
  · intro i; fin_cases i <;> simp [state,outer,frame_length,hz,hc]

theorem initial_metadata (bits : List Bool) :
    (RecoveryMarkerMetadata.read (state bits)).committed=frame (List.replicate (width bits) false) ∧
    (RecoveryMarkerMetadata.read (state bits)).count=frame (List.replicate (width bits) false) := by
  simp [RecoveryMarkerMetadata.read,state,inner,outer,RecoveryColdHeader.zeroWord,
    RecoveryColdPaddedCopy.data_eq_pad,RecoveryColdHeader.width,width]
  rfl

theorem fields_tapes (data : List Bool) (reset : Nat) (fields : Fin 3→List Bool) :
    (⟨data,reset,fun _=>[],fields,false,false⟩ : RecoveryClauseState.State).tapes=
      ![frame data,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],
        List.replicate (RecoveryReusableUnpair.capacity data) true,List.replicate reset false,
        [false],fields 0,fields 1,fields 2,[false]] := by
  funext i
  fin_cases i <;> rfl

def tapes (bits : List Bool) (i : Fin 57) : List Bool :=
  match i.val with
  | 0 | 25 | 55 => frame (RecoveryColdHeader.zeroWord bits)
  | 29 => frame (RecoveryColdHeader.codeWord bits)
  | 21 | 50 => List.replicate (erase bits) true
  | _ => []
def caps (bits : List Bool) (i : Fin 57) : Nat :=
  if i.val=22 then erase bits+1 else
  if i.val=23 ∨ i.val=27 ∨ i.val=28 ∨ i.val=52 ∨ i.val=56 then 1 else 0

theorem native_layout {s : Nat} (bits : List Bool) (q : Fin s) :
    ZeroPadding.config (caps bits) ⟨q,(fun _=>0),tapes bits⟩=(state bits).cfg q := by
  apply configuration_ext
  · rfl
  · rfl
  · change (fun i=>ZeroPadding.pad (caps bits i) (tapes bits i))=
      Fin.addCases (m:=29) (n:=28) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool)
          (inner bits).tapes (fun _=>[false])) (outer bits).tapes
    unfold inner outer
    rw [fields_tapes,fields_tapes]
    funext i
    fin_cases i <;> simp [tapes,caps,ZeroPadding.pad,Fin.addCases,
      RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,
      RecoveryColdHeader.zero_length,RecoveryColdHeader.code_length,erase,
      RecoveryColdValuation.capacity]
    all_goals rfl

end NearCubicWires.RepairOrdinary.RecoveryColdMarker
