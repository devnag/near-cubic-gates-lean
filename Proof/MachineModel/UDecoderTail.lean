import Proof.MachineModel.UDecoderCalls

/-! The successful input phase enters the actual guarded decoder using its
literal code/limit tapes; all other U fields and witness heads are retained. -/
namespace NearCubicWires.RepairOrdinary.UDecoder
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem code_budget (raw code x bound padding : List Bool)
    (he : raw=VerifierInputFields.source code x bound padding) :
    Ready.limitedBudget code.length (Nat.log 2 raw.length)≤
      Ready.limitedBudget raw.length (Nat.log 2 raw.length) := by
  have hc : code.length≤raw.length := by
    rw [he]
    simp only [VerifierInputFields.source,List.length_append,frame_length]
    omega
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right hc 1))

theorem decoder_tail (raw witness : List Bool) (base : Configuration 50 inputStates)
    (hp : UInputOrdinary.Prepared raw base.tapes) (hh : base.heads=UInputOrdinary.heads)
    (hwit : base.tapes 1=frame witness) (hwhead : base.heads 1=0) :
    ∃ n final, n≤Ready.limitedBudget raw.length (Nat.log 2 raw.length)+1 ∧
      Timed machine n (controlConfig (RecoveryCalls.code sizes 1) (decoderInput base)) final ∧
      machine.halted final.control=true ∧ (final.scanned 67=true ↔ Accepted raw) ∧
      (final.scanned 67=true → Successful raw witness final) := by
  have hpkeep := hp
  obtain ⟨code,x,bound,padding,hraw,hg,h0,hcode,hx,hB,hN,hw,hI,hK,hBn,hL,hlim⟩ := hp
  obtain ⟨last,small,hlast,hls,hlf,haccept,hout⟩ := decoder_run base code raw.length hh hcode hlim
  obtain ⟨m,hm,hstop⟩ := stop_receipt sizes programs 0 next 1
    (Ready.limitedBudget code.length (Nat.log 2 raw.length)) _ last hlast (by rfl)
  have hbound := code_budget raw code x bound padding hraw
  have haccepted := haccept.trans (accepted_iff raw code x bound padding hraw hg).symm
  refine ⟨m,_,by omega,hstop,?_,?_,?_⟩
  · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
  · simpa only [RecoveryCalls.stopped,Configuration.scanned] using haccepted
  · intro _
    refine ⟨code,x,bound,padding,base,small,hraw,hg,hpkeep,hh,hwit,hwhead,?_,?_,hout⟩
    · simpa only [RecoveryCalls.stopped] using congrArg Configuration.heads hlf
    · simpa only [RecoveryCalls.stopped] using congrArg Configuration.tapes hlf

end NearCubicWires.RepairOrdinary.UDecoder
