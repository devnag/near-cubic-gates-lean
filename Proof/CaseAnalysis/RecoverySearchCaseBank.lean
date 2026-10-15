import Proof.Amplification.RecoveryPrefixPrepareCall
import Proof.CaseAnalysis.RecoveryCaseQueryRun

/-! The one unconstrained query consumes the already-paid cold prefix bank.
Its two zero fields are the actual reset tapes, not the prefix sentinel or
its positive count. The original outer request remains outside the call. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedSearchCase
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryExecution RecoveryRootRound
open RecoveryPrefixCold RecoveryQueryKernel RecoveryOracle
open private query_halted from Proof.Amplification.RecoveryPrefixBody
open private query_start_initial from Proof.Amplification.RecoveryPrefixBodyReady
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 357) : Fin 389 :=
  ⟨if i.val=1 then 359 else if i.val=2 then 360 else i.val+1,
    by have hi:=i.isLt; split_ifs <;> omega⟩

theorem injective : Function.Injective slots := by
  intro a b h
  apply Fin.ext
  have hv:=congrArg (fun i : Fin 389=>i.val) h
  have ha:=a.isLt
  have hb:=b.isLt
  dsimp only [slots] at hv
  split_ifs at hv <;> omega

theorem query_port : slots (RecoveryQueryStep.program true).queryTape=
    RecoveryPrefixCold.ports.queryTape := rfl

theorem slot_high (i : Fin 357) (hi : 5 ≤ i.val) :
    slots i=RecoveryPrefixCold.nativeSlot (RecoveryPrefixUpdate.querySlots i) := by
  apply Fin.ext
  simp [slots,RecoveryPrefixCold.nativeSlot,RecoveryPrefixUpdate.querySlots,
    show i.val≠1 by omega,show i.val≠2 by omega]

theorem zero_capacity (C payload total : Nat) (hC : 1073741824 ≤ C) :
    RecoveryQuery.capacity payload 0 0 ≤ RecoveryPrefixColdPrepare.capacity C payload total := by
  have hb : RecoveryQuery.bytes payload 0 0+1 ≤ RecoveryPrefixMeasure.mass payload total+1 := by
    simp [RecoveryQuery.bytes,RecoveryPrefixMeasure.mass]
    omega
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb 2)).trans
    (Nat.mul_le_mul_right _ hC)

theorem zero_frame (cap : Nat) (hc : 1 ≤ cap) :
    List.replicate cap false=frame []++List.replicate (cap-1) false := by
  exact (padded_zero cap hc).symm

noncomputable abbrev piece := focused (RecoveryQueryStep.program true) slots
noncomputable abbrev program := RecoveryPrefixCold.ports.program piece

theorem prepared_ready (C payload total : Nat) (hC : 1073741824 ≤ C)
    (ambient : Fin 389→List Bool)
    (hp : Prepared C payload total ambient) :
    ∃ cost ≤ 18*RecoveryPrefixColdPrepare.capacity C payload total,
      ∃ out : Fin 389→List Bool,
      Ready correctedSat program cost ambient out ∧
      readTapeBit (out 357) 0=correctedSat (RecoveryQuery.code true payload 0 0) ∧
      out 0=ambient 0 ∧
      out 4=List.replicate (RecoveryPrefixColdPrepare.capacity C payload total) true ∧
      out 5=List.replicate (RecoveryPrefixColdPrepare.capacity C payload total+1) false ∧
      (out 344).length ≤ RecoveryPrefixColdPrepare.capacity C payload total := by
  classical
  let cap := RecoveryPrefixColdPrepare.capacity C payload total
  have hc : 5 ≤ cap := capacity_large C payload total hC
  have hb : Bounded cap (ambient ∘ slots) := by
    intro i hi
    change (ambient (slots i)).length ≤ cap
    rw [slot_high i hi]
    exact hp.1.bounded i hi
  have hd : (ambient ∘ slots) 3=List.replicate cap true := hp.1.driver
  have hl : (ambient ∘ slots) 4=List.replicate (cap+1) false := hp.1.logField
  have hpayload : (ambient ∘ slots) 0=frame payload.bits++frame (List.replicate total true) :=
    hp.1.payloadField
  have ha : (ambient ∘ slots) 1=frame []++List.replicate (cap-1) false :=
    hp.1.tailReset.trans (zero_frame cap (by omega))
  have hn : (ambient ∘ slots) 2=frame []++List.replicate (cap-1) false :=
    hp.1.countReset.trans (zero_frame cap (by omega))
  obtain ⟨cost,hcost,out,hr,answer,_,driver,logOut,bounded⟩ :=
    RecoveryQueryStep.step_trace cap (cap+1) true payload 0 0 (ambient ∘ slots)
      (frame (List.replicate total true)) (List.replicate (cap-1) false)
      (List.replicate (cap-1) false) (zero_capacity C payload total hC)
      hb hd hl (Nat.le_refl _) hpayload ha hn
  have hstart : RecoveryQueryStep.start true (ambient ∘ slots)=
      initialConfiguration (RecoveryQueryStep.program true).base.machine (ambient ∘ slots) :=
    query_start_initial _ _ _
  rw [hstart] at hr
  have ready : Ready correctedSat (RecoveryQueryStep.program true) cost (ambient ∘ slots) out :=
    ⟨RecoveryQueryStep.stopped true out,hr,
      query_halted (RecoveryQueryKernel.kernel true) RecoveryQueryStep.answerSlot out,
      fun _=>rfl,rfl⟩
  have whole := ready.focus RecoveryPrefixCold.ports slots injective query_port ambient (fun _=>rfl)
  refine ⟨cost,hcost,install slots ambient out,whole,?_,?_,?_,?_,?_⟩
  · change readTapeBit (install slots ambient out (slots 356)) 0=_
    rw [install_slot _ injective]
    exact answer
  · exact install_other slots ambient out (0 : Fin 389) (by
      intro i he
      have hv:=congrArg (fun j : Fin 389=>j.val) he
      change (if i.val=1 then 359 else if i.val=2 then 360 else i.val+1)=0 at hv
      split_ifs at hv)
  · change install slots ambient out (slots 3)=_
    rw [install_slot _ injective]
    exact driver
  · change install slots ambient out (slots 4)=_
    rw [install_slot _ injective]
    exact logOut
  · change (install slots ambient out (slots 343)).length ≤ cap
    rw [install_slot _ injective]
    exact bounded 343 (by decide)

end NearCubicWires.RepairSource.RecoveryBoundedSearchCase
