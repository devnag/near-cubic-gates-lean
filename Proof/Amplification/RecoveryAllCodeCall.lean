import Proof.Amplification.RecoveryAllCodeReady

/-! The actual focused all-code call on the cold493-tape endpoint. False
backing is removed by interpreter simulation; the cold parser gate stays
outside the checker bank and survives unchanged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdAllCode
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def checkerProgram := RecoveryFocus.machine slots RecoveryAllCode.machine
def checkerBudget (bits : List Bool) := RecoveryAllCode.budget (width bits)

theorem gate_outside (j : Fin 348) : slots j≠277 := by
  refine Fin.addCases (m:=136) (n:=212) (motive:=fun j=>slots j≠277) ?_ ?_ j
  · intro i he
    have h := rawSlots_lt i
    have hv := congrArg Fin.val he
    simp only [slots,Fin.addCases_left] at hv
    change (rawSlots i).val=277 at hv
    omega
  · intro i he
    have h := compactSlots_ge i
    have hv := congrArg Fin.val he
    simp only [slots,Fin.addCases_right] at hv
    change (compactSlots i).val=277 at hv
    omega

theorem gate_pick : RecoveryFocus.pick slots (277 : Fin 493)=none := by
  classical
  unfold RecoveryFocus.pick
  rw [dif_neg (by intro ⟨j,hj⟩; exact gate_outside j hj)]

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem checker_call (code : Nat) (word : List Bool) (H : Fin 493→Nat) (A : Fin 493→List Bool)
    (hr : RecoveryColdCompact.Ready code.bits word H A) :
    ∃ bit r,runFrom checkerProgram (checkerBudget code.bits) ⟨checkerProgram.start,H,A⟩=some r ∧
      r.steps≤4294967296*(width code.bits+1)^4 ∧
      r.final.scanned 127=bit ∧ r.final.heads 277=H 277 ∧ r.final.tapes 277=A 277 ∧
      (bit=true → correctedSat code=true) := by
  obtain ⟨count,n,ib,m,ob,hready,hnative⟩ := ready_native code word H A hr RecoveryAllCode.machine.start
  let x := state code.bits word (RecoveryColdCompact.buffer ib word)
    (RecoveryColdCompact.buffer ob word) count n m
  obtain ⟨base,hbase,hsteps,hhead,⟨bit,htape⟩,hsound⟩ := RecoveryAllCode.checker_run x
    (limit code.bits) word (count*(width code.bits+2)+1)
    (RecoveryColdCompact.buffer ib word) (RecoveryColdCompact.buffer ob word) [] [] hready
  rw [←hnative] at hbase
  obtain ⟨small,hsmall,hfinal,hss,_⟩ := ZeroPadding.run_unpad RecoveryAllCode.machine
    (caps code.bits word) (RecoveryAllCode.budget x.width)
    ⟨RecoveryAllCode.machine.start,(fun j=>H (slots j)),(fun j=>A (slots j))⟩ base hbase
  obtain ⟨r,hrun,hrfinal,hrsteps⟩ := RecoveryFocus.run_config slots slots_injective RecoveryAllCode.machine
    H A (RecoveryAllCode.budget x.width) _ small hsmall
  have hstart : RecoveryFocus.config slots H A
      ⟨RecoveryAllCode.machine.start,(fun j=>H (slots j)),(fun j=>A (slots j))⟩=
      (⟨checkerProgram.start,H,A⟩ : Configuration 493 _) := by
    apply focus_configuration slots slots_injective
    · rfl
    · intro _; rfl
    · intro _; rfl
    · intro _ _; rfl
    · intro _ _; rfl
  rw [hstart] at hrun
  have hw : x.width=width code.bits := state_width _ _ _ _ _ _ _
  rw [hw] at hrun hsteps
  have hscan : small.final.scanned 93=bit := by
    have h := congrFun (congrArg Configuration.scanned hfinal) (93 : Fin 348)
    rw [ZeroPadding.scanned_config] at h
    change small.final.scanned 93=readTapeBit (base.final.tapes 93) (base.final.heads 93) at h
    rw [hhead,htape] at h
    exact h
  refine ⟨bit,r,hrun,?_,?_,?_,?_,?_⟩
  · rw [hrsteps,hss]
    exact hsteps
  · rw [hrfinal]
    have h := congrFun (RecoveryFocus.scanned_config slots slots_injective H A small.final) (93 : Fin 348)
    change (RecoveryFocus.config slots H A small.final).scanned (slots 93)=small.final.scanned 93 at h
    have hs : slots 93=(127 : Fin 493) := by decide
    rw [hs] at h
    exact h.trans hscan
  · rw [hrfinal]
    simp only [RecoveryFocus.config,gate_pick]
  · rw [hrfinal]
    simp only [RecoveryFocus.config,gate_pick]
  · intro hb
    have hs := hsound (by rw [htape,hb])
    have hc : x.code=code := state_code _ _ _ _ _ _ _
    rwa [hc] at hs

end NearCubicWires.RepairOrdinary.RecoveryColdAllCode
