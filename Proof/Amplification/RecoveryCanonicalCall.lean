import Proof.Amplification.RecoveryCanonicalAllCode

/-! Actual canonical accepting execution of the focused348-tape checker
inside the493-tape machine; the independent cold-parser gate is retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem checker_accept (code : Nat) (c : Certificate) (hc : Fits code c) (hsel : selected c=c)
    (hcheck : check code c=true) (H : Fin 493→Nat) (A : Fin 493→List Bool)
    (hr : CompactReady code c H A) :
    ∃ r,runFrom RecoveryColdAllCode.checkerProgram (RecoveryColdAllCode.checkerBudget code.bits)
      ⟨RecoveryColdAllCode.checkerProgram.start,H,A⟩=some r ∧
      r.final.scanned 127=true ∧ r.final.heads 277=H 277 ∧ r.final.tapes 277=A 277 := by
  have hnative := canonical_native code c hc H A hr RecoveryAllCode.machine.start
  obtain ⟨base,hbase,hhead,htape⟩ := all_code_accept code c hc hsel hcheck
  rw [←hnative] at hbase
  obtain ⟨small,hsmall,hfinal,_,_⟩ := ZeroPadding.run_unpad RecoveryAllCode.machine
    (RecoveryColdAllCode.caps code.bits (witness code c)) (RecoveryColdAllCode.checkerBudget code.bits)
    ⟨RecoveryAllCode.machine.start,(fun j=>H (RecoveryColdAllCode.slots j)),
      (fun j=>A (RecoveryColdAllCode.slots j))⟩ base hbase
  obtain ⟨r,hrun,hrfinal,_⟩ := RecoveryFocus.run_config RecoveryColdAllCode.slots
    RecoveryColdAllCode.slots_injective RecoveryAllCode.machine H A
    (RecoveryColdAllCode.checkerBudget code.bits) _ small hsmall
  have hstart : RecoveryFocus.config RecoveryColdAllCode.slots H A
      ⟨RecoveryAllCode.machine.start,(fun j=>H (RecoveryColdAllCode.slots j)),
        (fun j=>A (RecoveryColdAllCode.slots j))⟩=
      (⟨RecoveryColdAllCode.checkerProgram.start,H,A⟩ : Configuration 493 _) := by
    apply focus_configuration RecoveryColdAllCode.slots RecoveryColdAllCode.slots_injective
    · rfl
    · intro _; rfl
    · intro _; rfl
    · intro _ _; rfl
    · intro _ _; rfl
  rw [hstart] at hrun
  have hscan : small.final.scanned 93=true := by
    have h := congrFun (congrArg Configuration.scanned hfinal) (93 : Fin 348)
    rw [ZeroPadding.scanned_config] at h
    change small.final.scanned 93=readTapeBit (base.final.tapes 93) (base.final.heads 93) at h
    rw [hhead,htape] at h
    exact h
  refine ⟨r,hrun,?_,?_,?_⟩
  · rw [hrfinal]
    have h := congrFun (RecoveryFocus.scanned_config RecoveryColdAllCode.slots
      RecoveryColdAllCode.slots_injective H A small.final) (93 : Fin 348)
    change (RecoveryFocus.config RecoveryColdAllCode.slots H A small.final).scanned
      (RecoveryColdAllCode.slots 93)=small.final.scanned 93 at h
    have hs : RecoveryColdAllCode.slots 93=(127 : Fin 493) := by decide
    rw [hs] at h
    exact h.trans hscan
  · rw [hrfinal]
    simp only [RecoveryFocus.config,RecoveryColdAllCode.gate_pick]
  · rw [hrfinal]
    simp only [RecoveryFocus.config,RecoveryColdAllCode.gate_pick]

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
