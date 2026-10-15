import Proof.Amplification.RecoveryWidthWhole
import Proof.PCP.VerifierDecodingLength

/-! First cold checker phase, from exactly framed binary input and one
blank count tape. Both source rewind and canonical-width production are
executed; the resulting unary driver remains at its required head1. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdWidthEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 1→Fin 2 := fun _=>1
theorem slots_injective : Function.Injective slots := by intro a b _; exact Subsingleton.elim a b
noncomputable def extendMachine := RecoveryFocus.machine slots RecoveryColdWidth.machine
noncomputable def machine := Composition.machine RepairSource.VerifierDecoding.LengthMachine.machine extendMachine

theorem width_code (code : Nat) : RecoveryColdWidth.width code.bits.length=natBitLength code+2 := by
  by_cases hz : code=0
  · subst code
    simp [RecoveryColdWidth.width,natBitLength]
  · have hl := Nat.log_lt_of_lt_pow hz (Nat.lt_size_self code)
    rw [←Nat.size_eq_bits_len] at hl
    have hu := RecoveryUnpair.bits_length code
    unfold RecoveryColdWidth.width
    rw [Nat.max_eq_right (by omega)]
    unfold natBitLength at hu ⊢
    omega

def output (bits : List Bool) : Fin 2→List Bool := ![frame bits,RecoveryColdWidth.word (RecoveryColdWidth.width bits.length)]
def outputHeads : Fin 2→Nat := ![0,1]

theorem entry_run (bits : List Bool) :
    ∃ r,run machine (6*bits.length+10) ![frame bits,[]]=some r ∧
      r.final.tapes=output bits ∧ r.final.heads=outputHeads ∧ r.steps=6*bits.length+10 := by
  obtain ⟨first,hfirst,hf,hs,_⟩ := RepairSource.VerifierDecoding.LengthMachine.length_run bits
  obtain ⟨base,hbase,hb,hsteps⟩ := RecoveryColdWidth.width_run bits.length
  let heads : Fin 2→Nat := ![0,1]
  let tapes : Fin 2→List Bool := ![frame bits,RecoveryColdWidth.word bits.length]
  obtain ⟨last,hlast,hl,hlsteps⟩ := RecoveryFocus.run_config slots slots_injective RecoveryColdWidth.machine
    heads tapes (2*bits.length+6) (RecoveryColdWidth.cfg 0 bits.length 1) base hbase
  have hi : RecoveryFocus.config slots heads tapes (RecoveryColdWidth.cfg 0 bits.length 1)=
      Composition.restart first.final extendMachine.start := by
    rw [hf]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [RecoveryFocus.config,RecoveryFocus.pick,slots,heads,Composition.restart,
        RepairSource.VerifierDecoding.LengthMachine.cfg,RecoveryColdWidth.cfg]
    · funext i
      fin_cases i <;> simp [RecoveryFocus.config,RecoveryFocus.pick,slots,tapes,Composition.restart,
        RepairSource.VerifierDecoding.LengthMachine.cfg,RecoveryColdWidth.cfg,RecoveryColdWidth.word]
  rw [hi] at hlast
  have h := Composition.run_join RepairSource.VerifierDecoding.LengthMachine.machine extendMachine
    (4*bits.length+3) (2*bits.length+6) _ first last hfirst hlast
  have he : 4*bits.length+3+1+(2*bits.length+6)=6*bits.length+10 := by omega
  rw [he] at h
  refine ⟨Composition.joinedReceipt first last,h,?_,?_,?_⟩
  · simp only [Composition.joinedReceipt,Composition.rightConfig,hl,hb]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,RecoveryFocus.pick,slots,tapes,output,RecoveryColdWidth.cfg]
  · simp only [Composition.joinedReceipt,Composition.rightConfig,hl,hb]
    funext i
    fin_cases i <;> simp [RecoveryFocus.config,RecoveryFocus.pick,slots,heads,outputHeads,RecoveryColdWidth.cfg]
  · simp only [Composition.joinedReceipt,hlsteps,hsteps,hs]
    omega

end NearCubicWires.RepairOrdinary.RecoveryColdWidthEntry
