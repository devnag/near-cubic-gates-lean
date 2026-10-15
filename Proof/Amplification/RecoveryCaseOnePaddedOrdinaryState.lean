import Proof.Amplification.RecoveryCaseOnePaddedOrdinaryLayout

/-! The ordinary input has one nonempty tape. Parsing supplies both live
ports of the bit computation, and all of its other tapes remain blank. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOnePaddedOrdinary
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (amp : OrdinaryProgram)

theorem input_lookup (k : Nat) (raw : List Bool) (i : Fin (tapes source amp k)) :
    input source amp k raw i=if i.val=0 then frame raw else [] := by
  refine Fin.addCases (m:=14) (n:=base source amp k) (fun j=>?_) (fun j=>?_) i
  · simp only [input,Fin.addCases_left,RecoveryCaseOneEntry.input_lookup,Fin.val_castAdd]
    rfl
  · simp only [input,Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]

theorem bit_tapes (k : Nat) (raw word address : List Bool) (out : Fin 14→List Bool)
    (hword : out 10=word) (haddress : out 7=frame address) (i : Fin (base source amp k)) :
    install (entrySlots source amp k) (input source amp k raw) out (bitSlots source amp k i)=
      RecoveryCaseOnePaddedBit.input source amp k word address i := by
  rw [RecoveryCaseOnePaddedBit.input_lookup]
  by_cases h0 : i.val=0
  · simp only [bitSlots,h0,ite_true]
    exact (install_slot (entrySlots source amp k) (entry_injective source amp k) _ out 10).trans hword
  · by_cases hb : i.val=RecoveryCaseOnePaddedBit.base source amp k+16
    · simp only [bitSlots,hb,ite_true]
      exact (install_slot (entrySlots source amp k) (entry_injective source amp k) _ out 7).trans haddress
    · simp only [bitSlots,h0,hb,ite_false]
      rw [install_other _ _ _ _ (by
        intro j hj
        have hv:=congrArg (fun z : Fin (tapes source amp k)=>z.val) hj
        have hlt:=j.isLt
        change j.val=14+i.val at hv
        omega)]
      simp only [input,Fin.addCases_right]

theorem input_tapes (k CH Cpad : Nat) (code raw : List Bool) :
    input source amp k raw=(program source amp k CH Cpad code).base.inputTapes raw := by
  funext i
  rw [input_lookup]
  rfl

end
end NearCubicWires.RepairSource.RecoveryCaseOnePaddedOrdinary
