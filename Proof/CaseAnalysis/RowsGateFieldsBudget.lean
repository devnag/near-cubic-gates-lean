import Proof.CaseAnalysis.RowsGateFields

/-! The three fields retain the input's fixed binary width. Whole supported
gate field decoding is therefore one fixed preprocessing polynomial. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateFields
open CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem field_length (bits : List Bool) (i : Fin 3) :
    (CloseoutRowsGateHeader.codeWord bits i).length=bits.length:=by
  rw [CloseoutRowsGateHeader.codeWord,(RecoveryFixedUnpair.word_lengths _).1,
    CompetitorWitnessTriple.word_length]

theorem budget_bound (bits : List Bool) :
    budget bits≤4000000000000000000000000*(bits.length+2)^26:=by
  have hw:=CloseoutRowsIntegerCold.ready_budget_bound (CloseoutRowsGateHeader.codeWord bits 0)
  rw [field_length] at hw
  have h24:(bits.length+1)^24≤(bits.length+2)^26:=
    (Nat.pow_le_pow_left (by omega) 24).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have h2:(bits.length+1)^2≤(bits.length+2)^26:=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by decide))
  have hl:bits.length+2≤(bits.length+2)^26:=Nat.le_self_pow (by decide) _
  have hp:1≤(bits.length+2)^26:=Nat.one_le_pow _ _ (by omega)
  unfold budget CloseoutRowsGateHeader.budget CloseoutRowsIntegerGuard.budget
    CloseoutRowsIntegerFields.budget NatCold.budget
  rw [field_length,field_length]
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsGateFields
