import Proof.CaseAnalysis.RowsCircuitFlags

/-! One source-independent D26 raw-code capacity pays the actual prefix,
gate parser and small circuit counters. Read-only policy words stay outside. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCapacity
open LocalBitMultitape RepairRepresentation CloseoutRowsCircuitWords
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (N : ℕ):=1000000000000000000000000000000*(N+2)^26

theorem positive (N : ℕ) : 2 ≤ capacity N:=by
  have hp:1 ≤ (N+2)^26:=Nat.one_le_pow _ _ (by omega)
  unfold capacity;omega

theorem monotone {n N : ℕ} (h : n ≤ N) : capacity n ≤ capacity N:=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 26)

theorem raw_fits (N : ℕ) : 2*N+1 ≤ capacity N ∧ 1+2*(N+1) ≤ capacity N:=by
  have hp:N+2 ≤ (N+2)^26:=Nat.le_self_pow (by decide) _
  unfold capacity;omega

theorem prefix_fits (bits : List Bool) : CloseoutRowsCircuitPrefix.budget bits+1 ≤ capacity bits.length:=by
  let N:=bits.length
  have h1:1 ≤ (N+2)^26:=Nat.one_le_pow _ _ (by omega)
  have hl:N+2 ≤ (N+2)^26:=Nat.le_self_pow (by decide) _
  have h2:(N+1)^2 ≤ (N+2)^26:=
    (Nat.pow_le_pow_left (by omega : N+1 ≤ N+2) 2).trans
      (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 26))
  have h24:(N+2)^24 ≤ (N+2)^26:=Nat.pow_le_pow_right (by omega) (by decide)
  have big:(2*N+2)^24 ≤ 16777216*(N+2)^26:=by
    have hp:=Nat.pow_le_pow_left (by omega : 2*N+2 ≤ 2*(N+2)) 24
    rw [mul_pow] at hp
    norm_num at hp
    exact hp.trans (Nat.mul_le_mul_left _ h24)
  unfold CloseoutRowsCircuitPrefix.budget CloseoutRowsCircuitTagged.budget
    CloseoutRowsCircuitCount.budget CloseoutRowsCircuitMode.budget capacity
  rw [code_length,code_length,code_length]
  change 51000*(N+1)^2+34000000000000000000*(N+N+2)^24+(4*N+30)+4+1 ≤
    1000000000000000000000000000000*(N+2)^26
  have he:N+N+2=2*N+2:=by omega
  rw [he]
  omega

theorem gate_fits (bits : List Bool) : 2*CloseoutRowsGateMeasured.budget bits+4 ≤ capacity bits.length:=by
  have hb:=CloseoutRowsGateMeasured.budget_bound bits
  have hp:1 ≤ (bits.length+2)^26:=Nat.one_le_pow _ _ (by omega)
  unfold capacity;omega

theorem top_fits (bits : List Bool) : CloseoutRowsCircuitSymTop.budget bits+1 ≤ capacity bits.length:=by
  have payload:(CloseoutWitness.BitFields.payload bits).length ≤ bits.length+1:=by
    simpa only [CloseoutWitness.BitFields.payload,CloseoutWitness.Reencode.fields,List.length_map,
      CloseoutWitness.TraversalCounted.count] using CloseoutWitness.Reencode.count_bound bits
  have hp:(bits.length+1)^24 ≤ (bits.length+2)^26:=
    (Nat.pow_le_pow_left (by omega : bits.length+1 ≤ bits.length+2) 24).trans
      (Nat.pow_le_pow_right (by omega) (by decide : 24 ≤ 26))
  have hl:bits.length+2 ≤ (bits.length+2)^26:=Nat.le_self_pow (by decide) _
  unfold CloseoutRowsCircuitSymTop.budget CloseoutWitness.NatCold.budget capacity
  omega

theorem stream_fits (bits : List Bool) : ((words bits).flatMap frame).length ≤ capacity bits.length:=by
  have hn:=CloseoutRowsCircuitWords.count_bound bits
  rw [stream_length]
  have bound:(words bits).length*(2*bits.length+1) ≤ 2*(bits.length+2)^2:=by
    have hmul:=Nat.mul_le_mul_right (2*bits.length+1) hn
    nlinarith
  have hp:(bits.length+2)^2 ≤ (bits.length+2)^26:=Nat.pow_le_pow_right (by omega) (by decide)
  unfold capacity;omega

theorem header_fits (N n : ℕ) (hn : n ≤ N+1) : EquationHeaderAppend.budget n+1 ≤ capacity N:=by
  have hb:natBitLength n ≤ n+1:=Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have hsq:n^2 ≤ (N+2)^26:=
    (Nat.pow_le_pow_left (by omega : n ≤ N+2) 2).trans
      (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 26))
  have hl:N+2 ≤ (N+2)^26:=Nat.le_self_pow (by decide) _
  unfold EquationHeaderAppend.budget capacity;omega

theorem counters_fit (N : ℕ) :
    2*CloseoutRowsCircuitResourceBounds.counterBound N ≤ capacity N:=by
  have hp:(N+2)^2 ≤ (N+2)^26:=Nat.pow_le_pow_right (by omega) (by decide)
  have h1:1 ≤ (N+2)^26:=Nat.one_le_pow _ _ (by omega)
  unfold CloseoutRowsCircuitResourceBounds.counterBound capacity;omega

theorem resource_fit (N D n wire : ℕ)
    (hd : D ≤ 132*(N+2)^3) (hn : n ≤ N+1) (hw : wire ≤ 132*(N+2)^3) :
    32*(D+n+wire+3) ≤ capacity N:=by
  have hp:(N+2)^3 ≤ (N+2)^26:=Nat.pow_le_pow_right (by omega) (by decide)
  have hl:N+2 ≤ (N+2)^26:=Nat.le_self_pow (by decide) _
  unfold capacity;omega

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCapacity
