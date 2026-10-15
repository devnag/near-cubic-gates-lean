import Proof.CaseAnalysis.Assembly

/-! Paper C.12's final resource consumer. One ordinary program with fixed
polynomial overhead on exponentially bounded data gives the literal
all-length certificate, including zero. This allowance is recovery-only. -/
namespace NearCubicWires.RepairSource.Closeout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem recovery_budget (coefficient degree n : Nat) :
    coefficient*(2^n+1)^degree ≤
      2^((natBitLength coefficient+2*degree+1)*max 1 n) := by
  have hc : coefficient ≤ 2^natBitLength coefficient :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) _).le
  have hn : 2^n+1 ≤ 2^(n+1) := by
    have hp:=Nat.one_le_pow n 2 (by decide)
    rw [pow_succ]
    omega
  have hmax : n+1 ≤ 2*max 1 n := by
    have h0:=Nat.le_max_left 1 n
    have h1:=Nat.le_max_right 1 n
    omega
  have he : natBitLength coefficient+(n+1)*degree ≤
      (natBitLength coefficient+2*degree+1)*max 1 n := by
    have h1:=Nat.le_max_left 1 n
    nlinarith
  calc
    _ ≤ 2^natBitLength coefficient*(2^(n+1))^degree := Nat.mul_le_mul hc (Nat.pow_le_pow_left hn _)
    _ = 2^(natBitLength coefficient+(n+1)*degree) := by rw [←pow_mul,←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < 2) he

def certificate_of_runs (language : Language) (program : OrdinaryOracleProgram)
    (coefficient degree : Nat)
    (runs : ∀ n (input : BitInput n),
      OrdinaryOracleRuns RecoveryOracle.correctedSat program (List.ofFn input)
        (language n input).toNat.bits (coefficient*(2^n+1)^degree)) :
    OrdinaryENPCertificate RecoveryOracle.correctedSat language where
  program := program
  exponent := natBitLength coefficient+2*degree+1
  exponentPositive := by omega
  computes n input := (runs n input).enlarge (recovery_budget coefficient degree n)

end NearCubicWires.RepairSource.Closeout
