import Proof.CaseAnalysis.RowsSourceDigits
import Proof.CaseAnalysis.RowsBankPolynomial

/-! The same paper load pays the generated cut family and all executed
BinLift driver/degree/clear costs plus the fixed110-port loading allowance.
This cost is added to table work; it is not internal-syntax Tprep. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSourceLoad
open CloseoutRowsSourceDigits CloseoutRowsCacheInput
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cuts_bound {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (ps : List (MvPolynomial (Fin gs.length) (ZMod 2))) (K : ℕ)
    (hbank : ps.length ≤ 2^K) :
    ((bank ps).flatMap (CloseoutRowsSharedDigits.cuts gs (K+1) (width ps))).length ≤
      2^load K (degree ps) gs.length := by
  let D:=degree ps*Nat.clog 2 (gs.length+1)
  have hp := CloseoutRowsSharedDigits.batch_perm gs (K+1) (width ps) (bank ps)
    (fun rs hr=>(bank_width ps rs hr).le)
  rw [hp.length_eq,RowPowerBinLift.batch_length]
  have hm : ∀ ms∈family gs (bank ps),ms.length ≤ 2^D := by
    intro ms hms
    obtain ⟨rs,hrs,rfl⟩ := List.mem_map.mp hms
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hrs
    simpa only [polynomial,List.length_map] using binary_support ps P hP
  have hb:=RowBinLift.batch_length_bound (K+1) (2^D) (family gs (bank ps)) hm
  have hq : K+1 ≤ 2^Nat.clog 2 (K+2) :=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have he : 1 ≤ 2^D := Nat.one_le_two_pow
  rw [max_eq_right he] at hb
  have hfamily : (family gs (bank ps)).length ≤ 2^K := by
    simpa only [family,bank,List.length_map] using hbank
  calc
    _ ≤ 2^K*(2^Nat.clog 2 (K+2))*(2^D)^(K+1) :=
      hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul hfamily hq))
    _ = 2^(K+Nat.clog 2 (K+2)+(K+1)*D) := by
      rw [←pow_add,←pow_mul,←pow_add,Nat.mul_comm D (K+1)]
    _ ≤ 2^load K (degree ps) gs.length := by
      apply Nat.pow_le_pow_right (by decide)
      dsimp [D,load]
      nlinarith

theorem cuts_gate {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (ps : List (MvPolynomial (Fin gs.length) (ZMod 2))) (K s : ℕ)
    (hbank : ps.length ≤ 2^K) (hload : 200*load K (degree ps) gs.length ≤ s) :
    ((bank ps).flatMap (CloseoutRowsSharedDigits.cuts gs (K+1) (width ps))).length^100 ≤ 2^s := by
  calc
    _ ≤ (2^load K (degree ps) gs.length)^100 :=
      Nat.pow_le_pow_left (cuts_bound gs ps K hbank) 100
    _ = 2^(100*load K (degree ps) gs.length) := by rw [←pow_mul,Nat.mul_comm]
    _ ≤ 2^s := Nat.pow_le_pow_right (by decide) (by omega)

def oneCost (Q C : ℕ) := CloseoutRowsBankPolynomial.budget Q C+110*(3*C+3)+8

theorem one_bound (S R Q : ℕ) (hQ : Q ≤ S) :
    oneCost Q (4096*S^4*2^R) ≤ 2000000*2^R*(S+1)^5 := by
  have hl := CloseoutRowsCapacityBudget.loop_bound S R Q hQ
  have hs : S^4 ≤ (S+1)^5 :=
    (Nat.pow_le_pow_left (Nat.le_succ S) 4).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hc : 4096*S^4*2^R ≤ 4096*2^R*(S+1)^5 := by
    nlinarith [Nat.mul_le_mul_left (4096*2^R) hs]
  have ht : 1 ≤ (S+1)^5 := Nat.one_le_pow 5 (S+1) (by omega)
  have he : 1 ≤ 2^R := Nat.one_le_two_pow
  have hu : 1 ≤ 2^R*(S+1)^5 := by nlinarith
  unfold oneCost CloseoutRowsBankPolynomial.budget CloseoutRowsBankClear.budget
  nlinarith

theorem bank_bound (S R K s : ℕ) (hQ : K+1 ≤ S) (hload : K+R ≤ s) :
    CloseoutRowsCapacityDriver.budget S R+2^K*oneCost (K+1) (4096*S^4*2^R) ≤
      3000000*2^s*(S+1)^5*(R+1) := by
  have hd:=CloseoutRowsCapacityBudget.driver_bound S R
  have ho:=one_bound S R (K+1) hQ
  have hR : 2^R ≤ 2^s := Nat.pow_le_pow_right (by decide) (by omega)
  have hKR : 2^K*2^R ≤ 2^s := by
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) hload
  have hd' : CloseoutRowsCapacityDriver.budget S R ≤ 1000000*2^s*(S+1)^5*(R+1) :=
    hd.trans (by gcongr)
  have ho' : 2^K*oneCost (K+1) (4096*S^4*2^R) ≤ 2000000*2^s*(S+1)^5*(R+1) := by
    calc
      _ ≤ 2^K*(2000000*2^R*(S+1)^5) := Nat.mul_le_mul_left _ ho
      _ = 2000000*(2^K*2^R)*(S+1)^5 := by ring
      _ ≤ 2000000*2^s*(S+1)^5 := by gcongr
      _ ≤ _ := by nlinarith
  nlinarith

theorem source_bank_bound {B : ℕ} (ps : List (MvPolynomial (Fin B) (ZMod 2)))
    (K s S : ℕ) (hQ : K+1 ≤ S) (hload : 200*load K (degree ps) B ≤ s) :
    CloseoutRowsCapacityDriver.budget S (width ps*(K+2))+
        2^K*oneCost (K+1) (4096*S^4*2^(width ps*(K+2))) ≤
      3000000*2^s*(S+1)^5*(width ps*(K+2)+1) := by
  apply bank_bound S _ K s hQ
  have h:=digit_margin ps K s hload
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsSourceLoad
