import Proof.Supplier.EquationRowRequest
import Proof.Supplier.SupplierCapacity

/-! Exact doubled-equation gate capacity, including the odd padded dimension.
The hundredth-power hypothesis is the natural-number form of the paper's
gate bound g ≤ 2^(s/100); all ceiling and constant slack is paid explicitly. -/
namespace NearCubicWires.RepairOrdinary.EquationRow
open SupplierCapacity SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem doubled_gate_power {s d g : ℕ} (hs : 67 ≤ s) (hd : s≤2*d)
    (hg : g^100≤2^s) : (2*g)^20≤2^d := by
  have hexp : 100+s≤d*5 := by omega
  have hp : ((2*g)^20)^5≤(2^d)^5 := by
    calc
      ((2*g)^20)^5 = 2^100*g^100 := by rw [←pow_mul,mul_pow]
      _ ≤ 2^100*2^s := Nat.mul_le_mul_left _ hg
      _ = 2^(100+s) := (pow_add 2 100 s).symm
      _ ≤ 2^(d*5) := Nat.pow_le_pow_right (by omega) hexp
      _ = (2^d)^5 := pow_mul 2 d 5
  by_contra h
  have hlt : 2^d<(2*g)^20 := by omega
  have hpow : (2^d)^5<((2*g)^20)^5 := by gcongr
  omega

theorem doubled_gateSquare {s g : ℕ} (hs : 67 ≤ s) (hg : g^100≤2^s) :
    (2*g)*(2*g)≤rectangularInnerDimension (2^((s+1)/2)) := by
  exact gateSquare_le_rectangularInnerDimension_of_pow_le
    (doubled_gate_power hs (by omega) hg)

theorem hundredth_power_of_paper_bound {s g : ℕ}
    (hg : (g : ℝ)≤(2 : ℝ)^((s : ℝ)/100)) : g^100≤2^s := by
  have hp : (g : ℝ)^100≤((2 : ℝ)^((s : ℝ)/100))^100 := by gcongr
  have he : ((2 : ℝ)^((s : ℝ)/100))^100=(2 : ℝ)^s := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0 : ℝ)≤2)]
    have h : (s : ℝ)/100*(100 : ℕ)=(s : ℝ) := by push_cast; ring
    rw [h,Real.rpow_natCast]
  rw [he] at hp
  exact_mod_cast hp

theorem doubled_gateSquare_of_paper_bound {s g : ℕ} (hs : 67 ≤ s)
    (hg : (g : ℝ)≤(2 : ℝ)^((s : ℝ)/100)) :
    (2*g)*(2*g)≤rectangularInnerDimension (2^((s+1)/2)) :=
  doubled_gateSquare hs (hundredth_power_of_paper_bound hg)

end NearCubicWires.RepairOrdinary.EquationRow
