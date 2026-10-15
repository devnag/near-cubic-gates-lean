import Proof.MachineModel.ClockTotal

/-! Literal arithmetic premises for the hierarchy bound's short binary
producer. The hierarchy coefficient and allocation coefficient are distinct.
The padded W-bit bound field is a representation of the original B_H. -/
namespace NearCubicWires.RepairOrdinary.HierarchyBinary
open PCPResourceLedger
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bound (C D n : ℕ) := C*(n^D+1)
def width (C D n : ℕ) := D*ell n+C.bits.length+3
def header (codeLength C : ℕ) := 2^codeLength+2*codeLength+2*C.bits.length+8
def allocation (Cpad codeLength C n : ℕ) := (2*Cpad+1)*(n+1)+header codeLength C
def inputLength (k Cpad codeLength C n : ℕ) := PowerSlice.length k (allocation Cpad codeLength C n)

theorem input_lt_pow (n : ℕ) : n<2^ell n := by
  exact lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_pow_clog (by decide) (n+1))

theorem power_bound (D n : ℕ) : n^D≤2^(D*ell n) := by
  have h := Nat.pow_le_pow_left (input_lt_pow n).le D
  simpa only [← pow_mul,Nat.mul_comm] using h

theorem power_call_fit (C D n j : ℕ) (hj : j<D) :
    n^j*2^ell n<2^width C D n := by
  calc n^j*2^ell n≤2^(j*ell n)*2^ell n := Nat.mul_le_mul_right _ (power_bound j n)
    _=2^((j+1)*ell n) := by rw [Nat.add_mul,pow_add]; simp
    _≤2^(D*ell n) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
    _<2^width C D n := Nat.pow_lt_pow_right (by decide) (by simp [width]; omega)

theorem successor_fit (C D n : ℕ) : n^D+1<2^width C D n := by
  have hn := power_bound D n
  have hp : 1≤2^(D*ell n) := Nat.one_le_pow _ _ (by decide)
  calc n^D+1≤2^(D*ell n+1) := by rw [pow_succ]; omega
    _<2^width C D n := Nat.pow_lt_pow_right (by decide) (by simp [width]; omega)

theorem coefficient_call_fit (C D n : ℕ) :
    (n^D+1)*2^C.bits.length<2^width C D n := by
  have hn := power_bound D n
  have hp : 1≤2^(D*ell n) := Nat.one_le_pow _ _ (by decide)
  calc (n^D+1)*2^C.bits.length≤2^(D*ell n+1)*2^C.bits.length := by
        apply Nat.mul_le_mul_right
        rw [pow_succ]
        omega
    _=2^(D*ell n+1+C.bits.length) := (pow_add _ _ _).symm
    _<2^width C D n := Nat.pow_lt_pow_right (by decide) (by simp [width]; omega)

theorem bound_fits (C D n : ℕ) : bound C D n<2^width C D n := by
  have hc : C<2^C.bits.length := by rw [Nat.size_eq_bits_len]; exact Nat.lt_size_self C
  calc bound C D n≤(n^D+1)*2^C.bits.length := by
        dsimp [bound]
        simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (n^D+1) hc.le
    _<2^width C D n := coefficient_call_fit C D n

theorem ell_linear (n : ℕ) : ell n≤n :=
  Nat.clog_le_of_le_pow (Nat.succ_le_of_lt Nat.lt_two_pow_self)

theorem padded_header_fits (C Cpad D n : ℕ) (code x : List Bool)
    (hn : x.length=n) (hD : D+1≤Cpad) :
    (frame code++frame x++frame (SignedSortKey.binary (width C D n) (bound C D n))).length≤
      allocation Cpad code.length C n := by
  have hel := Nat.mul_le_mul_left D (ell_linear n)
  have hc := Nat.mul_le_mul_right (n+1) hD
  have hp : 1≤2^code.length := Nat.one_le_pow _ _ (by decide)
  simp only [List.length_append,frame_length,SignedSortKey.binary_length,hn]
  dsimp only [allocation,header,width]
  nlinarith

theorem exact_slice_and_bound (k C Cpad codeLength n : ℕ) (hC : C≤Cpad) :
    PowerSlice.degree (inputLength k Cpad codeLength C n)=k+2 ∧
    bound C (k+2) n≤ClockDyadicLedger.limit (inputLength k Cpad codeLength C n) := by
  have hlen := (PowerSlice.length_bounds k (allocation Cpad codeLength C n)).1
  have hp : 0 < inputLength k Cpad codeLength C n := by dsimp [inputLength]; omega
  refine ⟨PowerSlice.length_degree _ _,?_⟩
  calc bound C (k+2) n≤Cpad*(n^(k+2)+1) := Nat.mul_le_mul_right _ hC
    _≤PowerSlice.limit (inputLength k Cpad codeLength C n) :=
      PowerSlice.hierarchy_fits k Cpad (header codeLength C) n
    _≤ClockDyadicLedger.limit (inputLength k Cpad codeLength C n) :=
      (ClockDyadicLedger.limit_bounds _ hp).1

theorem log_product_room (C n N : ℕ) (hC : 0<C) (hN : 2*C*(n+1)≤N) :
    ell n+C.bits.length≤ell N := by
  have hc : C.bits.length= C.size := Nat.size_eq_bits_len C
  have hcpos : 0<C.bits.length := by rw [hc]; exact Nat.size_pos.mpr hC
  have hcLower : 2^(C.bits.length-1)≤C := by
    apply Nat.lt_size.mp
    rw [← hc]
    omega
  by_cases hn : n=0
  · subst n
    have hCN : C<2^ell N := lt_of_le_of_lt (by nlinarith : C≤N) (input_lt_pow N)
    have hb := Nat.size_le.mpr hCN
    simpa [ell,hc] using hb
  · have hepos : 0<ell n := by
      have h := input_lt_pow n
      by_contra hz
      have he : ell n=0 := by omega
      rw [he] at h
      simp only [pow_zero] at h
      omega
    have helower : 2^(ell n-1)≤n := by
      have h := (ClockDyadicLedger.pow_ell_bounds n (by omega)).2
      have he : ell n=(ell n-1)+1 := by omega
      rw [he,pow_succ] at h
      omega
    have hexp : ell n+C.bits.length-1=(ell n-1)+(C.bits.length-1)+1 := by omega
    have hlow : 2^(ell n+C.bits.length-1)<N := by
      calc 2^(ell n+C.bits.length-1)=2*(2^(ell n-1)*2^(C.bits.length-1)) := by
            rw [hexp,pow_succ,pow_add]
            ring
        _≤2*(n*C) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul helower hcLower)
        _<2*C*(n+1) := by nlinarith
        _≤N := hN
    by_contra hbad
    have he : ell N≤ell n+C.bits.length-1 := by omega
    have hp := Nat.pow_le_pow_right (n:=2) (by decide) he
    have hnUpper := input_lt_pow N
    omega

theorem padded_width_fits (k C Cpad codeLength n : ℕ) (hC : 0<C) (hpad : C≤Cpad) :
    width C (k+2) n≤ClockDyadicLedger.width (inputLength k Cpad codeLength C n) := by
  let N := inputLength k Cpad codeLength C n
  have hlen := (PowerSlice.length_bounds k (allocation Cpad codeLength C n)).1
  have hN : 2*C*(n+1)≤N := by
    have hm := Nat.mul_le_mul_right (n+1) hpad
    dsimp only [N,inputLength,allocation] at *
    nlinarith
  have hl := log_product_room C n N hC hN
  have hm := Nat.mul_le_mul_left (k+2) hl
  have hdegree : PowerSlice.degree N=k+2 := PowerSlice.length_degree _ _
  dsimp only [ClockDyadicLedger.width,ClockDyadicLedger.exponent,width]
  rw [hdegree]
  nlinarith

end NearCubicWires.RepairOrdinary.HierarchyBinary
