import Proof.Circuits.CanonicalPositiveOutput

/-! Literal Nat.bits endpoint of the ordinary positive-field output machine.
The binary-width bound is semantic; no width word or zero count is an input. -/
namespace NearCubicWires.RepairOrdinary.CanonicalPositiveOutput
open LocalBitMultitape SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem nat_bits_value (n : ℕ) : value n.bits=n := by
  have he (bits : List Bool) : value bits=CanonicalBinary.bitsValue bits := by
    induction bits with
    | nil => rfl
    | cons b bits ih => simp only [value,CanonicalBinary.bitsValue,ih]
  exact (he n.bits).trans (CanonicalBinary.bitsValue_natBits n)

theorem nat_bits_suffix (n : ℕ) (hn : 0<n) : ∃ pre,n.bits=pre++[true] := by
  rcases CanonicalBinary.Nat.bits_canonical n with he | hl
  · have hv := nat_bits_value n
    rw [he] at hv
    change 0=n at hv
    omega
  · exact ⟨n.bits.dropLast,(List.dropLast_append_getLast? true (by simpa using hl)).symm⟩

theorem nat_bits_length_le (w n : ℕ) (hfit : n<2^w) : n.bits.length ≤ w :=
  (Nat.size_eq_bits_len n).le.trans (Nat.size_le.mpr hfit)

theorem binary_padding (w n : ℕ) (hfit : n<2^w) :
    binary w n=n.bits++List.replicate (w-n.bits.length) false := by
  have hlen : (n.bits++List.replicate (w-n.bits.length) false).length=w := by
    simp only [List.length_append,List.length_replicate]
    have h := nat_bits_length_le w n hfit
    omega
  have hvalue : value (n.bits++List.replicate (w-n.bits.length) false)=n := by
    rw [value_append,ClockScalarFields.zeros_value,nat_bits_value]
    omega
  have h := BoundedCounter.binary_of_value (n.bits++List.replicate (w-n.bits.length) false)
  rw [hlen,hvalue] at h
  exact h

theorem binary_output_run (w n : ℕ) (hn : 0<n) (hfit : n<2^w) :
    ∃ out : Fin 4 → List Bool,
      ClockJoin.ReadyRun machine (8*w+9) (input (binary w n)) out ∧ out 2=n.bits := by
  obtain ⟨pre,hpre⟩ := nat_bits_suffix n hn
  have hlen : pre.length+1=n.bits.length := by rw [hpre]; simp
  have hwidth := nat_bits_length_le w n hfit
  have he : binary w n=pre++[true]++List.replicate (w-n.bits.length) false := by
    rw [binary_padding w n hfit]
    exact congrArg (fun bits => bits++List.replicate (w-n.bits.length) false) hpre
  have h := output_run pre (w-n.bits.length)
  rw [←he] at h
  have htime : 8*(pre.length+1+(w-n.bits.length))+9=8*w+9 := by omega
  rw [htime] at h
  exact ⟨output pre (w-n.bits.length),h,hpre.symm⟩

end NearCubicWires.RepairOrdinary.CanonicalPositiveOutput
