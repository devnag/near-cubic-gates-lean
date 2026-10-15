import Proof.Circuits.CanonicalBinaryOutput

/-! Retain the physically trimmed framed field as well as its raw output.
The allocated high-zero cells remain explicit for reusable stack calls. -/
namespace NearCubicWires.RepairOrdinary.CanonicalPositiveOutput
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem binary_output_fields (w n : ℕ) (hn : 0<n) (hfit : n<2^w) :
    ∃ out : Fin 4 → List Bool,
      ClockJoin.ReadyRun machine (8*w+9) (input (binary w n)) out ∧
      out 2=n.bits ∧ out 0=ZeroPadding.pad (2*w+1) (frame n.bits) := by
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
  refine ⟨output pre (w-n.bits.length),h,hpre.symm,?_⟩
  change RepairSource.ProjectionNormalization.DimensionTrim.backTape pre 0 (w-n.bits.length)=_
  rw [back_tape,←hpre]
  unfold ZeroPadding.pad
  rw [frame_length]
  congr 2
  omega

end NearCubicWires.RepairOrdinary.CanonicalPositiveOutput
