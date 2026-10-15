import Proof.Gates.Outer.Apply
import Proof.MachineModel.ClockJoin

set_option autoImplicit false

namespace NearCubicGates.Close.OuterM

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

instance srcFitsDecidable (G ν : ℕ) {m : ℕ} (B : BooleanCircuit m) : Decidable (Outer.SrcFits G ν B) := by
  unfold Outer.SrcFits
  infer_instance

section
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
  (SV : Outer.SuccinctVerifier H G)

noncomputable def qOf (N : ℕ) : ℕ := Outer.width mw SV (2 ^ Nat.log 2 N)

/-- At `N = 2^ν`, `qOf` is the native width `q(N)`. -/
theorem qOf_two_pow (ν : ℕ) : qOf mw SV (2 ^ ν) = Outer.width mw SV (2 ^ ν) := by
  unfold qOf
  rw [Nat.log_pow (by norm_num)]

structure WidthDonor where
  K : ℕ
  /-- `q` in binary, framed (the schedule's and the cold decoder's form). -/
  word : OrdinaryWordFunction (Σ N, BitInput N) (fun r => List.ofFn r.2)
    (fun r => RepairOrdinary.frame (qOf mw SV r.1).bits) (fun r => K * (r.1 + 1) ^ 1)
  /-- `q` in unary (the ports `1^q` of the GR prefix and the Case 1/Case 2 machines). -/
  unary : OrdinaryWordFunction (Σ N, BitInput N) (fun r => List.ofFn r.2)
    (fun r => List.replicate (qOf mw SV r.1) true) (fun r => K * (r.1 + 1) ^ 1)

/-- The A-run's input bank: the raw descriptor of `B` on `dIn`, `1^ν` on `nIn`, every other tape empty. -/
def aBank {t : ℕ} (dIn nIn : Fin t) (ν : ℕ) {m : ℕ} (B : BooleanCircuit m) : Fin t → List Bool :=
  fun j => if j = dIn then PCPPNative.descriptor B else if j = nIn then List.replicate ν true else []

structure ARun where
  t : ℕ
  st : ℕ
  M : Machine t st
  dIn : Fin t
  nIn : Fin t
  fOut : Fin t
  wOut : Fin t
  nodup : [dIn, nIn, fOut, wOut].Nodup
  K : ℕ
  e : ℕ
  run : ∀ (ν m : ℕ) (B : BooleanCircuit m), ∃ out,
    ClockJoin.ReadyRun M (K * (ν + 1) ^ e) (aBank dIn nIn ν B) out ∧
      out dIn = PCPPNative.descriptor B ∧ out nIn = List.replicate ν true ∧
      out fOut = [decide (Outer.SrcFits G ν B)] ∧
      out wOut = (Outer.outC mw SV ν B).word

end

end NearCubicGates.Close.OuterM
