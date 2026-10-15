import Proof.Amplification.RecoveryHeaderFront

/-! The paid cold scalar-header tail executes three framed padded copies
and the existing quadratic erase-driver producer, retaining every source. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdHeader
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem seq_ready {t s u n m : Nat} {p : Machine t s} {q : Machine t u}
    {a b c : Fin t→List Bool} (hp : ReadyRun p n a b) (hq : ReadyRun q m b c) :
    ReadyRun (Composition.machine p q) (n+1+m) a c := by
  obtain ⟨first,hfirst,hft,hfh,hfs⟩ := hp
  obtain ⟨last,hlast,hlt,hlh,hls⟩ := hq
  have hi : Composition.restart first.final q.start=initialConfiguration q b := by
    apply configuration_ext
    · rfl
    · funext i
      exact hfh i
    · exact hft
  unfold run at hlast
  rw [←hi] at hlast
  have h := Composition.run_join p q n m _ first last hfirst hlast
  exact ⟨Composition.joinedReceipt first last,h,hlt,hlh,by simp only [Composition.joinedReceipt,hfs,hls]⟩

noncomputable def tailMachine := Composition.machine (copyMachine 0)
  (Composition.machine (copyMachine 1) (Composition.machine (copyMachine 2) driverMachine))
def tailTime (bits : List Bool) :=
  (4*width bits+8)+1+((4*width bits+8)+1+((4*width bits+8)+1+RecoveryEraseDriver.time (codeWord bits)))

theorem tail_ready (bits : List Bool) (cap scratch : Nat) :
    ReadyRun tailMachine (tailTime bits) (base bits cap scratch fields0) (output bits cap scratch) :=
  seq_ready (code_ready bits cap scratch)
    (seq_ready (bound_ready bits cap scratch) (seq_ready (zero_ready bits cap scratch) (driver_ready bits cap scratch)))

noncomputable def machine := Composition.machine frontMachine tailMachine
def budget (bits : List Bool) := RecoveryColdDimensions.budget bits+2+1+tailTime bits

theorem header_run (bits : List Bool) :
    ∃ cap scratch,cap ≤ 2*PCPResourceLedger.ell bits.length+3 ∧ scratch ≤ HierarchyInputLength.rawBudget bits ∧
      ∃ r,run machine (budget bits) (input bits)=some r ∧
        r.final.heads=(fun _=>0) ∧ r.final.tapes=output bits cap scratch ∧ r.steps ≤ budget bits := by
  obtain ⟨cap,scratch,hcap,hscratch,first,hfirst,hfh,hft⟩ := front_run bits
  obtain ⟨last,hlast,hlt,hlh,_⟩ := tail_ready bits cap scratch
  have hi : Composition.restart first.final tailMachine.start=
      initialConfiguration tailMachine (base bits cap scratch fields0) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  unfold run at hlast
  rw [←hi] at hlast
  have h := Composition.run_join frontMachine tailMachine
    (RecoveryColdDimensions.budget bits+2) (tailTime bits) _ first last hfirst hlast
  let r := Composition.joinedReceipt first last
  have hr : run machine (budget bits) (input bits)=some r := h
  exact ⟨cap,scratch,hcap,hscratch,r,hr,funext hlh,hlt,runFrom_steps_le machine (budget bits) _ r hr⟩

end NearCubicWires.RepairOrdinary.RecoveryColdHeader
