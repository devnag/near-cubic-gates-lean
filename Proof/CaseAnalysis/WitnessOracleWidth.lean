import Proof.CaseAnalysis.NativeWidthPolynomial

/-! The oracle parser's shared physical width N+1 accommodates the actual
native source arity at one common eventual onset. No mode guard is widened. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open RepairOrdinary SelectedRecoveryIntegration PolynomialSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem oracle_width_onset (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) :
    ∃ onset, ∀ s, onset ≤ s →
      (outer sources k clock).result.pcp.nativeWidth (2^s) ≤ 2^s ∧
      (outer sources k clock).result.pcp.nativeWidth (2^s) < 2^(2^s+1) := by
  obtain ⟨onset,hbound⟩ := polynomiallyBounded_eventually_le_sixteenth_exponential
    (native_dyadic_polynomial sources k clock)
  refine ⟨onset,?_⟩
  intro s hs
  have h := hbound s hs
  rw [pow_succ] at h
  have hq : (outer sources k clock).result.pcp.nativeWidth (2^s) ≤ 2^s := by omega
  have hp : 2^s+1 < 2^(2^s+1) := Nat.lt_two_pow_self
  exact ⟨hq,by omega⟩

end
end NearCubicWires.RepairSource.CloseoutLanguage
