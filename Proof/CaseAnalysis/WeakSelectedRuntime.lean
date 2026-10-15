import Proof.CaseAnalysis.WeakNativeBound
import Proof.Assembly.SelectedRecoveryIntegration

/-! The remaining M producer supplies only its actual preprocessing/hot
split. Native growth and the source proof-table bound are already discharged
at the SAME selected ordinary hierarchy/PCP instance. -/
namespace NearCubicWires.RepairSource.CloseoutWeakRuntime
open RepairOrdinary SelectedRecoveryIntegration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem selected_littleO (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (M : OrdinaryWeakMachine)
    (A B a sigma : Nat) (hot : Nat → Nat)
    (ha : a ≤ k+1) (hs : 6+(fixedProjection sources).degrees.proofLog ≤ sigma)
    (bound : ∃ onset, ∀ N, onset ≤ N →
      M.runtime N ≤ A*(N+1)^a+hot N ∧
      hot N*((outer sources k clock).result.pcp.nativeWidth N)^sigma ≤
        B*2^((outer sources k clock).result.pcp.nativeWidth N)) :
    OrdinaryLittleO M (fun n => n^(k+2)) := by
  let H := (sources.hierarchy (fun n => n^(k+2)) clock).hierarchy
  let source := fixedProjection sources
  let q := (outer sources k clock).result.pcp.nativeWidth
  apply littleO_of_split M k A B (tableCoefficient source H (padding sources k clock)) a
    (5+source.degrees.proofLog) sigma q hot ha (by dsimp [source]; omega)
  · exact native_grows source H (padding sources k clock)
  · obtain ⟨onset,hbound⟩ := bound
    refine ⟨max onset 1,?_⟩
    intro N hn
    obtain ⟨hr,hh⟩ := hbound N ((Nat.le_max_left _ _).trans hn)
    exact ⟨hr,hh,actual_table_bound source H (padding sources k clock)
      (Nat.le_max_left _ _) (Nat.le_max_right _ _) N ((Nat.le_max_right _ _).trans hn)⟩

end
end NearCubicWires.RepairSource.CloseoutWeakRuntime
