import Proof.CaseAnalysis.ScheduleNative

/-! Recovery-only bound for the actual native-width prefix. Reuse its
enclosing normalized-source bound; fixed polynomial losses are allowed by
C.12 and do not enter the weak-machine saving ledger. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule
open RepairOrdinary ProjectionNormalization SelectedRecoveryIntegration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem native_budget (sources : EightSources) (k : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) :
    ∃ coefficient degree : Nat, ∀ n (input : BitInput n),
      nativeBudget sources k clock (List.ofFn input) ≤ coefficient*(n+1)^degree := by
  let source:=fixedProjection sources
  let H:=(sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy
  let pad:=padding sources k clock
  let a:=HierarchyNormalizedBounds.inputExponent source
  let b:=HierarchyNormalizedBounds.logExponent source
  let C:=HierarchyNormalizedBounds.coefficient source H pad
  refine ⟨C*(2*H.coefficient+2)^b,a+(k+2)*b,?_⟩
  intro n input
  have hp : nativeBudget sources k clock (List.ofFn input) ≤
      HierarchyNormalized.budget source k H.coefficient pad (VerifierEncoding.code H.verifier)
        (List.ofFn input) := by
    unfold nativeBudget HierarchyNormalized.budget HierarchyClauses.budget HierarchyQuery.budget
      HierarchyStreams.budget HierarchySourceInput.budget HierarchySelectedSource.budget
    change HierarchyPrefix.budget k H.coefficient pad source.degrees.proofLog source.degrees.queries
      source.coefficient (VerifierEncoding.code H.verifier) (List.ofFn input) ≤ _
    dsimp only [HierarchySelectedSource.p,HierarchySelectedSource.q]
    omega
  have hb:=HierarchyNormalizedBounds.raw_budget_bound source H pad
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) ⟨n,input⟩
  have hs : natBitLength (H.time n)+1 ≤ (2*H.coefficient+2)*(n+1)^(k+2) := by
    have hl:=Nat.log_le_self 2 (H.time n)
    have hn:=Nat.one_le_pow (k+2) (n+1) (by omega)
    have hpower:=Nat.pow_le_pow_left (Nat.le_succ n) (k+2)
    have ht : H.time n ≤ 2*H.coefficient*(n+1)^(k+2) := by
      change H.coefficient*(n^(k+2)+1) ≤ _
      nlinarith
    unfold natBitLength
    nlinarith
  calc
    _ ≤ C*(n+1)^a*(natBitLength (H.time n)+1)^b := hp.trans hb
    _ ≤ C*(n+1)^a*((2*H.coefficient+2)*(n+1)^(k+2))^b := by gcongr
    _ = _ := by rw [mul_pow,←pow_mul,pow_add]; ring

end
end NearCubicWires.RepairSource.CloseoutSchedule
