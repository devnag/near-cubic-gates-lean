import Proof.CaseAnalysis.CommonProgramChoose
import Proof.CaseAnalysis.CommonProgramRuns
import Proof.CaseAnalysis.CommonProgramBudget

/-! One ordinary E^NP certificate for the original common language. The
only local inputs are the weak machine, its little-o bound, and the checked
clause supplier already required by the final hardness consumer. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces CloseoutLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem certificate (p : Parameters) (M : OrdinaryWeakMachine) (c : Constants)
    (sup : Suppliers p M c) :
    Nonempty (OrdinaryENPCertificate RecoveryOracle.correctedSat (target p M)):=by
  obtain ⟨C,E,h⟩:=exists_budget p c
  refine ⟨Closeout.certificate_of_runs (target p M) (program p) C E ?_⟩
  intro n point
  have hb:=h (List.ofFn point)
  simp only [List.length_ofFn] at hb
  exact (runs p M c sup n point).enlarge hb

theorem exists_certificate (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n=>n^(k+2)))
    (degree D copies cutoff : ℕ) (hD : 1 ≤ D) (clauses : ClauseReady sources degree D)
    (hcopies : (selectedAmplifier sources.amplification degree).arityCoefficient ≤ copies)
    (M : OrdinaryWeakMachine) (littleO : OrdinaryLittleO M (fun n=>n^(k+2))) :
    ∃ onset,cutoff ≤ onset ∧ Nonempty (OrdinaryENPCertificate RecoveryOracle.correctedSat
      (language sources k clock M degree copies D onset)):=by
  obtain ⟨onset,honset,As,Bs,Aw,Bw,Aq,Bq,refuter,c,sup⟩:=
    choose sources k clock degree D copies cutoff hD clauses hcopies M littleO
  exact ⟨onset,honset,certificate
    ⟨sources,k,degree,D,copies,As,Bs,onset,Aw,Bw,Aq,Bq,clock,refuter⟩ M c sup⟩

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
