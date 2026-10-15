import Proof.CaseAnalysis.WitnessMassTrace

/-! Reuse the existing native addition and copy-back directly after the
retained coefficient fields are installed. No mass-record stream is needed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.Mass
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open CompetitorSumFold CompetitorReusableDecision
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tailBudget (B : ℕ):=3000*(B+1)^2+1+(2*capacity B+40*B+63)

theorem tail_run (B pos : ℕ) (a c : Estimate) (source : List Bool) (ambient : Fin 94→List Bool)
    (h : Store B a source ambient) (ha : a.Valid B) (hc : c.Valid B) : ∃ r,
    runFrom bodyTail (tailBudget B) (cfg bodyTail.start pos (prepared B c ambient))=some r ∧
      r.steps ≤ tailBudget B ∧ r.final.heads=heads pos ∧
      Store B (CompetitorRationalNumerators.add a c) source r.final.tapes:=by
  obtain ⟨n,hn,nh,ns,nt⟩:=native_run B pos a c source ambient h ha hc
  obtain ⟨r,hr,rh,rs,rt⟩:=restore_run B pos (CompetitorRationalNumerators.add a c)
    source n.final.tapes ns
  have he:Composition.restart n.final restoreProgram.start=cfg restoreProgram.start pos n.final.tapes:=by
    apply configuration_ext
    · rfl
    · exact nh
    · rfl
  rw [←he] at hr
  have hall:=Composition.run_join nativeProgram restoreProgram _ _ _ n r hn hr
  refine ⟨_,hall,?_,rh,rs⟩
  change n.steps+1+r.steps ≤ tailBudget B
  unfold tailBudget
  omega

end NearCubicWires.RepairOrdinary.CloseoutWitness.Mass
