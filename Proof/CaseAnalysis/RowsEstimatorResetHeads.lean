import Proof.CaseAnalysis.RowsEstimatorReset

/-! Complete head projections of the already executed private reset,
including its reusable log. The source receipt supplies the native head. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reset
open LocalBitMultitape RepairRepresentation
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem heads (a : WilliamsAlgorithm) (row : EquationRow.Input) (C D Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (fuel : ℕ) (source : ExecutionReceipt _ _)
    (hr:runFrom (Whole.machine a) fuel (Whole.entry a row C Q q denominator select)=some source)
    (hD:source.steps+1≤D)
    (actual : ExecutionReceipt _ _)
    (ha:runFrom (machine a) (2*source.steps+2) (entry a row C D Q q denominator select)=some actual) :
    (∀ i:Fin (WholePrefix.tapes (producer a)),actual.final.heads (i.castAdd 1)=
      if selected (producer a) i then 0 else source.final.heads i) ∧
    actual.final.heads ((0 : Fin 1).natAdd (WholePrefix.tapes (producer a)))=0:=by
  obtain ⟨padded,hp,pf,ps,_⟩:=ZeroPadding.run_config (Whole.machine a) (caps (producer a) D) _ _ source hr
  have hh:∀ i,selected (producer a) i=true→
      (ZeroPadding.config (caps (producer a) D) (Whole.entry a row C Q q denominator select)).heads i=0:=by
    intro i hi
    exact private_head a row C Q q denominator select i (of_decide_eq_true hi)
  obtain ⟨base,hb,bf,_bs,_⟩:=MaskedReset.workspace_run (Whole.machine a)
    (selected (producer a)) fuel (D+1) _ padded hp hh (by omega)
  rw [ps] at hb
  have he:base=actual:=Option.some.inj (hb.symm.trans ha)
  constructor
  · intro i
    have h:=congrArg (fun c=>c.heads (i.castAdd 1)) bf
    simp only [SelectiveReset.finished,Rewind.config] at h
    change base.final.heads (i.castAdd 1) =
      Fin.addCases (m := WholePrefix.tapes (producer a)) (n := 1)
        (motive := fun _ => ℕ)
        (fun j => if selected (producer a) j then 0 else padded.final.heads j)
        (fun _ => 0) (i.castAdd 1) at h
    rw [Fin.addCases_left] at h
    have hphead : padded.final.heads i = source.final.heads i :=
      congrArg (fun c => c.heads i) pf
    rw [hphead] at h
    exact (congrArg (fun r=>r.final.heads (i.castAdd 1)) he).symm.trans h
  · let log : Fin (WholePrefix.tapes (producer a)+1):=(0 : Fin 1).natAdd (WholePrefix.tapes (producer a))
    have h:=congrArg (fun c=>c.heads log) bf
    simp only [SelectiveReset.finished,Rewind.config] at h
    change base.final.heads log =
      Fin.addCases (m := WholePrefix.tapes (producer a)) (n := 1)
        (motive := fun _ => ℕ)
        (fun j => if selected (producer a) j then 0 else padded.final.heads j)
        (fun _ => 0) ((0 : Fin 1).natAdd (WholePrefix.tapes (producer a))) at h
    rw [Fin.addCases_right] at h
    exact (congrArg (fun r=>r.final.heads log) he).symm.trans h

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reset
