import Proof.CaseAnalysis.CloseoutRowsEstimatorRetained
import Proof.CaseAnalysis.RowsProjectionReset

/-! Reuse the estimator's private bank with physically supplied D backing.
The native cut tape is external and enters at a nonzero append cursor, so
it is deliberately excluded from the zero-head reset and support claims.
D is separate from native C: the initial paid C rewind itself costs 2C+2. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reset
open LocalBitMultitape RepairRepresentation
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (p : Program) (i : Fin (WholePrefix.tapes p)):=decide (i.val≠52)
def caps (p : Program) (D : ℕ) (i : Fin (WholePrefix.tapes p)):=if i.val=52 ∨ i.val=68 then 0 else D
noncomputable def machine (a : WilliamsAlgorithm):=MaskedReset.machine (Whole.machine a) (selected (producer a))
noncomputable def entry (a : WilliamsAlgorithm) (row : EquationRow.Input) (C D Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool):=
  ZeroPadding.config (Rewind.Workspace.capacities (WholePrefix.tapes (producer a)) (D+1))
    (Rewind.recording (ZeroPadding.config (caps (producer a) D)
      (Whole.entry a row C Q q denominator select)) 0)

theorem private_head (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (i : Fin (WholePrefix.tapes (producer a))) (hi:i.val≠52) :
    (Whole.entry a row C Q q denominator select).heads i=0:=by
  change WholePrefix.heads (producer a) row i=0
  revert hi
  refine Fin.addCases (m:=70) (n:=CloseoutRowsRawRecord.tapes (producer a)) (fun j hj=>?_) (fun j _=>?_) i
  · simp only [WholePrefix.heads,Fin.addCases_left,Cold.heads]
    exact if_neg (fun he=>hj (congrArg Fin.val he))
  · simp only [WholePrefix.heads,Fin.addCases_right]

theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C D Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (fuel : ℕ) (source : ExecutionReceipt _ _)
    (hr:runFrom (Whole.machine a) fuel (Whole.entry a row C Q q denominator select)=some source)
    (hD:source.steps+1≤D)
    (hsize:∀ i:Fin (WholePrefix.tapes (producer a)),i.val≠52→
      ((Whole.entry a row C Q q denominator select).tapes i).length≤D) :
    ∃ r,runFrom (machine a) (2*source.steps+2) (entry a row C D Q q denominator select)=some r ∧
      r.steps≤2*D+2 ∧
      (∀ i:Fin (WholePrefix.tapes (producer a)),
        r.final.tapes (i.castAdd 1)=ZeroPadding.pad (caps (producer a) D i) (source.final.tapes i)) ∧
      (∀ i:Fin (WholePrefix.tapes (producer a)),i.val≠52→ r.final.heads (i.castAdd 1)=0) ∧
      (∀ i:Fin (WholePrefix.tapes (producer a)),i.val≠52→(r.final.tapes (i.castAdd 1)).length≤D) ∧
      r.final.tapes ((0 : Fin 1).natAdd (WholePrefix.tapes (producer a)))=List.replicate (D+1) false:=by
  obtain ⟨padded,hp,pf,ps,_⟩:=ZeroPadding.run_config (Whole.machine a) (caps (producer a) D) _ _ source hr
  have hh:∀ i,selected (producer a) i=true→
      (ZeroPadding.config (caps (producer a) D) (Whole.entry a row C Q q denominator select)).heads i=0:=by
    intro i hi
    exact private_head a row C Q q denominator select i (of_decide_eq_true hi)
  obtain ⟨r,rr,_rs,rt,rh,rl⟩:=CloseoutRowsProjectionReset.reset_keeps (Whole.machine a)
    (selected (producer a)) fuel (D+1) _ padded hp hh (by omega)
  rw [ps] at rr
  have hsteps:=runFrom_steps_le _ _ _ _ rr
  refine ⟨r,rr,by omega,?_,?_,?_,rl⟩
  · intro i
    exact (rt i).trans (congrArg (fun c=>c.tapes i) pf)
  · intro i hi
    exact (rh i).trans (if_pos (decide_eq_true hi))
  · intro i hi
    have ht: r.final.tapes (i.castAdd 1)=
        ZeroPadding.pad (caps (producer a) D i) (source.final.tapes i):=
      (rt i).trans (congrArg (fun c=>c.tapes i) pf)
    have hlen:=congrArg List.length ht
    rw [ZeroPadding.pad_length] at hlen
    have hs:=CloseoutRowsProjectionReset.scratch_support (Whole.machine a) fuel D _ source hr i
      (private_head a row C Q q denominator select i hi) (hsize i hi) hD
    have hcap:caps (producer a) D i≤D:=by unfold caps;split_ifs <;>omega
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reset
