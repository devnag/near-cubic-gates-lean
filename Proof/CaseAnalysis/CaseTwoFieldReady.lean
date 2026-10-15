import Proof.CaseAnalysis.CaseTwoFieldNative
import Proof.MachineModel.OrdinaryMaskedReset
import Proof.PCP.PCPSerializerTapeSupport

/-! Reusable original-field appending with one paid reset.  The native
descriptor cursor stays live; all work heads return to zero within the
single physically supplied capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.FieldReady
open LocalBitMultitape RepairRepresentation OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 22) : Bool:=decide (i≠21)
def pads (C : ℕ) (i : Fin 22) := if i=21 then 0 else C
noncomputable def machine:=MaskedReset.machine FieldNative.machine selected
noncomputable def entry (C : ℕ) (source : List Bool) (offset width : ℕ) (out : List Bool) :=
  ZeroPadding.config (Rewind.Workspace.capacities 22 C)
    (Rewind.recording (ZeroPadding.config (pads C)
      (⟨FieldNative.machine.start,FieldNative.heads out,FieldNative.data source offset width out⟩ :
        Configuration 22 _)) 0)
def budget (offset width value : ℕ):=2*FieldNative.budget offset width value+2

theorem field_run (pre tail : List Bool) (limit value C : ℕ) (out : List Bool)
    (hv : value≤limit) (hsource : 2*(pre++orderedNatBits limit value++tail).length+1≤C)
    (hoffset : pre.length≤C) (hwidth : limit≤C)
    (hbudget : FieldNative.budget pre.length limit value+1≤C) :
    let source:=pre++orderedNatBits limit value++tail
    ∃ r,runFrom machine (budget pre.length limit value)
      (entry C source pre.length limit out)=some r ∧
      r.steps≤budget pre.length limit value ∧
      r.final.tapes 0=ZeroPadding.pad C (frame source) ∧
      r.final.tapes 2=ZeroPadding.pad C (List.replicate pre.length true) ∧
      r.final.tapes 3=ZeroPadding.pad C (List.replicate limit true) ∧
      r.final.tapes 5=ZeroPadding.pad C (List.replicate value true) ∧
      r.final.tapes 21=out++natWord value ∧ r.final.heads 21=(out++natWord value).length ∧
      (∀ i : Fin 23, i≠21 → r.final.heads i=0 ∧ (r.final.tapes i).length≤C) := by
  obtain ⟨base,hr,hs,h0,_h0h,h2,_h2h,h3,_h3h,h5,_h5h,h21,hh21⟩:=
    FieldNative.field_run pre tail limit value out hv
  obtain ⟨p,hp,pf,ps,_⟩:=ZeroPadding.run_config FieldNative.machine (pads C) _ _ base hr
  have hlocal (i : Fin 22) (hi : i≠21) : (p.final.tapes i).length≤C := by
    have hinput : (FieldNative.data (pre++orderedNatBits limit value++tail) pre.length limit out i).length≤C := by
      unfold FieldNative.data
      split_ifs with h0 h2 h3
      · simpa only [frame_length] using hsource
      · simpa only [List.length_replicate] using hoffset
      · simpa only [List.length_replicate] using hwidth
      · simp
    have hsupport:=PCPSerializerReuse.tape_support FieldNative.machine _ _ p hp i C 0
      (by change FieldNative.heads out i≤0;simp [FieldNative.heads,hi])
      (by simp only [ZeroPadding.config,ZeroPadding.pad_length,pads,if_neg hi];omega)
    rw [ps] at hsupport
    omega
  obtain ⟨r,rr,rf,rs,_⟩:=MaskedReset.workspace_run FieldNative.machine selected _ C _ p hp
    (by intro i hi;change FieldNative.heads out i=0;simp [FieldNative.heads,of_decide_eq_true hi])
    (by rw [ps];omega)
  have hb : 2*p.steps+2≤budget pre.length limit value := by rw [ps];unfold budget;omega
  have more:=runFrom_moreFuel machine _ (budget pre.length limit value-(2*p.steps+2))
    (entry C (pre++orderedNatBits limit value++tail) pre.length limit out) r rr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,rs.le.trans hb,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [rf];change p.final.tapes 0=_;rw [pf];exact congrArg (ZeroPadding.pad C) h0
  · rw [rf];change p.final.tapes 2=_;rw [pf];exact congrArg (ZeroPadding.pad C) h2
  · rw [rf];change p.final.tapes 3=_;rw [pf];exact congrArg (ZeroPadding.pad C) h3
  · rw [rf];change p.final.tapes 5=_;rw [pf];exact congrArg (ZeroPadding.pad C) h5
  · rw [rf];change p.final.tapes 21=_;rw [pf]
    change ZeroPadding.pad 0 (base.final.tapes 21)=_
    simpa only [ZeroPadding.pad_zero] using h21
  · rw [rf];change p.final.heads 21=_;rw [pf];exact hh21
  · intro i hi
    rw [rf]
    revert hi
    refine Fin.addCases (m:=22) (n:=1) (fun j hj=>?_) (fun j _=>?_) i
    · have hj' : j≠21 := by intro he;subst j;exact hj rfl
      simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_left,selected,
        decide_eq_true hj',if_true]
      exact ⟨True.intro,hlocal j hj'⟩
    · fin_cases j
      simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_right,List.length_replicate]
      exact ⟨True.intro,le_rfl⟩

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.FieldReady
