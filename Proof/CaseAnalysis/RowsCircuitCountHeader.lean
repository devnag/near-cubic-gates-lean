import Proof.CaseAnalysis.RowsCircuitThreshold
import Proof.CaseAnalysis.RowsProjectionReset

/-! The existing total native count-header writer uses the shared circuit
workspace and preserves its append cursor. Every private head is returned
with the existing masked reset; no numeric count or scratch is free. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCountHeader
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 18):=decide (i≠17)
noncomputable def machine:=MaskedReset.machine EquationHeaderAppend.machine selected
def pads (C : ℕ) (i : Fin 19):=if i.val=17 then 0 else C
def heads (out : List Bool) (i : Fin 19):=if i.val=17 then out.length else 0
def input (C n : ℕ) (out : List Bool) (i : Fin 19):=
  if i.val=17 then out else if i.val=0 then ZeroPadding.pad C (List.replicate n true)
  else List.replicate C false
def budget (n : ℕ):=2*EquationHeaderAppend.budget n+2

theorem input_eq (C n : ℕ) (out : List Bool) :
    ZeroPadding.config (pads C)
      (ZeroPadding.config (Rewind.Workspace.capacities 18 C)
        (Rewind.recording (EquationHeaderAppend.entry n out) 0))=
      (⟨machine.start,heads out,input C n out⟩ : Configuration 19 _):=by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=18) (n:=1) ?_ ?_ i
    · intro j
      simp only [ZeroPadding.config,Rewind.recording,Rewind.config,Fin.addCases_left,
        EquationHeaderAppend.entry,EquationHeaderAppend.heads,heads,Fin.val_castAdd]
      by_cases hj:j=17
      · subst j;rfl
      · have hv:j.val≠17:=fun h=>hj (Fin.ext h)
        simp only [if_neg hj,if_neg hv]
    · intro j;have hj:j=0:=Fin.eq_zero j;subst j;rfl
  · funext i
    refine Fin.addCases (m:=18) (n:=1) ?_ ?_ i
    · intro j
      simp only [ZeroPadding.config,Rewind.recording,Rewind.config,Fin.addCases_left,
        Rewind.Workspace.capacities,ZeroPadding.pad_zero,EquationHeaderAppend.entry,
        EquationHeaderAppend.tapes,pads,input,Fin.val_castAdd]
      by_cases ho:j=17
      · subst j;change ZeroPadding.pad 0 out=out;exact ZeroPadding.pad_zero out
      · have hn17:j.val≠17:=fun h=>ho (Fin.ext h)
        rw [if_neg ho,if_neg hn17,if_neg hn17]
        by_cases hz:j=0
        · subst j;rfl
        · have hn0:j.val≠0:=fun h=>hz (Fin.ext h)
          simp [hz,hn0,ZeroPadding.pad]
    · intro j
      simp only [ZeroPadding.config,Rewind.Workspace.capacities,Rewind.recording,Rewind.config,
        Fin.addCases_right]
      have hj:j=0:=Fin.eq_zero j;subst j
      change ZeroPadding.pad C (ZeroPadding.pad C [])=List.replicate C false
      simp [ZeroPadding.pad]

theorem header_run (C n : ℕ) (out : List Bool)
    (hn : n ≤ C) (hc : EquationHeaderAppend.budget n+1 ≤ C) : ∃ r,
    runFrom machine (budget n) ⟨machine.start,heads out,input C n out⟩=some r ∧
      r.steps ≤ budget n ∧ r.final.heads=heads (out++natWord n) ∧
      r.final.tapes 17=out++natWord n ∧
      r.final.tapes 1=ZeroPadding.pad C (List.replicate n true) ∧
      r.final.tapes 18=List.replicate C false ∧
      ∀ i : Fin 19,i.val≠17 → (r.final.tapes i).length ≤ C:=by
  obtain ⟨base,hb,bt,bh,b1,_b1h,bs⟩:=EquationHeaderAppend.append_run n out
  obtain ⟨reset,rr,rf,rs,_⟩:=MaskedReset.workspace_run EquationHeaderAppend.machine selected
    _ C _ base hb (by
      intro i hi;change EquationHeaderAppend.heads out i=0
      have h:i≠17:=of_decide_eq_true hi
      simp only [EquationHeaderAppend.heads,if_neg h]) (by omega)
  obtain ⟨actual,ar,af,asteps,_⟩:=ZeroPadding.run_config machine (pads C) _ _ reset rr
  rw [input_eq] at ar
  have htime:2*base.steps+2 ≤ budget n:=by unfold budget;omega
  have more:=runFrom_moreFuel machine _ (budget n-(2*base.steps+2)) _ actual ar
  rw [Nat.add_sub_of_le htime] at more
  refine ⟨actual,more,by omega,?_,?_,?_,?_,?_⟩
  · rw [af,rf];funext i
    refine Fin.addCases (m:=18) (n:=1) ?_ ?_ i
    · intro j
      simp only [ZeroPadding.config,SelectiveReset.finished,Rewind.config,Fin.addCases_left]
      by_cases hj:j=17
      · subst j;simpa [selected,heads] using bh
      · have hv:j.val≠17:=fun h=>hj (Fin.ext h)
        simp [selected,hj,heads,hv]
    · intro j;have hj:j=0:=Fin.eq_zero j;subst j;rfl
  · rw [af,rf];change ZeroPadding.pad 0 (base.final.tapes 17)=_
    rw [ZeroPadding.pad_zero,bt]
  · rw [af,rf];change ZeroPadding.pad C (base.final.tapes 1)=_
    rw [b1]
  · rw [af,rf];change ZeroPadding.pad C (List.replicate C false)=_
    simp [ZeroPadding.pad]
  · intro i hi
    rw [af,rf]
    revert hi
    refine Fin.addCases (m:=18) (n:=1) ?_ ?_ i
    · intro j hj
      change j.val≠17 at hj
      simp only [ZeroPadding.config,SelectiveReset.finished,Rewind.config,Fin.addCases_left,
        pads,Fin.val_castAdd,if_neg hj]
      rw [ZeroPadding.pad_length]
      refine max_le le_rfl ?_
      have hn17:j≠17:=fun h=>hj (congrArg Fin.val h)
      have hh:EquationHeaderAppend.heads out j=0:=by
        simp only [EquationHeaderAppend.heads,if_neg hn17]
      have ht:(EquationHeaderAppend.tapes n out j).length ≤ C:=by
        simp only [EquationHeaderAppend.tapes,if_neg hn17]
        split_ifs with hz
        · simpa only [List.length_replicate] using hn
        · simp only [List.length_nil,Nat.zero_le]
      exact CloseoutRowsProjectionReset.scratch_support EquationHeaderAppend.machine _ C
        (EquationHeaderAppend.entry n out) base hb j hh ht (by omega)
    · intro j _;have hj:j=0:=Fin.eq_zero j;subst j
      change (ZeroPadding.pad C (List.replicate C false)).length ≤ C
      simp [ZeroPadding.pad]

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitCountHeader
