import Proof.CaseAnalysis.RowsOriginalPair
import Proof.CaseAnalysis.RowsProjectionReset

/-! Both native literal reads return all cursors together. Only their
logical running time controls the paid return log and private backing. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalPair
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (C : ℕ) (i : Fin 25) := if i=0 then 0 else C
noncomputable def reset := MaskedReset.machine machine (fun _=>true)
def resetBudget (a b : ℕ) (sa sb : Bool) := 2*budget a b sa sb+2
def resetInput (C : ℕ) (source : List Bool) : Fin 26 → List Bool :=
  Fin.addCases (m:=25) (n:=1) (motive:=fun _=>List Bool)
    (fun i=>if i=0 then source else List.replicate C false) (fun _=>List.replicate C false)

theorem reset_run (a b C : ℕ) (sa sb : Bool) (hc : budget a b sa sb+1 ≤ C) :
    ∃ r,runFrom reset (resetBudget a b sa sb)
      ⟨reset.start,fun _=>0,resetInput C (word a b sa sb)⟩=some r ∧
      r.final.heads=(fun _=>0) ∧ r.final.tapes 0=word a b sa sb ∧
      r.final.tapes 11=ZeroPadding.pad C (List.replicate a true) ∧
      r.final.tapes 12=ZeroPadding.pad C [sa] ∧
      r.final.tapes 23=ZeroPadding.pad C (List.replicate b true) ∧
      r.final.tapes 24=ZeroPadding.pad C [sb] ∧
      (∀ i : Fin 26,i≠0 → (r.final.tapes i).length=C) ∧
      r.final.tapes 25=List.replicate C false ∧ r.steps ≤ resetBudget a b sa sb := by
  obtain ⟨raw,hr,t0,_,t11,t12,t23,t24,_⟩:=raw_run a b sa sb
  obtain ⟨p,hp,pf,ps,_⟩:=ZeroPadding.run_config machine (caps C) _ _ raw hr
  obtain ⟨r,rr,rf,rs,_⟩:=MaskedReset.workspace_run machine (fun _=>true) _ C _ p hp
    (by intro i _;change heads 0 i=0;simp [heads]) (by omega)
  have ht : 2*p.steps+2 ≤ resetBudget a b sa sb := by
    have hs:=runFrom_steps_le machine _ _ raw hr
    unfold resetBudget;omega
  have run:=runFrom_moreFuel reset _ (resetBudget a b sa sb-(2*p.steps+2)) _ r rr
  rw [Nat.add_sub_of_le ht] at run
  have ein : ZeroPadding.config (Rewind.Workspace.capacities 25 C)
      (Rewind.recording (ZeroPadding.config (caps C)
        (⟨machine.start,heads 0,data (word a b sa sb)⟩ : Configuration 25 _)) 0)=
      (⟨reset.start,fun _=>0,resetInput C (word a b sa sb)⟩ : Configuration 26 _) := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;>
        simp [resetInput,caps,data,ZeroPadding.config,Rewind.Workspace.capacities,Rewind.recording,
          Rewind.config,Fin.addCases,ZeroPadding.pad]
  rw [ein] at run
  have head : r.final.heads=(fun _=>0) := by
    rw [rf,pf];funext i;fin_cases i <;> rfl
  have tape (i : Fin 25) : r.final.tapes (i.castAdd 1)=ZeroPadding.pad (caps C i) (raw.final.tapes i) := by
    rw [rf,pf]
    simp only [SelectiveReset.finished,Rewind.config,ZeroPadding.config,Fin.addCases_left]
  have zero : r.final.tapes 0=word a b sa sb := by
    change r.final.tapes ((0 : Fin 25).castAdd 1)=_
    rw [tape,t0]
    exact ZeroPadding.pad_zero _
  refine ⟨r,run,head,zero,?_,?_,?_,?_,?_,?_,by omega⟩
  · change r.final.tapes ((11 : Fin 25).castAdd 1)=_
    rw [tape,t11];rfl
  · change r.final.tapes ((12 : Fin 25).castAdd 1)=_
    rw [tape,t12];rfl
  · change r.final.tapes ((23 : Fin 25).castAdd 1)=_
    rw [tape,t23];rfl
  · change r.final.tapes ((24 : Fin 25).castAdd 1)=_
    rw [tape,t24];rfl
  · intro i hi
    refine Fin.addCases (m:=25) (n:=1) (motive:=fun i=>i≠0 → (r.final.tapes i).length=C) ?_ ?_ i hi
    · intro j hj
      have hz : j≠0:=by intro e;subst j;exact hj rfl
      have small:=CloseoutRowsProjectionReset.scratch_support machine _ C _ raw hr j
        (by simp [heads]) (by simp [data,hz]) (by omega)
      rw [tape]
      simp only [caps,hz,↓reduceIte,ZeroPadding.pad_length,max_eq_left small]
    · intro j _
      rw [rf]
      simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_right,List.length_replicate]
  · rw [rf];rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalPair
