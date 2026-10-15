import Proof.CaseAnalysis.RecoveryReferenceFrame

/-! Append one physically framed unary reference to the original forward
choice stream, and erase the copied length and temporary frame for reuse. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTagReferenceAppend
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool) : Fin 7→ℕ:=![0,0,0,0,out.length,0,0]
def data (n P C : ℕ) (out : List Bool) (prepared : Bool) : Fin 7→List Bool:=
  Fin.addCases (m:=4) (n:=3) (motive:=fun _=>List Bool)
    (if prepared then RecoveryBoundedReferenceFrame.framed n P C else RecoveryBoundedReferenceFrame.input n P C)
    ![out,List.replicate C true,List.replicate (C+1) false]
def prepareSlots (j : Fin 4) : Fin 7:=j.castAdd 3
def appendSlots : Fin 3→Fin 7:=![2,4,3]
def clearSlots : Fin 4→Fin 7:=![1,2,5,6]
noncomputable def prepare:=RecoveryFocus.machine prepareSlots RecoveryBoundedReferenceFrame.machine
noncomputable def append:=RecoveryFocus.machine appendSlots CompetitorFrameAppend.machine
noncomputable def clear:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 2)
noncomputable def machine:=Composition.machine (Composition.machine prepare append) clear
def budget (n C : ℕ):=10*n+2*C+18

theorem prepare_run (n P C : ℕ) (out : List Bool) (hC : 2*n+1 ≤ C) :
    ∃ r,runFrom prepare (6*n+9) ⟨prepare.start,heads out,data n P C out false⟩=some r ∧
      r.steps ≤ 6*n+9 ∧ r.final.heads=heads out ∧ r.final.tapes=data n P C out true := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryBoundedReferenceFrame.prepare_ready n P C hC).focus_at
    prepareSlots (by decide) (heads out) (data n P C out false)
    (by intro j;fin_cases j <;> rfl) (by intro j;fin_cases j <;> rfl)
  have he : install prepareSlots (data n P C out false) (RecoveryBoundedReferenceFrame.framed n P C)=data n P C out true := by
    apply HierarchyWidth.install_eq prepareSlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 1 rfl) | exact False.elim (hi 2 rfl)
  exact ⟨r,hr,rs,rh,rt.trans he⟩

theorem append_run (n P C : ℕ) (out : List Bool) (hC : 2*n+1 ≤ C) :
    ∃ r,runFrom append (4*n+3) ⟨append.start,heads out,data n P C out true⟩=some r ∧
      r.steps=4*n+3 ∧ r.final.heads=heads (out++frame (List.replicate n true)) ∧
      r.final.tapes=data n P C (out++frame (List.replicate n true)) true := by
  obtain ⟨p,hp,pf,ps⟩:=CompetitorFrameAppend.padded_append_run (List.replicate n true) out C
    (by simpa only [List.length_replicate] using hC)
  rw [List.length_replicate] at hp ps
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock appendSlots (by decide) CompetitorFrameAppend.machine _
    (heads out) (data n P C out true) (CompetitorFrameAppend.cfg 0 (List.replicate n true) out C)
    (by intro j;fin_cases j <;> rfl) (by intro j;fin_cases j <;> rfl) p hp
  refine ⟨r,hr,rs.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,appendSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,pf]
      fin_cases j <;> rfl
    · rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).1]
      fin_cases i
      all_goals first | rfl | exact False.elim (hi ⟨1,rfl⟩)
  · have he:=HierarchyWidth.install_eq appendSlots (by decide) (data n P C out true) r.final.tapes
      (CompetitorFrameAppend.cfg 3 (List.replicate n true) (out++frame (List.replicate n true)) C).tapes
      (by intro j;rw [rt j,pf]) (by intro i hi;exact (rkeep i hi).2)
    rw [←he]
    apply HierarchyWidth.install_eq appendSlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 1 rfl)

theorem clear_run (n P C : ℕ) (out : List Bool) (hC : 2*n+1 ≤ C) :
    ∃ r,runFrom clear (2*C+4) ⟨clear.start,heads out,data n P C out true⟩=some r ∧
      r.steps=2*C+4 ∧ r.final.heads=heads out ∧ r.final.tapes=data n P C out false := by
  let backing : Fin 2→List Bool:=![ZeroPadding.pad C (List.replicate n true),ZeroPadding.pad C (frame (List.replicate n true))]
  have hb : ∀ j,(backing j).length ≤ C := by
    intro j
    fin_cases j
    · change (ZeroPadding.pad C (List.replicate n true)).length ≤ C
      rw [ZeroPadding.pad_length,List.length_replicate]
      omega
    · change (ZeroPadding.pad C (frame (List.replicate n true))).length ≤ C
      rw [ZeroPadding.pad_length,frame_length,List.length_replicate]
      omega
  obtain ⟨r,hr,rh,rt,rs⟩:=(RecoveryScratchErase.erase_ready C (C+1) backing hb).focus_at
    clearSlots (by decide) (heads out) (data n P C out true)
    (by intro j;fin_cases j <;> rfl) (by intro j;fin_cases j <;> rfl)
  have he : install clearSlots (data n P C out true)
      (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
          (fun _=>List.replicate C false) (fun _=>List.replicate C true))
        (fun _=>List.replicate (max (C+1) (C+1)) false))=data n P C out false := by
    apply HierarchyWidth.install_eq clearSlots (by decide)
    · intro j;fin_cases j <;> simp only [max_self] <;> rfl
    · intro i hi
      fin_cases i
      all_goals first | rfl | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)
  exact ⟨r,hr,rs,rh,rt.trans he⟩

theorem reference_run (n P C : ℕ) (out : List Bool) (hC : 2*n+1 ≤ C) :
    ∃ r,runFrom machine (budget n C) ⟨machine.start,heads out,data n P C out false⟩=some r ∧
      r.steps ≤ budget n C ∧ r.final.heads=heads (out++frame (List.replicate n true)) ∧
      r.final.tapes=data n P C (out++frame (List.replicate n true)) false := by
  obtain ⟨a,ar,asteps,ah,atapes⟩:=prepare_run n P C out hC
  obtain ⟨b,br,bsteps,bh,bt⟩:=append_run n P C out hC
  have br' : runFrom append (4*n+3) (restart a.final append.start)=some b := by
    change runFrom append _ ⟨append.start,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]
    exact br
  have hab:=Composition.run_join prepare append _ _ _ a b ar br'
  obtain ⟨c,cr,csteps,ch,ct⟩:=clear_run n P C (out++frame (List.replicate n true)) hC
  have cr' : runFrom clear (2*C+4) (restart (joinedReceipt a b).final clear.start)=some c := by
    change runFrom clear _ ⟨clear.start,b.final.heads,b.final.tapes⟩=some c
    rw [bh,bt]
    exact cr
  have full:=Composition.run_join (Composition.machine prepare append) clear _ _ _ (joinedReceipt a b) c hab cr'
  have he : (6*n+9)+1+(4*n+3)+1+(2*C+4)=budget n C := by unfold budget;omega
  rw [he] at full
  refine ⟨joinedReceipt (joinedReceipt a b) c,full,?_,ch,ct⟩
  change a.steps+1+b.steps+1+c.steps ≤ budget n C
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedTagReferenceAppend
