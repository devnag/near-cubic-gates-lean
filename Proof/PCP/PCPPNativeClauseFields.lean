import Proof.PCP.PCPPNativeClauseBank

/-! Actual native scalar/tag append operations on the compact clause bank.
Every raw counter and every allocated scratch cell is retained for reuse. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseBank
open LocalBitMultitape RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem sum_run (left right : Fin 7) (hne : left≠right) (values : Fin 7→ℕ) (C : ℕ) (out : List Bool)
    (hC : PCPPNativeSumAppend.budget (values left) (values right)+1 ≤ C) :
    AppendRun (sumMachine left right) (PCPPNativeSumReusable.budget (values left) (values right) C)
      values C out (natWord (values left+values right)) := by
  classical
  obtain ⟨raw,hr,rs,rh,rt⟩:=PCPPNativeSumReusable.append_run (values left) (values right) C out hC
  obtain ⟨r,hrun,_,rsteps,rheads,rtapes,keep⟩:=RecoveryFocus.dock (sumSlots left right)
    (sum_injective left right hne) PCPPNativeSumReusable.machine _ (heads out) (data values C out)
    (PCPPNativeSumReusable.entry (values left) (values right) C out)
    (fun i=>(sum_input left right values C out i).1)
    (fun i=>(sum_input left right values C out i).2) raw hr
  refine ⟨r,hrun,rsteps.le.trans rs,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,sumSlots left right j=i
    · obtain ⟨j,hj⟩:=hi
      rw [←hj,rheads,rh]
      exact (sum_input left right values C _ j).1.symm
    · have away : ∀ j,sumSlots left right j≠i := by simpa using hi
      have h20 : i≠20 := by intro he; exact away 20 (by rw [he]; rfl)
      rw [(keep i away).1]
      simp only [heads,h20,ite_false]
  · funext i
    by_cases hi : ∃ j,sumSlots left right j=i
    · obtain ⟨j,hj⟩:=hi
      rw [←hj,rtapes,rt]
      exact (sum_input left right values C _ j).2.symm
    · have away : ∀ j,sumSlots left right j≠i := by simpa using hi
      have h20 : i≠20 := by intro he; exact away 20 (by rw [he]; rfl)
      rw [(keep i away).2]
      simp only [data,h20,ite_false]

def literalSlots : Fin 1→Fin 29 := fun _=>20
noncomputable def literalMachine (bits : List Bool) := RecoveryFocus.machine literalSlots (HierarchyFixedWord.raw bits)

theorem literal_run (bits : List Bool) (values : Fin 7→ℕ) (C : ℕ) (out : List Bool) :
    AppendRun (literalMachine bits) bits.length values C out bits := by
  obtain ⟨raw,hr,rf,rs⟩:=Constants.write_run bits out
  obtain ⟨r,hrun,_,rsteps,rheads,rtapes,keep⟩:=RecoveryFocus.dock literalSlots
    (by intro i j _; exact Subsingleton.elim i j) (HierarchyFixedWord.raw bits) _
    (heads out) (data values C out) (Constants.cfg bits out 0 (by omega))
    (by intro i; fin_cases i; simp [literalSlots,heads,Constants.cfg])
    (by intro i; fin_cases i; simp [literalSlots,data,Constants.cfg]) raw hr
  refine ⟨r,hrun,(rsteps.trans rs).le,?_,?_⟩
  · funext i
    by_cases hi : i=20
    · rw [hi]
      have h:=rheads 0
      rw [rf] at h
      simpa [literalSlots,heads,Constants.cfg,List.length_append] using h
    · rw [(keep i (by intro j; simpa only [literalSlots] using Ne.symm hi)).1]
      simp only [heads,hi,ite_false]
  · funext i
    by_cases hi : i=20
    · rw [hi]
      have h:=rtapes 0
      rw [rf] at h
      simpa [literalSlots,data,Constants.cfg] using h
    · rw [(keep i (by intro j; simpa only [literalSlots] using Ne.symm hi)).2]
      simp only [data,hi,ite_false]

theorem AppendRun.join {s t : ℕ} (p : Machine 29 s) (q : Machine 29 t)
    (fp fq : ℕ) (values : Fin 7→ℕ) (C : ℕ) (out first last : List Bool)
    (hp : AppendRun p fp values C out first) (hq : AppendRun q fq values C (out++first) last) :
    AppendRun (Composition.machine p q) (fp+1+fq) values C out (first++last) := by
  obtain ⟨a,ha,as,ah,atapes⟩:=hp
  obtain ⟨b,hb,bs,bh,bt⟩:=hq
  have he : Composition.restart a.final q.start=entry q values C (out++first) := by
    apply configuration_ext
    · rfl
    · exact ah
    · exact atapes
  rw [←he] at hb
  have hr:=Composition.run_join p q fp fq _ a b ha hb
  refine ⟨Composition.joinedReceipt a b,hr,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ fp+1+fq
    omega
  · change b.final.heads=_
    simpa only [List.append_assoc] using bh
  · change b.final.tapes=_
    simpa only [List.append_assoc] using bt

end NearCubicWires.RepairOrdinary.PCPPNativeClauseBank
