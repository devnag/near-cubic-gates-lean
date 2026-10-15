import Proof.CaseAnalysis.RowsPacketField

/-! A fixed native-port packet loader. Every field is read sequentially
and all native target heads return to zero before the polynomial begins. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPacketLoad
open LocalBitMultitape RecoveryExecution RecoveryRootRound CloseoutRowsPacketField
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def states {t : ℕ} : List (Fin t)→ℕ
  | []=>1
  | _::js=>4+states js
def halt (t : ℕ) : Machine t 1 where
  descriptionBits := 0
  start := 0
  halted := fun _=>true
  rule := fun _ _=>none
noncomputable def machine {t : ℕ} (source log : Fin t) : (js : List (Fin t))→Machine t (states js)
  | []=>halt t
  | j::js=>Composition.machine (program source j log) (machine source log js)
def cost {t : ℕ} (fields : Fin t→List Bool) : List (Fin t)→ℕ
  | []=>0
  | j::js=>3*(fields j).length+3+cost fields js
def stream {t : ℕ} (fields : Fin t→List Bool) (js : List (Fin t)) := js.flatMap fun j=>frame (fields j)
def written {t : ℕ} (fields : Fin t→List Bool) (C : ℕ) : List (Fin t)→(Fin t→List Bool)→Fin t→List Bool
  | [],data=>data
  | j::js,data=>written fields C js (Function.update data j (ZeroPadding.pad C (fields j)))

theorem list_run {t : ℕ} (source log : Fin t) (js : List (Fin t)) (fields : Fin t→List Bool)
    (hsl : source≠log) (hn : js.Nodup) (hts : ∀ j∈js,j≠source) (htl : ∀ j∈js,j≠log)
    (pre tail : List Bool) (C D : ℕ) (heads : Fin t→ℕ) (data : Fin t→List Bool)
    (hs : heads source=pre.length) (hl : heads log=0) (hj : ∀ j∈js,heads j=0)
    (ds : data source=pre++stream fields js++tail) (dl : data log=List.replicate D false)
    (dj : ∀ j∈js,data j=List.replicate C false) (hD : ∀ j∈js,(fields j).length ≤ D) :
    ∃ r,runFrom (machine source log js) (cost fields js)
      ⟨(machine source log js).start,heads,data⟩=some r ∧
      r.final.heads=Function.update heads source (pre.length+(stream fields js).length) ∧
      r.final.tapes=written fields C js data ∧ r.steps=cost fields js := by
  induction js generalizing pre heads data with
  | nil =>
    let r : ExecutionReceipt t 1 := ⟨⟨0,heads,data⟩,0,(⟨0,heads,data⟩ : Configuration t 1).tapeCells⟩
    refine ⟨r,rfl,?_,rfl,rfl⟩
    funext i
    by_cases hi : i=source
    · subst i
      simp [r,stream,hs]
    · simp [r,stream,hi]
  | cons j js ih =>
    have hmem : j∈j::js := by simp
    have hn' := List.nodup_cons.mp hn
    have hst := (hts j hmem).symm
    have hjl := htl j hmem
    have hsource : data source=pre++frame (fields j)++(stream fields js++tail) := by
      simpa only [stream,List.flatMap_cons,List.append_assoc] using ds
    obtain ⟨a,ha,ah,atape,asteps⟩ := field_load source j log hst hsl hjl pre (fields j)
      (stream fields js++tail) C D (hD j hmem) heads data hs (hj j hmem) hl hsource (dj j hmem) dl
    let nh := Function.update heads source (pre.length+2*(fields j).length+1)
    let nd := Function.update data j (ZeroPadding.pad C (fields j))
    have hs' : nh source=(pre++frame (fields j)).length := by simp [nh,frame_length]; omega
    have hl' : nh log=0 := by simpa [nh,Function.update_of_ne hsl.symm] using hl
    have hj' : ∀ k∈js,nh k=0 := by
      intro k hk
      rw [show nh k=heads k from Function.update_of_ne (hts k (by simp [hk])) _ _]
      exact hj k (by simp [hk])
    have ds' : nd source=(pre++frame (fields j))++stream fields js++tail := by
      rw [show nd source=data source from Function.update_of_ne hst _ _]
      simpa only [List.append_assoc] using hsource
    have dl' : nd log=List.replicate D false := by
      rw [show nd log=data log from Function.update_of_ne hjl.symm _ _]
      exact dl
    have dj' : ∀ k∈js,nd k=List.replicate C false := by
      intro k hk
      have hkj : k≠j := by intro he; subst k; exact hn'.1 hk
      rw [show nd k=data k from Function.update_of_ne hkj _ _]
      exact dj k (by simp [hk])
    obtain ⟨b,hb,bh,btape,bsteps⟩ := ih hn'.2 (fun k hk=>hts k (by simp [hk]))
      (fun k hk=>htl k (by simp [hk])) (pre++frame (fields j)) nh nd hs' hl' hj' ds' dl' dj'
      (fun k hk=>hD k (by simp [hk]))
    have he : Composition.restart a.final (machine source log js).start=
        ⟨(machine source log js).start,nh,nd⟩ := by
      apply configuration_ext
      · rfl
      · exact ah
      · exact atape
    rw [←he] at hb
    have whole := Composition.run_join (program source j log) (machine source log js) _ _ _ a b ha hb
    have hfuel : 3*(fields j).length+2+1+cost fields js=cost fields (j::js) := by simp only [cost]
    rw [hfuel] at whole
    refine ⟨Composition.joinedReceipt a b,whole,?_,btape,?_⟩
    · change b.final.heads=_
      rw [bh]
      simp only [nh,Function.update_idem,stream,List.flatMap_cons,List.length_append]
      congr 1
      simp [frame_length,Nat.add_assoc]
    · change a.steps+1+b.steps=cost fields (j::js)
      rw [asteps,bsteps,←hfuel]

theorem cost_bound {t : ℕ} (fields : Fin t→List Bool) (js : List (Fin t)) (C : ℕ)
    (hC : ∀ j∈js,(fields j).length ≤ C) : cost fields js ≤ js.length*(3*C+3) := by
  induction js with
  | nil => simp [cost]
  | cons j js ih =>
    have h0 := hC j (by simp)
    have h1 := ih (fun k hk=>hC k (by simp [hk]))
    simp only [cost,List.length_cons]
    nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsPacketLoad
