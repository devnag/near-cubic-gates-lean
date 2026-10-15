import Proof.Hierarchy.CompetitorRawFieldEmit

/-! A fixed sequence of physical scalar-field appends. The source wiring
may reuse a field; its head is restored before each subsequent call. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def states {t : ℕ} : List (Fin t) → ℕ
  | [] => 1
  | _::js => 4+states js
def halt (t : ℕ) : Machine t 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none
noncomputable def listProgram {t : ℕ} (target counter : Fin t) : (js : List (Fin t)) → Machine t (states js)
  | [] => halt t
  | j::js => Composition.machine (program j target counter) (listProgram target counter js)
def listCost {t : ℕ} (fields : Fin t → List Bool) : List (Fin t) → ℕ
  | [] => 0
  | j::js => 4*(fields j).length+4+listCost fields js
def stream {t : ℕ} (fields : Fin t → List Bool) (js : List (Fin t)) := js.flatMap (fun j => frame (fields j))

theorem update_existing {t : ℕ} {α : Type} (f : Fin t → α) (i : Fin t) (v : α) (h : f i=v) :
    Function.update f i v=f := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [h]
  · simp [Function.update_of_ne hj]
theorem list_run {t : ℕ} (target counter : Fin t) (js : List (Fin t)) (fields : Fin t → List Bool)
    (htc : target≠counter) (hst : ∀ j∈js,j≠target) (hsc : ∀ j∈js,j≠counter)
    (out : List Bool) (cap : ℕ) (heads : Fin t → ℕ) (ambient : Fin t → List Bool)
    (hs : ∀ j∈js,heads j=0) (ht : heads target=out.length) (hc : heads counter=0)
    (hsource : ∀ j∈js,ambient j=frame (fields j))
    (htarget : ambient target=out) (hcounter : ambient counter=List.replicate cap false)
    (hcap : ∀ j∈js,2*(fields j).length+1≤cap) :
    ∃ r : ExecutionReceipt t (states js),
      runFrom (listProgram target counter js) (listCost fields js)
        (RecoveryCalls.restarted (listProgram target counter js) heads ambient)=some r ∧
      r.final.heads=Function.update heads target (out++stream fields js).length ∧
      r.final.tapes=Function.update ambient target (out++stream fields js) ∧ r.steps=listCost fields js := by
  induction js generalizing out heads ambient with
  | nil =>
    let r : ExecutionReceipt t 1 := ⟨RecoveryCalls.restarted (halt t) heads ambient,0,
      (RecoveryCalls.restarted (halt t) heads ambient).tapeCells⟩
    refine ⟨r,rfl,?_,?_,rfl⟩
    · change heads=Function.update heads target (out++stream fields []).length
      simp only [stream,List.flatMap_nil,List.append_nil,update_existing heads target out.length ht]
    · change ambient=Function.update ambient target (out++stream fields [])
      simp only [stream,List.flatMap_nil,List.append_nil,update_existing ambient target out htarget]
  | cons j js ih =>
    have hj : j∈j::js := by simp
    obtain ⟨first,hfirst,hfh,hft,hfs⟩ := field_run j target counter (hst j hj) (hsc j hj) htc
      (fields j) out cap heads ambient (hs j hj) ht hc (hsource j hj) htarget hcounter (hcap j hj)
    let nextOut := out++frame (fields j)
    let nextHeads := Function.update heads target nextOut.length
    let nextTapes := Function.update ambient target nextOut
    have hhsource : ∀ k∈js,nextHeads k=0 := by
      intro k hk
      change Function.update heads target nextOut.length k=0
      rw [Function.update_of_ne (hst k (by simp [hk]))]
      exact hs k (by simp [hk])
    have htsource : ∀ k∈js,nextTapes k=frame (fields k) := by
      intro k hk
      change Function.update ambient target nextOut k=_
      rw [Function.update_of_ne (hst k (by simp [hk]))]
      exact hsource k (by simp [hk])
    obtain ⟨last,hlast,hlh,hlt,hls⟩ := ih (fun k hk => hst k (by simp [hk]))
      (fun k hk => hsc k (by simp [hk])) nextOut nextHeads nextTapes hhsource
      (by simp [nextHeads]) (by simpa [nextHeads,Function.update_of_ne htc.symm] using hc)
      htsource (by simp [nextTapes]) (by simpa [nextTapes,Function.update_of_ne htc.symm] using hcounter)
      (fun k hk => hcap k (by simp [hk]))
    have he : Composition.restart first.final (listProgram target counter js).start=
        RecoveryCalls.restarted (listProgram target counter js) nextHeads nextTapes := by
      apply configuration_ext
      · rfl
      · exact hfh
      · exact hft
    have hl' : runFrom (listProgram target counter js) (listCost fields js)
        (Composition.restart first.final (listProgram target counter js).start)=some last := by rw [he]; exact hlast
    have hall := Composition.run_join (program j target counter) (listProgram target counter js)
      (4*(fields j).length+3) (listCost fields js) _ first last hfirst hl'
    have hcost : (4*(fields j).length+3)+1+listCost fields js=listCost fields (j::js) := by simp only [listCost]
    rw [hcost] at hall
    refine ⟨Composition.joinedReceipt first last,hall,?_,?_,?_⟩
    · change last.final.heads=_
      rw [hlh]
      simp [nextHeads,nextOut,stream,List.append_assoc]
    · change last.final.tapes=_
      rw [hlt]
      simp [nextTapes,nextOut,stream,List.append_assoc]
    · change first.steps+1+last.steps=_
      rw [hfs,hls]
      exact hcost

end NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit
