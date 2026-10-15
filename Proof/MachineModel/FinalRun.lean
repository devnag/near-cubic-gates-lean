import Proof.MachineModel.FinalLayout

/-! The actual accumulated total and ordered body produce the native cache,
inside the original reusable source bank and its twelve named ports. -/
namespace NearCubicWires.ExtDecompositionBatch.FinalLayout
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a:DecompositionAlgorithm)

noncomputable def finishedHeads {q:ℕ} (gs:List (ExactThresholdGate q)) (H:Fin (T a) → ℕ):=
  dockH (tailSlots a) (dockH (prefixSlots a) H (CachePrefix.heads gs.length)) (CacheTail.outputHeads gs)
def finalCost {q:ℕ} (C:ℕ) (gs:List (ExactThresholdGate q)):=
  (gs.flatMap exactWord).length+(6*q+15)*gs.length+2*PCPPNativeNaturalAppend.budget gs.length+4*C+28

theorem final_run {q:ℕ} (C:ℕ) (gs:List (ExactThresholdGate q))
    (H:Fin (T a) → ℕ) (A:Fin (T a) → List Bool)
    (hH:∀j,H (prefixSlots a j)=CacheStart.inputHeads gs.length j)
    (hA:∀j,A (prefixSlots a j)=CacheStart.input C gs.length j)
    (hbH:H (bod a)=(gs.flatMap exactWord).length) (hbA:A (bod a)=gs.flatMap exactWord)
    (hdH:H (dom a)=1) (hdA:A (dom a)=UnaryTemplate.tape q)
    (hcH:H (drv a)=0) (hcA:A (drv a)=List.replicate C true)
    (hwH:H (wsp a)=0) (hwA:A (wsp a)=List.replicate (C+1) false)
    (hn:gs.length+2≤C) (hh:PCPPNativeNaturalAppend.budget gs.length≤C)
    (hb:(gs.flatMap exactWord).length≤C) (hc:(exactListWord gs).length≤C) :
    ∃ O:Fin (T a) → List Bool,
      Step (machine a) (finalCost C gs) H A (finishedHeads a gs H) O ∧
      O (cch a)=exactListWord gs ∧ O (tot a)=UnaryTemplate.tape gs.length ∧
      O (dom a)=UnaryTemplate.tape q ∧
      O (drv a)=List.replicate C true ∧ O (wsp a)=List.replicate (C+1) false ∧
      O (scr a)=List.replicate gs.length false ∧
      ∀e:Fin 12,e.val=0 ∨ e.val=1 → O (ex a e)=A (ex a e) := by
  obtain ⟨P,pre,p0,p1,p19,_p20⟩:=CachePrefix.prefix_run C gs.length hn hh
  have first:=pre.dock (prefixSlots a) (prefix_injective a) H A hH hA
  let PH:=dockH (prefixSlots a) H (CachePrefix.heads gs.length)
  let PA:=install (prefixSlots a) A P
  have ph (j:Fin 21):PH (prefixSlots a j)=CachePrefix.heads gs.length j:=
    dockH_slot (prefixSlots a) (prefix_injective a) H _ j
  have pa (j:Fin 21):PA (prefixSlots a j)=P j:=
    install_slot (prefixSlots a) (prefix_injective a) A P j
  have oh (e:Fin 12) (h3:e.val≠3) (h4:e.val≠4) (h5:e.val≠5) (h6:e.val≠6) (h7:e.val≠7):
      PH (ex a e)=H (ex a e):=
    dockH_other (prefixSlots a) H _ _ (prefix_other a e h3 h4 h5 h6 h7)
  have oa (e:Fin 12) (h3:e.val≠3) (h4:e.val≠4) (h5:e.val≠5) (h6:e.val≠6) (h7:e.val≠7):
      PA (ex a e)=A (ex a e):=
    install_other (prefixSlots a) A _ _ (prefix_other a e h3 h4 h5 h6 h7)
  let backing:=PA (bfld a)
  have th:∀j,PH (tailSlots a j)=CacheTail.inputHeads gs j:=by
    intro j;fin_cases j
    · exact (oh 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbH
    · exact ph 17
    · exact ph 19
    · exact (oh 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdH
    · exact ph 0
    · exact (oh 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcH
    · exact (oh 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hwH
  have ta:∀j,PA (tailSlots a j)=CacheTail.input C gs backing j:=by
    intro j;fin_cases j
    · exact (oa 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbA
    · rfl
    · exact (pa 19).trans p19
    · exact (oa 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hdA
    · exact (pa 0).trans p0
    · exact (oa 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcA
    · exact (oa 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hwA
  have second:=(CacheTail.tail_run C gs backing hb hc).dock (tailSlots a) (tail_injective a) PH PA th ta
  have run:=first.seq second
  have time:5*gs.length+2*PCPPNativeNaturalAppend.budget gs.length+18+1+
      ((gs.flatMap exactWord).length+(6*q+10)*gs.length+4*C+9)=finalCost C gs:=by
    unfold finalCost;ring
  rw [time] at run
  refine ⟨install (tailSlots a) PA (CacheTail.output C gs backing),run,?_,?_,?_,?_,?_,?_,?_⟩
  · exact install_slot (tailSlots a) (tail_injective a) PA _ 2
  · exact install_slot (tailSlots a) (tail_injective a) PA _ 4
  · exact install_slot (tailSlots a) (tail_injective a) PA _ 3
  · exact install_slot (tailSlots a) (tail_injective a) PA _ 5
  · exact install_slot (tailSlots a) (tail_injective a) PA _ 6
  · have unchanged:=install_other (tailSlots a) PA (CacheTail.output C gs backing) (scr a)
      (tail_other a 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    exact unchanged.trans ((pa 1).trans p1)
  · intro e he
    have he2:e.val≠2:=by omega
    have he3:e.val≠3:=by omega
    have he4:e.val≠4:=by omega
    have he5:e.val≠5:=by omega
    have he6:e.val≠6:=by omega
    have he7:e.val≠7:=by omega
    have he8:e.val≠8:=by omega
    have he9:e.val≠9:=by omega
    have he10:e.val≠10:=by omega
    exact (install_other (tailSlots a) PA _ _ (tail_other a e he2 he3 he4 he8 he9 he10)).trans
      (oa e he3 he4 he5 he6 he7)

theorem finished_cache {q:ℕ} (gs:List (ExactThresholdGate q)) (H:Fin (T a) → ℕ):
    finishedHeads a gs H (cch a)=0 ∧ finishedHeads a gs H (tot a)=1 ∧
    finishedHeads a gs H (scr a)=0 ∧ finishedHeads a gs H (dom a)=1 ∧
    finishedHeads a gs H (drv a)=0 ∧ finishedHeads a gs H (wsp a)=0 := by
  refine ⟨dockH_slot (tailSlots a) (tail_injective a) _ _ 2,
    dockH_slot (tailSlots a) (tail_injective a) _ _ 4,?_,
    dockH_slot (tailSlots a) (tail_injective a) _ _ 3,
    dockH_slot (tailSlots a) (tail_injective a) _ _ 5,
    dockH_slot (tailSlots a) (tail_injective a) _ _ 6⟩
  have h:=dockH_other (tailSlots a) (dockH (prefixSlots a) H (CachePrefix.heads gs.length))
    (CacheTail.outputHeads gs) (scr a)
    (tail_other a 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  exact h.trans (dockH_slot (prefixSlots a) (prefix_injective a) H _ 1)

end NearCubicWires.ExtDecompositionBatch.FinalLayout
