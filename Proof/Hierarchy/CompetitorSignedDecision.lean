import Proof.Hierarchy.HierarchyBinaryKernel
import Proof.MachineModel.OrdinaryCompare

/-! Actual final signed comparison for the fast competitor. Four bounded
natural scalar words represent two signed numerators. Two paid additions,
their resets, a physical comparison and its reset decide the order. The
input words are preserved; all heads return to zero. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSignedDecision
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def compareMachine : Machine 4 7 := Rewind.machine Compare.machine

theorem compare_ready (w a b : ℕ) (ha : a<2^w) (hb : b<2^w) :
    ReadyRun compareMachine (4*w+4)
      ![frame (binary w a),frame (binary w b),[],List.replicate (2*w+1) false]
      ![frame (binary w a),frame (binary w b),[decide (a≤b)],List.replicate (2*w+1) false] := by
  obtain ⟨base,hr,hf,hs,_⟩ := Compare.compare_run [] [] (binary w a) (binary w b) [] [] [] (by simp)
  have hi : Compare.config (Compare.scanState true) (frame (binary w a)) (frame (binary w b)) 0 0 []=
      initialConfiguration Compare.machine ![frame (binary w a),frame (binary w b),[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have hr' : run Compare.machine (2*w+1) ![frame (binary w a),frame (binary w b),[]]=some base := by
    rw [run,← hi]
    simpa using hr
  have hs' : base.steps=2*w+1 := by simpa using hs
  have hf' : base.final.tapes=![frame (binary w a),frame (binary w b),[decide (a≤b)]] := by
    rw [hf]
    simp [Compare.config,binary_value w a ha,binary_value w b hb]
  obtain ⟨r,hrun,ht,hc,hh,hsteps,_⟩ :=
    Rewind.Workspace.reset_workspace Compare.machine _ _ base hr' (2*w+1)
  have he : 2*base.steps+2=4*w+4 := by omega
  rw [he] at hrun
  refine ⟨r,?_,?_,hh,hsteps.trans he⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i; fin_cases i
    · exact (ht 0).trans (congrFun hf' 0)
    · exact (ht 1).trans (congrFun hf' 1)
    · exact (ht 2).trans (congrFun hf' 2)
    · simpa [hs'] using hc

def leftSlots : Fin 4 → Fin 8 := ![0,3,4,7]
def rightSlots : Fin 4 → Fin 8 := ![1,2,5,7]
def compareSlots : Fin 4 → Fin 8 := ![5,4,6,7]
noncomputable def leftProgram := RecoveryFocus.machine leftSlots BoundaryAdvance.machine
noncomputable def rightProgram := RecoveryFocus.machine rightSlots BoundaryAdvance.machine
noncomputable def compareProgram := RecoveryFocus.machine compareSlots compareMachine
def sizes : Fin 3 → ℕ := fun _ => 7
noncomputable def programs (j : Fin 3) : Machine 8 (sizes j) :=
  if j=0 then leftProgram else if j=1 then rightProgram else compareProgram
def next (j : Fin 3) (_ : Fin (sizes j)) (_ : Fin 8 → Bool) : Option (Fin 3) :=
  if j=0 then some 1 else if j=1 then some 2 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def input (w p n r s : ℕ) : Fin 8 → List Bool :=
  fun i => match i.val with
    | 0 => frame (binary w p)
    | 1 => frame (binary w n)
    | 2 => frame (binary w r)
    | 3 => frame (binary w s)
    | _ => []
def leftOutput (w p n r s : ℕ) : Fin 8 → List Bool :=
  fun i => match i.val with
    | 0 => frame (binary w p)
    | 1 => frame (binary w n)
    | 2 => frame (binary w r)
    | 3 => frame (binary w s)
    | 4 => frame (binary w (p+s))
    | 7 => List.replicate (2*w+1) false
    | _ => []
def rightOutput (w p n r s : ℕ) : Fin 8 → List Bool :=
  fun i => match i.val with
    | 0 => frame (binary w p)
    | 1 => frame (binary w n)
    | 2 => frame (binary w r)
    | 3 => frame (binary w s)
    | 4 => frame (binary w (p+s))
    | 5 => frame (binary w (n+r))
    | 7 => List.replicate (2*w+1) false
    | _ => []
def output (w p n r s : ℕ) : Fin 8 → List Bool :=
  fun i => match i.val with
    | 0 => frame (binary w p)
    | 1 => frame (binary w n)
    | 2 => frame (binary w r)
    | 3 => frame (binary w s)
    | 4 => frame (binary w (p+s))
    | 5 => frame (binary w (n+r))
    | 6 => [decide (n+r≤p+s)]
    | _ => List.replicate (2*w+1) false

theorem left_ready (w p n r s : ℕ) (hfit : p+s<2^w) :
    ReadyRun leftProgram (4*w+4) (input w p n r s) (leftOutput w p n r s) := by
  have h := HierarchyBinary.add_ready w p s 0 [] hfit (by simp)
  simp only [max_eq_right (Nat.zero_le _)] at h
  have hrun := h.focus leftSlots (by decide) (input w p n r s) (by intro j; fin_cases j <;> rfl)
  have he : install leftSlots (input w p n r s)
      ![frame (binary w p),frame (binary w s),frame (binary w (p+s)),List.replicate (2*w+1) false]=
      leftOutput w p n r s := by
    funext i; fin_cases i
    all_goals first
      | exact install_slot leftSlots (by decide) _ _ 0
      | exact install_slot leftSlots (by decide) _ _ 1
      | exact install_slot leftSlots (by decide) _ _ 2
      | exact install_slot leftSlots (by decide) _ _ 3
      | exact install_other leftSlots _ _ _ (by decide)
  exact he ▸ hrun

theorem right_ready (w p n r s : ℕ) (hfit : n+r<2^w) :
    ReadyRun rightProgram (4*w+4) (leftOutput w p n r s) (rightOutput w p n r s) := by
  have h := HierarchyBinary.add_ready w n r (2*w+1) [] hfit (by simp)
  simp only [max_self] at h
  have hrun := h.focus rightSlots (by decide) (leftOutput w p n r s) (by intro j; fin_cases j <;> rfl)
  have he : install rightSlots (leftOutput w p n r s)
      ![frame (binary w n),frame (binary w r),frame (binary w (n+r)),List.replicate (2*w+1) false]=
      rightOutput w p n r s := by
    funext i; fin_cases i
    all_goals first
      | exact install_slot rightSlots (by decide) _ _ 0
      | exact install_slot rightSlots (by decide) _ _ 1
      | exact install_slot rightSlots (by decide) _ _ 2
      | exact install_slot rightSlots (by decide) _ _ 3
      | exact install_other rightSlots _ _ _ (by decide)
  exact he ▸ hrun

theorem finish_ready (w p n r s : ℕ) (hl : p+s<2^w) (hr : n+r<2^w) :
    ReadyRun compareProgram (4*w+4) (rightOutput w p n r s) (output w p n r s) := by
  have h := compare_ready w (n+r) (p+s) hr hl
  have hrun := h.focus compareSlots (by decide) (rightOutput w p n r s) (by intro j; fin_cases j <;> rfl)
  have he : install compareSlots (rightOutput w p n r s)
      ![frame (binary w (n+r)),frame (binary w (p+s)),[decide (n+r≤p+s)],List.replicate (2*w+1) false]=
      output w p n r s := by
    funext i; fin_cases i
    all_goals first
      | exact install_slot compareSlots (by decide) _ _ 0
      | exact install_slot compareSlots (by decide) _ _ 1
      | exact install_slot compareSlots (by decide) _ _ 2
      | exact install_slot compareSlots (by decide) _ _ 3
      | exact install_other compareSlots _ _ _ (by decide)
  exact he ▸ hrun

theorem signed_decision_run (w p n r s : ℕ) (hl : p+s<2^w) (hr : n+r<2^w) :
    ReadyRun machine (12*w+15) (input w p n r s) (output w p n r s) := by
  have hleft : ReadyRun (programs 0) (4*w+4) (input w p n r s) (leftOutput w p n r s) :=
    left_ready w p n r s hl
  have hright : ReadyRun (programs 1) (4*w+4) (leftOutput w p n r s) (rightOutput w p n r s) :=
    right_ready w p n r s hr
  have hfinish : ReadyRun (programs 2) (4*w+4) (rightOutput w p n r s) (output w p n r s) :=
    finish_ready w p n r s hl hr
  have h0 := hleft.call sizes programs 0 next 0 1 (by intro q; rfl)
  have h1 := hright.call sizes programs 0 next 1 2 (by intro q; rfl)
  have h2 := hfinish.stop sizes programs 0 next 2 (by intro q; rfl)
  have h := h0.trans (h1.trans h2)
  have he : 4*w+4+1+(4*w+4+1+(4*w+4+1))=12*w+15 := by omega
  rw [he] at h
  obtain ⟨receipt,hrun,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  refine ⟨receipt,hrun,?_,?_,hs⟩
  · rw [hf]; rfl
  · intro i; rw [hf]; rfl

theorem signed_decision_exact (w p n r s : ℕ) :
    readTapeBit (output w p n r s 6) 0=true ↔ (r : ℤ)-s≤(p : ℤ)-n := by
  change decide (n+r≤p+s)=true ↔ _
  rw [decide_eq_true_eq]
  omega

end NearCubicWires.RepairOrdinary.CompetitorSignedDecision
