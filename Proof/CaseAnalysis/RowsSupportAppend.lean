import Proof.CaseAnalysis.RowsSupportSideStream
import Proof.CaseAnalysis.RowsCircuitAppendFocus

/-! Append a declared bitmap on the unchanged bottom-retention guard. The
new output is outside the original bank; every original tape is restored. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
open LocalBitMultitape RadixSemantics ExtDecompositionBatch
open CloseoutRowsGatePairHeads CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extend {α : Type} (old : Fin 1059 → α) (last : α) : Fin 1060 → α :=
  Fin.addCases (m:=1059) (n:=1) old (fun _=>last)
theorem extend_update {α : Type} (old : Fin 1059 → α) (x y : α) :
    Function.update (extend old x) 1059 y=extend old y := by
  funext i
  refine Fin.addCases (m:=1059) (n:=1) ?_ ?_ i
  · intro j
    rw [Function.update_of_ne (by
      intro h
      have hv:=congrArg Fin.val h
      change j.val=1059 at hv
      omega)]
    simp only [extend,Fin.addCases_left]
  · intro j
    have hj:j=0:=Fin.eq_zero j
    subst j
    have he:(0 : Fin 1).natAdd 1059=(1059 : Fin 1060):=Fin.ext rfl
    have last:extend old y ((0 : Fin 1).natAdd 1059)=y:=by
      simp only [extend,Fin.addCases_right]
    rw [he,Function.update_self]
    rw [he] at last
    exact last.symm

noncomputable def append:=RecoveryFocus.machine CloseoutRowsSupportSideStream.slots
  CompetitorFrameAppend.machine
def halt : Machine 1060 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def selected (threshold : Bool) (bits : Fin 1060 → Bool) : Bool:=
  bits 1037 && (if threshold then bits 1053 else true)
noncomputable def choice (threshold : Bool):=
  CloseoutRowsGateColdPair.machine halt append (selected threshold)

theorem append_run {q : ℕ} (support : Finset (Fin q)) (cap : ℕ) (out : List Bool)
    (H : Fin 1059 → ℕ) (A : Fin 1059 → List Bool)
    (hheads : H 994=0 ∧ H 1057=0)
    (hbitmap : A 994=ZeroPadding.pad cap (frame (gateMembers support)))
    (hlog : A 1057=List.replicate cap false) (hcap : 2*q+1≤cap) :
    Step append (4*q+3) (extend H out.length) (extend A out)
      (extend H (out++frame (gateMembers support)).length)
      (extend A (out++frame (gateMembers support))) := by
  have hlen:(gateMembers support).length=q:=List.length_ofFn
  obtain ⟨r,hr,rh,rt,_⟩:=CloseoutRowsCircuitAppend.frame_focus
    CloseoutRowsSupportSideStream.slots CloseoutRowsSupportSideStream.slots_injective
    cap (gateMembers support) out (by simpa only [hlen] using hcap)
    (extend H out.length) (extend A out)
    (by intro i;fin_cases i <;> first | exact hheads.1 | exact hheads.2 | rfl)
    (by intro i;fin_cases i <;> first | exact hbitmap | exact hlog | rfl)
  rw [hlen] at hr
  exact Step.of_run hr (rh.trans (extend_update H _ _)) (rt.trans (extend_update A _ _))

theorem halt_run (H : Fin 1060 → ℕ) (A : Fin 1060 → List Bool) :
    ReadyAt halt 0 H A A := by
  exact ⟨⟨⟨0,H,A⟩,0,_⟩,rfl,rfl,rfl,by rfl⟩

theorem selected_run {q : ℕ} (threshold : Bool) (support : Finset (Fin q))
    (cap : ℕ) (out : List Bool) (H : Fin 1059 → ℕ) (A : Fin 1059 → List Bool)
    (hheads : H 994=0 ∧ H 1057=0)
    (hbitmap : A 994=ZeroPadding.pad cap (frame (gateMembers support)))
    (hlog : A 1057=List.replicate cap false) (hcap : 2*q+1≤cap)
    (hkeep : selected threshold (fun i=>readTapeBit (extend A out i) (extend H out.length i))=true) :
    Step (choice threshold) (4*q+5) (extend H out.length) (extend A out)
      (extend H (out++frame (gateMembers support)).length)
      (extend A (out++frame (gateMembers support))) := by
  obtain ⟨a,ha,hh,ht,_⟩:=append_run support cap out H A hheads hbitmap hlog hcap
  obtain ⟨r,hr,rt,rh,_⟩:=CloseoutRowsGateSourceCalls.joined halt append (selected threshold)
    0 (4*q+3) (extend H out.length) (extend A out) (extend A out)
    (halt_run _ _) a ha hkeep
  have hc:0+1+(4*q+3)+1=4*q+5:=by omega
  rw [hc] at hr
  exact Step.of_run hr (rh.trans hh) (rt.trans ht)

theorem rejected_run (threshold : Bool) (H : Fin 1060 → ℕ) (A : Fin 1060 → List Bool)
    (hkeep : selected threshold (fun i=>readTapeBit (A i) (H i))=false) :
    Step (choice threshold) 1 H A H A := by
  obtain ⟨r,hr,rt,rh,_⟩:=CloseoutRowsGatePairHeads.rejected halt append (selected threshold)
    0 H A A (halt_run H A) hkeep
  exact Step.of_run hr rh rt

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
