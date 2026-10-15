import Proof.PCP.PCPTraversalRightPop

/-! The whole left-child return physically saves its canonical result and
restores the pending right count before starting the second recursive call. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def leftReturned (continuation : List Bool) (z : ℕ) (ambient : Fin 128 → List Bool) :=
  install ![81] ambient (fun _ => continuation++true::true::List.replicate z false)
noncomputable def resumeRightOutput (bits leftStack rightStack continuation : List Bool)
    (n cap leftCap rightZeros continuationZeros log : ℕ) (ambient : Fin 128 → List Bool) :=
  rightPopped n cap rightZeros (max log (cap+1)) rightStack
    (leftSaved bits leftStack cap leftCap log (leftReturned continuation continuationZeros ambient))
noncomputable def resumeRightHeads (bits leftStack rightStack : List Bool) (heads : Fin 128 → ℕ) :=
  installedHeads rightPopSlots (installedHeads saveLeftSlots heads (saveLeftHeads bits leftStack))
    (PCPUnaryStackPop.heads rightStack)

theorem resume_right_path (bits leftStack rightStack continuation : List Bool)
    (n cap leftCap rightZeros continuationZeros log : ℕ)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hc : 2*n+2≤cap) (hleftCap : leftCap≤cap)
    (hleftFit : leftStack.length+2*bits.length+1≤cap)
    (hb : WorkBound cap ambient) (hh : WorkingHeads heads)
    (hdriver : ambient 28=List.replicate cap true) (hlog : ambient 127=List.replicate log false)
    (hresult : ambient 77=ZeroPadding.pad cap (frame bits))
    (hleft : ambient 82=ZeroPadding.pad leftCap leftStack)
    (hright : ambient 80=rightStack++(frame (List.replicate n true)).reverse++List.replicate rightZeros false)
    (hcont : ambient 81=continuation++false::true::List.replicate continuationZeros false)
    (hhleft : heads 82=leftStack.length) (hhright : heads 80=rightStack.length+2*n+1)
    (hhcont : heads 81=continuation.length+2) (hhd : heads 28=0) :
    Path 9 0 (10*cap+29) heads ambient (resumeRightHeads bits leftStack rightStack heads)
      (resumeRightOutput bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log ambient) ∧
    WorkBound cap (resumeRightOutput bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log ambient) ∧
    WorkingHeads (resumeRightHeads bits leftStack rightStack heads) := by
  let returned := leftReturned continuation continuationZeros ambient
  let saved := leftSaved bits leftStack cap leftCap log returned
  let savedHeads := installedHeads saveLeftSlots heads (saveLeftHeads bits leftStack)
  have returned_bound : WorkBound cap returned := by
    apply hb.install ![81]
    intro i _ _
    have h := hb 81 (by decide) (by decide)
    rw [hcont] at h
    simpa only [List.length_append,List.length_cons,List.length_replicate] using h
  have returned_driver : returned 28=List.replicate cap true :=
    (install_other ![81] ambient (fun _ => continuation++true::true::List.replicate continuationZeros false)
      28 (by decide)).trans hdriver
  have returned_log : returned 127=List.replicate log false :=
    (install_other ![81] ambient (fun _ => continuation++true::true::List.replicate continuationZeros false)
      127 (by decide)).trans hlog
  have returned_result : returned 77=ZeroPadding.pad cap (frame bits) :=
    (install_other ![81] ambient (fun _ => continuation++true::true::List.replicate continuationZeros false)
      77 (by decide)).trans hresult
  have returned_left : returned 82=ZeroPadding.pad leftCap leftStack :=
    (install_other ![81] ambient (fun _ => continuation++true::true::List.replicate continuationZeros false)
      82 (by decide)).trans hleft
  have returned_right : returned 80=rightStack++(frame (List.replicate n true)).reverse++List.replicate rightZeros false :=
    (install_other ![81] ambient (fun _ => continuation++true::true::List.replicate continuationZeros false)
      80 (by decide)).trans hright
  have saved_bound : WorkBound cap saved := returned_bound.leftSaved bits leftStack leftCap hleftCap hleftFit
  have saved_heads : WorkingHeads savedHeads := hh.leftSaved bits leftStack
  have saved_driver : saved 28=List.replicate cap true :=
    install_cleared_driver saveLeftSlots rightPushClearSlots rightPushClearSlots_injective
      (by decide) (by decide) cap log returned (saveLeftLocal bits leftStack cap leftCap) (by decide)
  have saved_log : saved 127=List.replicate (max log (cap+1)) false :=
    install_cleared_log saveLeftSlots rightPushClearSlots rightPushClearSlots_injective
      (by decide) (by decide) cap log returned (saveLeftLocal bits leftStack cap leftCap) (by decide)
  have saved_right : saved 80=rightStack++(frame (List.replicate n true)).reverse++List.replicate rightZeros false :=
    (install_cleared_other saveLeftSlots rightPushClearSlots cap log returned
      (saveLeftLocal bits leftStack cap leftCap) 80 (by decide) (by decide) (by decide) (by decide)).trans returned_right
  have saved_right_head : savedHeads 80=rightStack.length+2*n+1 :=
    (installedHeads_other saveLeftSlots heads (saveLeftHeads bits leftStack) 80 (by decide)).trans hhright
  have saved_driver_head : savedHeads 28=0 :=
    (installedHeads_other saveLeftSlots heads (saveLeftHeads bits leftStack) 28 (by decide)).trans hhd
  have right_fit : rightStack.length+2*n+1+rightZeros≤cap := by
    have h := hb 80 (by decide) (by decide)
    rw [hright,List.length_append,List.length_append,List.length_reverse,frame_length,
      List.length_replicate,List.length_replicate] at h
    omega
  have hret := return_left_path continuation continuationZeros heads ambient hcont hhcont
  have hsave := save_left_path bits leftStack cap leftCap log heads returned (by omega)
    returned_bound hh returned_driver returned_log returned_result returned_left hhleft hhd
  have hpop := right_pop_path n cap rightZeros (max log (cap+1)) rightStack savedHeads saved hc
    saved_bound saved_heads saved_driver saved_log saved_right saved_right_head saved_driver_head
  have hpath := (hret.trans hsave).trans hpop
  exact ⟨hpath.mono (by omega),saved_bound.rightPopped n rightZeros rightStack right_fit,
    saved_heads.rightPopped rightStack⟩

theorem resume_right_count (bits leftStack rightStack continuation : List Bool)
    (n cap leftCap rightZeros continuationZeros log : ℕ) (ambient : Fin 128 → List Bool) :
    resumeRightOutput bits leftStack rightStack continuation n cap leftCap rightZeros continuationZeros log ambient 79=
      ZeroPadding.pad cap (List.replicate n true) :=
  install_slot rightPopSlots rightPopSlots_injective
    (cleared rightPopClearSlots cap (max log (cap+1))
      (leftSaved bits leftStack cap leftCap log (leftReturned continuation continuationZeros ambient)))
    (rightPopLocal n cap rightZeros rightStack) 3

end NearCubicWires.RepairOrdinary.PCPTraversal
