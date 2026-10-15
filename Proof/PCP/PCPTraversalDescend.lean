import Proof.PCP.PCPTraversalLeftEntry

/-! The entire internal-node descent: physical count test, midpoint scan,
pending-right/continuation pushes and left-count installation, all in the
same39-node controller. The next call starts the strictly smaller left child. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem install_cleared_other {t u : ℕ} (slot : Fin t → Fin 128) (clearSlot : Fin u → Fin 128)
    (cap log : ℕ) (ambient : Fin 128 → List Bool) (out : Fin t → List Bool) (i : Fin 128)
    (hs : ∀ j,slot j≠i) (hc : ∀ j,clearSlot j≠i) (hd : 28≠i) (hl : 127≠i) :
    install slot (cleared clearSlot cap log ambient) out i=ambient i :=
  (install_other slot _ out i hs).trans (cleared_other clearSlot cap log ambient i hc hd hl)
theorem install_cleared_driver {t u : ℕ} (slot : Fin t → Fin 128) (clearSlot : Fin u → Fin 128)
    (hi : Function.Injective clearSlot) (hd : ∀ j,clearSlot j≠28) (hl : ∀ j,clearSlot j≠127)
    (cap log : ℕ) (ambient : Fin 128 → List Bool) (out : Fin t → List Bool)
    (hs : ∀ j,slot j≠28) :
    install slot (cleared clearSlot cap log ambient) out 28=List.replicate cap true :=
  (install_other slot _ out 28 hs).trans (cleared_driver clearSlot hi hd hl cap log ambient)
theorem install_cleared_log {t u : ℕ} (slot : Fin t → Fin 128) (clearSlot : Fin u → Fin 128)
    (hi : Function.Injective clearSlot) (hd : ∀ j,clearSlot j≠28) (hl : ∀ j,clearSlot j≠127)
    (cap log : ℕ) (ambient : Fin 128 → List Bool) (out : Fin t → List Bool)
    (hs : ∀ j,slot j≠127) :
    install slot (cleared clearSlot cap log ambient) out 127=List.replicate (max log (cap+1)) false :=
  (install_other slot _ out 127 hs).trans (cleared_log clearSlot hi hd hl cap log ambient)

noncomputable def descendPushed (n cap countCap rightCap log : ℕ) (rightStack : List Bool)
    (ambient : Fin 128 → List Bool) :=
  rightPushed (n/2) cap rightCap (max log (cap+1)) rightStack
    (splitOutput n cap countCap log ambient)
noncomputable def descendContinued (n cap countCap rightCap continuationCap log : ℕ)
    (rightStack continuation : List Bool) (ambient : Fin 128 → List Bool) :=
  continuationPushed continuationCap continuation (descendPushed n cap countCap rightCap log rightStack ambient)
noncomputable def descendOutput (n cap countCap rightCap continuationCap log : ℕ)
    (rightStack continuation : List Bool) (ambient : Fin 128 → List Bool) :=
  leftCopied ((n+1)/2) cap (max log (cap+1))
    (descendContinued n cap countCap rightCap continuationCap log rightStack continuation ambient)
noncomputable def descendHeads (n : ℕ) (rightStack continuation : List Bool) (heads : Fin 128 → ℕ) :=
  installedHeads ![81] (installedHeads rightPushSlots heads (rightPushHeads (n/2) rightStack))
    (fun _ => continuation.length+2)

theorem descend_path (n cap countCap rightCap continuationCap log : ℕ)
    (rightStack continuation : List Bool) (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hn : 2≤n) (hc : 3*n+3≤cap) (hcountCap : countCap≤cap)
    (hrightCap : rightCap≤cap) (hcontCap : continuationCap≤cap)
    (hrightFit : rightStack.length+2*(n/2)+1≤cap) (hcontFit : continuation.length+2≤cap)
    (hb : WorkBound cap ambient) (hh : WorkingHeads heads)
    (hdriver : ambient 28=List.replicate cap true) (hlog : ambient 127=List.replicate log false)
    (hcount : ambient 79=ZeroPadding.pad countCap (List.replicate n true))
    (hright : ambient 80=ZeroPadding.pad rightCap rightStack)
    (hcont : ambient 81=ZeroPadding.pad continuationCap continuation)
    (hhright : heads 80=rightStack.length) (hhcont : heads 81=continuation.length) (hhd : heads 28=0) :
    Path 0 0 (11*cap+38) heads ambient (descendHeads n rightStack continuation heads)
      (descendOutput n cap countCap rightCap continuationCap log rightStack continuation ambient) ∧
    WorkBound cap (descendOutput n cap countCap rightCap continuationCap log rightStack continuation ambient) ∧
    WorkingHeads (descendHeads n rightStack continuation heads) := by
  let splitT := splitOutput n cap countCap log ambient
  let pushT := descendPushed n cap countCap rightCap log rightStack ambient
  let contT := descendContinued n cap countCap rightCap continuationCap log rightStack continuation ambient
  let pushH := installedHeads rightPushSlots heads (rightPushHeads (n/2) rightStack)
  let contH := descendHeads n rightStack continuation heads
  have split_bound : WorkBound cap splitT := hb.splitOutput n countCap (by omega) hcountCap
  have split_driver : splitT 28=List.replicate cap true := install_cleared_driver splitSlots splitClearSlots
    splitClearSlots_injective (by decide) (by decide) cap log ambient _ (by decide)
  have split_log : splitT 127=List.replicate (max log (cap+1)) false := install_cleared_log splitSlots splitClearSlots
    splitClearSlots_injective (by decide) (by decide) cap log ambient _ (by decide)
  have split_right : splitT 80=ZeroPadding.pad rightCap rightStack :=
    (install_cleared_other splitSlots splitClearSlots cap log ambient _ 80
      (by decide) (by decide) (by decide) (by decide)).trans hright
  have split_cont : splitT 81=ZeroPadding.pad continuationCap continuation :=
    (install_cleared_other splitSlots splitClearSlots cap log ambient _ 81
      (by decide) (by decide) (by decide) (by decide)).trans hcont
  have push_heads : WorkingHeads pushH := hh.rightPush (n/2) rightStack
  have push_bound : WorkBound cap pushT := split_bound.rightPushed (n/2) rightCap rightStack hrightCap hrightFit
  have push_driver : pushT 28=List.replicate cap true := install_cleared_driver rightPushSlots rightPushClearSlots
    rightPushClearSlots_injective (by decide) (by decide) cap (max log (cap+1)) splitT
      (rightPushLocal (n/2) cap rightCap rightStack) (by decide)
  have push_log : pushT 127=List.replicate (max log (cap+1)) false := by
    have h := install_cleared_log rightPushSlots rightPushClearSlots rightPushClearSlots_injective
      (by decide) (by decide) cap (max log (cap+1)) splitT (rightPushLocal (n/2) cap rightCap rightStack) (by decide)
    rw [max_eq_left (le_max_right log (cap+1))] at h
    exact h
  have push_cont : pushT 81=ZeroPadding.pad continuationCap continuation :=
    (install_cleared_other rightPushSlots rightPushClearSlots cap (max log (cap+1)) splitT
      (rightPushLocal (n/2) cap rightCap rightStack) 81
      (by decide) (by decide) (by decide) (by decide)).trans split_cont
  have push_left : pushT 85=ZeroPadding.pad cap (List.replicate ((n+1)/2) true) :=
    (install_cleared_other rightPushSlots rightPushClearSlots cap (max log (cap+1)) splitT
      (rightPushLocal (n/2) cap rightCap rightStack) 85
      (by decide) (by decide) (by decide) (by decide)).trans (split_output_halves n cap countCap log ambient).1
  have push_cont_head : pushH 81=continuation.length :=
    (installedHeads_other rightPushSlots heads _ 81 (by decide)).trans hhcont
  have push_driver_head : pushH 28=0 := (installedHeads_other rightPushSlots heads _ 28 (by decide)).trans hhd
  have cont_heads : WorkingHeads contH := push_heads.continuationPushed continuation
  have cont_bound : WorkBound cap contT := push_bound.continuationPushed continuationCap continuation hcontCap hcontFit
  have cont_driver : contT 28=List.replicate cap true :=
    (install_other ![81] pushT (fun _ => ZeroPadding.pad continuationCap (continuation++[false,true]))
      28 (by decide)).trans push_driver
  have cont_log : contT 127=List.replicate (max log (cap+1)) false :=
    (install_other ![81] pushT (fun _ => ZeroPadding.pad continuationCap (continuation++[false,true]))
      127 (by decide)).trans push_log
  have cont_left : contT 85=ZeroPadding.pad cap (List.replicate ((n+1)/2) true) :=
    (install_other ![81] pushT (fun _ => ZeroPadding.pad continuationCap (continuation++[false,true]))
      85 (by decide)).trans push_left
  have cont_driver_head : contH 28=0 :=
    (installedHeads_other ![81] pushH (fun _ => continuation.length+2) 28 (by decide)).trans push_driver_head
  have htest := test_path n countCap heads ambient hcount (hh 79 (by decide) (by decide) (by decide) (by decide))
  have hsplit := split_path n cap countCap log heads ambient (by omega) hb hh hdriver hlog hcount hhd
  have hpush := right_push_path (n/2) cap rightCap (max log (cap+1)) rightStack heads splitT (by omega)
    split_bound hh split_driver split_log (split_output_halves n cap countCap log ambient).2 split_right hhright hhd
  have hcontPath := continuation_push_path continuationCap continuation pushH pushT push_cont push_cont_head
  have hcopy := left_copy_path ((n+1)/2) cap (max log (cap+1)) contH contT (by omega)
    cont_bound cont_heads cont_driver cont_log cont_left cont_driver_head
  have ht : testNext n=14 := by simp [testNext,show n≠0 by omega,show n≠1 by omega]
  rw [ht] at htest
  have hpath := (((htest.trans hsplit).trans hpush).trans hcontPath).trans hcopy
  exact ⟨hpath.mono (by dsimp [PCPControlOps.testCost]; split <;> omega),
    cont_bound.leftCopied ((n+1)/2) (by omega),cont_heads⟩

theorem descend_count (n cap countCap rightCap continuationCap log : ℕ)
    (rightStack continuation : List Bool) (ambient : Fin 128 → List Bool) :
    descendOutput n cap countCap rightCap continuationCap log rightStack continuation ambient 79=
      ZeroPadding.pad cap (List.replicate ((n+1)/2) true) := leftCopied_count _ _ _ _

end NearCubicWires.RepairOrdinary.PCPTraversal
