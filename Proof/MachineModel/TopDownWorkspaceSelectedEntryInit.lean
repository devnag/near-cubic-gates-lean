import Proof.MachineModel.TopDownWorkspaceSelectedEntryCount

/-! Dock the existing grouped initializer after the actual direct prologue.
It aliases the retained original cache and the produced width driver, and uses
96 further fresh tapes. The envelope-counter head is outside this call. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntryInit
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RecoveryRootRound
open WorkspaceSelectedProgram (finalBank)
open WorkspaceSelectedEntry (size slots output outputHeads)
open WorkspaceSelectedEntryFacts
noncomputable section

/-- First 19 are the real cache, port19 is the produced width driver;
ports20..115 own a disjoint fresh bank immediately after the prologue. -/
def ports {t extra : Nat} (P : Nat) (hP : 219≤P) (hspace : P+96≤extra)
    (C : Fin 19→Fin t) (i : Fin 116) : Fin (t+1+1+extra) :=
  if h:i.val<19 then (((C ⟨i.val,h⟩).castAdd 1).castAdd 1).castAdd extra
  else ⟨if i.val=19 then t+2+218 else t+2+(P+i.val-20),by
    have hi:=i.isLt
    split_ifs <;>omega⟩

theorem ports_injective {t extra : Nat} (P : Nat) (hP : 219≤P) (hspace : P+96≤extra)
    (C : Fin 19→Fin t) (hc : Function.Injective C) : Function.Injective (ports P hP hspace C) := by
  intro i j he
  have hi:=i.isLt
  have hj:=j.isLt
  by_cases hci:i.val<19
  · by_cases hcj:j.val<19
    · simp only [ports,dif_pos hci,dif_pos hcj] at he
      have old : C ⟨i.val,hci⟩=C ⟨j.val,hcj⟩ :=
        Fin.ext (congrArg (@Fin.val (t+1+1+extra)) he)
      exact Fin.ext (congrArg (@Fin.val 19) (hc old))
    · have hv:=congrArg Fin.val he
      have hlo:=(C ⟨i.val,hci⟩).isLt
      simp only [ports,dif_pos hci,dif_neg hcj,Fin.val_castAdd,Fin.val_mk] at hv
      split_ifs at hv <;>omega
  · by_cases hcj:j.val<19
    · have hv:=congrArg Fin.val he
      have hlo:=(C ⟨j.val,hcj⟩).isLt
      simp only [ports,dif_neg hci,dif_pos hcj,Fin.val_castAdd,Fin.val_mk] at hv
      split_ifs at hv <;>omega
    · have hv:=congrArg Fin.val he
      simp only [ports,dif_neg hci,dif_neg hcj,Fin.val_mk] at hv
      split_ifs at hv <;>apply Fin.ext <;>omega

theorem old_heads_zero (sources : EightSources) (k r D t extra : Nat)
    (ht : 2≤t) (hspace : size sources k r D≤extra) (i : Fin t) :
    dockH (slots ht hspace) (fun _=>0) (outputHeads sources k r D)
      (((i.castAdd 1).castAdd 1).castAdd extra)=0 := by
  by_cases h0:i.val=0
  · let j : Fin (size sources k r D) := ⟨0,by dsimp [size];omega⟩
    have he:slots ht hspace j=(((i.castAdd 1).castAdd 1).castAdd extra):=by
      apply Fin.ext;simp [slots,j,h0]
    rw [←he,dockH_slot _ (WorkspaceSelectedEntry.slots_injective ht hspace)]
    rfl
  by_cases h1:i.val=1
  · let j : Fin (size sources k r D) := ⟨1,by dsimp [size];omega⟩
    have he:slots ht hspace j=(((i.castAdd 1).castAdd 1).castAdd extra):=by
      apply Fin.ext;simp [slots,j,h1]
    rw [←he,dockH_slot _ (WorkspaceSelectedEntry.slots_injective ht hspace)]
    rfl
  · exact dockH_other _ _ _ _ (by
      intro j he
      have hv:=congrArg Fin.val he
      have hi:=i.isLt
      dsimp only [slots,Fin.val_castAdd] at hv
      split_ifs at hv <;>omega)

theorem input_ready (sources : EightSources) (k r D n t extra : Nat)
    (ht : 2≤t) (hspace : size sources k r D+96≤extra)
    (A : Fin t→List Bool) (L : Nat) (x bits : List Bool) (w : Nat→List Bool)
    (C : Fin 19→Fin t) (data : Fin 19→List Bool)
    (hx : A ⟨0,by omega⟩=RepairOrdinary.frame x)
    (hb : A ⟨1,by omega⟩=RepairOrdinary.frame bits)
    (hcache : ∀j,A (C j)=data j) :
    let hfit : size sources k r D≤extra := by omega
    let hP : 219 ≤ size sources k r D := by dsimp [size];omega
    let pre := slots ht hfit
    let post := install pre (finalBank A L extra) (output sources k r D n x bits w)
    let H := dockH pre (fun _=>0) (outputHeads sources k r D)
    ∀i,H (ports (size sources k r D) hP hspace C i)=0 ∧
      post (ports (size sources k r D) hP hspace C i)=
        WorkspaceSelectedEntryCount.input data (C10PartsSchedule.entryWidthSchedule sources k r n) i := by
  intro hfit hP pre post H i
  by_cases hc:i.val<19
  · have he : ports (size sources k r D) hP hspace C i=
        (((C ⟨i.val,hc⟩).castAdd 1).castAdd 1).castAdd extra := dif_pos hc
    rw [he]
    refine ⟨old_heads_zero sources k r D t extra ht hfit _,?_⟩
    have keep:=old_bank_retained sources k r D n t extra ht hfit A L x bits w hx hb (C ⟨i.val,hc⟩)
    exact keep.trans ((hcache _).trans (by simp only [WorkspaceSelectedEntryCount.input,dif_pos hc]))
  by_cases hw:i.val=19
  · let j0 : Fin (218+(60+(WorkspaceSelectedEntry.engineTapes sources k r D+23))) := ⟨218,by omega⟩
    let j : Fin (size sources k r D) := j0.castAdd 1
    have he : ports (size sources k r D) hP hspace C i=pre j := by
      apply Fin.ext
      simp [ports,hw,pre,slots,j,j0]
    rw [he]
    constructor
    · change dockH pre _ _ (pre j)=0
      rw [dockH_slot _ (WorkspaceSelectedEntry.slots_injective ht hfit)]
      simp only [outputHeads,j,Fin.addCases_left]
    · change install pre _ _ (pre j)=_
      rw [install_slot _ (WorkspaceSelectedEntry.slots_injective ht hfit)]
      simp only [output,j,Fin.addCases_left]
      simp [C10SupplierCall.bank,C10SupplierCall.bankAt,WorkspaceSelectedEntryCount.input,hw,j0]
  · let j : Fin extra := ⟨size sources k r D+i.val-20,by have:=i.isLt;omega⟩
    have he : ports (size sources k r D) hP hspace C i=j.natAdd (t+1+1) := by
      apply Fin.ext
      simp only [ports,dif_neg hc,if_neg hw,Fin.val_natAdd,j]
    have hj:size sources k r D≤j.val:=by dsimp[j];omega
    rw [he]
    constructor
    · apply dockH_other
      intro z he
      have hv:=congrArg Fin.val he
      have hz:=z.isLt
      dsimp only [pre,slots,Fin.val_natAdd] at hv
      split_ifs at hv <;>omega
    · have empty:=fresh_retained sources k r D n t extra ht hfit A L x bits w j hj
      exact empty.trans (by simp only [WorkspaceSelectedEntryCount.input,dif_neg hc,if_neg hw])

theorem run_init (sources : EightSources) (k r D n t extra : Nat)
    (ht : 2≤t) (hspace : size sources k r D+96≤extra)
    (A : Fin t→List Bool) (L : Nat) (x bits : List Bool) (w : Nat→List Bool)
    (C : Fin 19→Fin t) (hc : Function.Injective C)
    (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity)
    (hx : A ⟨0,by omega⟩=RepairOrdinary.frame x)
    (hb : A ⟨1,by omega⟩=RepairOrdinary.frame bits)
    (hcache : ∀j,A (C j)=WorkspaceSelectedEntryCount.cacheData a rq j) :
    let hfit : size sources k r D≤extra := by omega
    let hP : 219 ≤ size sources k r D := by dsimp [size];omega
    let pre := slots ht hfit
    let post := install pre (finalBank A L extra) (output sources k r D n x bits w)
    let H := dockH pre (fun _=>0) (outputHeads sources k r D)
    let port:=ports (size sources k r D) hP hspace C
    ∃ out,Step (RecoveryFocus.machine port WorkspaceSelectedEntryCount.machine)
      (WorkspaceSelectedEntryCount.budget a rq (C10PartsSchedule.entryWidthSchedule sources k r n))
      H post H (install port post out) ∧
      (∀j,install port post out (port (WorkspaceSelectedEntryCount.cache j))=WorkspaceSelectedEntryCount.cacheData a rq j) ∧
      install port post out (port (WorkspaceSelectedEntryCount.count 70))=UnaryTemplate.tape (2^(a.output rq).clauseBits) ∧
      install port post out (port (WorkspaceSelectedEntryCount.count 72))=List.replicate (2^(a.output rq).clauseBits) true ∧
      install port post out (port (WorkspaceSelectedEntryCount.append 20))=UnaryTemplate.tape (20*C10PartsSchedule.entryWidthSchedule sources k r n+22) ∧
      (∀v,(∀i,port i≠v) → install port post out v=post v) := by
  intro hfit hP pre post H port
  have ready:=input_ready sources k r D n t extra ht hspace A L x bits w C
    (WorkspaceSelectedEntryCount.cacheData a rq) hx hb hcache
  have inj:=ports_injective (size sources k r D) hP hspace C hc
  obtain ⟨out,hr,kept,_sys,clause,raw,_width,recordWidth,_log1,_log2,_other⟩:=
    WorkspaceSelectedEntryCount.run a rq (C10PartsSchedule.entryWidthSchedule sources k r n)
  have hH:∀i,H (port i)=0:=fun i=>(ready i).1
  have call:=(hr.dock port inj H post hH (fun i=>(ready i).2)).congr (dockH_existing port H _ hH) rfl
  exact ⟨out,call,fun j=>(install_slot port inj post out _).trans (kept j),
    (install_slot port inj post out _).trans clause,(install_slot port inj post out _).trans raw,
    (install_slot port inj post out _).trans recordWidth,fun v hv=>install_other port post out v hv⟩

end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntryInit
