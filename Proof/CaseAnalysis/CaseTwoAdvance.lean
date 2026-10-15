import Proof.CaseAnalysis.CaseTwoFieldNative
import Proof.MachineModel.ClockUnarySum

/-! In-place advance of the paid raw description offset by the paid field
width. The two scans and their complete rewind are charged; both drivers
remain reusable with their explicit false allocation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Advance
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 2 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q bits=>if q.val=0 then
      some (if bits 1 then ⟨0,fun _=>none,![.stay,.right]⟩
        else ⟨1,fun _=>none,fun _=>.stay⟩)
    else if q.val=1 then
      some (if bits 0 then ⟨1,![none,some true],fun _=>.right⟩
        else ⟨2,fun _=>none,fun _=>.stay⟩)
    else none
def cfg (q : Fin 3) (width sourceHead targetHead count : ℕ) : Configuration 2 3:=
  ⟨q,![sourceHead,targetHead],![List.replicate width true,List.replicate count true]⟩

theorem seek_step (width count pos : ℕ) (hp : pos<count) :
    step raw (cfg 0 width 0 pos count)=some (cfg 0 width 0 (pos+1) count) := by
  simp [step,raw,cfg,Configuration.scanned,ClockUnaryProduct.read_unary,hp]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl
theorem seek_stop (width count : ℕ) :
    step raw (cfg 0 width 0 count count)=some (cfg 1 width 0 count count) := by
  simp [step,raw,cfg,Configuration.scanned,ClockUnaryProduct.read_unary]
  rfl
theorem copy_step (width pos count : ℕ) (hp : pos<width) :
    step raw (cfg 1 width pos count count)=some (cfg 1 width (pos+1) (count+1) (count+1)) := by
  simp [step,raw,cfg,Configuration.scanned,ClockUnaryProduct.read_unary,hp]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i
    · rfl
    · change writeTapeBit (List.replicate count true) count true=List.replicate (count+1) true
      simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using
        Streaming.write_append (List.replicate count true) true
theorem copy_stop (width count : ℕ) :
    step raw (cfg 1 width width count count)=some (cfg 2 width width count count) := by
  simp [step,raw,cfg,Configuration.scanned,ClockUnaryProduct.read_unary]
  rfl

theorem seek (width count pos remaining : ℕ) (hp : pos+remaining=count) :
    Timed raw (remaining+1) (cfg 0 width 0 pos count) (cfg 1 width 0 count count) := by
  induction remaining generalizing pos with
  | zero=>
    have he:pos=count:=by omega
    subst pos
    exact Timed.single (by rfl) (seek_stop width count)
  | succ remaining ih=>
    have h:=(Timed.single (by rfl) (seek_step width count pos (by omega))).trans (ih (pos+1) (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
theorem copy (width pos remaining count : ℕ) (hp : pos+remaining=width) :
    Timed raw (remaining+1) (cfg 1 width pos count count)
      (cfg 2 width width (count+remaining) (count+remaining)) := by
  induction remaining generalizing pos count with
  | zero=>
    have he:pos=width:=by omega
    subst pos
    simpa only [Nat.add_zero] using Timed.single (by rfl) (copy_stop width count)
  | succ remaining ih=>
    have h:=(Timed.single (by rfl) (copy_step width pos count (by omega))).trans (ih (pos+1) (count+1) (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem raw_run (width count : ℕ) : ∃ r,
    run raw (width+count+2) ![List.replicate width true,List.replicate count true]=some r ∧
      r.final=cfg 2 width width (count+width) (count+width) ∧ r.steps=width+count+2 := by
  have h:=(seek width count 0 count (by omega)).trans (copy width 0 width count (by omega))
  obtain ⟨r,rr,rf,rs⟩:=h.run (by rfl)
  have he:(count+1)+(width+1)=width+count+2:=by omega
  rw [he] at rr rs
  refine ⟨r,?_,rf,rs⟩
  change runFrom raw _ _=some r
  have hi:initialConfiguration raw ![List.replicate width true,List.replicate count true]=cfg 0 width 0 0 count:=by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  rw [hi]
  exact rr

def machine:=Rewind.machine raw
theorem ready (width count C : ℕ) (hC : width+count+2≤C) :
    ReadyRun machine (2*(width+count)+6)
      ![ZeroPadding.pad C (List.replicate width true),ZeroPadding.pad C (List.replicate count true),List.replicate C false]
      ![ZeroPadding.pad C (List.replicate width true),ZeroPadding.pad C (List.replicate (count+width) true),List.replicate C false] := by
  obtain ⟨base,hr,hf,hs⟩:=raw_run width count
  obtain ⟨a,ar,atp,alog,ah,ast,_⟩:=Rewind.Workspace.reset_workspace raw _ _ base hr C
  have hb:2*base.steps+2=2*(width+count)+6:=by rw [hs];omega
  rw [hb] at ar ast
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config machine (![C,C,0] : Fin 3→ℕ) _ _ a ar
  have hi : ZeroPadding.config (![C,C,0] : Fin 3→ℕ)
      (initialConfiguration machine (Fin.addCases (motive:=fun _ : Fin 3=>List Bool)
        ![List.replicate width true,List.replicate count true] (fun _ : Fin 1=>List.replicate C false))) =
      initialConfiguration machine
        ![ZeroPadding.pad C (List.replicate width true),ZeroPadding.pad C (List.replicate count true),List.replicate C false] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,ZeroPadding.pad_zero,Fin.addCases]
  change runFrom machine _ (ZeroPadding.config _ (initialConfiguration machine _))=some r at rr
  rw [hi] at rr
  refine ⟨r,rr,?_,?_,rs.trans ast⟩
  · funext i;fin_cases i
    · rw [rf]
      change ZeroPadding.pad C (a.final.tapes 0)=ZeroPadding.pad C (List.replicate width true)
      apply congrArg (ZeroPadding.pad C)
      exact (atp 0).trans (by rw [hf];rfl)
    · rw [rf]
      change ZeroPadding.pad C (a.final.tapes 1)=ZeroPadding.pad C (List.replicate (count+width) true)
      apply congrArg (ZeroPadding.pad C)
      exact (atp 1).trans (by rw [hf];rfl)
    · rw [rf];change ZeroPadding.pad 0 (a.final.tapes 2)=_
      rw [ZeroPadding.pad_zero]
      rw [hs,Nat.max_eq_left hC] at alog
      exact alog
  · intro i;rw [rf];exact ah i

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Advance
