import Proof.PCP.PCPPNativeLiteralSplit

/-! Select the actual positive/negative literal offset using its original
sign bit, physically copying the selected raw unary counter. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseOffset
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def active (sign : Bool) : Fin 4 := if sign then 2 else 1
def value (sign : Bool) (p n : ℕ) := if sign then n else p
def raw : Machine 4 4 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==3
  rule := fun q bs=>if q.val=0 then some ⟨active (bs 0),fun _=>none,fun _=>.stay⟩
    else if q.val=1 then some (if bs 1 then ⟨1,![none,none,none,some true],![.stay,.right,.stay,.right]⟩
      else ⟨3,fun _=>none,fun _=>.stay⟩)
    else if q.val=2 then some (if bs 2 then ⟨2,![none,none,none,some true],![.stay,.stay,.right,.right]⟩
      else ⟨3,fun _=>none,fun _=>.stay⟩)
    else none
def cfg (q : Fin 4) (sign : Bool) (p n done : ℕ) : Configuration 4 4 :=
  ⟨q,![0,if sign then 0 else done,if sign then done else 0,done],
    ![[sign],List.replicate p true,List.replicate n true,List.replicate done true]⟩

theorem start_step (sign : Bool) (p n : ℕ) :
    step raw (cfg 0 sign p n 0)=some (cfg (active sign) sign p n 0) := by
  cases sign <;> simp [step,raw,cfg,active,Configuration.scanned,readTapeBit,List.getD]
  all_goals rfl

theorem copy_step (sign : Bool) (p n done : ℕ) (h : done<value sign p n) :
    step raw (cfg (active sign) sign p n done)=some (cfg (active sign) sign p n (done+1)) := by
  have hw : writeTapeBit (List.replicate done true) done true=List.replicate (done+1) true := by
    have hx:=Streaming.write_append (List.replicate done true) true
    simpa only [List.length_replicate,List.replicate_add,List.replicate_one] using hx
  cases sign
  all_goals simp only [value,Bool.false_eq_true,ite_false,ite_true] at h
  all_goals simp [step,raw,cfg,active,Configuration.scanned,ClockUnaryProduct.read_unary,h]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,hw])

theorem stop_step (sign : Bool) (p n : ℕ) :
    step raw (cfg (active sign) sign p n (value sign p n))=some (cfg 3 sign p n (value sign p n)) := by
  cases sign <;> simp [step,raw,cfg,active,value,Configuration.scanned,ClockUnaryProduct.read_unary]
  all_goals rfl

theorem copy (sign : Bool) (p n done remaining : ℕ) (h : done+remaining ≤ value sign p n) :
    Timed raw remaining (cfg (active sign) sign p n done) (cfg (active sign) sign p n (done+remaining)) := by
  induction remaining generalizing done with
  | zero => simpa only [Nat.add_zero] using Timed.refl raw (cfg (active sign) sign p n done)
  | succ remaining ih =>
    have hs:=Timed.single (by cases sign <;> rfl) (copy_step sign p n done (by omega))
    have ht:=ih (done+1) (by omega)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs.trans ht

theorem raw_run (sign : Bool) (p n : ℕ) : ∃ r,
    run raw (value sign p n+2) ![[sign],List.replicate p true,List.replicate n true,[]]=some r ∧
      r.final=cfg 3 sign p n (value sign p n) ∧ r.steps=value sign p n+2 := by
  have hs:=Timed.single (by rfl) (start_step sign p n)
  have hm:=copy sign p n 0 (value sign p n) (by omega)
  simp only [Nat.zero_add] at hm
  have he:=Timed.single (by cases sign <;> rfl) (stop_step sign p n)
  have hr:=((hs.trans hm).trans he).run (by rfl)
  have hi : cfg 0 sign p n 0=initialConfiguration raw ![[sign],List.replicate p true,List.replicate n true,[]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> cases sign <;> rfl
    · rfl
  rw [hi,show 1+value sign p n+1=value sign p n+2 by omega] at hr
  exact hr

def machine := Rewind.machine raw
theorem ready_run (sign : Bool) (p n : ℕ) :
    ReadyRun machine (2*value sign p n+6)
      ![[sign],List.replicate p true,List.replicate n true,[],[]]
      ![[sign],List.replicate p true,List.replicate n true,List.replicate (value sign p n) true,
        List.replicate (value sign p n+2) false] := by
  obtain ⟨base,hb,hf,hs⟩:=raw_run sign p n
  obtain ⟨r,hr,ht,log,hh,rs,_⟩:=Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have hi : (Fin.addCases (m := 4) (n := 1) (motive := fun _ : Fin 5=>List Bool)
      ![[sign],List.replicate p true,List.replicate n true,[]] (fun _=>List.replicate 0 false))=
      ![[sign],List.replicate p true,List.replicate n true,[],[]] := by
    funext i; fin_cases i <;> rfl
  have htime : 2*base.steps+2=2*value sign p n+6 := by omega
  change run machine (2*base.steps+2)
    (Fin.addCases (m := 4) (n := 1) (motive := fun _ : Fin 5=>List Bool)
      ![[sign],List.replicate p true,List.replicate n true,[]] (fun _=>List.replicate 0 false))=some r at hr
  rw [hi,htime] at hr
  refine ⟨r,hr,?_,hh,by omega⟩
  funext i
  fin_cases i
  · exact (ht 0).trans (by rw [hf]; rfl)
  · exact (ht 1).trans (by rw [hf]; rfl)
  · exact (ht 2).trans (by rw [hf]; rfl)
  · exact (ht 3).trans (by rw [hf]; rfl)
  · simpa [hs,Fin.natAdd] using log

end NearCubicWires.RepairOrdinary.PCPPNativeClauseOffset
