import Proof.CaseAnalysis.CaseTwoHonestCall

/-! Select one raw auxiliary bit by its physically produced unary index.
The source and index are retained and all four heads are restored. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.UnaryLookup
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 3 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q bits=>if q.val=0 then
    some (if bits 0 then ⟨0,fun _=>none,![.right,.right,.stay]⟩
      else ⟨1,![none,none,some (bits 1)],fun _=>.stay⟩)
    else none
def cfg (q : Fin 2) (pre tail : List Bool) (remaining : ℕ) (out : List Bool) : Configuration 3 2:=
  ⟨q,![pre.length,pre.length,0],![List.replicate (pre.length+remaining) true,pre++tail,out]⟩

theorem skip_step (pre tail : List Bool) (b : Bool) (remaining : ℕ) :
    step raw (cfg 0 pre (b::tail) (remaining+1) [])=some (cfg 0 (pre++[b]) tail remaining []):=by
  have hd:readTapeBit (List.replicate (pre.length+(remaining+1)) true) pre.length=true:=by
    rw [ClockUnaryProduct.read_unary]
    simp
  simp only [step,raw,cfg,Fin.val_zero,if_true,Configuration.scanned,Matrix.cons_val_zero,hd]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;>simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i
    · change List.replicate (pre.length+(remaining+1)) true=List.replicate ((pre++[b]).length+remaining) true
      congr 1
      simp
      omega
    · simp [applyAction,List.append_assoc]
    · rfl

theorem pick_step (pre tail : List Bool) (b : Bool) :
    step raw (cfg 0 pre (b::tail) 0 [])=some (cfg 1 pre (b::tail) 0 [b]):=by
  have hr:=Streaming.read_append pre tail b
  simp only [step,raw,cfg,Fin.val_zero,if_true,Configuration.scanned,Matrix.cons_val_zero,
    Nat.add_zero,ClockUnaryProduct.read_unary,lt_self_iff_false,decide_false,Bool.false_eq_true,if_false]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i <;>simp [applyAction,writeTapeBit,hr]

theorem loop (pre skipped tail : List Bool) (b : Bool) :
    Timed raw (skipped.length+1) (cfg 0 pre (skipped++b::tail) skipped.length [])
      (cfg 1 (pre++skipped) (b::tail) 0 [b]):=by
  induction skipped generalizing pre with
  | nil=>simpa using Timed.single (by rfl) (pick_step pre tail b)
  | cons x skipped ih=>
    have ht:=(Timed.single (by rfl) (skip_step pre (skipped++b::tail) x skipped.length)).trans (ih (pre++[x]))
    have he:1+(skipped.length+1)=(x::skipped).length+1:=by simp;omega
    rw [he] at ht
    simpa only [List.cons_append,List.append_assoc,List.singleton_append,List.nil_append,List.length_cons] using ht

def rawInput (pre tail : List Bool) (b : Bool) : Fin 3→List Bool:=
  ![List.replicate pre.length true,pre++b::tail,[]]
def machine:=Rewind.machine raw
def input (pre tail : List Bool) (b : Bool) : Fin 4→List Bool:=
  ![List.replicate pre.length true,pre++b::tail,[],[]]
theorem lookup_run (pre tail : List Bool) (b : Bool) : ∃ out,
    ClockJoin.ReadyRun machine (2*pre.length+4) (input pre tail b) out ∧
      out 2=[b] ∧ out 0=List.replicate pre.length true ∧ out 1=pre++b::tail:=by
  have ht:=loop [] pre tail b
  have hi:cfg 0 [] (pre++b::tail) pre.length []=initialConfiguration raw (rawInput pre tail b):=by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>simp [cfg,initialConfiguration,rawInput]
  rw [hi] at ht
  obtain ⟨base,hb,bf,bs⟩:=ht.run (by rfl)
  obtain ⟨r,hr,rt,rh,rs,_⟩:=Rewind.reset_run raw _ _ base hb
  have hcost:2*base.steps+2=2*pre.length+4:=by rw [bs];omega
  rw [hcost] at hr rs
  have hin:Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool) (rawInput pre tail b) (fun _=>[])=input pre tail b:=by
    funext i;fin_cases i <;>rfl
  rw [hin] at hr
  refine ⟨_,⟨r,hr,rfl,rh,rs.le⟩,?_,?_,?_⟩
  · exact (rt 2).trans (by rw [bf];rfl)
  · exact (rt 0).trans (by rw [bf];simp [cfg])
  · exact (rt 1).trans (by rw [bf];simp [cfg])

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.UnaryLookup
