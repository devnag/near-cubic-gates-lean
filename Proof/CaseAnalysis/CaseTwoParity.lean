import Proof.CaseAnalysis.CaseTwoShape
import Proof.MachineModel.GeneratedAmplifierSemantics

/-! A physical masked XOR scan over the actual support mask and input.
The semantic parity bridge is reused; no support-code enumeration runs. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Parity
open LocalBitMultitape RecoveryExecution SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 4 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q bits=>if q.val=0 then some ⟨1,fun i=>if i=3 then some false else none,fun _=>.stay⟩
    else if q.val=1 then
      some (if bits 0 then ⟨1,fun i=>if i=3 then some (xor (bits 3) (bits 1&&bits 2)) else none,
        fun i=>if i=3 then .stay else .right⟩
      else ⟨2,fun _=>none,fun _=>.stay⟩)
    else none
def fold (pairs : List (Bool×Bool)) (acc : Bool):=pairs.foldl (fun b p=>xor b (p.1&&p.2)) acc
def cfg (q : Fin 3) (pre tail : List (Bool×Bool)) (acc : Bool) : Configuration 4 3:=
  ⟨q,![pre.length,pre.length,pre.length,0],
    ![List.replicate (pre.length+tail.length) true,(pre++tail).map Prod.fst,(pre++tail).map Prod.snd,[acc]]⟩
def rawInput (pairs : List (Bool×Bool)) : Fin 4→List Bool:=
  ![List.replicate pairs.length true,pairs.map Prod.fst,pairs.map Prod.snd,[]]

theorem start_step (pairs : List (Bool×Bool)) :
    step raw (initialConfiguration raw (rawInput pairs))=some (cfg 1 [] pairs false):=by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i <;>simp [applyAction,initialConfiguration,rawInput,cfg,writeTapeBit]

theorem bit_step (pre tail : List (Bool×Bool)) (p : Bool×Bool) (acc : Bool) :
    step raw (cfg 1 pre (p::tail) acc)=some (cfg 1 (pre++[p]) tail (xor acc (p.1&&p.2))):=by
  have hd : readTapeBit (List.replicate (pre.length+(p::tail).length) true) pre.length=true:=by
    rw [ClockUnaryProduct.read_unary]
    simp
  have hm : readTapeBit ((pre++p::tail).map Prod.fst) pre.length=p.1:=by
    simpa only [List.map_append,List.map_cons,List.length_map] using
      Streaming.read_append (pre.map Prod.fst) (tail.map Prod.fst) p.1
  have hu : readTapeBit ((pre++p::tail).map Prod.snd) pre.length=p.2:=by
    simpa only [List.map_append,List.map_cons,List.length_map] using
      Streaming.read_append (pre.map Prod.snd) (tail.map Prod.snd) p.2
  simp only [step,raw,cfg,Fin.val_one,if_true,Configuration.scanned,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,hd,hm]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;>simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i
    · change List.replicate (pre.length+(p::tail).length) true=
        List.replicate ((pre++[p]).length+tail.length) true
      congr 1
      simp
      omega
    all_goals simp [applyAction,List.append_assoc,List.map_append,writeTapeBit,readTapeBit,List.getD]

theorem stop_step (pre : List (Bool×Bool)) (acc : Bool) :
    step raw (cfg 1 pre [] acc)=some (cfg 2 pre [] acc):=by
  simp only [step,raw,cfg,Fin.val_one,if_false,if_true,Configuration.scanned,Matrix.cons_val_zero,
    List.length_nil,Nat.add_zero,ClockUnaryProduct.read_unary,lt_self_iff_false,decide_false,
    Bool.false_eq_true]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;>rfl
  · rfl

theorem loop (pre tail : List (Bool×Bool)) (acc : Bool) :
    Timed raw (tail.length+1) (cfg 1 pre tail acc) (cfg 2 (pre++tail) [] (fold tail acc)):=by
  induction tail generalizing pre acc with
  | nil=>simpa [fold] using Timed.single (by rfl) (stop_step pre acc)
  | cons p tail ih=>
    have ht:=(Timed.single (by rfl) (bit_step pre tail p acc)).trans (ih (pre++[p]) (xor acc (p.1&&p.2)))
    have he:1+(tail.length+1)=(p::tail).length+1:=by simp;omega
    rw [he] at ht
    simpa only [fold,List.foldl_cons,List.append_assoc,List.singleton_append] using ht

theorem raw_run (pairs : List (Bool×Bool)) :
    ∃ r,run raw (pairs.length+2) (rawInput pairs)=some r ∧
      r.final=cfg 2 pairs [] (fold pairs false) ∧ r.steps=pairs.length+2:=by
  have ht:=(Timed.single (by rfl) (start_step pairs)).trans (loop [] pairs false)
  have he:1+(pairs.length+1)=pairs.length+2:=by omega
  rw [he] at ht
  have ht':Timed raw (pairs.length+2) (initialConfiguration raw (rawInput pairs))
      (cfg 2 pairs [] (fold pairs false)):=by simpa only [List.nil_append] using ht
  exact ht'.run (by rfl)

def machine:=Rewind.machine raw
def input (pairs : List (Bool×Bool)) : Fin 5→List Bool:=
  ![List.replicate pairs.length true,pairs.map Prod.fst,pairs.map Prod.snd,[],[]]
theorem parity_run (pairs : List (Bool×Bool)) : ∃ out,
    ClockJoin.ReadyRun machine (2*pairs.length+6) (input pairs) out ∧ out 3=[fold pairs false]:=by
  obtain ⟨base,hb,bf,bs⟩:=raw_run pairs
  obtain ⟨r,hr,rt,rh,rs,_⟩:=Rewind.reset_run raw _ _ base hb
  have ht:2*base.steps+2=2*pairs.length+6:=by rw [bs];omega
  rw [ht] at hr rs
  have hi:Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool) (rawInput pairs) (fun _=>[])=input pairs:=by
    funext i;fin_cases i <;>rfl
  rw [hi] at hr
  refine ⟨_,⟨r,hr,rfl,rh,rs.le⟩,?_⟩
  exact (rt 3).trans (by rw [bf];rfl)

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Parity
