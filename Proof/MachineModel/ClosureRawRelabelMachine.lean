import Proof.MachineModel.Run
import Proof.MachineModel.ClockUnaryProduct

/-! Fixed physical stream reindexer. Tape 1 is the retained unary displacement
with a leading false sentinel; every address block gets that many new marks.
The next composition supplies that displacement by paid multiplication. -/
namespace NearCubicWires.P1Closure.RawRelabelMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtIncidence
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 3 6 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=5)
  rule:=fun q b=>if q=0 then some
      ⟨if b 0 then 1 else 5,![none,none,some (b 0)],![.right,.stay,.right]⟩
    else if q=1 then some (if b 0 then ⟨2,fun _=>none,fun _=>.stay⟩
      else ⟨0,![none,none,some false],![.right,.stay,.right]⟩)
    else if q=2 then some (if b 1 then
      ⟨2,![none,none,some true],![.stay,.right,.right]⟩
      else ⟨3,fun _=>none,![.stay,.left,.stay]⟩)
    else if q=3 then some (if b 1 then ⟨3,fun _=>none,![.stay,.left,.stay]⟩
      else ⟨4,fun _=>none,![.stay,.right,.stay]⟩)
    else if q=4 then some
      ⟨if b 0 then 4 else 1,![none,none,some (b 0)],![.right,.stay,.right]⟩
    else none

def cfg (state : Fin 6) (W : List Bool) (pos offset cursor : ℕ) (out : List Bool) : Configuration 3 6 :=
  ⟨state,![pos,cursor,out.length],![W,false::List.replicate offset true,out]⟩

theorem emit (q : Fin 6) (hq : q=0 ∨ q=4) (W : List Bool) (pos offset cursor : ℕ)
    (out : List Bool) :
    step machine (cfg q W pos offset cursor out)=some
      (cfg (if q=0 then (if readTapeBit W pos then 1 else 5)
        else (if readTapeBit W pos then 4 else 1)) W (pos+1) offset cursor
        (out++[readTapeBit W pos])) := by
  rcases hq with rfl|rfl
  all_goals
    simp [step,machine,cfg,Configuration.scanned]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem enter (W : List Bool) (pos offset : ℕ) (out : List Bool)
    (h : readTapeBit W pos=true) :
    step machine (cfg 1 W pos offset 1 out)=some (cfg 2 W pos offset 1 out) := by
  simp [step,machine,cfg,Configuration.scanned,h]
  rfl

theorem finish (W : List Bool) (pos offset : ℕ) (out : List Bool)
    (h : readTapeBit W pos=false) :
    step machine (cfg 1 W pos offset 1 out)=some (cfg 0 W (pos+1) offset 1 (out++[false])) := by
  simp [step,machine,cfg,Configuration.scanned,h]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem copy_step (W : List Bool) (pos offset j : ℕ) (out : List Bool) (hj : j<offset) :
    step machine (cfg 2 W pos offset (j+1) out)=some (cfg 2 W pos offset (j+2) (out++[true])) := by
  have hr:=ClockUnaryProduct.read_sentinel offset j
  simp only [hj,decide_true] at hr
  simp [step,machine,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem back_step (W : List Bool) (pos offset j : ℕ) (out : List Bool) (hj : j<offset) :
    step machine (cfg 3 W pos offset (j+1) out)=some (cfg 3 W pos offset j out) := by
  have hr:=ClockUnaryProduct.read_sentinel offset j
  simp only [hj,decide_true] at hr
  simp [step,machine,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem copy_end (W : List Bool) (pos offset : ℕ) (out : List Bool) :
    step machine (cfg 2 W pos offset (offset+1) out)=some (cfg 3 W pos offset offset out) := by
  have hr:=ClockUnaryProduct.read_sentinel offset offset
  simp only [Nat.lt_irrefl,decide_false] at hr
  simp [step,machine,cfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem back_end (W : List Bool) (pos offset : ℕ) (out : List Bool) :
    step machine (cfg 3 W pos offset 0 out)=some (cfg 4 W pos offset 1 out) := by
  simp [step,machine,cfg,Configuration.scanned,readTapeBit,List.getD]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem back_loop (W : List Bool) (pos offset j : ℕ) (out : List Bool) (hj : j≤offset) :
    Timed machine (j+1) (cfg 3 W pos offset j out) (cfg 4 W pos offset 1 out) := by
  induction j with
  | zero=>exact Timed.single (by rfl) (back_end W pos offset out)
  | succ j ih=>
    have h:=(Timed.single (by rfl) (back_step W pos offset j out (by omega))).trans (ih (by omega))
    simpa only [Nat.add_comm 1] using h

theorem copy_loop (W : List Bool) (pos offset j remaining : ℕ) (out : List Bool)
    (hj : j+remaining=offset) :
    Timed machine remaining (cfg 2 W pos offset (j+1) out)
      (cfg 2 W pos offset (offset+1) (out++List.replicate remaining true)) := by
  induction remaining generalizing j out with
  | zero=>
    have he:j=offset:=by omega
    subst j
    simpa using Timed.refl machine (cfg 2 W pos offset (offset+1) out)
  | succ r ih=>
    have first:=Timed.single (by rfl) (copy_step W pos offset j out (by omega))
    have rest:=ih (j+1) (out++[true]) (by omega)
    have h:=first.trans rest
    simpa [List.replicate_succ,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem prefix_run (W : List Bool) (pos offset : ℕ) (out : List Bool)
    (h : readTapeBit W pos=true) :
    Timed machine (2*offset+3) (cfg 1 W pos offset 1 out)
      (cfg 4 W pos offset 1 (out++List.replicate offset true)) := by
  have first:=Timed.single (by rfl) (enter W pos offset out h)
  have copying:=copy_loop W pos offset 0 offset out (by omega)
  have last:=Timed.single (by rfl) (copy_end W pos offset (out++List.replicate offset true))
  have back:=back_loop W pos offset offset (out++List.replicate offset true) (by rfl)
  have run:=((first.trans copying).trans last).trans back
  convert run using 1
  omega

theorem true_run (n : ℕ) (pre tail out : List Bool) (offset : ℕ) :
    Timed machine n (cfg 4 (pre++List.replicate n true++tail) pre.length offset 1 out)
      (cfg 4 (pre++List.replicate n true++tail) (pre.length+n) offset 1
        (out++List.replicate n true)) := by
  induction n generalizing pre out with
  | zero=>simpa using Timed.refl machine (cfg 4 (pre++tail) pre.length offset 1 out)
  | succ n ih=>
    have first:=emit 4 (Or.inr rfl) (pre++true::(List.replicate n true++tail)) pre.length offset 1 out
    rw [Streaming.read_append] at first
    have rest:=ih (pre++[true]) (out++[true])
    simp only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append] at rest
    have h:=(Timed.single (by rfl) first).trans rest
    simpa [List.replicate_succ,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def blockCost (offset c : ℕ) := 2*offset+c+5

theorem block_run (offset c : ℕ) (pre tail out : List Bool) :
    Timed machine (blockCost offset c)
      (cfg 1 (pre++block c++tail) pre.length offset 1 out)
      (cfg 1 (pre++block c++tail) (pre.length+(block c).length) offset 1 (out++block (offset+c))) := by
  have read:readTapeBit (pre++block c++tail) pre.length=true:=by
    simpa [block,List.replicate_succ,List.append_assoc] using
      Streaming.read_append pre (List.replicate c true++false::tail) true
  have first:=prefix_run (pre++block c++tail) pre.length offset out read
  have rest:=true_run (c+1) pre (false::tail) (out++List.replicate offset true) offset
  have source:pre++List.replicate (c+1) true++false::tail=pre++block c++tail:=by
    simp [block,List.append_assoc]
  rw [source] at rest
  have last:=emit 4 (Or.inr rfl) (pre++block c++tail) (pre.length+(c+1)) offset 1
    ((out++List.replicate offset true)++List.replicate (c+1) true)
  have endread:readTapeBit (pre++block c++tail) (pre.length+(c+1))=false:=by
    rw [read_shift pre (block c) tail (c+1) (by simp),read_block_end]
  rw [endread] at last
  have h:=(first.trans rest).trans (Timed.single (by rfl) last)
  have outEq:((out++List.replicate offset true)++List.replicate (c+1) true)++[false]=out++block (offset+c):=by
    rw [List.append_assoc out,List.append_assoc out,←List.replicate_add]
    simp [block,Nat.add_assoc]
  rw [outEq] at h
  have cost:2*offset+3+(c+1)+1=blockCost offset c:=by unfold blockCost;omega
  rw [cost] at h
  simpa [Nat.add_assoc] using h

def monoCost (offset : ℕ) (m : List ℕ) := (m.map (blockCost offset)).sum+2

theorem blocks_run (m : List ℕ) (pre tail out : List Bool) (offset : ℕ) :
    Timed machine ((m.map (blockCost offset)).sum)
      (cfg 1 (pre++m.flatMap block++tail) pre.length offset 1 out)
      (cfg 1 (pre++m.flatMap block++tail) (pre.length+(m.flatMap block).length) offset 1
        (out++(m.map (offset+·)).flatMap block)) := by
  induction m generalizing pre out with
  | nil=>simpa using Timed.refl machine (cfg 1 (pre++tail) pre.length offset 1 out)
  | cons c m ih=>
    have first:=block_run offset c pre (m.flatMap block++tail) out
    have rest:=ih (pre++block c) (out++block (offset+c))
    simp only [List.append_assoc,List.length_append] at first rest
    have h:=first.trans rest
    simpa only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append,List.append_assoc,
      Nat.add_assoc] using h

theorem monomial_run (m : List ℕ) (pre tail out : List Bool) (offset : ℕ) :
    Timed machine (monoCost offset m)
      (cfg 0 (pre++monomialWord m++tail) pre.length offset 1 out)
      (cfg 0 (pre++monomialWord m++tail) (pre.length+(monomialWord m).length) offset 1
        (out++monomialWord (m.map (offset+·)))) := by
  have first:=emit 0 (Or.inl rfl) (pre++true::(m.flatMap block++false::tail)) pre.length offset 1 out
  rw [Streaming.read_append] at first
  have rest:=blocks_run m (pre++[true]) (false::tail) (out++[true]) offset
  simp only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append] at rest
  have last:=finish ((pre++true::m.flatMap block)++false::tail)
    (pre++true::m.flatMap block).length offset ((out++[true])++(m.map (offset+·)).flatMap block)
    (Streaming.read_append _ _ false)
  simp only [List.length_append,List.length_cons,List.append_assoc,List.cons_append,List.nil_append] at last
  simp only [List.cons_append,Nat.add_comm,Nat.add_left_comm] at first rest last
  have h:=(Timed.single (by rfl) first).trans (rest.trans (Timed.single (by rfl) last))
  have cost:1+((m.map (blockCost offset)).sum+1)=monoCost offset m:=by unfold monoCost;omega
  rw [cost] at h
  simpa [monomialWord,List.append_assoc,Nat.add_assoc] using h

def budget (offset : ℕ) (P : List (List ℕ)) := (P.map (monoCost offset)).sum+1

theorem stream_run (P : List (List ℕ)) (pre tail out : List Bool) (offset : ℕ) :
    Timed machine (budget offset P)
      (cfg 0 (pre++stream P++tail) pre.length offset 1 out)
      (cfg 5 (pre++stream P++tail) (pre.length+(stream P).length) offset 1
        (out++stream (P.map (List.map (offset+·))))) := by
  induction P generalizing pre out with
  | nil=>
    have h:=emit 0 (Or.inl rfl) (pre++false::tail) pre.length offset 1 out
    rw [Streaming.read_append] at h
    simpa [budget,stream] using Timed.single (by rfl) h
  | cons m P ih=>
    have first:=monomial_run m pre (stream P++tail) out offset
    have rest:=ih (pre++monomialWord m) (out++monomialWord (m.map (offset+·)))
    simp only [List.append_assoc,List.length_append] at first rest
    have h:=first.trans rest
    simpa only [budget,List.map_cons,List.sum_cons,stream_cons,List.length_append,List.append_assoc,
      Nat.add_assoc] using h

end NearCubicWires.P1Closure.RawRelabelMachine
