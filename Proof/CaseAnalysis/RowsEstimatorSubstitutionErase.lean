import Proof.CaseAnalysis.RowsRawPairReusable

/-! Erase a raw polynomial by its actual delimiters. Padding is not scanned. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionErase
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def next (q : Fin 4) (bit : Bool) : Fin 4 :=
  if q=0 then if bit then 1 else 3 else if q=1 then if bit then 2 else 0 else if bit then 2 else 1
def machine : Machine 1 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=3)
  rule:=fun q bits=>if q=3 then none else some ⟨next q (bits 0),fun _=>some false,fun _=>.right⟩
def cfg (q : Fin 4) (pre tail : List Bool) : Configuration 1 4:=
  ⟨q,fun _=>pre.length,fun _=>pre++tail⟩

theorem write_prefix (pre tail : List Bool) (bit : Bool) :
    writeTapeBit (pre++bit::tail) pre.length false=pre++false::tail := by
  induction pre with
  | nil=>rfl
  | cons b pre ih=>simp [writeTapeBit,ih]

theorem byte (q : Fin 4) (hq : q≠3) (pre tail : List Bool) (bit : Bool) :
    Timed machine 1 (cfg q pre (bit::tail)) (cfg (next q bit) (pre++[false]) tail) := by
  refine Timed.single (by simp [machine,cfg,hq]) ?_
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append,hq]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i;simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i;simp [applyAction,write_prefix]

theorem trues (n : ℕ) (pre tail : List Bool) :
    Timed machine n (cfg 2 pre (List.replicate n true++tail))
      (cfg 2 (pre++List.replicate n false) tail) := by
  induction n generalizing pre with
  | zero=>simpa using (Timed.refl (p:=machine) (cfg 2 pre tail))
  | succ n ih=>
    have first:=byte 2 (by decide) pre (List.replicate n true++tail) true
    have rest:=ih (pre++[false])
    have all:=(by simpa [next] using first : Timed machine 1
      (cfg 2 pre (true::(List.replicate n true++tail)))
      (cfg 2 (pre++[false]) (List.replicate n true++tail))).trans rest
    simpa [List.replicate_succ,List.append_assoc,Nat.add_comm] using all

theorem block (n : ℕ) (pre tail : List Bool) :
    Timed machine (n+2) (cfg 1 pre (ExtIncidence.block n++tail))
      (cfg 1 (pre++List.replicate (n+2) false) tail) := by
  have first:=byte 1 (by decide) pre (List.replicate n true++false::tail) true
  have middle:=trues n (pre++[false]) (false::tail)
  have last:=byte 2 (by decide) ((pre++[false])++List.replicate n false) tail false
  simp only [next,show ¬(1 : Fin 4)=0 by decide,ite_false,ite_true] at first
  simp only [next,show ¬(2 : Fin 4)=0 by decide,show ¬(2 : Fin 4)=1 by decide,ite_false] at last
  have all:=first.trans (middle.trans last)
  have hz : ((pre++[false])++List.replicate n false)++[false]=pre++List.replicate (n+2) false := by
    calc
      _=pre++(List.replicate 1 false++List.replicate n false++List.replicate 1 false) := by simp [List.append_assoc]
      _=_ := by rw [←List.replicate_add,←List.replicate_add];congr 2;omega
  rw [hz] at all
  simpa [ExtIncidence.block,List.replicate_succ,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all

theorem monomial (m : List ℕ) (pre tail : List Bool) :
    Timed machine ((m.flatMap ExtIncidence.block).length+1)
      (cfg 1 pre (m.flatMap ExtIncidence.block++false::tail))
      (cfg 0 (pre++List.replicate ((m.flatMap ExtIncidence.block).length+1) false) tail) := by
  induction m generalizing pre with
  | nil=>simpa [next] using byte 1 (by decide) pre tail false
  | cons i m ih=>
    have first:=block i pre (m.flatMap ExtIncidence.block++false::tail)
    have rest:=ih (pre++List.replicate (i+2) false)
    have all:=first.trans rest
    simpa [List.flatMap_cons,ExtIncidence.block_length,List.replicate_add,List.append_assoc,Nat.add_assoc] using all

theorem stream (p : List (List ℕ)) (pre tail : List Bool) :
    Timed machine (ExtIncidence.stream p).length (cfg 0 pre (ExtIncidence.stream p++tail))
      (cfg 3 (pre++List.replicate (ExtIncidence.stream p).length false) tail) := by
  induction p generalizing pre with
  | nil=>simpa [ExtIncidence.stream,next] using byte 0 (by decide) pre tail false
  | cons m p ih=>
    have first:=byte 0 (by decide) pre (m.flatMap ExtIncidence.block++false::(ExtIncidence.stream p++tail)) true
    have body:=monomial m (pre++[false]) (ExtIncidence.stream p++tail)
    have rest:=ih ((pre++[false])++List.replicate ((m.flatMap ExtIncidence.block).length+1) false)
    simp only [next,ite_true] at first
    have all:=first.trans (body.trans rest)
    have hl : 1+((m.flatMap ExtIncidence.block).length+1+(ExtIncidence.stream p).length)=
        (ExtIncidence.stream (m::p)).length := by
      rw [ExtIncidence.stream_cons,List.length_append,ExtIncidence.monomialWord_length]
      omega
    have hi : true::(m.flatMap ExtIncidence.block++false::(ExtIncidence.stream p++tail))=
        ExtIncidence.stream (m::p)++tail := by
      simp [ExtIncidence.stream_cons,ExtIncidence.monomialWord,List.append_assoc]
    have hz : (((pre++[false])++List.replicate ((m.flatMap ExtIncidence.block).length+1) false)++
        List.replicate (ExtIncidence.stream p).length false)=pre++List.replicate (ExtIncidence.stream (m::p)).length false := by
      calc
        _=pre++(List.replicate 1 false++List.replicate ((m.flatMap ExtIncidence.block).length+1) false++
            List.replicate (ExtIncidence.stream p).length false) := by simp [List.append_assoc]
        _=_ := by rw [←List.replicate_add,←List.replicate_add];congr 2;omega
    rw [hl,hi,hz] at all
    exact all

theorem run (p : List (List ℕ)) : Step machine (ExtIncidence.stream p).length
    (fun _=>0) (fun _=>ExtIncidence.stream p)
    (fun _=>(ExtIncidence.stream p).length) (fun _=>List.replicate (ExtIncidence.stream p).length false) := by
  obtain ⟨r,hr,rf,_⟩:=(stream p [] []).run (by rfl)
  simpa only [cfg,List.nil_append,List.append_nil,List.length_nil,List.length_replicate] using
    Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionErase
