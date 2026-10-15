import Proof.CaseAnalysis.RowsRawAtomProducer

/-! The raw multiplication consumer copies a monomial's actual address
blocks, excluding its two outer markers. It scans each retained bit once;
indices, their repetitions, and the live source/output cursors are exact. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawMonomialCopy
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then some (if bits 0 then
      ⟨1,![none,some true],fun _=>.right⟩ else ⟨2,fun _=>none,![.right,.stay]⟩)
    else if q=1 then some ⟨if bits 0 then 1 else 0,![none,some (bits 0)],fun _=>.right⟩ else none
def cfg (state : Fin 3) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 3:=
  ⟨state,![pos,out.length],![source,out]⟩

theorem true_step (q : Fin 3) (hq : q=0 ∨ q=1) (pre tail out : List Bool) :
    step machine (cfg q (pre++true::tail) pre.length out)=
      some (cfg 1 (pre++true::tail) (pre.length+1) (out++[true])) := by
  rcases hq with rfl|rfl
  all_goals
    simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,write_append]

theorem false_step (pre tail out : List Bool) :
    step machine (cfg 1 (pre++false::tail) pre.length out)=
      some (cfg 0 (pre++false::tail) (pre.length+1) (out++[false])) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,write_append]

theorem stop_step (pre tail out : List Bool) :
    step machine (cfg 0 (pre++false::tail) pre.length out)=
      some (cfg 2 (pre++false::tail) (pre.length+1) out) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem true_run (n : ℕ) (pre tail out : List Bool) :
    Timed machine n (cfg 1 (pre++List.replicate n true++tail) pre.length out)
      (cfg 1 (pre++List.replicate n true++tail) (pre.length+n) (out++List.replicate n true)) := by
  induction n generalizing pre out with
  | zero=>simpa using (Timed.refl (p:=machine) (cfg 1 (pre++tail) pre.length out))
  | succ n ih=>
    have rest:=ih (pre++[true]) (out++[true])
    have source:(pre++[true])++List.replicate n true++tail=pre++true::(List.replicate n true++tail):=by
      simp [List.append_assoc]
    simp only [List.length_append,List.length_singleton,source] at rest
    have h:=(Timed.single (by rfl) (true_step 1 (Or.inr rfl) pre
      (List.replicate n true++tail) out)).trans rest
    simpa [List.replicate_succ,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem block_run (d : ℕ) (pre tail out : List Bool) :
    Timed machine (d+2) (cfg 0 (pre++ExtIncidence.block d++tail) pre.length out)
      (cfg 0 (pre++ExtIncidence.block d++tail) (pre.length+(ExtIncidence.block d).length)
        (out++ExtIncidence.block d)) := by
  have rest:=true_run d (pre++[true]) (false::tail) (out++[true])
  have source:(pre++[true])++List.replicate d true++false::tail=pre++ExtIncidence.block d++tail:=by
    simp [ExtIncidence.block,List.replicate_succ,List.append_assoc]
  rw [source] at rest
  simp only [List.length_append,List.length_singleton] at rest
  have first:=Timed.single (by rfl) (true_step 0 (Or.inl rfl) pre
    (List.replicate d true++false::tail) out)
  have source':pre++true::(List.replicate d true++false::tail)=pre++ExtIncidence.block d++tail:=by
    simp [ExtIncidence.block,List.replicate_succ,List.append_assoc]
  rw [source'] at first
  have last:=Timed.single (by rfl) (false_step (pre++List.replicate (d+1) true) tail
    (out++List.replicate (d+1) true))
  have source'':(pre++List.replicate (d+1) true)++false::tail=pre++ExtIncidence.block d++tail:=by
    simp [ExtIncidence.block,List.append_assoc]
  rw [source''] at last
  simp only [List.length_append,List.length_replicate] at last
  have outEq:(out++[true])++List.replicate d true=out++List.replicate (d+1) true:=by
    simp [List.replicate_succ,List.append_assoc]
  rw [outEq] at rest
  have h:=first.trans (rest.trans (by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using last))
  simpa [ExtIncidence.block,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem body_run (m : List ℕ) (pre tail out : List Bool) :
    Timed machine ((m.flatMap ExtIncidence.block).length+1)
      (cfg 0 (pre++m.flatMap ExtIncidence.block++false::tail) pre.length out)
      (cfg 2 (pre++m.flatMap ExtIncidence.block++false::tail)
        (pre.length+(m.flatMap ExtIncidence.block).length+1) (out++m.flatMap ExtIncidence.block)) := by
  induction m generalizing pre out with
  | nil=>simpa using Timed.single (by rfl) (stop_step pre tail out)
  | cons d m ih=>
    have rest:=ih (pre++ExtIncidence.block d) (out++ExtIncidence.block d)
    have first:=block_run d pre (m.flatMap ExtIncidence.block++false::tail) out
    simp only [List.append_assoc,List.length_append] at rest first
    have h:=first.trans rest
    have len:=ExtIncidence.block_length d
    rw [←len] at h
    simpa only [List.flatMap_cons,List.length_append,List.append_assoc,Nat.add_assoc] using h

theorem copy_run (m : List ℕ) (pre tail out : List Bool) :
    ∃ r,runFrom machine ((m.flatMap ExtIncidence.block).length+1)
      (cfg 0 (pre++m.flatMap ExtIncidence.block++false::tail) pre.length out)=some r ∧
      r.final=cfg 2 (pre++m.flatMap ExtIncidence.block++false::tail)
        (pre.length+(m.flatMap ExtIncidence.block).length+1) (out++m.flatMap ExtIncidence.block) ∧
      r.steps=(m.flatMap ExtIncidence.block).length+1 := by
  exact (body_run m pre tail out).run (by rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsRawMonomialCopy
