import Proof.CaseAnalysis.RowsRawPolynomialAdd

/-! The substitution cache cursor consumes one actual raw polynomial.
Its monomial traversal is the source projection of the checked copier;
every logical bit is read once, including the final polynomial marker. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawPolynomialSkip
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 1 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=3)
  rule:=fun q bits=>if q=0 then some ⟨if bits 0 then 1 else 3,fun _=>none,fun _=>.right⟩
    else if q=1 then some ⟨if bits 0 then 2 else 0,fun _=>none,fun _=>.right⟩
    else if q=2 then some ⟨if bits 0 then 2 else 1,fun _=>none,fun _=>.right⟩ else none
def state : Fin 3→Fin 4:=![1,2,0]
def cfg (q : Fin 4) (source : List Bool) (pos : ℕ) : Configuration 1 4:=
  ⟨q,fun _=>pos,fun _=>source⟩
def project (c : Configuration 2 3) : Configuration 1 4:=
  cfg (state c.control) (c.tapes 0) (c.heads 0)

theorem step_project (c d : Configuration 2 3)
    (hs : step CloseoutRowsRawMonomialCopy.machine c=some d) :
    step machine (project c)=some (project d) := by
  rcases c with ⟨q,H,A⟩
  fin_cases q
  all_goals cases hread:readTapeBit (A 0) (H 0)
  all_goals simp [step,CloseoutRowsRawMonomialCopy.machine,Configuration.scanned,hread] at hs
  all_goals subst d
  all_goals
    simp [step,machine,project,cfg,state,Configuration.scanned,hread]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i;simp [applyAction,HeadMove.apply]
    · funext i;fin_cases i;rfl

theorem cells (c : Configuration 2 3) : (project c).tapeCells≤c.tapeCells := by
  simp [Configuration.tapeCells,project,cfg,Fin.sum_univ_two]

theorem active (c : Configuration 2 3) : machine.halted (project c).control=false := by
  rcases c with ⟨q,H,A⟩
  fin_cases q <;> rfl

theorem prefix_project {space n : ℕ} {c d : Configuration 2 3}
    (h : Prefix CloseoutRowsRawMonomialCopy.machine space n c d) :
    Prefix machine space n (project c) (project d) := by
  induction h with
  | refl c hc=>exact Prefix.refl _ ((cells c).trans hc)
  | step hc _ hs _ ih=>exact Prefix.step ((cells _).trans hc) (active _) (step_project _ _ hs) ih

theorem monomial_trace (m : List ℕ) (pre tail : List Bool) :
    Timed machine ((m.flatMap ExtIncidence.block).length+1)
      (cfg 1 (pre++m.flatMap ExtIncidence.block++false::tail) pre.length)
      (cfg 0 (pre++m.flatMap ExtIncidence.block++false::tail)
        (pre.length+(m.flatMap ExtIncidence.block).length+1)) := by
  obtain ⟨space,h⟩:=CloseoutRowsRawMonomialCopy.body_run m pre tail []
  exact ⟨space,prefix_project h⟩

theorem boundary (bit : Bool) (pre tail : List Bool) :
    Timed machine 1 (cfg 0 (pre++bit::tail) pre.length)
      (cfg (if bit then 1 else 3) (pre++bit::tail) (pre.length+1)) := by
  refine Timed.single (by rfl) ?_
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i;simp [applyAction,HeadMove.apply]
  · rfl

theorem stream_trace (p : List (List ℕ)) (pre tail : List Bool) :
    Timed machine (ExtIncidence.stream p).length
      (cfg 0 (pre++ExtIncidence.stream p++tail) pre.length)
      (cfg 3 (pre++ExtIncidence.stream p++tail) (pre.length+(ExtIncidence.stream p).length)) := by
  induction p generalizing pre with
  | nil=>simpa [ExtIncidence.stream] using boundary false pre tail
  | cons m p ih=>
    have first:=boundary true pre (m.flatMap ExtIncidence.block++false::(ExtIncidence.stream p++tail))
    have body:=monomial_trace m (pre++[true]) (ExtIncidence.stream p++tail)
    have rest:=ih (pre++ExtIncidence.monomialWord m)
    have source:(pre++[true])++m.flatMap ExtIncidence.block++false::(ExtIncidence.stream p++tail)=
        pre++ExtIncidence.monomialWord m++ExtIncidence.stream p++tail:=by
      simp [ExtIncidence.monomialWord,List.append_assoc]
    have source':pre++true::(m.flatMap ExtIncidence.block++false::(ExtIncidence.stream p++tail))=
        pre++ExtIncidence.monomialWord m++ExtIncidence.stream p++tail:=by
      simp [ExtIncidence.monomialWord,List.append_assoc]
    rw [source'] at first
    rw [source] at body
    simp only [List.length_append,List.length_singleton] at body rest
    have position:pre.length+1+(m.flatMap ExtIncidence.block).length+1=
        pre.length+(ExtIncidence.monomialWord m).length:=by
      rw [ExtIncidence.monomialWord_length];omega
    rw [position] at body
    have all:=first.trans (body.trans rest)
    have time:1+((m.flatMap ExtIncidence.block).length+1+(ExtIncidence.stream p).length)=
        (ExtIncidence.stream (m::p)).length:=by
      rw [ExtIncidence.stream_cons,List.length_append,ExtIncidence.monomialWord_length];omega
    rw [time] at all
    simpa only [ExtIncidence.stream_cons,List.length_append,List.append_assoc,Nat.add_assoc] using all

theorem skip_run (p : List (List ℕ)) (pre tail : List Bool) :
    Step machine (ExtIncidence.stream p).length
      (fun _=>pre.length) (fun _=>pre++ExtIncidence.stream p++tail)
      (fun _=>pre.length+(ExtIncidence.stream p).length)
      (fun _=>pre++ExtIncidence.stream p++tail) := by
  obtain ⟨r,hr,rf,_⟩:=(stream_trace p pre tail).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end NearCubicWires.RepairOrdinary.CloseoutRowsRawPolynomialSkip
