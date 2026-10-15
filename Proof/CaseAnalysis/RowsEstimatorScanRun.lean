import Proof.CaseAnalysis.RowsEstimatorScan

/-! The grouped scanner applied to the exact emitted cut bytes. The unary
cut count and byte count are outputs of this run, including the empty row. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Scan
open LocalBitMultitape RecoveryExecution Streaming MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countFields (row : EquationRow.Input):=2*row.d-row.odd.toNat+2

theorem row_fields (row : EquationRow.Input) (c : Cut) (hc:c∈row.cuts) :
    (fields c).length=countFields row:=by
  obtain ⟨hl,hr⟩:=row.lengths c hc
  simp only [fields,List.length_append,List.length_cons,List.length_nil] 
  unfold countFields
  omega

theorem cut_head (pre tail : List Bool) (p : ℕ) (c : Cut) :
    readTapeBit (pre++cutWord p c++tail) pre.length=true:=by
  have hn:fields c≠[]:=by
    intro he
    have h:=congrArg List.length he
    simp [fields] at h
  cases he:fields c with
  | nil=>exact (hn he).elim
  | cons z zs=>simp [cutWord,he,signMagnitude,frame,read_append]

theorem cut_timed (pre tail : List Bool) (p n count : ℕ) (c : Cut)
    (hn:(fields c).length=n) :
    Timed machine ((cutWord p c).length+2*n+3)
      (cfg 1 (pre++cutWord p c++tail) pre.length n 1 count)
      (cfg 1 (pre++cutWord p c++tail) (pre.length+(cutWord p c).length) n 1 (count+1)):=by
  have he:((fields c).map (signMagnitude p)).flatMap frame=cutWord p c:=by
    simp [cutWord,List.flatMap_map]
  have h:=group_timed pre tail ((fields c).map (signMagnitude p)) n count
    (by simpa using hn) (by rw [he];exact cut_head pre tail p c)
  simpa only [he] using h

theorem stop (source : List Bool) (n count : ℕ) :
    step machine (cfg 1 source source.length n 1 count)=
      some (cfg 6 source source.length n 1 count):=by
  simp [step,machine,cfg,Configuration.scanned,readTapeBit]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · rfl

theorem cuts_timed (pre : List Bool) (p n count : ℕ) (cs : List Cut)
    (hn:∀ c∈cs,(fields c).length=n) :
    Timed machine ((cs.flatMap (cutWord p)).length+cs.length*(2*n+3)+1)
      (cfg 1 (pre++cs.flatMap (cutWord p)) pre.length n 1 count)
      (cfg 6 (pre++cs.flatMap (cutWord p))
        (pre.length+(cs.flatMap (cutWord p)).length) n 1 (count+cs.length)):=by
  induction cs generalizing pre count with
  | nil=>simpa using Timed.single (by rfl) (stop pre n count)
  | cons c cs ih=>
    have h0:=cut_timed pre (cs.flatMap (cutWord p)) p n count c (hn c (by simp))
    have h1:=ih (pre++cutWord p c) (count+1) (fun c hc=>hn c (by simp [hc]))
    have h:=h0.trans (by simpa only [List.append_assoc,List.length_append] using h1)
    have ht:(cutWord p c).length+2*n+3+
        ((cs.flatMap (cutWord p)).length+cs.length*(2*n+3)+1)=
        ((c::cs).flatMap (cutWord p)).length+(c::cs).length*(2*n+3)+1:=by
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      ring
    rw [ht] at h
    simpa only [List.flatMap_cons,List.append_assoc,List.length_append,List.length_cons,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def ticks (row : EquationRow.Input):=
  (row.cuts.flatMap (cutWord row.p)).length+row.cuts.length*(2*countFields row+3)+2

def input (row : EquationRow.Input) : Fin 4→List Bool:=
  ![row.cuts.flatMap (cutWord row.p),UnaryTemplate.tape (countFields row),[],[]]

theorem raw_run (row : EquationRow.Input) : ∃ actual,
    run machine (ticks row) (input row)=some actual ∧
    actual.final=cfg 6 (row.cuts.flatMap (cutWord row.p))
      (row.cuts.flatMap (cutWord row.p)).length (countFields row) 1 row.cuts.length ∧
    actual.steps=ticks row:=by
  let source:=row.cuts.flatMap (cutWord row.p)
  have hb:step machine (cfg 0 source 0 (countFields row) 0 0)=
      some (cfg 1 source 0 (countFields row) 1 0):=by
    simp [step,machine,cfg]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  have h:= (Timed.single (by rfl) hb).trans
    (by simpa only [List.nil_append,List.length_nil,Nat.zero_add]
      using cuts_timed [] row.p (countFields row) 0 row.cuts (row_fields row))
  have htime:1+((row.cuts.flatMap (cutWord row.p)).length+
      row.cuts.length*(2*countFields row+3)+1)=ticks row:=by unfold ticks;omega
  rw [htime] at h
  obtain ⟨actual,hr,hf,hs⟩:=h.run (by rfl)
  have hi:cfg 0 source 0 (countFields row) 0 0=initialConfiguration machine (input row):=by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  rw [hi] at hr
  exact ⟨actual,hr,hf,hs⟩

def readyMachine:=Rewind.machine machine
def readyInput (row : EquationRow.Input) : Fin 5→List Bool:=
  ![row.cuts.flatMap (cutWord row.p),UnaryTemplate.tape (countFields row),[],[],[]]
def output (row : EquationRow.Input) : Fin 5→List Bool:=
  ![row.cuts.flatMap (cutWord row.p),UnaryTemplate.tape (countFields row),
    List.replicate row.cuts.length true,
    List.replicate (row.cuts.flatMap (cutWord row.p)).length true,
    List.replicate (ticks row) false]

theorem ready (row : EquationRow.Input) :
    ClockJoin.ReadyRun readyMachine (2*ticks row+2) (readyInput row) (output row):=by
  obtain ⟨base,hb,bf,bs⟩:=raw_run row
  obtain ⟨actual,ha,htape,al,ah,ast,_⟩:=Rewind.Workspace.reset_workspace machine
    (ticks row) (input row) base hb 0
  rw [bs] at ha al ast
  refine ⟨actual,?_,?_,ah,ast.le⟩
  · convert ha using 2
    all_goals first | rfl | (funext i;fin_cases i <;> rfl)
  · funext i;fin_cases i
    · exact (htape 0).trans (by rw [bf];rfl)
    · exact (htape 1).trans (by rw [bf];rfl)
    · exact (htape 2).trans (by rw [bf];rfl)
    · exact (htape 3).trans (by rw [bf];rfl)
    · simpa [output] using al

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Scan
