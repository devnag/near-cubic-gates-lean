import Proof.CaseAnalysis.RowsRawPairSeekBody
import Proof.CaseAnalysis.RowsRawAtomRead

/-! Residualization appends the original and frozen-gate atom bodies under
one polynomial delimiter. No X/C pattern is chosen from a column: the
physical output is their characteristic-two sum. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawPairCopy
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open CloseoutRowsRawPolynomialAdd
open CloseoutRowsRawPairSeek (Pair word)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boundary (emit : Bool) : Machine 5 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,
    ![none,none,if emit then some false else none,none,none],
    ![.stay,.right,if emit then .right else .stay,.stay,.stay]⟩ else none
noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine rightMachine (boundary false)) rightMachine) (boundary true)
def budget (p : Pair):=
  CloseoutRowsRawProductRow.budget [] p.1+CloseoutRowsRawProductRow.budget [] p.2+5

theorem boundary_run (emit : Bool) (C ip cp : ℕ) (index source out : List Bool) :
    Step (boundary emit) 1 (heads ip cp out) (data C index source out)
      (heads ip (cp+1) (out++if emit then [false] else []))
      (data C index source (out++if emit then [false] else [])) := by
  have hs:step (boundary emit) ⟨0,heads ip cp out,data C index source out⟩=
      some ⟨1,heads ip (cp+1) (out++if emit then [false] else []),
        data C index source (out++if emit then [false] else [])⟩:=by
    simp only [step,boundary,↓reduceIte,Option.map_some]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> cases emit <;> simp [applyAction,heads,HeadMove.apply]
    · funext i;fin_cases i <;> cases emit <;> simp [applyAction,data,heads,Streaming.write_append]
  obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem copy_run (C ip : ℕ) (index pre tail out : List Bool) (p : Pair) (hc : 1≤C) :
    Step machine (budget p) (heads ip pre.length out) (data C index (pre++word p++tail) out)
      (heads ip (pre.length+(word p).length) (out++ExtIncidence.stream (p.1++p.2)))
      (data C index (pre++word p++tail) (out++ExtIncidence.stream (p.1++p.2))) := by
  have first:=CloseoutRowsRawAtomRead.copy_run C ip index pre (ExtIncidence.stream p.2++tail) out p.1 hc
  have sep:=boundary_run false C ip (pre.length+(body p.1).length) index
    (pre++word p++tail) (out++body p.1)
  have second:=CloseoutRowsRawAtomRead.copy_run C ip index (pre++ExtIncidence.stream p.1)
    tail (out++body p.1) p.2 hc
  have last:=boundary_run true C ip ((pre++ExtIncidence.stream p.1).length+(body p.2).length)
    index (pre++word p++tail) ((out++body p.1)++body p.2)
  have leftLength:pre.length+(body p.1).length+1=(pre++ExtIncidence.stream p.1).length:=by
    simp [body,ExtIncidence.stream,Nat.add_assoc]
  simp only [Bool.false_eq_true,↓reduceIte,List.append_nil,leftLength] at sep
  simp only [↓reduceIte] at last
  simp only [word,List.append_assoc] at first sep second last
  have all:=((first.seq sep).seq second).seq last
  have cost:CloseoutRowsRawProductRow.budget [] p.1+1+1+1+
      CloseoutRowsRawProductRow.budget [] p.2+1+1=budget p:=by unfold budget;omega
  rw [cost] at all
  have finishPos:(pre++ExtIncidence.stream p.1).length+(body p.2).length+1=
      pre.length+(word p).length:=by simp [word,body,ExtIncidence.stream];omega
  rw [finishPos] at all
  have output:(out++body p.1)++body p.2++[false]=out++ExtIncidence.stream (p.1++p.2):=by
    simp [body,ExtIncidence.stream,List.flatMap_append,List.append_assoc]
  simp only [List.append_assoc] at output
  simpa only [machine,word,output,List.append_assoc] using all

theorem budget_bound (p : Pair) : budget p≤32*((word p).length+2) := by
  have left:=CloseoutRowsRawProductBudget.row_bound [] p.1
  have right:=CloseoutRowsRawProductBudget.row_bound [] p.2
  simp only [List.flatMap_nil,List.length_nil] at left right
  unfold budget word
  simp only [List.length_append]
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsRawPairCopy
