import Proof.CaseAnalysis.RowsRawProductFields

/-! An actual raw left/right monomial pair appends their ordered product.
The left cursor and paid log are reusable; the right cursor consumes exactly
one original monomial. Repeated variable occurrences are preserved. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawProductPair
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsRawProductFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine (mark true true) leftMachine) rightMachine) (mark false false)
def budget (left right : List ℕ):=
  2*(left.flatMap ExtIncidence.block).length+(right.flatMap ExtIncidence.block).length+10

theorem pair_run (C : ℕ) (left right : List ℕ) (lp lt rp rt out : List Bool)
    (hc : (left.flatMap ExtIncidence.block).length+1≤C) :
    Step machine (budget left right) (heads lp.length rp.length out)
      (data C (lp++left.flatMap ExtIncidence.block++false::lt) (rp++ExtIncidence.monomialWord right++rt) out)
      (heads lp.length (rp.length+(ExtIncidence.monomialWord right).length)
        (out++ExtIncidence.monomialWord (left++right)))
      (data C (lp++left.flatMap ExtIncidence.block++false::lt) (rp++ExtIncidence.monomialWord right++rt)
        (out++ExtIncidence.monomialWord (left++right))) := by
  let srcL:=lp++left.flatMap ExtIncidence.block++false::lt
  let srcR:=rp++ExtIncidence.monomialWord right++rt
  have first:=mark_run true true C lp.length rp.length srcL srcR out
  have second:=left_run C left lp lt srcR (out++[true]) (rp.length+1) hc
  have third:=right_run C right (rp++[true]) rt srcL
    ((out++[true])++left.flatMap ExtIncidence.block) lp.length
  have source:(rp++[true])++right.flatMap ExtIncidence.block++false::rt=srcR:=by
    simp [srcR,ExtIncidence.monomialWord,List.append_assoc]
  rw [source] at third
  simp only [List.length_append,List.length_singleton] at third
  have last:=mark_run false false C lp.length (rp.length+1+(right.flatMap ExtIncidence.block).length+1)
    srcL srcR (((out++[true])++left.flatMap ExtIncidence.block)++right.flatMap ExtIncidence.block)
  have all:=((first.seq second).seq third).seq last
  have time:1+1+CloseoutRowsRawMonomialReturn.budget left+1+
      ((right.flatMap ExtIncidence.block).length+1)+1+1=budget left right:=by
    unfold budget CloseoutRowsRawMonomialReturn.budget
    omega
  rw [time] at all
  have word:(((out++[true])++left.flatMap ExtIncidence.block)++right.flatMap ExtIncidence.block)++[false]=
      out++ExtIncidence.monomialWord (left++right):=by
    simp [ExtIncidence.monomialWord,List.flatMap_append,List.append_assoc]
  apply all.congr
  · funext i;fin_cases i
    · rfl
    · change rp.length+1+(right.flatMap ExtIncidence.block).length+1+0=
        rp.length+(ExtIncidence.monomialWord right).length
      rw [ExtIncidence.monomialWord_length]
      omega
    · exact congrArg List.length word
    · rfl
  · funext i;fin_cases i
    · rfl
    · rfl
    · exact word
    · rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsRawProductPair
