import Proof.CaseAnalysis.RecoveryCountResultSupport
import Proof.CaseAnalysis.CloseoutRecoveryGrammarBank
import Proof.Amplification.RecoveryQueryCellReuse

/-! Reuse the paid save/count/erase/reload worker directly after the
original fixed-count graph. An erased suffix remains the same stack backing. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedFixedFinish
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def lower (A : Fin 116→List Bool) (stack : List Bool) (i : Fin 78):=
  if i=74 then stack else A (i.castAdd 38)
def upper (A : Fin 116→List Bool) (i : Fin 38):=A (i.natAdd 78)

theorem lower_keep (A : Fin 116→List Bool) (stack : List Bool) (i : Fin 78) (hi : i≠74) :
    lower A stack i=A (i.castAdd 38) := if_neg hi

theorem clean_data (A : Fin 116→List Bool) (stack : List Bool) (z P : ℕ)
    (hs : A 74=stack++List.replicate z false) (hP : stack.length+z≤P) :
    RecoveryBoundedFixedContinue.data P (lower A stack) (upper A)=RecoveryBoundedFixedRows.stackPadded P A := by
  funext i
  refine Fin.addCases (m:=78) (n:=38) ?_ ?_ i
  · intro j
    by_cases hj : j=74
    · subst j
      change ZeroPadding.pad P stack=ZeroPadding.pad P (A 74)
      rw [hs]
      exact (RecoveryQueryCell.pad_suffix P stack z hP).symm
    · have hn : (j.castAdd 38 : Fin 116)≠74:=by
        intro he
        exact hj (Fin.ext (congrArg (fun k : Fin 116=>k.val) he))
      simp only [RecoveryBoundedFixedContinue.data,Fin.addCases_left,
        RecoveryBoundedFixedContinue.padded,RecoveryBoundedFixedContinue.capacity,if_neg hj,
        lower,RecoveryBoundedFixedRows.stackPadded,RecoveryBoundedFixedRows.stackCapacity,if_neg hn]
  · intro j
    have hn : (j.natAdd 78 : Fin 116)≠74:=by
      intro he
      have hv:=congrArg Fin.val he
      change 78+j.val=74 at hv
      omega
    simp only [RecoveryBoundedFixedContinue.data,Fin.addCases_right,upper,
      RecoveryBoundedFixedRows.stackPadded,RecoveryBoundedFixedRows.stackCapacity,if_neg hn,ZeroPadding.pad_zero]

theorem run (out stack source tail : List Bool) (A : Fin 116→List Bool) (fields : Fin 78→List Bool)
    (extraH : Fin 38→ℕ) (ref z B P : ℕ)
    (h20 : A 20=out) (h25 : A 25=List.replicate ref true) (h70 : A 70=source)
    (h73 : A 73=List.replicate B false) (h74 : A 74=stack++List.replicate z false)
    (h75 : A 75=RecoveryBoundedRowReload.word fields++tail)
    (h76 : A 76=List.replicate B true) (h77 : A 77=List.replicate (B+1) false)
    (hP : stack.length+z≤P) (hRef : 2*ref+2≤B)
    (hA : ∀ i,(A ((RecoveryBoundedRowErase.work i).castAdd 38)).length≤B)
    (hf : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B)
    (hp : (RecoveryBoundedRowReload.word fields).length≤B) :
    ∃ r,runFrom RecoveryBoundedFixedContinue.machine (RecoveryBoundedGrammarAfter.budget ref B fields)
      ⟨RecoveryBoundedFixedContinue.machine.start,RecoveryBoundedFixedContinue.heads out stack extraH,
        RecoveryBoundedFixedRows.stackPadded P A⟩=some r ∧
      r.steps≤RecoveryBoundedGrammarAfter.budget ref B fields ∧
      r.final.heads=RecoveryBoundedFixedContinue.heads out (RecoveryBoundedAddress.pushed ref stack) extraH ∧
      r.final.tapes=RecoveryBoundedFixedContinue.data P
        (RecoveryBoundedGrammarBank.ready fields (ref+1) B out (RecoveryBoundedAddress.pushed ref stack)
          (RecoveryBoundedRowReload.word fields++tail) source) (upper A) := by
  obtain ⟨r,rr,rs,rh,rt⟩:=RecoveryBoundedFixedContinue.run out stack tail (lower A stack) fields ref B P extraH (upper A)
    (by rw [lower_keep A stack 25 (by decide)];exact h25) rfl
    (by rw [lower_keep A stack 73 (by decide)];exact h73)
    (by rw [lower_keep A stack 75 (by decide)];exact h75)
    (by rw [lower_keep A stack 76 (by decide)];exact h76)
    (by rw [lower_keep A stack 77 (by decide)];exact h77) hRef
    (by intro i;rw [lower_keep A stack _ (RecoveryBoundedRowErase.work_high i 74 (by decide))];exact hA i) hf hp
  rw [clean_data A stack z P h74 hP] at rr
  refine ⟨r,rr,rs,rh,?_⟩
  rw [rt,RecoveryBoundedGrammarBank.after_ready fields (lower A stack) ref B out stack
    (RecoveryBoundedRowReload.word fields++tail) source
    (by rw [lower_keep A stack 20 (by decide)];exact h20)
    (by rw [lower_keep A stack 70 (by decide)];exact h70)
    (by rw [lower_keep A stack 73 (by decide)];exact h73)
    (by rw [lower_keep A stack 75 (by decide)];exact h75)
    (by rw [lower_keep A stack 76 (by decide)];exact h76)
    (by rw [lower_keep A stack 77 (by decide)];exact h77)]

end NearCubicWires.RepairOrdinary.RecoveryBoundedFixedFinish
