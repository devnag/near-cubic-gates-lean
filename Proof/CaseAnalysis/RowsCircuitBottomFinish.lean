import Proof.CaseAnalysis.RowsCircuitBottomErase

namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open LocalBitMultitape RadixSemantics RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def foldFlag:=RecoveryFocus.machine flagSlots CloseoutRowsIntegerRound.flagMachine
def directions (i : Fin 1059) : HeadMove:=if i.val=1053 then .right else .stay
def advance:=DecompositionCountPosition.move directions
def advanceTwice:=Composition.machine advance advance
noncomputable def folded:=Composition.machine foldFlag eraser
noncomputable def finish:=Composition.machine folded advanceTwice

theorem fold_run (cap core pos memberPos : ℕ) (out source membership : List Bool)
    (description wireCount : ℕ) (flag : Bool) (tapes : Fin 1059→List Bool)
    (hs : Stored cap core out source membership description wireCount flag tapes) :
    PCPOuter.Exact foldFlag 1 (heads pos memberPos out description wireCount) tapes
      (heads pos memberPos out description wireCount)
      (Function.update tapes 1054 [flag && readTapeBit (tapes 1037) 0]) := by
  obtain ⟨r,hr,rh,rt,rs⟩:=(CloseoutRowsIntegerRound.flag_ready (tapes 1037) flag).focus_at flagSlots (by decide)
    (heads pos memberPos out description wireCount) tapes
    (by intro i;fin_cases i; rfl;exact hs.extra 5) (by intro i;fin_cases i <;> rfl)
  refine ⟨r,hr,rh,?_,rs⟩
  rw [rt]
  apply HierarchyAllocation.install_eq flagSlots (by decide)
  · intro i;fin_cases i
    · exact Function.update_of_ne (by decide) _ _
    · exact Function.update_self _ _ _
  · intro i hi
    exact Function.update_of_ne (Ne.symm (hi 1)) _ _

theorem advance_run (pos memberPos : ℕ) (out : List Bool) (description wireCount : ℕ)
    (tapes : Fin 1059→List Bool) :
    PCPOuter.Exact advance 1 (heads pos memberPos out description wireCount) tapes
      (heads pos (memberPos+1) out description wireCount) tapes := by
  obtain ⟨r,hr,rf,rs⟩:=DecompositionCountPosition.move_run directions
    (heads pos memberPos out description wireCount) tapes
  refine ⟨r,hr,?_,by rw [rf],rs⟩
  rw [rf]
  funext i
  by_cases hi:i.val=1053
  · have he:i=1053:=Fin.ext hi;subst i;rfl
  · change (directions i).apply (heads pos memberPos out description wireCount i)=_
    simp only [directions,if_neg hi,HeadMove.apply,heads]

theorem advance_twice (pos memberPos : ℕ) (out : List Bool) (description wireCount : ℕ)
    (tapes : Fin 1059→List Bool) :
    PCPOuter.Exact advanceTwice 3 (heads pos memberPos out description wireCount) tapes
      (heads pos (memberPos+2) out description wireCount) tapes := by
  exact PCPOuter.exact_join (advance_run pos memberPos out description wireCount tapes)
    (advance_run pos (memberPos+1) out description wireCount tapes)

theorem finish_run (cap core pos memberPos : ℕ) (out source membership : List Bool)
    (description wireCount : ℕ) (flag : Bool) (tapes : Fin 1059→List Bool) (hc : 1 ≤ cap)
    (hs : Stored cap core out source membership description wireCount flag tapes) :
    PCPOuter.Exact finish (2*cap+10) (heads pos memberPos out description wireCount) tapes
      (heads pos (memberPos+2) out description wireCount)
      (data cap core [] out source membership description wireCount (flag && readTapeBit (tapes 1037) 0)) := by
  have first:=fold_run cap core pos memberPos out source membership description wireCount flag tapes hs
  have second:=erase_run cap core pos memberPos out source membership description wireCount
    (flag && readTapeBit (tapes 1037) 0) (Function.update tapes 1054 [flag && readTapeBit (tapes 1037) 0])
    hc (hs.flagged _)
  have last:=advance_twice pos memberPos out description wireCount
    (data cap core [] out source membership description wireCount (flag && readTapeBit (tapes 1037) 0))
  have joined:=PCPOuter.exact_join (PCPOuter.exact_join first second) last
  have ht:(1+1+(2*cap+4))+1+3=2*cap+10:=by omega
  simpa only [ht,finish,folded] using joined

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
