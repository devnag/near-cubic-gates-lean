import Proof.CaseAnalysis.CommonProgramPorts

/-! The actual common program prints canonical false after a rejected
prefix. Both the prefix and fixed-word writer execute and are charged. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem false_injective (p : Parameters) : Function.Injective (falseSlot p):=
  CloseoutCommonPortBank.injective _ _ (fun i j _=>Subsingleton.elim i j)
theorem false_output (p : Parameters) : falseSlot p 0=(ports p).outputTape:=by
  change falseSlot p (falseLocal 0)=_
  rw [falseSlot,CloseoutCommonPortBank.shared_slot _ _ (by decide : Function.Injective falseLocal)]
  rfl
theorem false_scratch (p : Parameters) : falseSlot p 1=(1 : Fin 2).natAdd (n4 p):=
  CloseoutCommonPortBank.fresh_slot _ _ _ (by decide)

private theorem blank_after {t u : ℕ} (slot : Fin t→Fin u)
    (bits : List Bool) (out : Fin t→List Bool) (i : Fin u)
    (hv : i.val≠0) (away : ∀ j,slot j≠i) :
    install slot (fun z=>if z.val=0 then frame bits else []) out i=[]:=by
  rw [install_other _ _ _ _ away,if_neg hv]

theorem false_blank (p : Parameters) (bits : List Bool)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (j : Fin 2) :
    install (prefixSlot p) (input p bits) out (falseSlot p j)=[]:=by
  have hb:=(prefixProgram p).base.twoTapes
  have boundary:(prefixProgram p).base.tapeCount<n4 p:=by
    unfold n4 n3 n2 n1 n0
    omega
  have hval:(falseSlot p j).val=(if j=0 then (prefixProgram p).base.tapeCount else n4 p+1):=by
    fin_cases j
    · change (falseSlot p (0 : Fin 2)).val=(prefixProgram p).base.tapeCount
      exact congrArg (fun z : Fin (tapes p)=>z.val) (false_output p)
    · change (falseSlot p (1 : Fin 2)).val=n4 p+1
      exact congrArg (fun z : Fin (tapes p)=>z.val) (false_scratch p)
  apply blank_after (prefixSlot p) bits out (falseSlot p j)
  · rw [hval]
    split_ifs <;>omega
  · intro i he
    have hv:=congrArg (fun z : Fin (tapes p)=>z.val) he
    have hi:=i.isLt
    change i.val=(falseSlot p j).val at hv
    rw [hval] at hv
    split_ifs at hv <;>omega

theorem inactive_ready (p : Parameters) (bits : List Bool) (fuel : ℕ)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool)
    (actual : Ready RecoveryOracle.correctedSat (prefixProgram p) fuel
      (CloseoutCommonPrefix.input (work p) p.refuter p.k bits) out)
    (flag : readTapeBit (out (CloseoutCommonPrefix.firstSlots (work p) p.refuter p.k
      (CloseoutRetainedRefuter.old p.refuter (CloseoutSchedule.RefuterPrefix.flagPort (work p))))) 0=false) :
    ∃ final,Ready RecoveryOracle.correctedSat (program p) (fuel+6) (input p bits) final ∧
      final (ports p).outputTape=frame false.toNat.bits:=by
  let mid:=install (prefixSlot p) (input p bits) out
  have hp:=actual.focus (ports p) (prefixSlot p) (prefix_injective p) rfl (input p bits) (fun _=>rfl)
  have hflag:readTapeBit (mid (liveFlag p)) 0=false:=by
    change readTapeBit (install (prefixSlot p) (input p bits) out (prefixSlot p _)) 0=false
    rw [install_slot _ (prefix_injective p)]
    exact flag
  have hf:ReadyRun (RecoveryFocus.machine (falseSlot p) (HierarchyFixedWord.machine [false])) 4 mid
      (install (falseSlot p) mid ![[false],[false]]):=
    (HierarchyFixedWord.word_ready [false]).focus (falseSlot p) (false_injective p) mid (false_blank p bits out)
  have ta:=hp.call (ports p) (pieces p) 0 (next p) 0 5 (by
    intro q
    change some (if readTapeBit (mid (liveFlag p)) 0 then (1 : Fin 6) else 5)=some 5
    rw [hflag]
    rfl)
  have tb:=(Ready.ordinary (o:=RecoveryOracle.correctedSat) (ports p) hf).stop
    (ports p) (pieces p) 0 (next p) 5 (by intro q;rfl)
  have trace:=trans ta tb
  have hc:(fuel+1)+(4+1)=fuel+6:=by omega
  rw [hc] at trace
  refine ⟨_,⟨_,trace,?_,fun _=>rfl,rfl⟩,?_⟩
  · simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · rw [←false_output]
    exact install_slot (falseSlot p) (false_injective p) mid ![[false],[false]] 0

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
