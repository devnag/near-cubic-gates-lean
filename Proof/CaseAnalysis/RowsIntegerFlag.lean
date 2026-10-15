import Proof.CaseAnalysis.RowsIntegerParse

/-! The exact signed-integer verdict is folded before workspace erasure. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerRound
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flagMachine : Machine 2 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q scanned=>if q.val=0 then
    some ⟨1,![none,some (scanned 1 && scanned 0)],fun _=>.stay⟩ else none

theorem flag_ready (bits : List Bool) (flag : Bool) :
    ReadyRun flagMachine 1 ![bits,[flag]] ![bits,[flag && readTapeBit bits 0]]:=by
  let final : Configuration 2 2:=⟨1,fun _=>0,![bits,[flag && readTapeBit bits 0]]⟩
  have h:step flagMachine (initialConfiguration flagMachine ![bits,[flag]])=some final:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,rf,rs⟩:=(Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [rf],by intro i;rw [rf],rs⟩

noncomputable def foldFlag:=RecoveryFocus.machine flagSlots flagMachine
noncomputable def folded (tapes : Fin 220→List Bool) (flag : Bool):=
  install flagSlots tapes ![tapes 211,[flag && readTapeBit (tapes 211) 0]]

theorem folded_other (tapes : Fin 220→List Bool) (flag : Bool) (i : Fin 220) (hi : i≠219) :
    folded tapes flag i=tapes i:=by
  by_cases h:i=211
  · subst i
    exact install_slot flagSlots (by decide) _ _ 0
  · exact install_other _ _ _ _ (by
      intro j;fin_cases j
      · exact Ne.symm h
      · exact Ne.symm hi)
theorem folded_flag (tapes : Fin 220→List Bool) (flag : Bool) :
    folded tapes flag 219=[flag && readTapeBit (tapes 211) 0]:=
  install_slot flagSlots (by decide) _ _ 1

theorem flag_run (cap position : ℕ) (out source : List Bool) (flag : Bool)
    (tapes : Fin 220→List Bool) (hstore : Stored cap out source flag tapes) : ∃ result,
    runFrom foldFlag 1 ⟨foldFlag.start,heads out position,tapes⟩=some result ∧
      result.steps=1 ∧ result.final.heads=heads out position ∧
      result.final.tapes=folded tapes flag ∧
      Stored cap out source (flag && readTapeBit (tapes 211) 0) result.final.tapes:=by
  obtain ⟨r,hr,rh,rt,rs⟩:=(flag_ready (tapes 211) flag).focus_at flagSlots (by decide)
    (heads out position) tapes (by
      intro i;fin_cases i
      · rfl
      · exact hstore.extra 4) (by intro i;fin_cases i <;> rfl)
  refine ⟨r,hr,rs,rh,rt,?_⟩
  rw [rt]
  change Stored _ _ _ _ (folded tapes flag)
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [folded_other _ _ _ (by
      intro h
      have hv:=congrArg Fin.val h
      have hb:=scratch_small i
      change (scratchSlots i).val=219 at hv
      omega)]
    exact hstore.scratch i
  · rw [folded_other _ _ _ (by decide)]
    exact hstore.output
  · intro i
    fin_cases i
    · rw [folded_other _ _ _ (by decide)]
      exact hstore.extra 0
    · rw [folded_other _ _ _ (by decide)]
      exact hstore.extra 1
    · rw [folded_other _ _ _ (by decide)]
      exact hstore.extra 2
    · rw [folded_other _ _ _ (by decide)]
      exact hstore.extra 3
    · exact folded_flag tapes flag

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerRound
