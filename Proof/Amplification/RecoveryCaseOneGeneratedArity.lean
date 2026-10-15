import Proof.Amplification.RecoveryCaseOneAddressCrop

/-! The generated schema supplies its own unary arity through the existing
physical header parser. The complete head return is paid. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneGeneratedArity
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def machine := Rewind.machine GeneratedAmplifier.Prepared.machine
def input (word : List Bool) : Fin 14→List Bool :=
  Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool) (GeneratedAmplifier.Prepared.input word) (fun _=>[])
def budget (n : Nat) (tail : List Bool) := 2*GeneratedAmplifier.Prepared.budget n tail+2

theorem input_lookup (word : List Bool) (i : Fin 14) :
    input word i=if i.val=0 then frame word else [] := by
  refine Fin.addCases (m:=13) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [input,Fin.addCases_left,GeneratedAmplifier.Prepared.input,Fin.val_castAdd]
    simp only [Fin.ext_iff,Fin.val_zero]
    rfl
  · simp only [input,Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]

theorem ready (n : Nat) (tail : List Bool) :
    ∃ out,ClockJoin.ReadyRun machine (budget n tail) (input (frame n.bits++tail)) out ∧
      out 12=UnaryTemplate.tape n := by
  obtain ⟨base,hbase,hsteps,_h1,_hh1,_h3,_hh3,hout,_hhead⟩ := GeneratedAmplifier.Prepared.prepared_run n tail
  obtain ⟨r,hr,rt,rh,rs,_⟩ := Rewind.reset_run _ _ _ base hbase
  have hb : 2*base.steps+2≤budget n tail := by unfold budget; omega
  have hm:=run_moreFuel machine _ (budget n tail-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at hm
  exact ⟨r.final.tapes,⟨r,hm,rfl,rh,rs.le.trans hb⟩,(rt 12).trans hout⟩

end
end NearCubicWires.RepairSource.RecoveryCaseOneGeneratedArity
