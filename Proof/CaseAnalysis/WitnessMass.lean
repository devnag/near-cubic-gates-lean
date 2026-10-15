import Proof.CaseAnalysis.WitnessTermRead
import Proof.CaseAnalysis.WitnessMassPolicy

/-! The exact paid T and b produce the reusable mass widths, driver and
initial zero accumulator in one cold run. No mass-record stream is supplied. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassCold
open LocalBitMultitape RecoveryRootRound CompetitorSumFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def policySlots (i : Fin 25) : Fin 119:=i.castAdd 94
def nativeSlots (i : Fin 94) : Fin 119:=⟨if i.val=6 then 16 else if i.val=84 then 8
  else if i.val=90 then 23 else 25+i.val,by split_ifs <;> omega⟩
theorem policy_injective : Function.Injective policySlots:=by
  intro i j h;exact Fin.ext (congrArg (fun k : Fin 119=>k.val) h)
theorem native_injective : Function.Injective nativeSlots:=by
  intro i j h
  have hv:=congrArg Fin.val h
  dsimp only [nativeSlots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega
noncomputable def policy:=RecoveryFocus.machine policySlots MassPolicy.machine
noncomputable def boot:=RecoveryFocus.machine nativeSlots bootstrapProgram
noncomputable def machine:=Composition.machine policy boot
def input (T b : ℕ) (i : Fin 119):=
  if i.val=0 then List.replicate T true else if i.val=1 then List.replicate b true else []
def project (tapes : Fin 119→List Bool) (i : Fin 94):=tapes (nativeSlots i)
def budget (T b : ℕ):=MassPolicy.budget T b+1+bootstrapBudget (CompetitorSumWidth.width T b)

theorem cold_run (T b : ℕ) : ∃ output,
    ClockJoin.ReadyRun machine (budget T b) (input T b) output ∧
      output 0=List.replicate T true ∧ output 1=List.replicate b true ∧
      Store (CompetitorSumWidth.width T b) CompetitorSumWidth.zero [] (project output):=by
  let B:=CompetitorSumWidth.width T b
  have hB:1≤B:=by unfold B CompetitorSumWidth.width;nlinarith
  obtain ⟨p,hp,p0,p1,p8,p16,p23⟩:=MassPolicy.policy_run T b
  have hpf:=hp.focus policySlots policy_injective (input T b) (by intro i;rfl)
  let bank:=install policySlots (input T b) p
  have keep (i : Fin 25) : bank (policySlots i)=p i:=install_slot _ policy_injective _ _ _
  have fresh (i : Fin 119) (hi : 25 ≤ i.val) : bank i=[]:=by
    rw [show bank=install _ _ _ by rfl,install_other _ _ _ _ (by
      intro j h;have hv:=congrArg Fin.val h;change j.val=i.val at hv;omega)]
    simp only [input,if_neg (show i.val≠0 by omega),if_neg (show i.val≠1 by omega)]
  obtain ⟨out,hr,hstore⟩:=bootstrap_run B [] hB
  have hf:=hr.focus nativeSlots native_injective bank (by
    intro i
    unfold coldInput
    by_cases h6:i.val=6
    · rw [if_pos h6]
      have he:i=6:=Fin.ext h6
      subst i;exact (keep 16).trans p16
    rw [if_neg h6]
    by_cases h84:i.val=84
    · rw [if_pos h84]
      have he:i=84:=Fin.ext h84
      subst i;exact (keep 8).trans p8
    rw [if_neg h84]
    by_cases h90:i.val=90
    · have he:i=90:=Fin.ext h90
      subst i;exact (keep 23).trans p23
    have hfr:=fresh (nativeSlots i) (by simp only [nativeSlots,if_neg h6,if_neg h84,if_neg h90];omega)
    simp only [if_neg h90]
    split_ifs <;> exact hfr)
  refine ⟨_,ClockJoin.join policy boot _ _ _ _ _ hpf hf,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by
      intro i h;have hv:=congrArg Fin.val h;dsimp only [nativeSlots] at hv;split_ifs at hv <;> omega)]
    exact (keep 0).trans p0
  · rw [install_other _ _ _ _ (by
      intro i h;have hv:=congrArg Fin.val h;dsimp only [nativeSlots] at hv;split_ifs at hv <;> omega)]
    exact (keep 1).trans p1
  · have he:project (install nativeSlots bank out)=out:=by
      funext i;exact install_slot _ native_injective _ _ _
    rw [he]
    exact hstore

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassCold
