import Proof.CaseAnalysis.WitnessMassDimensions

/-! The complete common mass policy is physically produced once from the
exact paid term and coefficient caps, including its reusable erase driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassPolicy
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old (i : Fin 10) : Fin 25:=i.castAdd 15
def slots (i : Fin 15) : Fin 25:=⟨if i.val=0 then 8 else 10+i.val,by split_ifs <;> omega⟩
def first:=RecoveryFocus.machine old MassWidth.machine
def second:=RecoveryFocus.machine slots MassDimensions.machine
def machine:=Composition.machine first second
def input (T b : ℕ) (i : Fin 25):=
  if i.val=0 then List.replicate T true else if i.val=1 then List.replicate b true else []
def budget (T b : ℕ):=MassWidth.budget T b+1+MassDimensions.budget (CompetitorSumWidth.width T b)
theorem old_injective : Function.Injective old:=by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 25=>k.val) h)
theorem slots_injective : Function.Injective slots:=by
  intro i j h
  have hv:=congrArg (fun k : Fin 25=>k.val) h
  dsimp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> omega

theorem policy_run (T b : ℕ) : ∃ output,
    ClockJoin.ReadyRun machine (budget T b) (input T b) output ∧
      output 0=List.replicate T true ∧ output 1=List.replicate b true ∧
      output 8=List.replicate (CompetitorSumWidth.width T b) true ∧
      output 16=List.replicate (CompetitorRationalDecision.width (CompetitorSumWidth.width T b)) true ∧
      output 23=List.replicate (CompetitorReusableDecision.capacity (CompetitorSumWidth.width T b)) true:=by
  obtain ⟨w,hw,w0,w1,w8⟩:=MassWidth.width_run T b
  have hwf:=hw.focus old old_injective (input T b) (by intro i;fin_cases i <;> rfl)
  let bank:=install old (input T b) w
  have keep (i : Fin 10) : bank (old i)=w i:=install_slot _ old_injective _ _ _
  have fresh (i : Fin 25) (hi : 10 ≤ i.val) : bank i=[]:=by
    rw [show bank=install old _ _ by rfl,install_other _ _ _ _ (by
      intro j h
      have hv:=congrArg (fun k : Fin 25=>k.val) h
      change j.val=i.val at hv
      omega)]
    simp only [input,if_neg (show i.val≠0 by omega),if_neg (show i.val≠1 by omega)]
  obtain ⟨d,hd,d0,d6,d13⟩:=MassDimensions.dimensions_run (CompetitorSumWidth.width T b)
  have hdf:=hd.focus slots slots_injective bank (by
    intro i
    by_cases h0:i=0
    · subst i;exact (keep 8).trans w8
    have hv:i.val≠0:=fun h=>h0 (Fin.ext h)
    rw [MassDimensions.input,if_neg h0]
    exact fresh _ (by simp only [slots,if_neg hv];omega))
  refine ⟨_,ClockJoin.join first second _ _ _ _ _ hwf hdf,?_,?_,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide)]
    exact (keep 0).trans w0
  · rw [install_other _ _ _ _ (by decide)]
    exact (keep 1).trans w1
  · exact (install_slot slots slots_injective _ d 0).trans d0
  · exact (install_slot slots slots_injective _ d 6).trans d6
  · exact (install_slot slots slots_injective _ d 13).trans d13

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassPolicy
