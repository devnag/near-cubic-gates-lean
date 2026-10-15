import Proof.Amplification.RecoveryTseitinNativeDrivers

/-! The cold tautology stream returns all scratch heads physically while
preserving its append cursor. Its scratch starts blank and grows only by
the checked run, so the common circuit capacity can erase and reuse it. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
open LocalBitMultitape RepairOrdinary ProjectionNormalization RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem recording_initial {t s : Nat} (p : Machine t s) (selected : Fin t→Bool) (data : Fin t→List Bool) :
    Rewind.recording (initialConfiguration p data) 0=
      initialConfiguration (MaskedReset.machine p selected) (Fin.addCases data (fun _ : Fin 1=>[])) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=t) (n:=1) (fun j=>?_) (fun j=>?_) i
    all_goals simp only [Rewind.recording,Rewind.config,initialConfiguration,Fin.addCases_left,Fin.addCases_right]
  · rfl
theorem reset_from_zero {t s : Nat} (p : Machine t s) (selected : Fin t→Bool)
    (fuel : Nat) (data : Fin t→List Bool) (base : ExecutionReceipt t s)
    (hr : run p fuel data=some base) : ∃ r,
    run (MaskedReset.machine p selected) (2*base.steps+2) (Fin.addCases data (fun _ : Fin 1=>[]))=some r ∧
      (∀ i,r.final.tapes (i.castAdd 1)=base.final.tapes i) ∧
      (∀ i,r.final.heads (i.castAdd 1)=if selected i then 0 else base.final.heads i) ∧
      r.final.tapes ((0 : Fin 1).natAdd t)=List.replicate base.steps false ∧
      r.final.heads ((0 : Fin 1).natAdd t)=0 ∧ r.steps=2*base.steps+2 := by
  obtain ⟨r,hreset,rf,rs,_rp⟩:=MaskedReset.reset_run p selected fuel (initialConfiguration p data) base hr
    (by
      intro i _hi
      have h:=SelectiveReset.prefix_head (prefix_of_run p fuel _ base hr).1 i
      simpa only [initialConfiguration,Nat.zero_add] using h)
  rw [recording_initial p selected data] at hreset
  refine ⟨r,hreset,?_,?_,?_,?_,rs⟩
  · intro i
    rw [rf]
    simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_left]
  · intro i
    rw [rf]
    simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_left]
  · rw [rf]
    simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_right]
  · rw [rf]
    simp only [SelectiveReset.finished,Rewind.config,Fin.addCases_right]

def tautSelected (i : Fin 262) := decide (i≠239)
noncomputable def tautMachine:=MaskedReset.machine RecoveryTseitinTautology.Cold.machine tautSelected
def tautInput (n : Nat) : Fin 263→List Bool :=
  Fin.addCases (m:=262) (n:=1) (motive:=fun _=>List Bool)
    (RecoveryTseitinTautology.Cold.driversInput n) (fun _=>[])
def tautBudget (n : Nat) := 2*RecoveryTseitinTautology.Cold.budget n+2
theorem taut_run (n : Nat) : ∃ r,
    run tautMachine (tautBudget n) (tautInput n)=some r ∧
      r.final.tapes 239=RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n) ∧
      r.final.heads 239=(RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n)).length ∧
      r.final.tapes 242=List.replicate n true ∧
      (∀ i : Fin 263,i≠239 → r.final.heads i=0) ∧
      (∀ i : Fin 263,i≠242 → (r.final.tapes i).length ≤ RecoveryTseitinTautology.Cold.budget n) ∧
      r.steps ≤ tautBudget n := by
  obtain ⟨base,hbase,bo,bh,_bc,_bch,br,_brh,bs⟩:=RecoveryTseitinTautology.Cold.cold_run n
  obtain ⟨r,hr,rt,rh,rl,rlh,rs⟩:=reset_from_zero RecoveryTseitinTautology.Cold.machine tautSelected _ _ base hbase
  have htime : 2*base.steps+2 ≤ tautBudget n := by unfold tautBudget; omega
  have hm:=runFrom_moreFuel tautMachine _ (tautBudget n-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le htime] at hm
  refine ⟨r,hm,(rt 239).trans bo,(rh 239).trans bh,(rt 242).trans br,?_,?_,rs.le.trans htime⟩
  · intro i
    refine Fin.addCases (m:=262) (n:=1) (fun j hj=>?_) (fun j _hj=>?_) i
    · rw [rh]
      have hn : j≠239 := by intro he; apply hj; exact congrArg (Fin.castAdd 1) he
      have hs : tautSelected j=true := decide_eq_true hn
      rw [hs]
      rfl
    · have hj0 : j=0 := Subsingleton.elim _ _
      subst j
      exact rlh
  · intro i
    refine Fin.addCases (m:=262) (n:=1) (fun j hj=>?_) (fun j _hj=>?_) i
    · rw [rt]
      have hn : j≠242 := by intro he; apply hj; exact congrArg (Fin.castAdd 1) he
      have h:=DecompositionSource.one_tape_support RecoveryTseitinTautology.Cold.machine _ _ base j 0 hbase
        (by simp only [initialConfiguration,Nat.le_refl])
        (by simp only [initialConfiguration,RecoveryTseitinTautology.Cold.driversInput,if_neg hn,List.length_nil,Nat.le_refl])
      exact h.trans (by simpa only [Nat.zero_add] using bs)
    · have hj0 : j=0 := Subsingleton.elim _ _
      subst j
      change (r.final.tapes ((0 : Fin 1).natAdd 262)).length ≤ _
      rw [rl,List.length_replicate]
      exact bs
theorem taut_forward : CursorRestore.NoLeft tautMachine (239 : Fin 263) :=
  PCPPNativeForward.masked RecoveryTseitinTautology.Cold.machine tautSelected 239 (by decide)
    RecoveryTseitinTautology.Cold.output_forward

end NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
