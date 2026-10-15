import Proof.Hierarchy.CompetitorMonomialTargetWidth

/-! The exact coefficient-normalization denominator is physically widened
to the same common scalar width as every other record in the whole fold. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorRationalDecision CompetitorMonomialProducts CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outer (i : Fin 75) : Fin 79 := i.castAdd 4
def targetHeads (out : List Bool) : Fin 79 → ℕ := fun i => if i.val=74 then out.length else 0
def targetInput (b t : ℕ) (q : ℚ) (count denominator : ℕ) (pre : List Bool) : Fin 79 → List Bool :=
  Fin.addCases (m := 75) (n := 4) (motive := fun _ => List Bool) (input b t q count denominator pre)
    ![List.replicate t true,[],[],[]]
def denominatorSlots : Fin 5 → Fin 79 := ![75,38,76,77,78]
noncomputable def prefixProgram := RecoveryFocus.machine outer prepareProgram
noncomputable def denominatorProgram := RecoveryFocus.machine denominatorSlots ClockNormalize.machine
noncomputable def targetProgram := Composition.machine prefixProgram denominatorProgram
def targetBudget (b t : ℕ) := prepareBudget b t+4*t+5

theorem outer_injective : Function.Injective outer := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 79 => a.val) h)
theorem outer_other (j : Fin 75) (i : Fin 79) (hi : 75 ≤ i.val) : outer j≠i := by
  intro h
  have hv := congrArg (fun a : Fin 79 => a.val) h
  change j.val=i.val at hv
  omega

theorem target_run (b t : ℕ) (q : ℚ) (count denominator : ℕ) (pre : List Bool)
    (hp : positive q<2^b) (hn : negative q<2^b) (hq : q.den<2^b)
    (hc : count<2^b) (hd : denominator<2^b) (htarget : width b≤t) :
    ∃ r out,runFrom targetProgram (targetBudget b t)
        (RecoveryCalls.restarted targetProgram (targetHeads pre) (targetInput b t q count denominator pre))=some r ∧
      r.steps≤targetBudget b t ∧ r.final.heads=targetHeads pre ∧ r.final.tapes=out ∧
      out 68=frame (binary (width t) (contribution q count denominator).positive) ∧
      out 71=frame (binary (width t) (contribution q count denominator).negative) ∧
      out 76=frame (binary t (contribution q count denominator).denominator) ∧
      out 70=List.replicate (2*width t+1) false ∧ out 74=pre := by
  obtain ⟨base,prepared,hbase,hbs,hbh,hbt,hpos,hneg,hden,hcounter,hpre⟩ :=
    prepare_run b t q count denominator pre hp hn hq hc hd htarget
  let ambient := targetInput b t q count denominator pre
  obtain ⟨first,hfirst,hff,hfs⟩ := RecoveryFocus.run_config outer outer_injective prepareProgram
    (targetHeads pre) ambient _ _ base hbase
  have hi : RecoveryFocus.config outer (targetHeads pre) ambient
      (RecoveryCalls.restarted prepareProgram (heads pre) (input b t q count denominator pre))=
      RecoveryCalls.restarted prefixProgram (targetHeads pre) ambient := by
    apply configuration_ext
    · rfl
    · funext i
      cases hh : RecoveryFocus.pick outer i with
      | none => simp [RecoveryFocus.config,hh,RecoveryCalls.restarted]
      | some j =>
        have he := RecoveryFocus.slot_of_pick outer hh
        simp only [RecoveryFocus.config,hh,RecoveryCalls.restarted]
        change targetHeads pre (outer j)=targetHeads pre i
        exact congrArg (targetHeads pre) he
    · exact install_existing outer ambient (input b t q count denominator pre)
        (by intro i; simp [ambient,targetInput,outer])
  rw [hi] at hfirst
  have hfh : first.final.heads=targetHeads pre := by
    rw [hff]
    funext i
    cases hh : RecoveryFocus.pick outer i with
    | none => simp [RecoveryFocus.config,hh]
    | some j =>
      have he := RecoveryFocus.slot_of_pick outer hh
      simp only [RecoveryFocus.config,hh,hbh]
      change targetHeads pre (outer j)=targetHeads pre i
      exact congrArg (targetHeads pre) he
  let wide := install outer ambient prepared
  have hft : first.final.tapes=wide := by rw [hff]; change install outer ambient base.final.tapes=wide; rw [hbt]
  obtain ⟨denRun,hdRun,_,_,hd2,_,_,hdh,hds⟩ := ClockScalarFields.scalar_run t
    (binary (width b) (contribution q count denominator).denominator) (by simpa using htarget)
  have hdenFit : (contribution q count denominator).denominator<2^width b := product_fit b _ _ hq hd
  rw [binary_value (width b) (contribution q count denominator).denominator hdenFit] at hd2
  have denReady : ClockJoin.ReadyRun ClockNormalize.machine (4*t+4)
      (ClockNormalize.input t (binary (width b) (contribution q count denominator).denominator)) denRun.final.tapes :=
    ⟨denRun,hdRun,rfl,hdh,hds.le⟩
  have hdh' : ∀ i,targetHeads pre (denominatorSlots i)=0 := by intro i; fin_cases i <;> rfl
  have hdt : ∀ i,wide (denominatorSlots i)=ClockNormalize.input t
      (binary (width b) (contribution q count denominator).denominator) i := by
    intro i
    fin_cases i
    · exact install_other outer _ _ 75 (fun j => outer_other j 75 (by decide))
    · exact (install_slot outer outer_injective _ prepared 38).trans hden
    · exact install_other outer _ _ 76 (fun j => outer_other j 76 (by decide))
    · exact install_other outer _ _ 77 (fun j => outer_other j 77 (by decide))
    · exact install_other outer _ _ 78 (fun j => outer_other j 78 (by decide))
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := bounded_focused_run denominatorSlots (by decide) _ _ _ denReady
    (targetHeads pre) wide hdh' hdt
  have he : Composition.restart first.final denominatorProgram.start=RecoveryCalls.restarted denominatorProgram (targetHeads pre) wide := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom denominatorProgram (4*t+4) (Composition.restart first.final denominatorProgram.start)=some last := by
    rw [he]
    exact hlast
  have hall := Composition.run_join prefixProgram denominatorProgram _ _ _ first last hfirst hl'
  have hcost : prepareBudget b t+1+(4*t+4)=targetBudget b t := by unfold targetBudget; omega
  rw [hcost] at hall
  refine ⟨Composition.joinedReceipt first last,install denominatorSlots wide denRun.final.tapes,hall,?_,hlh,hlt,?_,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps≤targetBudget b t
    omega
  · exact (install_other denominatorSlots _ _ 68 (by decide)).trans ((install_slot outer outer_injective _ prepared 68).trans hpos)
  · exact (install_other denominatorSlots _ _ 71 (by decide)).trans ((install_slot outer outer_injective _ prepared 71).trans hneg)
  · exact (install_slot denominatorSlots (by decide) _ denRun.final.tapes 2).trans hd2
  · exact (install_other denominatorSlots _ _ 70 (by decide)).trans ((install_slot outer outer_injective _ prepared 70).trans hcounter)
  · exact (install_other denominatorSlots _ _ 74 (by decide)).trans ((install_slot outer outer_injective _ prepared 74).trans hpre)

end NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
