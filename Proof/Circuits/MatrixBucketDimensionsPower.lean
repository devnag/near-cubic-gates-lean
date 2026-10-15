import Proof.Circuits.MatrixBucketDimensionsBounds

namespace NearCubicWires.RepairOrdinary.MatrixBucketDimensions.Power
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine : Machine 22 (2+Fintype.card (RecoveryCalls.Control (WilliamsPower.sizes 10))) :=
  WilliamsPower.fullMachine 10 (by decide)
def capacities (C : ℕ) : Fin 22→ℕ := fun i => if i=0 then 0 else C
def input (c C : ℕ) : Fin 22→List Bool :=
  fun i => if i=0 then UnaryTemplate.tape c else List.replicate C false

theorem power_run (U c : ℕ) (hU : 1 ≤ U) (hc : 1 ≤ c) (hroot : c ≤ capacity U) :
    ∃ r,run machine (WilliamsPower.budget 10 c+2) (input c (scratchCapacity U))=some r ∧
      r.steps ≤ WilliamsPower.budget 10 c+2 ∧
      r.final.tapes 0=UnaryTemplate.tape c ∧
      r.final.tapes 20=ZeroPadding.pad (scratchCapacity U) (List.replicate (c^10) true) ∧
      (∀ i,r.final.heads i=0) ∧
      (∀ i,(r.final.tapes i).length ≤ scratchCapacity U) := by
  obtain ⟨base,hb,hfactor,hout,hh,hs⟩ := WilliamsPower.full_run 10 c (by decide) hc
  have hfactorIndex : WilliamsPower.factor 10=(0 : Fin 22) := by apply Fin.ext; rfl
  have houtIndex : WilliamsPower.outputTape 10 (by decide)=(20 : Fin 22) := by apply Fin.ext; rfl
  rw [hfactorIndex] at hfactor
  rw [houtIndex] at hout
  have hb' : run machine (WilliamsPower.budget 10 c+2) (WilliamsPower.input 10 c)=some base := hb
  have hbase : ∀ i,(base.final.tapes i).length ≤ scratchCapacity U := by
    have hi : ∀ i,(WilliamsPower.input 10 c i).length ≤ max (c+2) (0+1) := by
      intro i
      simp [WilliamsPower.input]
      split <;> simp [UnaryTemplate.tape]
    have hsupport := RecoveryTapeSupport.run_support (WilliamsPower.fullMachine 10 (by decide)) _ _ base hb
      (c+2) 0 (by intro i; rfl) hi
    have hcU : c ≤ U := hroot.trans (capacity_le U)
    have hinput : c+2 ≤ scratchCapacity U := by unfold scratchCapacity; omega
    have hsteps : base.steps+1 ≤ scratchCapacity U := by
      have h := power_budget U c hU hroot
      omega
    intro i
    have h := hsupport i
    omega
  obtain ⟨r,hr,hf,hsteps,_⟩ := ZeroPadding.run_config machine (capacities (scratchCapacity U)) _ _ base hb'
  have hi : ZeroPadding.config (capacities (scratchCapacity U))
      (initialConfiguration machine (WilliamsPower.input 10 c))=
      initialConfiguration machine (input c (scratchCapacity U)) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases h : i=0
      · subst i; simp [ZeroPadding.config,capacities,initialConfiguration,WilliamsPower.input,input]
      · have hv : i.val≠0 := by intro hz; apply h; exact Fin.ext hz
        simp [ZeroPadding.config,capacities,initialConfiguration,WilliamsPower.input,input,h,hv,ZeroPadding.pad]
  rw [hi] at hr
  refine ⟨r,hr,hsteps.trans_le hs,?_,?_,?_,?_⟩
  · rw [hf]
    simpa [ZeroPadding.config,capacities] using hfactor
  · rw [hf]
    change ZeroPadding.pad (scratchCapacity U) (base.final.tapes (20 : Fin 22))=_
    exact congrArg (ZeroPadding.pad (scratchCapacity U)) hout
  · intro i; rw [hf]; exact hh i
  · intro i
    rw [hf]
    have h := hbase i
    by_cases hi : i=0
    · subst i; simpa [ZeroPadding.config,capacities] using h
    · simp only [ZeroPadding.config,capacities,hi,if_false,ZeroPadding.pad,List.length_append,List.length_replicate]
      omega

end NearCubicWires.RepairOrdinary.MatrixBucketDimensions.Power
