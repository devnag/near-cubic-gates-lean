import Proof.PCP.PCPPNativeResources
import Proof.PCP.PCPPNativeQueryRun

/-! Physical resource output slots are shared with the cold query caller.
Only its descriptor and original stream are loaded in the disjoint bank. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeResourceQuery
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def resourceSlots (i : Fin 95) : Fin 275 := i.castAdd 180
def querySlots (i : Fin 178) : Fin 275 :=
  if i=0 then 95 else if i=4 then 42 else if i=120 then 62 else if i=169 then 84
  else if i=171 then 96 else if i=174 then 18 else if i=175 then 0 else ⟨97+i.val,by omega⟩
theorem resource_injective : Function.Injective resourceSlots := by decide
theorem query_injective : Function.Injective querySlots := by decide
def input (bits fields : List Bool) (R Q s M Lq Lc : ℕ) (i : Fin 275) : List Bool :=
  if h : i.val<95 then PCPPNativeResources.input R Q s M Lq Lc ⟨i.val,h⟩
  else if i=95 then bits else if i=96 then fields else []
noncomputable def prepared (bits fields : List Bool) (R Q s M Lq Lc : ℕ)
    (caps : Fin 95 → List Bool) := install resourceSlots (input bits fields R Q s M Lq Lc) caps
noncomputable def first := RecoveryFocus.machine resourceSlots PCPPNativeResources.machine
noncomputable def second := RecoveryFocus.machine querySlots PCPPNativeQueryCold.queryMachine
noncomputable def machine := Composition.machine first second
def budget (R Q s M Lq Lc : ℕ) := PCPPNativeResources.budget R Q s M Lq Lc+1+
  PCPPNativeQueryCold.queryBudget R Q (PCPPNativeCapacityReady.G (PCPPNativeResources.W R Q s M Lq Lc))

theorem resource_input (bits fields : List Bool) (R Q s M Lq Lc : ℕ) (i : Fin 95) :
    input bits fields R Q s M Lq Lc (resourceSlots i)=PCPPNativeResources.input R Q s M Lq Lc i := by
  simp [input,resourceSlots]
theorem prepared_low (bits fields : List Bool) (R Q s M Lq Lc : ℕ)
    (caps : Fin 95 → List Bool) (i : Fin 95) :
    prepared bits fields R Q s M Lq Lc caps (resourceSlots i)=caps i :=
  install_slot _ resource_injective _ _ _
theorem prepared_high (bits fields : List Bool) (R Q s M Lq Lc : ℕ)
    (caps : Fin 95 → List Bool) (i : Fin 275) (hi : 95 ≤ i.val) :
    prepared bits fields R Q s M Lq Lc caps i=input bits fields R Q s M Lq Lc i := by
  apply install_other
  intro j he
  have hv := congrArg (fun i : Fin 275 => i.val) he
  change j.val=i.val at hv
  omega

theorem query_input (bits fields : List Bool) (R Q s M Lq Lc C F G : ℕ)
    (caps : Fin 95 → List Bool) (hC : caps 42=List.replicate C true)
    (hF : caps 62=List.replicate F true) (hG : caps 84=List.replicate G true)
    (hQ : caps 0=List.replicate Q true) (hR : caps 18=List.replicate R true) (i : Fin 178) :
    prepared bits fields R Q s M Lq Lc caps (querySlots i)=
      PCPPNativeQueryCold.data bits fields R Q C F G 0 i := by
  by_cases h0 : i=0
  · subst i
    exact prepared_high bits fields R Q s M Lq Lc caps 95 (by decide)
  by_cases h4 : i=4
  · subst i
    exact (prepared_low bits fields R Q s M Lq Lc caps 42).trans hC
  by_cases h120 : i=120
  · subst i
    exact (prepared_low bits fields R Q s M Lq Lc caps 62).trans hF
  by_cases h169 : i=169
  · subst i
    exact (prepared_low bits fields R Q s M Lq Lc caps 84).trans hG
  by_cases h171 : i=171
  · subst i
    exact prepared_high bits fields R Q s M Lq Lc caps 96 (by decide)
  by_cases h174 : i=174
  · subst i
    exact (prepared_low bits fields R Q s M Lq Lc caps 18).trans hR
  by_cases h175 : i=175
  · subst i
    exact (prepared_low bits fields R Q s M Lq Lc caps 0).trans hQ
  have hs : querySlots i=⟨97+i.val,by omega⟩ := by
    simp [querySlots,h0,h4,h120,h169,h171,h174,h175]
  rw [prepared_high bits fields R Q s M Lq Lc caps (querySlots i) (by rw [hs]; dsimp; omega)]
  have h95 : querySlots i≠95 := by rw [hs]; intro he; have hv := congrArg Fin.val he; dsimp at hv; omega
  have h96 : querySlots i≠96 := by rw [hs]; intro he; have hv := congrArg Fin.val he; dsimp at hv; omega
  have hlow : ¬(querySlots i).val<95 := by rw [hs]; dsimp; omega
  rw [input,dif_neg hlow,if_neg h95,if_neg h96]
  by_cases hi : i.val<171
  · have j0 : (⟨i.val,hi⟩ : Fin 171)≠0 := by
      intro he; apply h0; apply Fin.ext; exact congrArg (fun j : Fin 171 => j.val) he
    have j4 : (⟨i.val,hi⟩ : Fin 171)≠4 := by
      intro he; apply h4; apply Fin.ext; exact congrArg (fun j : Fin 171 => j.val) he
    have j120 : (⟨i.val,hi⟩ : Fin 171)≠120 := by
      intro he; apply h120; apply Fin.ext; exact congrArg (fun j : Fin 171 => j.val) he
    have j169 : (⟨i.val,hi⟩ : Fin 171)≠169 := by
      intro he; apply h169; apply Fin.ext; exact congrArg (fun j : Fin 171 => j.val) he
    have hin : i=Fin.castAdd 7 (⟨i.val,hi⟩ : Fin 171) := rfl
    rw [hin]
    simp only [PCPPNativeQueryCold.data,Fin.addCases_left,ite_true]
    simp only [PCPPNativeQueryAllocate.input,j0,j4,j120,j169,ite_false]
  · have hin : i=(⟨i.val-171,by omega⟩ : Fin 7).natAdd 171 := by apply Fin.ext; dsimp; omega
    rw [hin] at h171 h174 h175 ⊢
    generalize (⟨i.val-171,by omega⟩ : Fin 7)=j at *
    fin_cases j <;> simp_all [PCPPNativeQueryCold.data,Fin.addCases]

end NearCubicWires.RepairOrdinary.PCPPNativeResourceQuery
