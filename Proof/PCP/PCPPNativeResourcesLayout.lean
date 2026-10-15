import Proof.PCP.PCPPNativeEnvelope

/-! Physical native count, envelope and common-capacity caller. Its six
inputs are retained raw hierarchy/oracle counts and measured stream bytes. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeResources
open LocalBitMultitape RecoveryRootRound RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countSlots (i : Fin 18) : Fin 95 := i.castAdd 77
def envelopeSlots (i : Fin 20) : Fin 95 :=
  if i=0 then 18 else if i=1 then 0 else if i=2 then 16 else if i=3 then 4
  else if i=4 then 19 else if i=5 then 20 else ⟨15+i.val,by omega⟩
def capacitySlots (i : Fin 61) : Fin 95 := if i=0 then 33 else ⟨34+i.val,by omega⟩
theorem count_injective : Function.Injective countSlots := by decide
theorem envelope_injective : Function.Injective envelopeSlots := by decide
theorem capacity_injective : Function.Injective capacitySlots := by decide
def input (R Q s M Lq Lc : ℕ) (i : Fin 95) : List Bool :=
  if i=0 then List.replicate Q true else if i=1 then List.replicate s true
  else if i=2 then List.replicate M true else if i=18 then List.replicate R true
  else if i=19 then List.replicate Lq true else if i=20 then List.replicate Lc true else []
def W (R Q s M Lq Lc : ℕ) := PCPPNativeEnvelope.value R Q
  (PCPPNativeCount.nativeSize Q s M) (PCPPNativeCount.stride s) Lq Lc
noncomputable def counted (R Q s M Lq Lc : ℕ) :=
  install countSlots (input R Q s M Lq Lc) (PCPPNativeCount.data Q s M 7)
noncomputable def measured (R Q s M Lq Lc : ℕ) := install envelopeSlots (counted R Q s M Lq Lc)
  (PCPPNativeEnvelope.data R Q (PCPPNativeCount.nativeSize Q s M) (PCPPNativeCount.stride s) Lq Lc 7)
noncomputable def first := RecoveryFocus.machine countSlots PCPPNativeCount.machine
noncomputable def second := RecoveryFocus.machine envelopeSlots PCPPNativeEnvelope.machine
noncomputable def third := RecoveryFocus.machine capacitySlots (PCPPNativeCapacityCold.machine 2 16384)
noncomputable def machine := Composition.machine (Composition.machine first second) third
def budget (R Q s M Lq Lc : ℕ) := PCPPNativeCount.budget Q s M+1+
  PCPPNativeEnvelope.budget R Q (PCPPNativeCount.nativeSize Q s M) (PCPPNativeCount.stride s) Lq Lc+1+
  PCPPNativeCapacityCold.budget 2 16384 (W R Q s M Lq Lc)

theorem count_input (R Q s M Lq Lc : ℕ) (i : Fin 18) :
    input R Q s M Lq Lc (countSlots i)=PCPPNativeCount.data Q s M 0 i := by
  fin_cases i <;> rfl
theorem counted_low (R Q s M Lq Lc : ℕ) (i : Fin 18) :
    counted R Q s M Lq Lc (countSlots i)=PCPPNativeCount.data Q s M 7 i :=
  install_slot _ count_injective _ _ _
theorem counted_high (R Q s M Lq Lc : ℕ) (i : Fin 95) (hi : 18 ≤ i.val) :
    counted R Q s M Lq Lc i=input R Q s M Lq Lc i := by
  exact install_other _ _ _ _ (by
    intro j he
    have h := congrArg Fin.val he
    have hj := j.isLt
    change j.val=i.val at h
    omega)
theorem envelope_input (R Q s M Lq Lc : ℕ) (i : Fin 20) :
    counted R Q s M Lq Lc (envelopeSlots i)=
      PCPPNativeEnvelope.data R Q (PCPPNativeCount.nativeSize Q s M) (PCPPNativeCount.stride s) Lq Lc 0 i := by
  fin_cases i
  · exact counted_high R Q s M Lq Lc 18 (by decide)
  · exact counted_low R Q s M Lq Lc 0
  · exact counted_low R Q s M Lq Lc 16
  · exact counted_low R Q s M Lq Lc 4
  · exact counted_high R Q s M Lq Lc 19 (by decide)
  · exact counted_high R Q s M Lq Lc 20 (by decide)
  all_goals exact counted_high R Q s M Lq Lc _ (by decide)

theorem measured_slot (R Q s M Lq Lc : ℕ) (i : Fin 20) :
    measured R Q s M Lq Lc (envelopeSlots i)=
      PCPPNativeEnvelope.data R Q (PCPPNativeCount.nativeSize Q s M) (PCPPNativeCount.stride s) Lq Lc 7 i :=
  install_slot _ envelope_injective _ _ _
theorem measured_high (R Q s M Lq Lc : ℕ) (i : Fin 95) (hi : 35 ≤ i.val) :
    measured R Q s M Lq Lc i=[] := by
  rw [measured,install_other _ _ _ _ (by
    intro j he
    have h := congrArg Fin.val he
    have hj := j.isLt
    dsimp only [envelopeSlots] at h
    split_ifs at h <;> dsimp at h <;> omega),counted_high _ _ _ _ _ _ _ (by omega)]
  have h0 : i≠0 := by intro he; subst i; contradiction
  have h1 : i≠1 := by intro he; subst i; contradiction
  have h2 : i≠2 := by intro he; subst i; contradiction
  have h18 : i≠18 := by intro he; subst i; contradiction
  have h19 : i≠19 := by intro he; subst i; contradiction
  have h20 : i≠20 := by intro he; subst i; contradiction
  simp [input,h0,h1,h2,h18,h19,h20]

theorem capacity_input (R Q s M Lq Lc : ℕ) (i : Fin 61) :
    measured R Q s M Lq Lc (capacitySlots i)=PCPPNativeCapacityCold.input 2 (W R Q s M Lq Lc) i := by
  by_cases hi : i=0
  · subst i
    exact measured_slot R Q s M Lq Lc 18
  · rw [measured_high _ _ _ _ _ _ _ (by
      have hv : i.val≠0 := fun h => hi (Fin.ext h)
      simp only [capacitySlots,if_neg hi,Fin.val_mk]
      omega)]
    have hv : i.val≠0 := fun h => hi (Fin.ext h)
    simp [PCPPNativeCapacityCold.input,hv]

theorem capacity_away (j : Fin 61) (i : Fin 95) (hi : i.val<33) : capacitySlots j≠i := by
  intro he
  have h := congrArg Fin.val he
  dsimp only [capacitySlots] at h
  split_ifs at h <;> dsimp at h <;> omega

end NearCubicWires.RepairOrdinary.PCPPNativeResources
