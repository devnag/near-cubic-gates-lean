import Proof.PCP.PCPPNativeQueryHeader

/-! Fixed original-query caller layout. Header, node loop, footer and tail
share the original descriptor, the prepared projection row and the live output.
Layout identities abstract tape vectors before introducing large controls. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQuery
open LocalBitMultitape PCPPNativeNodeReusable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerSlots (j : Fin 31) : Fin 168 :=
  if j=0 then 0 else if j=10 then 123 else if j=20 then 122 else ⟨j.val+124,by omega⟩
def loopSlots (j : Fin 123) : Fin 168 := j.castAdd 45
def footerSlots (j : Fin 11) : Fin 168 :=
  if j=0 then 0 else if j=10 then 124 else ⟨j.val+154,by omega⟩
def valueSlots : Fin 5 → Fin 168 := ![124,164,165,166,167]
def tailSlots (j : Fin 24) : Fin 168 :=
  if j=0 then 2 else if j=1 then 164 else if j=20 then 5 else if j=21 then 118
  else if j=22 then 4 else if j=23 then 12 else ⟨j.val+98,by omega⟩

theorem header_injective : Function.Injective headerSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [headerSlots] at hv
  split_ifs at hv <;> simp_all only [Fin.ext_iff]
  all_goals omega
theorem header_away (j : Fin 31) (hj : j≠0) : 122 ≤ (headerSlots j).val := by
  simp only [headerSlots,hj,ite_false]
  split_ifs
  · decide
  · decide
  · change 122 ≤ j.val+124
    omega
theorem loop_injective : Function.Injective loopSlots := by
  intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 168 => k.val) h
theorem footer_injective : Function.Injective footerSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [footerSlots] at hv
  split_ifs at hv <;> simp_all only [Fin.ext_iff]
  all_goals omega
theorem value_injective : Function.Injective valueSlots := by decide
theorem tail_injective : Function.Injective tailSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [tailSlots] at hv
  split_ifs at hv <;> simp_all only [Fin.ext_iff]
  all_goals omega

noncomputable def header := RecoveryFocus.machine headerSlots PCPPNativeQueryHeader.machine
noncomputable def nodes := RecoveryFocus.machine loopSlots PCPPNativeNodeLoop.machine
noncomputable def footer := RecoveryFocus.machine footerSlots PCPPQueryNatural.machine
noncomputable def value := RecoveryFocus.machine valueSlots PCPPNativeTemplateRaw.machine
noncomputable def tail := RecoveryFocus.machine tailSlots PCPPNativeQueryTail.machine
noncomputable def body := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine header nodes) footer) value) tail

def heads (cursor : ℕ) (out : List Bool) : Fin 168 → ℕ :=
  Fin.addCases (m := 122) (n := 46) (PCPPNativeNodeReusable.heads cursor out) (fun _ => 0)
def data (bits queries : List Bool) (base position C F : ℕ) (out : List Bool) : Fin 168 → List Bool :=
  Fin.addCases (m := 122) (n := 46) (PCPPNativeNodeReusable.data bits queries base position C F out) (fun _ => [])
noncomputable def entry (bits queries : List Bool) (cursor base position C F : ℕ) (out : List Bool) :=
  (⟨body.start,heads cursor out,data bits queries base position C F out⟩ : Configuration 168 _)
def lowFrame (bits queries : List Bool) (cursor base position C F : ℕ) (out : List Bool)
    (ah : Fin 168 → ℕ) (atapes : Fin 168 → List Bool) : Prop :=
  ∀ j : Fin 122,ah (j.castAdd 46)=PCPPNativeNodeReusable.heads cursor out j ∧
    atapes (j.castAdd 46)=PCPPNativeNodeReusable.data bits queries base position C F out j

theorem loop_lower (phase : Fin 5) (bits queries : List Bool) (cursor base position C F : ℕ)
    (out : List Bool) (count driverHead : ℕ) (j : Fin 122) :
    (PCPPNativeNodeLoop.templateConfiguration phase bits queries cursor base position C F out count driverHead).heads (j.castAdd 1)=
      PCPPNativeNodeReusable.heads cursor out j ∧
    (PCPPNativeNodeLoop.templateConfiguration phase bits queries cursor base position C F out count driverHead).tapes (j.castAdd 1)=
      PCPPNativeNodeReusable.data bits queries base position C F out j := by
  have hj : j.castAdd 1≠(122 : Fin 123) := by
    intro h
    have hv := congrArg (fun k : Fin 123 => k.val) h
    change j.val=122 at hv
    omega
  simp only [PCPPNativeNodeLoop.templateConfiguration,ZeroPadding.config,
    PCPPNativeNodeLoop.configuration,RepairSource.VerifierDecoding.RepeatMachine.cfg,
    controlConfig,TapeEmbedding.config,Fin.addCases_left,PCPPNativeNodeStep.entry,
    PCPPNativeNodeLoop.templateCaps,hj,ite_false,ZeroPadding.pad_zero,and_self]

theorem loop_input (phase : Fin 5) (bits queries : List Bool) (cursor base position C F : ℕ)
    (out : List Bool) (count driverHead : ℕ) (ah : Fin 168 → ℕ) (atapes : Fin 168 → List Bool)
    (hlow : lowFrame bits queries cursor base position C F out ah atapes)
    (hdriver : ah 122=driverHead ∧ atapes 122=UnaryTemplate.tape count) (j : Fin 123) :
    ah (loopSlots j)=(PCPPNativeNodeLoop.templateConfiguration phase bits queries cursor base position C F out count driverHead).heads j ∧
    atapes (loopSlots j)=(PCPPNativeNodeLoop.templateConfiguration phase bits queries cursor base position C F out count driverHead).tapes j := by
  refine Fin.addCases (m := 122) (n := 1) (fun i => ?_) (fun i => ?_) j
  · have h := loop_lower phase bits queries cursor base position C F out count driverHead i
    exact ⟨(hlow i).1.trans h.1.symm,(hlow i).2.trans h.2.symm⟩
  · fin_cases i
    have h := PCPPNativeNodeLoop.template_count phase bits queries cursor base position C F out count driverHead
    exact ⟨hdriver.1.trans h.2.symm,hdriver.2.trans h.1.symm⟩

end NearCubicWires.RepairOrdinary.PCPPNativeQuery
