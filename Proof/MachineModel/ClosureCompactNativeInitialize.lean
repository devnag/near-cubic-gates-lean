import Proof.MachineModel.ClosureCompactMetadataConsumer

/-! Physically produce and distribute the compact metadata into the actual
native bank. Runtime dimensions, the encoded cache, raw source, and loop
counter are explicit inputs; they are not silently treated as outputs.
The extra workspace holds the arithmetic computation, outside the native
bank. All machines and slot maps are independent of runtime data. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactNativeInitialize
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtIncidence ExtDecompositionBatch
open RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding

def native (i : Fin 277) : Fin 440 := i.castAdd 163
def metadataSlots : Fin 162 → Fin 440 := ![278,3,4,15,282,283,88,0,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,27,307,308,309,31,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,53,332,333,334,57,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,86,379,380,381,382,383,384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,133,425,135,427,428,429,139,431,141,433,143,435,436,146,438,439]
def ports : Fin 141 → Fin 440 := native ∘ NativeFanoutLayout.ports
theorem meta_injective : Function.Injective metadataSlots := by decide
theorem ports_injective : Function.Injective ports := by decide
theorem meta_fields (j : Fin 15) : metadataSlots (CompactMetadata.fields j) =
    native (NativeFanoutLayout.sources j) := by fin_cases j <;> rfl
theorem meta_cap : metadataSlots 146 = native (NativeFanoutLayout.bank 104) := rfl
theorem meta_away_targets : ∀ j i,
    metadataSlots i ≠ native (NativeFanoutLayout.bank (NativeFanoutLayout.targets j)) := by decide

def heads (pos : Nat) (out : List Bool) (i : Fin 440) : Nat :=
  if i=180 then out.length else if i=262 then pos else if i=277 then 1 else 0
def base (M : Nat) (source out : List Bool) (i : Fin 440) : List Bool :=
  if i=180 then out else if i=262 then source else if i=277 then CompareMachine.word M else []

variable {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs] (Q w : Nat)

noncomputable def input (M : Nat) (source out : List Bool) : Fin 440 → List Bool :=
  install metadataSlots (base M source out)
    (CompactMetadata.input (exactListWord gs).length n gs.length (P1Radix.bits gs)
      (P1Radix.effectiveDegree gs) Q w (exactListWord gs))
noncomputable def middle (M : Nat) (source out : List Bool) : Fin 440 → List Bool :=
  install metadataSlots (input gs Q w M source out)
    (CompactMetadata.output (exactListWord gs).length n gs.length (P1Radix.bits gs)
      (P1Radix.effectiveDegree gs) Q w (exactListWord gs))
noncomputable def output (M : Nat) (source out : List Bool) : Fin 440 → List Bool :=
  install ports (middle gs Q w M source out)
    (NativeFanout.output NativeFanoutLayout.choice (P1CompactNativeMaster.words gs Q w)
      (P1CompactNativeMeasured.capacity gs Q w))

noncomputable def first := RecoveryFocus.machine metadataSlots CompactMetadata.machine
noncomputable def last := RecoveryFocus.machine ports (NativeFanout.machine NativeFanoutLayout.choice)
noncomputable def machine := Composition.machine first last
def budget := CompactMetadata.budget (exactListWord gs).length n gs.length (P1Radix.bits gs)
  (P1Radix.effectiveDegree gs) Q w + 1 + (2*P1CompactNativeMeasured.capacity gs Q w+4)

theorem meta_heads (pos : Nat) (out : List Bool) (i : Fin 162) : heads pos out (metadataSlots i)=0 := by
  have h : ∀ j, metadataSlots j ≠ (180 : Fin 440) ∧ metadataSlots j ≠ 262 ∧ metadataSlots j ≠ 277 := by decide
  simp only [heads,if_neg (h i).1,if_neg (h i).2.1,if_neg (h i).2.2]
theorem ports_heads (pos : Nat) (out : List Bool) (i : Fin 141) : heads pos out (ports i)=0 := by
  have h : ∀ j, ports j ≠ (180 : Fin 440) ∧ ports j ≠ 262 ∧ ports j ≠ 277 := by decide
  simp only [heads,if_neg (h i).1,if_neg (h i).2.1,if_neg (h i).2.2]

theorem middle_fields (M : Nat) (source out : List Bool) (j : Fin 15) :
    middle gs Q w M source out (native (NativeFanoutLayout.sources j)) =
      P1CompactNativeMaster.words gs Q w j := by
  rw [←meta_fields,middle,install_slot metadataSlots meta_injective]
  exact (CompactMetadata.consumer_run gs Q w).2.1 j
theorem middle_capacity (M : Nat) (source out : List Bool) :
    middle gs Q w M source out (native (NativeFanoutLayout.bank 104)) =
      List.replicate (P1CompactNativeMeasured.capacity gs Q w) true := by
  rw [←meta_cap,middle,install_slot metadataSlots meta_injective]
  exact (CompactMetadata.consumer_run gs Q w).2.2
theorem middle_other (M : Nat) (source out : List Bool) (i : Fin 440)
    (hi : ∀ j,metadataSlots j≠i) : middle gs Q w M source out i=base M source out i := by
  rw [middle,install_other metadataSlots _ _ i hi,input,install_other metadataSlots _ _ i hi]

theorem fanout_input (M : Nat) (source out : List Bool) : ∀ j,
    middle gs Q w M source out (ports j) =
      NativeFanout.input (m:=124) (P1CompactNativeMaster.words gs Q w) (P1CompactNativeMeasured.capacity gs Q w) j := by
  intro j
  refine Fin.addCases (m:=15+(124+1)) (n:=1) (fun i=>?_) (fun i=>?_) j
  · refine Fin.addCases (m:=15) (n:=124+1) (fun a=>?_) (fun a=>?_) i
    · simpa only [ports,Function.comp_apply,NativeFanoutLayout.ports,NativeFanout.input,
        Fin.addCases_left] using middle_fields gs Q w M source out a
    · refine Fin.addCases (m:=124) (n:=1) (fun a=>?_) (fun a=>?_) a
      · simp only [ports,Function.comp_apply,NativeFanoutLayout.ports,NativeFanout.input,
          Fin.addCases_left,Fin.addCases_right]
        rw [middle_other gs Q w M source out _ (meta_away_targets a)]
        have h : ∀ j, native (NativeFanoutLayout.bank (NativeFanoutLayout.targets j)) ≠ (180 : Fin 440) ∧
            native (NativeFanoutLayout.bank (NativeFanoutLayout.targets j)) ≠ 262 ∧
            native (NativeFanoutLayout.bank (NativeFanoutLayout.targets j)) ≠ 277 := by decide
        simp only [base,if_neg (h a).1,if_neg (h a).2.1,if_neg (h a).2.2]
      · simpa only [ports,Function.comp_apply,NativeFanoutLayout.ports,NativeFanout.input,
          Fin.addCases_left,Fin.addCases_right] using middle_capacity gs Q w M source out
  · simp only [ports,Function.comp_apply,NativeFanoutLayout.ports,NativeFanout.input,
      Fin.addCases_right]
    change middle gs Q w M source out 254=[]
    rw [middle_other gs Q w M source out 254 (by decide)]
    rfl

theorem run (M pos : Nat) (source out : List Bool) :
    Step machine (budget gs Q w) (heads pos out) (input gs Q w M source out)
      (heads pos out) (output gs Q w M source out) := by
  obtain ⟨r,hr,rh,rt,_rs⟩ := (CompactMetadata.consumer_run gs Q w).1.focus_at
    metadataSlots meta_injective (heads pos out) (input gs Q w M source out)
    (fun j => install_slot metadataSlots meta_injective _ _ j) (meta_heads pos out)
  have start := Step.of_run hr rh rt
  obtain ⟨f,hf,ft,fh,fs⟩ := NativeFanout.ready NativeFanoutLayout.choice
    (P1CompactNativeMaster.words gs Q w) (P1CompactNativeMeasured.capacity gs Q w)
    (CompactMetadata.words_fit gs Q w)
  have ready : ClockJoin.ReadyRun (NativeFanout.machine NativeFanoutLayout.choice)
      (2*P1CompactNativeMeasured.capacity gs Q w+4)
      (NativeFanout.input (P1CompactNativeMaster.words gs Q w) (P1CompactNativeMeasured.capacity gs Q w))
      (NativeFanout.output NativeFanoutLayout.choice (P1CompactNativeMaster.words gs Q w)
        (P1CompactNativeMeasured.capacity gs Q w)) := ⟨f,hf,ft,fh,fs.le⟩
  obtain ⟨s,hs,sh,st,_ss⟩ := ready.focus_at ports ports_injective (heads pos out)
    (middle gs Q w M source out) (fanout_input gs Q w M source out) (ports_heads pos out)
  exact start.seq (Step.of_run hs sh st)

theorem output_ports (M : Nat) (source out : List Bool) (j : Fin 141) :
    output gs Q w M source out (ports j) =
      NativeFanout.output NativeFanoutLayout.choice (P1CompactNativeMaster.words gs Q w)
        (P1CompactNativeMeasured.capacity gs Q w) j := install_slot ports ports_injective _ _ j

theorem output_other (M : Nat) (source out : List Bool) (i : Fin 440)
    (hp : ∀ j,ports j≠i) (hm : ∀ j,metadataSlots j≠i) :
    output gs Q w M source out i=base M source out i := by
  rw [output,install_other ports _ _ i hp,middle_other gs Q w M source out i hm]

theorem initialized (M pos : Nat) (source out : List Bool) (i : Fin 128) :
    heads pos out (native (NativeFanoutLayout.bank i))=NativeInitialize.extraH pos out i ∧
    output gs Q w M source out (native (NativeFanoutLayout.bank i)) =
      NativeInitializedPorts.word (P1CompactNativeMaster.words gs Q w)
        (P1CompactNativeMeasured.capacity gs Q w) source out i := by
  apply NativeInitializedPorts.fields (heads pos out ∘ native)
    (output gs Q w M source out ∘ native) (P1CompactNativeMaster.words gs Q w)
    (P1CompactNativeMeasured.capacity gs Q w) pos source out
  · exact ports_heads pos out
  · exact output_ports gs Q w M source out
  · rfl
  · exact output_other gs Q w M source out 180 (by decide) (by decide)
  · rfl
  · exact output_other gs Q w M source out 262 (by decide) (by decide)

theorem masters (M pos : Nat) (source out : List Bool) (j : Fin 15) :
    heads pos out (native (NativeFanoutLayout.sources j))=0 ∧
    output gs Q w M source out (native (NativeFanoutLayout.sources j)) =
      P1CompactNativeMaster.words gs Q w j := by
  have hh := ports_heads pos out ((j.castAdd 125).castAdd 1)
  have ht := output_ports gs Q w M source out ((j.castAdd 125).castAdd 1)
  simpa only [ports,Function.comp_apply,NativeFanoutLayout.ports,NativeFanout.output,
    Fin.addCases_left] using And.intro hh ht

end NearCubicWires.P1Closure.CompactNativeInitialize
