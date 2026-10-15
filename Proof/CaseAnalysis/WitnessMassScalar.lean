import Proof.CaseAnalysis.WitnessMassPolicy

/-! The accepted coefficient's framed binary fields are widened directly
into cleared accumulator argument cells. Source fields and widths survive;
all padding is the physically paid native-bank backing. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassScalar
open LocalBitMultitape RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (C : ℕ) (i : Fin 5):=if i=2 then C else 0
def input (C w : ℕ) (bits : List Bool) : Fin 5→List Bool:=
  ![List.replicate w true,frame bits,List.replicate C false,[],[]]
def zeroInput (C w : ℕ) : Fin 5→List Bool:=
  ![List.replicate w true,[],List.replicate C false,[],[]]

theorem scalar_run (C w : ℕ) (bits : List Bool) (hw : bits.length ≤ w) : ∃ output,
    ClockJoin.ReadyRun ClockNormalize.machine (4*w+4) (input C w bits) output ∧
      output 0=List.replicate w true ∧ output 1=frame bits ∧
      output 2=ZeroPadding.pad C (frame (binary w (RadixSemantics.value bits))):=by
  obtain ⟨b,hb,b0,b1,b2,_,_,bh,bt⟩:=ClockScalarFields.scalar_run w bits hw
  obtain ⟨r,hr,rf,rt,_⟩:=ZeroPadding.run_config ClockNormalize.machine (padding C) _ _ b hb
  have hi:ZeroPadding.config (padding C)
      (initialConfiguration ClockNormalize.machine (ClockNormalize.input w bits))=
      initialConfiguration ClockNormalize.machine (input C w bits):=by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> simp [ZeroPadding.config,padding,initialConfiguration,
        input,ClockNormalize.input,ZeroPadding.pad,Fin.addCases]
  rw [hi] at hr
  refine ⟨r.final.tapes,⟨r,hr,rfl,?_,rt.trans_le bt.le⟩,?_,?_,?_⟩
  · intro i;rw [rf];exact bh i
  · simpa only [rf,ZeroPadding.config,padding,if_neg (by decide : (0 : Fin 5)≠2),
      ZeroPadding.pad_zero] using b0
  · simpa only [rf,ZeroPadding.config,padding,if_neg (by decide : (1 : Fin 5)≠2),
      ZeroPadding.pad_zero] using b1
  · rw [rf]
    change ZeroPadding.pad C (b.final.tapes 2)=_
    rw [b2]

theorem zero_run (C w : ℕ) : ∃ output,
    ClockJoin.ReadyRun ClockNormalize.machine (4*w+4) (zeroInput C w) output ∧
      output 0=List.replicate w true ∧ output 2=ZeroPadding.pad C (frame (binary w 0)):=by
  obtain ⟨b,hb,b0,_,b2,_,_,bh,bt⟩:=ClockScalarFields.zero_run w
  obtain ⟨r,hr,rf,rt,_⟩:=ZeroPadding.run_config ClockNormalize.machine (padding C) _ _ b hb
  have hi:ZeroPadding.config (padding C)
      (initialConfiguration ClockNormalize.machine (ClockScalarFields.zeroInput w))=
      initialConfiguration ClockNormalize.machine (zeroInput C w):=by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> simp [ZeroPadding.config,padding,initialConfiguration,
        zeroInput,ClockScalarFields.zeroInput,ZeroPadding.pad]
  rw [hi] at hr
  refine ⟨r.final.tapes,⟨r,hr,rfl,?_,rt.trans_le bt.le⟩,?_,?_⟩
  · intro i;rw [rf];exact bh i
  · simpa only [rf,ZeroPadding.config,padding,if_neg (by decide : (0 : Fin 5)≠2),
      ZeroPadding.pad_zero] using b0
  · rw [rf]
    change ZeroPadding.pad C (b.final.tapes 2)=_
    rw [b2]

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassScalar
