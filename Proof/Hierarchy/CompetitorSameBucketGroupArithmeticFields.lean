import Proof.MachineModel.OrdinaryMatrixScoreWeightLayout
import Proof.Amplification.RecoveryScratchErase

/-! Existing scalar kernels on the literal reusable grouping workspace.
Every returned padding byte is accounted for; the caller executes the
common-capacity clear before reusing temporary arithmetic fields. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupArithmetic
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zeros (cap : ℕ) := List.replicate cap false
def field (cap : ℕ) (bits : List Bool) := ZeroPadding.pad cap (frame bits)
def scalar (cap w a : ℕ) := field cap (binary w a)
def normalCaps (cap : ℕ) : Fin 5 → ℕ := ![0,cap,cap,cap,cap]
def normalInput (cap w : ℕ) (bits : List Bool) : Fin 5 → List Bool :=
  ![List.replicate w true,field cap bits,zeros cap,zeros cap,zeros cap]
def normalOutput (cap w : ℕ) (bits : List Bool) : Fin 5 → List Bool :=
  ![List.replicate w true,field cap bits,scalar cap w (value bits),ZeroPadding.pad cap [true],zeros cap]

theorem normal_ready (cap w : ℕ) (bits : List Bool) (hw : bits.length≤w) (hc : 2*w+1≤cap) :
    ReadyRun ClockNormalize.machine (4*w+4) (normalInput cap w bits) (normalOutput cap w bits) := by
  obtain ⟨base,hr,h0,h1,h2,h3,h4,hh,hs⟩ := ClockScalarFields.scalar_run w bits hw
  have ht : base.final.tapes=![List.replicate w true,frame bits,frame (binary w (value bits)),
      [true],List.replicate (2*w+1) false] := by funext i; fin_cases i <;> assumption
  obtain ⟨r,ha,hfinal,hsteps,_⟩ := ZeroPadding.run_config ClockNormalize.machine (normalCaps cap) _ _ base hr
  have hi : ZeroPadding.config (normalCaps cap)
      (initialConfiguration ClockNormalize.machine (ClockNormalize.input w bits))=
      initialConfiguration ClockNormalize.machine (normalInput cap w bits) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,normalCaps,ClockNormalize.input,
        initialConfiguration,normalInput,field,zeros,ZeroPadding.pad,Fin.addCases]
  rw [hi] at ha
  refine ⟨r,ha,?_,?_,hsteps.trans hs⟩
  · rw [hfinal]
    change (fun i => ZeroPadding.pad (normalCaps cap i) (base.final.tapes i))=_
    rw [ht]
    funext i
    fin_cases i <;> simp [normalCaps,normalOutput,field,scalar,zeros,
      Rewind.Workspace.pad_zeros,max_eq_left hc]
  · intro i
    rw [hfinal]
    exact hh i

def copyInput (cap : ℕ) (bits backing : List Bool) : Fin 4 → List Bool :=
  ![field cap bits,ZeroPadding.pad cap backing,zeros cap,zeros cap]
def copyOutput (cap : ℕ) (bits : List Bool) : Fin 4 → List Bool :=
  ![field cap bits,field cap bits,zeros cap,zeros cap]

theorem field_copy_ready (cap : ℕ) (bits backing : List Bool)
    (hb : backing.length≤2*bits.length+1) (hc : 4*bits.length+3≤cap) :
    ReadyRun copyMachine (8*bits.length+8) (copyInput cap bits backing) (copyOutput cap bits) := by
  obtain ⟨base,hr,ht,hh,hs⟩ := copy_ready bits backing 0 0 hb
  simp only [Nat.zero_max] at ht
  obtain ⟨r,ha,hfinal,hsteps,_⟩ := ZeroPadding.run_config copyMachine (fun _ => cap) _ _ base hr
  have hi : ZeroPadding.config (fun _ : Fin 4 => cap)
      (initialConfiguration copyMachine ![frame bits,backing,List.replicate 0 false,List.replicate 0 false])=
      initialConfiguration copyMachine (copyInput cap bits backing) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,copyInput,field,zeros,ZeroPadding.pad]
  rw [hi] at ha
  refine ⟨r,ha,?_,?_,hsteps.trans hs⟩
  · rw [hfinal]
    change (fun i => ZeroPadding.pad cap (base.final.tapes i))=_
    rw [ht]
    funext i
    fin_cases i <;> simp [copyOutput,field,zeros,Rewind.Workspace.pad_zeros,
      max_eq_left hc,max_eq_left (by omega : 2*bits.length+1≤cap)]
  · intro i
    rw [hfinal]
    exact hh i

theorem field_support (cap : ℕ) (bits : List Bool) (hc : 2*bits.length+1≤cap) :
    (field cap bits).length≤cap := by simp [field,ZeroPadding.pad_length]; omega
theorem scalar_support (cap w a : ℕ) (hc : 2*w+1≤cap) : (scalar cap w a).length≤cap :=
  field_support cap (binary w a) (by simpa using hc)

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupArithmetic
