import Proof.CaseAnalysis.WitnessReencodeReady
import Proof.Amplification.RecoveryWitnessCopy
import Proof.Hierarchy.CompetitorRationalProducts

/-! Cold canonical-list checking retains the original word before traversal.
Every auxiliary input is blank; copied words and flags are produced physically. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CanonicalTest
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots (i : Fin 4) : Fin 174 := i.castAdd 170
def walkSlots (i : Fin (36+1+3+128+1)) : Fin 174 :=
  if i.val=0 then 1 else ⟨i.val+3,by omega⟩
def equalSlots : Fin 4→Fin 174 := ![0,120,172,173]
theorem copy_injective : Function.Injective copySlots := by
  intro i j h
  have hv:=congrArg (fun x : Fin 174=>x.val) h
  exact Fin.ext hv
theorem walk_injective : Function.Injective walkSlots := by
  intro i j h
  have hv:=congrArg Fin.val h
  unfold walkSlots at hv
  split at hv <;> split at hv <;> simp only [Fin.val_one] at hv
  all_goals apply Fin.ext; omega
theorem equal_injective : Function.Injective equalSlots := by decide
theorem walk_range (i : Fin (36+1+3+128+1)) :
    0<(walkSlots i).val ∧ (walkSlots i).val<172 := by
  unfold walkSlots
  split <;> simp only [Fin.val_one] <;> omega

def input (bits : List Bool) (i : Fin 174) := if i.val=0 then frame bits else []
noncomputable def copied (bits : List Bool) :=
  install copySlots (input bits) (RecoveryColdWitnessCopy.output bits)
noncomputable def primed (bits : List Bool) := Function.update (copied bits) 172 [true]
noncomputable def copy := RecoveryFocus.machine copySlots RecoveryColdWitnessCopy.machine
noncomputable def walk := RecoveryFocus.machine walkSlots Reencode.readyMachine
noncomputable def equality := RecoveryFocus.machine equalSlots NumericEquality.readyMachine

theorem copied_at (bits : List Bool) (i : Fin 4) :
    copied bits (copySlots i)=RecoveryColdWitnessCopy.output bits i :=
  install_slot copySlots copy_injective _ _ i
theorem copied_other (bits : List Bool) (i : Fin 174) (hi : 4 ≤ i.val) : copied bits i=[] := by
  rw [copied,install_other]
  · simp [input,show i.val≠0 by omega]
  · intro j h
    have hv:=congrArg Fin.val h
    change j.val=i.val at hv
    omega
theorem primed_other (bits : List Bool) (i : Fin 174) (hi : i≠172) :
    primed bits i=copied bits i := Function.update_of_ne hi _ _

def boot : Machine 174 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=172 then some true else none,fun _=>.stay⟩ else none

theorem boot_ready (bits : List Bool) : ClockJoin.ReadyRun boot 1 (copied bits) (primed bits) := by
  let final : Configuration 174 2:=⟨1,fun _=>0,primed bits⟩
  have h:step boot (initialConfiguration boot (copied bits))=some final:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi:i=172
      · subst i
        change writeTapeBit (copied bits 172) 0 true=[true]
        rw [copied_other bits 172 (by decide)]
        rfl
      · simp only [applyAction,hi,↓reduceIte]
        exact (primed_other bits i hi).symm
  obtain ⟨r,hr,hf,hs⟩:=(Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i;rw [hf],hs.le⟩

theorem copy_ready (bits : List Bool) :
    ClockJoin.ReadyRun copy (8*bits.length+14) (input bits) (copied bits) := by
  obtain ⟨r,hr,ht,hh,hs⟩:=RecoveryColdWitnessCopy.copy_ready bits
  exact bounded_focus copySlots copy_injective _ _ _ ⟨r,hr,ht,hh,hs.le⟩ (input bits)
    (by intro i;fin_cases i <;> rfl)

theorem reencode_input (bits : List Bool) (i : Fin (36+1+3+128+1)) :
    Reencode.readyInput bits i=if i.val=0 then frame bits else [] := by
  fin_cases i <;> rfl

theorem walk_input (bits : List Bool) (i : Fin (36+1+3+128+1)) :
    primed bits (walkSlots i)=Reencode.readyInput bits i := by
  rw [reencode_input,primed_other bits _ (by
    intro h;have hv:=congrArg Fin.val h;have hb:=(walk_range i).2;omega)]
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi
    subst i
    change copied bits (copySlots 1)=frame bits
    exact copied_at bits 1
  · simp only [hi,↓reduceIte]
    apply copied_other
    simp only [walkSlots,hi,↓reduceIte]
    omega

noncomputable def walked (bits : List Bool) (out : Fin (36+1+3+128+1)→List Bool) :=
  install walkSlots (primed bits) out
theorem walked_other (bits : List Bool) (out : Fin (36+1+3+128+1)→List Bool)
    (i : Fin 174) (hi : i.val=0 ∨ 172 ≤ i.val) : walked bits out i=primed bits i := by
  apply install_other
  intro j h
  have hv:=congrArg Fin.val h
  have hb:=walk_range j
  omega

theorem canonical_bits (bits : List Bool) : (Reencode.canonical bits).bits.length≤Reencode.polynomialBudget bits := by
  have hc:=Reencode.count_bound bits
  have hm:PCPSerializerMass.mass (Reencode.fields bits)+1≤3*(bits.length+1)^2:=by
    rw [Reencode.fields_mass]
    have hn:=Nat.mul_le_mul_right (2*bits.length+1) hc
    change (PCPPNativeCanonicalTree.tree (value bits)).atoms.length*(2*bits.length+1)≤_ at hn
    nlinarith
  have hcode:=PCPSerializerMass.code_bits (Reencode.fields bits)
  have hp:=Nat.pow_le_pow_left hm 5
  rw [mul_pow,←pow_mul] at hp
  norm_num at hp
  have h24:(bits.length+1)^10≤(bits.length+1)^24:=pow_le_pow_right₀ (by omega) (by omega)
  rw [Reencode.fields_values] at hcode
  change (Reencode.canonical bits).bits.length≤3*(PCPSerializerMass.mass (Reencode.fields bits)+1)^5 at hcode
  unfold Reencode.polynomialBudget
  omega

end NearCubicWires.RepairOrdinary.CloseoutWitness.CanonicalTest
