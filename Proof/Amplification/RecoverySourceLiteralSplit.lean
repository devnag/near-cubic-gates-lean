import Proof.Amplification.RecoveryProjectionDimensionUnary
import Proof.PCP.PCPPNativeClauseLiteralReady

/-! Read the original source literal's binary code 2*j+negative. Existing
binary dimension parsing and the existing parity splitter produce its raw
query index and sign; no new source encoding or literal decoder is used. -/
namespace NearCubicWires.RepairSource.RecoverySourceLiteral
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def wordInput (index : Nat) (negative : Bool) : Fin 4→List Bool :=
  ![CompareMachine.word (2*index+negative.toNat),[],[],[]]
def wordCaps (index : Nat) (negative : Bool) : Fin 4→Nat :=
  ![2*index+negative.toNat+2,0,0,0]

theorem word_ready (index : Nat) (negative : Bool) : ∃ out,
    ClockJoin.ReadyRun PCPPNativeLiteralSplit.machine (4*index+2*negative.toNat+6)
      (wordInput index negative) out ∧ out 1=List.replicate index true ∧ out 2=[negative] := by
  obtain ⟨base,hb,bt,bh,bs⟩ := PCPPNativeLiteralSplit.ready_run index negative
  have hi : ZeroPadding.config (wordCaps index negative)
      (initialConfiguration PCPPNativeLiteralSplit.machine (wordInput index negative))=
      initialConfiguration PCPPNativeLiteralSplit.machine
        ![UnaryTemplate.tape (2*index+negative.toNat),[],[],[]] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,wordCaps,wordInput,initialConfiguration,
        ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]
  change runFrom PCPPNativeLiteralSplit.machine _ _=some base at hb
  rw [←hi] at hb
  obtain ⟨r,hr,hf,hs,_space⟩ := ZeroPadding.run_unpad PCPPNativeLiteralSplit.machine (wordCaps index negative) _ _ base hb
  have h1:=congrArg (fun c=>c.tapes 1) hf
  have h2:=congrArg (fun c=>c.tapes 2) hf
  rw [bt] at h1 h2
  refine ⟨r.final.tapes,⟨r,hr,rfl,?_,by omega⟩,?_,?_⟩
  · intro i
    have hh:=congrArg (fun c=>c.heads i) hf
    exact hh.trans (bh i)
  · simpa only [ZeroPadding.config,wordCaps,Matrix.cons_val_one,Matrix.cons_val_zero,ZeroPadding.pad_zero] using h1
  · change ZeroPadding.pad 0 (r.final.tapes 2)=[negative] at h2
    simpa only [ZeroPadding.pad_zero] using h2

def parserSlots (i : Fin 5) : Fin 8 := i.castAdd 3
def splitSlots : Fin 4→Fin 8 := ![3,5,6,7]
theorem parser_injective : Function.Injective parserSlots := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 8=>i.val) h)
theorem split_injective : Function.Injective splitSlots := by decide
noncomputable def parserMachine := RecoveryFocus.machine parserSlots RecoveryProjectionDimension.parsedMachine
noncomputable def splitMachine := RecoveryFocus.machine splitSlots PCPPNativeLiteralSplit.machine
noncomputable def machine := Composition.machine parserMachine splitMachine
def input (bits : List Bool) (i : Fin 8) := if i=0 then RepairOrdinary.frame bits else []
noncomputable def parsed (bits : List Bool) (data : Fin 5→List Bool) := install parserSlots (input bits) data

def budget (index : Nat) (negative : Bool) := Unary.budget (2*index+negative.toNat).bits+4*index+2*negative.toNat+9

theorem split_run (index : Nat) (negative : Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget index negative) (input (2*index+negative.toNat).bits) out ∧
      out 5=List.replicate index true ∧ out 6=[negative] := by
  let bits := (2*index+negative.toNat).bits
  obtain ⟨parser,hParser,hCode⟩ := RecoveryProjectionDimension.parsed_ready bits
  have first := hParser.focus parserSlots parser_injective (input bits) (by intro i; fin_cases i <;> rfl)
  obtain ⟨split,hSplit,hIndex,hNegative⟩ := word_ready index negative
  have second := hSplit.focus splitSlots split_injective (parsed bits parser) (by
    intro i; fin_cases i
    · change install parserSlots _ _ (parserSlots 3)=_
      rw [install_slot _ parser_injective,hCode]
      change CompareMachine.word (value bits)=CompareMachine.word (2*index+negative.toNat)
      rw [show value bits=2*index+negative.toNat from DimensionProducer.bits_value _]
    all_goals
      rw [parsed,install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl)
  have hall := ClockJoin.join _ _ _ _ _ _ _ first second
  have ht : (Unary.budget bits+2)+1+(4*index+2*negative.toNat+6)=budget index negative := by unfold budget bits; omega
  rw [ht] at hall
  refine ⟨_,hall,?_,?_⟩
  · change install splitSlots _ _ (splitSlots 1)=_
    rw [install_slot _ split_injective]
    exact hIndex
  · change install splitSlots _ _ (splitSlots 2)=_
    rw [install_slot _ split_injective]
    exact hNegative

end NearCubicWires.RepairSource.RecoverySourceLiteral
