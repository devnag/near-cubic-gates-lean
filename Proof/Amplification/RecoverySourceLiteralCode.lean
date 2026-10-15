import Proof.Amplification.RecoverySourceLiteralAddress
import Proof.Amplification.RecoveryLiteralSignFrame

/-! Complete actual source-literal to original CNF literal code. Source
index/sign decoding, projected-address lookup, sign framing and the original
natural pair execute on a fixed bank. High zero bits remain valid natural
code fields for the existing balanced serializer. -/
namespace NearCubicWires.RepairSource.RecoverySourceLiteralCode
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics SignedSortKey
open VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (i : Fin 16) : Fin 53 := i.castAdd 37
def signSlots : Fin 3→Fin 53 := ![6,16,17]
def pairSlots (i : Fin 35) : Fin 53 :=
  if i.val=2 then 16 else if i.val=3 then 13 else ⟨i.val+18,by have hi:=i.isLt; omega⟩
theorem native_injective : Function.Injective nativeSlots := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 53=>i.val) h)
theorem sign_injective : Function.Injective signSlots := by decide
theorem pair_injective : Function.Injective pairSlots := by
  intro a b h; apply Fin.ext
  have hv:=congrArg Fin.val h
  dsimp only [pairSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

noncomputable def nativeMachine := RecoveryFocus.machine nativeSlots RecoverySourceLiteralAddress.machine
noncomputable def signMachine := RecoveryFocus.machine signSlots RecoveryLiteralSignFrame.machine
noncomputable def pairMachine := RecoveryFocus.machine pairSlots PCPPairCold.machine
noncomputable def machine := Composition.machine (Composition.machine nativeMachine signMachine) pairMachine
def input (code source : List Bool) (i : Fin 53) :=
  if i=0 then RepairOrdinary.frame code else if i=11 then source else []
noncomputable def addressed (code source : List Bool) (out : Fin 16→List Bool) := install nativeSlots (input code source) out
noncomputable def signed (code source : List Bool) (out : Fin 16→List Bool) (negative : Bool) :=
  install signSlots (addressed code source out)
    ![[negative],RepairOrdinary.frame [!negative],List.replicate 3 false]

def word (negative : Bool) (bits : List Bool) :=
  binary (PCPPair.width [!negative] bits) (Nat.pair (!negative).toNat (value bits))
def budget (negative : Bool) (skipped : List (List Bool)) (bits : List Bool) :=
  RecoverySourceLiteralAddress.budget negative skipped bits+1+8+1+PCPPairCold.budget [!negative] bits

theorem pair_input (code source bits : List Bool) (out : Fin 16→List Bool) (negative : Bool)
    (hfield : out 13=RepairOrdinary.frame bits) (i : Fin 35) :
    signed code source out negative (pairSlots i)=PCPPairCold.input [!negative] bits i := by
  classical
  by_cases h2 : i.val=2
  · have hi : i=2 := Fin.ext h2
    subst i
    change install signSlots _ _ (signSlots 1)=_
    rw [install_slot _ sign_injective]
    rfl
  by_cases h3 : i.val=3
  · have hi : i=3 := Fin.ext h3
    subst i
    rw [signed,install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
    change install nativeSlots _ _ (nativeSlots 13)=_
    rw [install_slot _ native_injective]
    exact hfield
  have hv : (pairSlots i).val=i.val+18 := by simp only [pairSlots,h2,h3,ite_false]
  have awaySign : ∀ j,signSlots j≠pairSlots i := by
    intro j h
    have hval:=congrArg Fin.val h
    have hj : (signSlots j).val<18 := by fin_cases j <;> decide
    rw [hv] at hval
    omega
  have awayNative : ∀ j,nativeSlots j≠pairSlots i := by
    intro j h; have hval:=congrArg Fin.val h; have hj:=j.isLt
    rw [hv] at hval
    change j.val=i.val+18 at hval
    omega
  rw [signed,install_other _ _ _ _ awaySign,addressed,install_other _ _ _ _ awayNative]
  have h0 : pairSlots i≠0 := by intro he; have hh:=congrArg Fin.val he; rw [hv] at hh; change i.val+18=0 at hh; omega
  have h11 : pairSlots i≠11 := by intro he; have hh:=congrArg Fin.val he; rw [hv] at hh; change i.val+18=11 at hh; omega
  simp only [input,h0,h11,ite_false,PCPPairCold.input,h2,h3]

theorem code_run (negative : Bool) (skipped : List (List Bool)) (bits suffix : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget negative skipped bits)
      (input (2*skipped.length+negative.toNat).bits (FieldList.stream skipped++RepairOrdinary.frame bits++suffix)) out ∧
      out 44=RepairOrdinary.frame (word negative bits) := by
  let code := (2*skipped.length+negative.toNat).bits
  let source := FieldList.stream skipped++RepairOrdinary.frame bits++suffix
  obtain ⟨native,hNative,hSign,hAddress,_hSource⟩ := RecoverySourceLiteralAddress.address_run negative skipped bits suffix
  have first := hNative.focus nativeSlots native_injective (input code source) (by intro i; fin_cases i <;> rfl)
  have second := (RecoveryLiteralSignFrame.sign_ready negative).focus signSlots sign_injective (addressed code source native) (by
    intro i; fin_cases i
    · change install nativeSlots _ _ (nativeSlots 6)=_
      rw [install_slot _ native_injective]
      exact hSign
    all_goals
      rw [addressed,install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl)
  obtain ⟨paired,hPair,hPairField⟩ := PCPPairCold.pair_run [!negative] bits
  have third := hPair.focus pairSlots pair_injective (signed code source native negative)
    (pair_input code source bits native negative hAddress)
  have hall := ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ first second) third
  refine ⟨_,hall,?_⟩
  change install pairSlots _ _ (pairSlots 26)=_
  rw [install_slot _ pair_injective,hPairField]
  simp only [word,value,Nat.mul_zero,Nat.add_zero]

theorem word_value (negative : Bool) (bits : List Bool) :
    value (word negative bits)=Encodable.encode ((!negative,value bits) : TseitinCNF.EncodedLiteral) := by
  have hp := PCPPair.pair_bound [!negative] bits
  have hb := binary_value (PCPPair.width [!negative] bits) (Nat.pair (value [!negative]) (value bits)) hp
  have he : value [!negative]=(!negative).toNat := by simp only [value,Nat.mul_zero,Nat.add_zero]
  rw [he] at hb
  rw [word,hb]
  cases negative <;> rfl

end NearCubicWires.RepairSource.RecoverySourceLiteralCode
