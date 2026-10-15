import Proof.PCP.PCPPNativeCanonicalGuard
import Proof.Amplification.RecoveryDecodeStep

/-! The concrete reusable balanced-tree head call. It decodes one natural
pair and classifies its retained tag while preserving the payload at tape0.
All scratch is finite, reused and bounded by the original word width. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalTree
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Data where
  bits : List Bool
  reset : ℕ
  backing : Fin 20→List Bool
  flags : Fin 3→Bool

def Data.tapes (d : Data) : Fin 26→List Bool := Fin.addCases
  (m:=23) (n:=3) (motive:=fun _=>List Bool)
  (RecoveryReusableUnpair.input d.bits d.reset d.backing) (fun i=>[d.flags i])
def Data.Valid (d : Data) := ∀ i,(d.backing i).length≤RecoveryReusableUnpair.capacity d.bits

def decoded (left : Bool) (d : Data) : Data :=
  ⟨RecoveryChildSelection.word left d.bits,
    max d.reset (RecoveryReusableUnpair.capacity d.bits+1),
    RecoveryChildSelection.backing d.bits d.reset,d.flags⟩
noncomputable def decode (left : Bool) := TapeEmbedding.machine 3 (RecoveryDecodeStep.machine left)

theorem decode_ready (left : Bool) (d : Data) (hd : d.Valid) :
    ReadyRun (decode left) (RecoveryDecodeStep.time d.bits) d.tapes (decoded left d).tapes := by
  exact (RecoveryDecodeStep.decode_ready left d.bits d.reset d.backing hd).embed (fun i=>[d.flags i])

theorem decoded_valid (left : Bool) (d : Data) : (decoded left d).Valid :=
  RecoveryDecodeStep.next_backing_bound left d.bits d.reset

def tag (d : Data) := RecoveryFixedUnpair.leftWord d.bits
def kindSlots : Fin 5→Fin 26 := ![17,23,24,25,22]
theorem kindSlots_injective : Function.Injective kindSlots := by decide
noncomputable def kind := RecoveryFocus.machine kindSlots RecoveryRowKind.machine

def classified (d : Data) : Data :=
  { decoded false d with
    backing:=Function.update (decoded false d).backing 16
      (ZeroPadding.pad (RecoveryReusableUnpair.capacity d.bits) (frame (RecoveryRowKind.after (tag d))))
    flags:=fun i=>decide (value (tag d)=i.val) }

theorem capacity_frame (bits : List Bool) : 2*bits.length+1≤RecoveryReusableUnpair.capacity bits := by
  unfold RecoveryReusableUnpair.capacity RecoveryTapeSupport.capacity
  nlinarith [sq_nonneg (bits.length : ℤ)]

theorem kind_ready (d : Data) : ReadyRun kind (RecoveryRowKind.time (tag d))
    (decoded false d).tapes (classified d).tapes := by
  let C:=RecoveryReusableUnpair.capacity d.bits
  let R:=max d.reset (C+1)
  have hw:(tag d).length=d.bits.length:=(RecoveryFixedUnpair.word_lengths d.bits).1
  have hc:2*(tag d).length+1≤R:=by
    rw [hw]
    exact (capacity_frame d.bits).trans (by dsimp [R];omega)
  have h:=RecoveryChildSelection.ReadyRun.pad
    (RecoveryRowKind.kind_ready (tag d) d.flags R) ![C,0,0,0,0]
  rw [Nat.max_eq_left hc] at h
  have hfocus:=h.focus kindSlots kindSlots_injective (decoded false d).tapes (by
    intro i
    fin_cases i
    · rfl
    · simp [RecoveryRowKind.tapes]
      rfl
    · simp [RecoveryRowKind.tapes]
      rfl
    · simp [RecoveryRowKind.tapes]
      rfl
    · simp [RecoveryRowKind.tapes]
      rfl)
  have he:install kindSlots (decoded false d).tapes
      (fun i=>ZeroPadding.pad (![C,0,0,0,0] i)
        (RecoveryRowKind.tapes (RecoveryRowKind.after (tag d))
          (fun i=>decide (value (tag d)=i.val)) R i))=(classified d).tapes := by
    funext i
    fin_cases i
    case «17»=>exact (install_slot kindSlots kindSlots_injective _ _ 0).trans (by rfl)
    case «23»=>exact (install_slot kindSlots kindSlots_injective _ _ 1).trans (by rfl)
    case «24»=>exact (install_slot kindSlots kindSlots_injective _ _ 2).trans (by rfl)
    case «25»=>exact (install_slot kindSlots kindSlots_injective _ _ 3).trans (by rfl)
    case «22»=>exact (install_slot kindSlots kindSlots_injective _ _ 4).trans (ZeroPadding.pad_zero _)
    all_goals
      rw [install_other kindSlots _ _ _ (by intro j;fin_cases j <;> decide)]
      rfl
  rw [he] at hfocus
  exact hfocus

theorem classified_valid (d : Data) : (classified d).Valid := by
  intro i
  by_cases hi:i=16
  · subst i
    dsimp only [classified]
    rw [Function.update_self]
    simp only [ZeroPadding.pad,List.length_append,List.length_replicate,frame_length]
    have hafter:(RecoveryRowKind.after (tag d)).length=d.bits.length:=by
      simp [RecoveryRowKind.after,RecoveryLiteralTag.predWord,RecoveryListPredecessor.result_length,tag,RecoveryFixedUnpair.word_lengths]
    have hc:=capacity_frame d.bits
    have hw:=RecoveryChildSelection.word_length false d.bits
    simp only [hafter,decoded,RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,hw] at *
    omega
  · dsimp only [classified]
    rw [Function.update_of_ne hi]
    exact decoded_valid false d i

noncomputable def head := Composition.machine (decode false) kind
def headTime (d : Data) := RecoveryDecodeStep.time d.bits+1+RecoveryRowKind.time (tag d)

theorem head_ready (d : Data) (hd : d.Valid) : ReadyRun head (headTime d) d.tapes (classified d).tapes := by
  obtain ⟨first,hfirst,hft,hfh,hfs⟩:=decode_ready false d hd
  obtain ⟨last,hlast,hlt,hlh,hls⟩:=kind_ready d
  have hi:Composition.restart first.final kind.start=initialConfiguration kind (decoded false d).tapes:=by
    apply configuration_ext
    · rfl
    · funext i;exact hfh i
    · exact hft
  unfold run at hlast
  rw [←hi] at hlast
  have h:=Composition.run_join (decode false) kind _ _ _ first last hfirst hlast
  exact ⟨Composition.joinedReceipt first last,h,hlt,hlh,by simp only [Composition.joinedReceipt,hfs,hls,headTime]⟩

theorem head_bound (d : Data) : headTime d≤131072*(d.bits.length+1)^2 := by
  have h:=RecoveryDecodeStep.time_bound d.bits
  have hw:(tag d).length=d.bits.length:=(RecoveryFixedUnpair.word_lengths d.bits).1
  unfold headTime RecoveryRowKind.time RecoveryDecodeStep.budget at *
  rw [hw]
  nlinarith

theorem classified_payload (d : Data) : value (classified d).bits=(Nat.unpair (value d.bits)).2 :=
  RecoveryDecodeStep.child_value false d.bits

theorem classified_flag (d : Data) (i : Fin 3) :
    (classified d).flags i=decide ((Nat.unpair (value d.bits)).1=i.val) := by
  change decide (value (tag d)=i.val)=_
  rw [tag,(RecoveryFixedUnpair.word_values d.bits).1]

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalTree
