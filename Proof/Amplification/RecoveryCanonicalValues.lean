import Proof.Amplification.RecoveryCanonicalMarker

/-! The retained physical source equality identifies every broadcast's
canonical count and row suffix. No certificate value is supplied as a tape. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem frame_injective : Function.Injective frame := by
  intro xs
  induction xs with
  | nil=>
    intro ys h
    cases ys with
    | nil=>rfl
    | cons y ys=>simp [frame] at h
  | cons x xs ih=>
    intro ys h
    cases ys with
    | nil=>simp [frame] at h
    | cons y ys=>
      have hh := List.cons.inj (List.cons.inj h).2
      exact congrArg₂ List.cons hh.1 (ih hh.2)

theorem count_word_injective : Function.Injective CompareMachine.word := by
  intro n m h
  have hh := congrArg List.length h
  simpa only [CompareMachine.word,List.length_cons,List.length_replicate,Nat.add_left_inj] using hh

theorem source_values (code : Nat) (c : Certificate) (a : Fin 338→List Bool)
    (n m : Nat) (ib ob : List Bool)
    (ht : TableTapes markerTableSlots code c a)
    (hs : (fun j=>a (RecoveryColdCompact.sourceSlots j))=
      RecoveryColdCompact.sourceTapes code.bits (TableFirst.pack (Serialization.width code) c) ib ob n m) :
    n=c.inner.length ∧ ib=innerBits code c ∧ m=c.outer.length ∧ ob=outerBits code c := by
  obtain ⟨hn,hib,hm,hob⟩ := ht
  have h8 := congrFun hs 8
  have h4 := congrFun hs 4
  have h9 := congrFun hs 9
  have h5 := congrFun hs 5
  change a 270=CompareMachine.word n at h8
  change a 271=frame ib at h4
  change a 274=CompareMachine.word m at h9
  change a 275=frame ob at h5
  exact ⟨count_word_injective (h8.symm.trans hn),frame_injective (h4.symm.trans hib),
    count_word_injective (h9.symm.trans hm),frame_injective (h5.symm.trans hob)⟩

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
