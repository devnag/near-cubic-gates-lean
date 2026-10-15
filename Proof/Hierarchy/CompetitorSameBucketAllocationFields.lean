import Proof.Hierarchy.CompetitorSameBucketAllocate

/-! Exact allocated fields and preservation for the next scalar initializer. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdAllocate
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scalar_avoids_old (i : Fin 398) (hi : i≠358) (j : Fin 40) : scalarSlots j≠i.castAdd 44 := by
  intro h
  have hv:=congrArg Fin.val h
  unfold scalarSlots at hv
  split at hv
  · change 398+j.val=i.val at hv; omega
  · split at hv
    · have he : i=358 := Fin.ext (by simpa using hv.symm)
      exact hi he
    · change 436=i.val at hv; omega

theorem packet_avoids_old (i : Fin 398) (hi : i≠132) (j : Fin 6) : packetSlots j≠i.castAdd 44 := by
  intro h
  have hv:=congrArg Fin.val h
  fin_cases j
  · change 437=i.val at hv; omega
  · change 438=i.val at hv; omega
  · change 439=i.val at hv; omega
  · change 440=i.val at hv; omega
  · exact hi (Fin.ext hv.symm)
  · change 441=i.val at hv; omega

theorem output_old (c d : ℕ) (tapes : Fin 398 → List Bool)
    (hc : tapes 358=List.replicate c true) (hd : tapes 132=List.replicate d true) (i : Fin 398) :
    output c d tapes (i.castAdd 44)=tapes i := by
  by_cases h132 : i=132
  · subst i
    exact (install_slot packetSlots packet_injective _ (eraseOutput 4 d) 4).trans hd.symm
  unfold output
  rw [install_other packetSlots _ _ _ (packet_avoids_old i h132)]
  by_cases h358 : i=358
  · subst i
    exact (install_slot scalarSlots scalar_injective _ (eraseOutput 38 c) 38).trans hc.symm
  rw [install_other scalarSlots _ _ _ (scalar_avoids_old i h358)]
  simp only [oldTapes,Fin.addCases_left]

theorem scalar_output (c d : ℕ) (tapes : Fin 398 → List Bool) (j : Fin 40) :
    output c d tapes (scalarSlots j)=eraseOutput 38 c j := by
  unfold output
  rw [install_other packetSlots _ _ _ (fun k => Ne.symm (packet_avoids k j))]
  exact install_slot scalarSlots scalar_injective _ _ j

theorem packet_output (c d : ℕ) (tapes : Fin 398 → List Bool) (j : Fin 6) :
    output c d tapes (packetSlots j)=eraseOutput 4 d j :=
  install_slot packetSlots packet_injective _ _ j

theorem scalar_cell (c d : ℕ) (tapes : Fin 398 → List Bool) (j : Fin 38) :
    output c d tapes ⟨398+j.val,by omega⟩=List.replicate c false := by
  have h:=scalar_output c d tapes (j.castAdd 2)
  have hs : scalarSlots (j.castAdd 2)=⟨398+j.val,by omega⟩ := by simp only [scalarSlots,Fin.val_castAdd,j.isLt,ite_true]
  rw [hs] at h
  have he : (j.castAdd 1).castAdd 1=j.castAdd 2 := Fin.ext rfl
  rw [←he] at h
  simpa only [eraseOutput,Fin.addCases_left] using h

theorem scalar_reset (c d : ℕ) (tapes : Fin 398 → List Bool) :
    output c d tapes 436=List.replicate (c+1) false := scalar_output c d tapes 39

theorem packet_cell (c d : ℕ) (tapes : Fin 398 → List Bool) (j : Fin 4) :
    output c d tapes ⟨437+j.val,by omega⟩=List.replicate d false := by
  fin_cases j
  · exact packet_output c d tapes 0
  · exact packet_output c d tapes 1
  · exact packet_output c d tapes 2
  · exact packet_output c d tapes 3

theorem packet_reset (c d : ℕ) (tapes : Fin 398 → List Bool) :
    output c d tapes 441=List.replicate (d+1) false := packet_output c d tapes 5

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdAllocate
