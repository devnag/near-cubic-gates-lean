import Proof.Amplification.RecoveryQueryMoves

/-! Whole physical preparation of the three prefix-query operands. It
executes one complete clear, two literal prints and three retained-source
copies, including every composition return and all local head resets. -/
namespace NearCubicWires.RepairOrdinary.RecoveryQueryKernel.Prepare
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prepare_run (cap log : Nat) (flat : Bool) (payload committed count : Nat)
    (ambient : Fin 357→List Bool) (paddedPayload paddedCommitted paddedCount : List Bool)
    (hcap : capacity payload committed count ≤ cap) (hb : Bounded cap ambient)
    (hd : ambient 3=List.replicate cap true) (hl : ambient 4=List.replicate log false)
    (hz : log ≤ cap+1)
    (hp : ambient 0=frame payload.bits++paddedPayload)
    (ha : ambient 1=frame committed.bits++paddedCommitted)
    (hn : ambient 2=frame count.bits++paddedCount) :
    ClockJoin.ReadyRun (machine flat) (2*cap+4*bytes payload committed count+40) ambient
      (prepared cap flat payload committed count (cleared cap ambient)) := by
  classical
  have hbase : bytes payload committed count+1 ≤ (bytes payload committed count+1)^2 := by nlinarith
  have hpos : 1 ≤ (bytes payload committed count+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hlarge : 4*bytes payload committed count+40 ≤ cap := by unfold capacity at hcap; omega
  have hpw : (frame payload.bits).length ≤ cap := by rw [frame_length]; unfold bytes at hlarge; omega
  have haw : (frame committed.bits).length ≤ cap := by rw [frame_length]; unfold bytes at hlarge; omega
  have hnw : (frame count.bits).length ≤ cap := by rw [frame_length]; unfold bytes at hlarge; omega
  have htag : (frame flat.toNat.bits).length ≤ 3 := by cases flat <;> decide
  let a := cleared cap ambient
  let b := Function.update a (bank 0 2) (ZeroPadding.pad cap (frame (1 : Nat).bits))
  let c := Function.update b (bank 5 2) (ZeroPadding.pad cap (frame flat.toNat.bits))
  let d := Function.update c (bank 5 3) (ZeroPadding.pad cap (frame payload.bits))
  let e := Function.update d (bank 2 3) (ZeroPadding.pad cap (frame committed.bits))
  let f := Function.update e (bank 0 3) (ZeroPadding.pad cap (frame count.bits))
  obtain ⟨r,hr,ht,hh,hs⟩ := clear_run cap log ambient hb hd hl hz
  have hclear : ClockJoin.ReadyRun clearMachine (2*cap+4) ambient a := ⟨r,hr,ht,hh,hs.le⟩
  have hone := literal_run (bank 0 2) (frame (1 : Nat).bits) cap a (by decide)
    (by change 3 ≤ cap; omega) (by simp [a,cleared,bank]) (by simp [a,cleared])
  have htagrun := literal_run (bank 5 2) (frame flat.toNat.bits) cap b (by decide)
    (by omega) (by simp [b,a,cleared,bank]) (by simp [b,a,cleared,bank])
  have hcopy0 := copy_run 0 cap payload.bits paddedPayload c hpw
    (by simpa [c,b,a,cleared,bank,sourceSlot] using hp)
    (by simp [c,b,a,cleared,bank,destinationSlot]) (by simp [c,b,a,cleared,bank])
  have hcopy1 := copy_run 1 cap committed.bits paddedCommitted d haw
    (by simpa [d,c,b,a,cleared,bank,sourceSlot] using ha)
    (by simp [d,c,b,a,cleared,bank,destinationSlot]) (by simp [d,c,b,a,cleared,bank])
  have hcopy2 := copy_run 2 cap count.bits paddedCount e hnw
    (by simpa [e,d,c,b,a,cleared,bank,sourceSlot] using hn)
    (by simp [e,d,c,b,a,cleared,bank,destinationSlot]) (by simp [e,d,c,b,a,cleared,bank])
  have whole := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _
      (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hclear hone) htagrun) hcopy0) hcopy1) hcopy2
  have he : f=prepared cap flat payload committed count a := by
    funext i
    by_cases h0 : i=bank 0 2
    · subst i; simp [f,e,d,c,b,a,prepared,bank]
    by_cases h1 : i=bank 0 3
    · subst i; simp [f,e,d,c,b,a,prepared,bank]
    by_cases h2 : i=bank 2 3
    · subst i; simp [f,e,d,c,b,a,prepared,bank]
    by_cases h3 : i=bank 5 2
    · subst i; simp [f,e,d,c,b,a,prepared,bank]
    by_cases h4 : i=bank 5 3
    · subst i; simp [f,e,d,c,b,a,prepared,bank]
    simp only [f,e,d,c,b,Function.update,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,prepared]
    by_cases hi : i.val<5
    · simp [hi,h0,h1,h2,h3,h4]
    · simp [hi,h0,h1,h2,h3,h4,a,cleared,show ¬i.val<3 by omega,show i.val≠3 by omega,show i.val≠4 by omega]
  have hbudget : (2*cap+4)+1+(2*(frame (1 : Nat).bits).length+2)+1+
      (2*(frame flat.toNat.bits).length+2)+1+(4*payload.bits.length+4)+1+
      (4*committed.bits.length+4)+1+(4*count.bits.length+4) ≤
      2*cap+4*bytes payload committed count+40 := by
    have hones : (frame (1 : Nat).bits).length=3 := rfl
    unfold bytes
    omega
  have result := ClockJoin.enlarge _ _ _ _ _ whole hbudget
  change ClockJoin.ReadyRun (machine flat) _ ambient f at result
  rw [he] at result
  exact result

end NearCubicWires.RepairOrdinary.RecoveryQueryKernel.Prepare
