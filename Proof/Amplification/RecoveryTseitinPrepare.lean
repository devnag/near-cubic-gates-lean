import Proof.Amplification.RecoveryTseitinMoves

/-! Reusable physical preparation for three original literal indices.
The finite signs select fixed prints; indices are copied from retained source
fields. The same source field may supply several repeated literals. -/
namespace NearCubicWires.RepairOrdinary.RecoveryTseitinKernel.Prepare
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.RecoveryTseitin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def literals (signs : Fin 3→Bool) (indices : Fin 3→Nat) : Literals := fun k=>(signs k,indices k)
def bytes (indices : Fin 3→Nat) := (indices 0).bits.length+(indices 1).bits.length+(indices 2).bits.length

theorem prepare_run (cap log : Nat) (signs : Fin 3→Bool) (sources : Fin 3→Fin 3) (indices : Fin 3→Nat)
    (ambient : Fin 239→List Bool) (padding : Fin 3→List Bool)
    (hcap : capacity (literals signs indices) ≤ cap) (hb : Bounded cap ambient)
    (hd : ambient 3=List.replicate cap true) (hl : ambient 4=List.replicate log false)
    (hz : log ≤ cap+1)
    (hp : ∀ k,ambient (sourceSlot sources k)=frame (indices k).bits++padding k) :
    ClockJoin.ReadyRun (machine signs sources) (2*cap+4*bytes indices+46) ambient
      (prepared cap (literals signs indices) (cleared cap ambient)) := by
  classical
  have hsign (k : Fin 3) : (frame (signs k).toNat.bits).length ≤ 3 := by
    generalize signs k=b
    cases b <;> decide
  have hlarge : 4*bytes indices+46 ≤ cap := by
    have h0 := (argument_widths (literals signs indices) 0).2
    have h1 := (argument_widths (literals signs indices) 1).2
    have h2 := (argument_widths (literals signs indices) 2).2
    change (indices 0).bits.length ≤ width (literals signs indices) at h0
    change (indices 1).bits.length ≤ width (literals signs indices) at h1
    change (indices 2).bits.length ≤ width (literals signs indices) at h2
    have hw : width (literals signs indices)+1 ≤ (width (literals signs indices)+1)^2 := by nlinarith
    unfold capacity at hcap
    unfold bytes
    omega
  have hword (k : Fin 3) : (frame (indices k).bits).length ≤ cap := by
    rw [frame_length]
    fin_cases k <;> dsimp <;> unfold bytes at hlarge <;> omega
  let a := cleared cap ambient
  let b := Function.update a (bank 0 2) (ZeroPadding.pad cap (frame (signs 0).toNat.bits))
  let c := Function.update b (bank 1 2) (ZeroPadding.pad cap (frame (signs 1).toNat.bits))
  let d := Function.update c (bank 2 2) (ZeroPadding.pad cap (frame (signs 2).toNat.bits))
  let e := Function.update d (bank 0 3) (ZeroPadding.pad cap (frame (indices 0).bits))
  let f := Function.update e (bank 1 3) (ZeroPadding.pad cap (frame (indices 1).bits))
  let g := Function.update f (bank 2 3) (ZeroPadding.pad cap (frame (indices 2).bits))
  obtain ⟨r,hr,ht,hh,hs⟩ := clear_run cap log ambient hb hd hl hz
  have hclear : ClockJoin.ReadyRun clearMachine (2*cap+4) ambient a := ⟨r,hr,ht,hh,hs.le⟩
  have hsign0 := literal_run (bank 0 2) (frame (signs 0).toNat.bits) cap a (by decide)
    ((hsign 0).trans (by omega)) (by simp [a,cleared,bank])
    (by simp [a,cleared])
  have hsign1 := literal_run (bank 1 2) (frame (signs 1).toNat.bits) cap b (by decide)
    ((hsign 1).trans (by omega)) (by simp [b,a,cleared,bank])
    (by simp [b,a,cleared,bank])
  have hsign2 := literal_run (bank 2 2) (frame (signs 2).toNat.bits) cap c (by decide)
    ((hsign 2).trans (by omega)) (by simp [c,b,a,cleared,bank])
    (by simp [c,b,a,cleared,bank])
  have hsource0 : d (sourceSlot sources 0)=frame (indices 0).bits++padding 0 := by
    have hv : (sourceSlot sources 0).val<3 := (sources 0).isLt
    have he0 : sourceSlot sources 0≠bank 0 2 := by intro he; rw [he] at hv; contradiction
    have he1 : sourceSlot sources 0≠bank 1 2 := by intro he; rw [he] at hv; contradiction
    have he2 : sourceSlot sources 0≠bank 2 2 := by intro he; rw [he] at hv; contradiction
    have he3 : sourceSlot sources 0≠bank 0 3 := by intro he; rw [he] at hv; contradiction
    have he4 : sourceSlot sources 0≠bank 1 3 := by intro he; rw [he] at hv; contradiction
    simpa [d,c,b,a,cleared,he0,he1,he2,he3,he4,hv] using hp 0
  have hcopy0 := copy_run sources 0 cap (indices 0).bits (padding 0) d (hword 0) hsource0
    (by simp [d,c,b,a,cleared,bank,destinationSlot]) (by simp [d,c,b,a,cleared,bank])
  have hsource1 : e (sourceSlot sources 1)=frame (indices 1).bits++padding 1 := by
    have hv : (sourceSlot sources 1).val<3 := (sources 1).isLt
    have he0 : sourceSlot sources 1≠bank 0 2 := by intro he; rw [he] at hv; contradiction
    have he1 : sourceSlot sources 1≠bank 1 2 := by intro he; rw [he] at hv; contradiction
    have he2 : sourceSlot sources 1≠bank 2 2 := by intro he; rw [he] at hv; contradiction
    have he3 : sourceSlot sources 1≠bank 0 3 := by intro he; rw [he] at hv; contradiction
    have he4 : sourceSlot sources 1≠bank 1 3 := by intro he; rw [he] at hv; contradiction
    simpa [e,d,c,b,a,cleared,he0,he1,he2,he3,he4,hv] using hp 1
  have hcopy1 := copy_run sources 1 cap (indices 1).bits (padding 1) e (hword 1) hsource1
    (by simp [e,d,c,b,a,cleared,bank,destinationSlot]) (by simp [e,d,c,b,a,cleared,bank])
  have hsource2 : f (sourceSlot sources 2)=frame (indices 2).bits++padding 2 := by
    have hv : (sourceSlot sources 2).val<3 := (sources 2).isLt
    have he0 : sourceSlot sources 2≠bank 0 2 := by intro he; rw [he] at hv; contradiction
    have he1 : sourceSlot sources 2≠bank 1 2 := by intro he; rw [he] at hv; contradiction
    have he2 : sourceSlot sources 2≠bank 2 2 := by intro he; rw [he] at hv; contradiction
    have he3 : sourceSlot sources 2≠bank 0 3 := by intro he; rw [he] at hv; contradiction
    have he4 : sourceSlot sources 2≠bank 1 3 := by intro he; rw [he] at hv; contradiction
    simpa [f,e,d,c,b,a,cleared,he0,he1,he2,he3,he4,hv] using hp 2
  have hcopy2 := copy_run sources 2 cap (indices 2).bits (padding 2) f (hword 2) hsource2
    (by simp [f,e,d,c,b,a,cleared,bank,destinationSlot]) (by simp [f,e,d,c,b,a,cleared,bank])
  have whole := ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _
      (ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _
        (ClockJoin.join _ _ _ _ _ _ _ hclear hsign0) hsign1) hsign2) hcopy0) hcopy1) hcopy2
  have he : g=prepared cap (literals signs indices) a := by
    funext i
    by_cases h0 : i=bank 0 2
    · subst i; simp [g,f,e,d,c,b,a,prepared,bank,literals]
    by_cases h1 : i=bank 0 3
    · subst i; simp [g,f,e,d,c,b,a,prepared,bank,literals]
    by_cases h2 : i=bank 1 2
    · subst i; simp [g,f,e,d,c,b,a,prepared,bank,literals]
    by_cases h3 : i=bank 1 3
    · subst i; simp [g,f,e,d,c,b,a,prepared,bank,literals]
    by_cases h4 : i=bank 2 2
    · subst i; simp [g,f,e,d,c,b,a,prepared,bank,literals]
    by_cases h5 : i=bank 2 3
    · subst i; simp [g,f,e,d,c,b,a,prepared,bank,literals]
    simp only [g,f,e,d,c,b,Function.update,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,prepared]
    by_cases hi : i.val<5
    · simp [hi,h0,h1,h2,h3,h4,h5]
    · simp [hi,h0,h1,h2,h3,h4,h5,a,cleared,show ¬i.val<3 by omega,show i.val≠3 by omega,show i.val≠4 by omega]
  have hbudget : (2*cap+4)+1+(2*(frame (signs 0).toNat.bits).length+2)+1+
      (2*(frame (signs 1).toNat.bits).length+2)+1+(2*(frame (signs 2).toNat.bits).length+2)+1+
      (4*(indices 0).bits.length+4)+1+(4*(indices 1).bits.length+4)+1+(4*(indices 2).bits.length+4) ≤
      2*cap+4*bytes indices+46 := by
    have h0 := hsign 0
    have h1 := hsign 1
    have h2 := hsign 2
    unfold bytes
    omega
  have result := ClockJoin.enlarge _ _ _ _ _ whole hbudget
  change ClockJoin.ReadyRun (machine signs sources) _ ambient g at result
  rw [he] at result
  exact result

end NearCubicWires.RepairOrdinary.RecoveryTseitinKernel.Prepare
