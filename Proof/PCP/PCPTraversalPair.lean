import Proof.PCP.PCPTraversalClear

/-! Executed clear/pair blocks inside the one fixed traversal controller.
All three pair sites use the same physical bank, retained operands, measured
capacity and reset log. Call and return transitions are charged. -/
namespace NearCubicWires.RepairOrdinary.PCPTraversal
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def atCall (j : Fin 39) (heads : Fin 128 → ℕ) (tapes : Fin 128 → List Bool) :=
  controlConfig (RecoveryCalls.code sizes j)
    (RecoveryCalls.restarted (programs j) heads tapes)
def Path (j k : Fin 39) (fuel : ℕ) (beforeHeads : Fin 128 → ℕ)
    (beforeTapes : Fin 128 → List Bool) (afterHeads : Fin 128 → ℕ)
    (afterTapes : Fin 128 → List Bool) : Prop :=
  ∃ n≤fuel,Timed machine n (atCall j beforeHeads beforeTapes) (atCall k afterHeads afterTapes)

theorem Path.trans {j k l : Fin 39} {a b : ℕ} {h₁ h₂ h₃ : Fin 128 → ℕ}
    {t₁ t₂ t₃ : Fin 128 → List Bool} (first : Path j k a h₁ t₁ h₂ t₂)
    (second : Path k l b h₂ t₂ h₃ t₃) : Path j l (a+b) h₁ t₁ h₃ t₃ := by
  obtain ⟨n,hn,hfirst⟩ := first
  obtain ⟨m,hm,hsecond⟩ := second
  exact ⟨n+m,by omega,hfirst.trans hsecond⟩

theorem packed_path (j k : Fin 39) (p : Packed) (hp : call j=p)
    (fuel : ℕ) (heads : Fin 128 → ℕ) (ambient out : Fin 128 → List Bool)
    (hrun : ∃ r,runFrom p.2 fuel ⟨p.2.start,heads,ambient⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=out)
    (hn : ∀ q scanned,next j q scanned=some k) :
    Path j k (fuel+1) heads ambient heads out := by
  subst p
  obtain ⟨r,hr,hh,ht⟩ := hrun
  obtain ⟨n,hbound,hpath⟩ := call_receipt sizes programs 37 next j k fuel
    (RecoveryCalls.restarted (programs j) heads ambient) r hr (hn _ _)
  rw [hh,ht] at hpath
  exact ⟨n,hbound,hpath⟩

theorem clear_path {t : ℕ} (j k : Fin 39) (slot : Fin t → Fin 128)
    (hp : call j=clear slot) (hn : ∀ q scanned,next j q scanned=some k)
    (hi : Function.Injective slot) (hd : ∀ i,slot i≠28) (hl : ∀ i,slot i≠127)
    (cap log : ℕ) (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hb : ∀ i,(ambient (slot i)).length≤cap)
    (hdriver : ambient 28=List.replicate cap true)
    (hlog : ambient 127=List.replicate log false)
    (hh : ∀ i,heads (slot i)=0) (hhd : heads 28=0) (hhl : heads 127=0) :
    Path j k (2*cap+5) heads ambient heads (cleared slot cap log ambient) := by
  obtain ⟨r,hr,hheads,htapes,_⟩ := clear_run slot hi hd hl cap log heads ambient
    hb hdriver hlog hh hhd hhl
  exact packed_path j k (clear slot) hp (2*cap+4) heads ambient _
    ⟨r,hr,hheads,htapes⟩ hn

theorem bank_ne (i : Fin 38) (j : Fin 128) (hj : 77≤j.val ∨ j.val<39) : bank i≠j := by
  intro h
  have hv := congrArg (fun k : Fin 128 => k.val) h
  dsimp [bank] at hv
  omega

theorem cleared_bank_input (cap log : ℕ) (left right : List Bool)
    (ambient : Fin 128 → List Bool)
    (hl : ambient 83=ZeroPadding.pad cap (frame left))
    (hr : ambient 84=ZeroPadding.pad cap (frame right)) (i : Fin 38) :
    cleared bank cap log ambient (pairSlots i)=PCPPairReusable.input cap left right i := by
  simp only [PCPPairReusable.input,PCPPairCanonical.input,pairSlots]
  split
  · exact (cleared_other bank cap log ambient 83
      (fun j => bank_ne j 83 (by decide)) (by decide) (by decide)).trans hl
  · split
    · exact (cleared_other bank cap log ambient 84
        (fun j => bank_ne j 84 (by decide)) (by decide) (by decide)).trans hr
    · rw [cleared_slot bank bank_injective (fun j => (clear_preserves_drivers j).1)
        (fun j => (clear_preserves_drivers j).2)]
      simp [ZeroPadding.pad]

theorem pair_clear_calls (j k l : Fin 39)
    (hj : call j=clear bank) (hk : call k=focused pairSlots PCPPairCanonical.machine)
    (hjk : ∀ q scanned,next j q scanned=some k)
    (hkl : ∀ q scanned,next k q scanned=some l)
    (cap log : ℕ) (left right : List Bool)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hpos : 0<Nat.pair (value left) (value right))
    (hcap : PCPPairCanonical.budget left right+1≤cap)
    (hb : ∀ i,(ambient (bank i)).length≤cap)
    (hdriver : ambient 28=List.replicate cap true)
    (hlog : ambient 127=List.replicate log false)
    (hleft : ambient 83=ZeroPadding.pad cap (frame left))
    (hright : ambient 84=ZeroPadding.pad cap (frame right))
    (hhbank : ∀ i,heads (bank i)=0) (hhpair : ∀ i,heads (pairSlots i)=0)
    (hhd : heads 28=0) (hhl : heads 127=0) :
    ∃ localOut : Fin 38 → List Bool,
      Path j l (2*cap+PCPPairCanonical.budget left right+6) heads ambient heads
        (install pairSlots (cleared bank cap log ambient) localOut) ∧
      localOut 26=ZeroPadding.pad cap (frame (Nat.pair (value left) (value right)).bits) ∧
      ∀ i,(localOut i).length≤cap := by
  have hclear := clear_path j k bank hj hjk bank_injective
    (fun i => (clear_preserves_drivers i).1) (fun i => (clear_preserves_drivers i).2)
    cap log heads ambient hb hdriver hlog hhbank hhd hhl
  obtain ⟨localOut,hready,hout,hsize⟩ := PCPPairReusable.pair_run cap left right hpos hcap
  obtain ⟨r,hr,hh,ht,_⟩ := hready.focus_at pairSlots pair_injective heads
    (cleared bank cap log ambient) (cleared_bank_input cap log left right ambient hleft hright) hhpair
  have hpair := packed_path k l (focused pairSlots PCPPairCanonical.machine) hk _ heads
    (cleared bank cap log ambient) _ ⟨r,hr,hh,ht⟩ hkl
  have hpath := hclear.trans hpair
  have he : (2*cap+5)+(PCPPairCanonical.budget left right+1)=
      2*cap+PCPPairCanonical.budget left right+6 := by omega
  rw [he] at hpath
  exact ⟨localOut,hpath,hout,hsize⟩

theorem pair_leaf_path (cap log : ℕ) (left right : List Bool)
    (heads : Fin 128 → ℕ) (ambient : Fin 128 → List Bool)
    (hpos : 0<Nat.pair (value left) (value right))
    (hcap : PCPPairCanonical.budget left right+1≤cap)
    (hb : ∀ i,(ambient (bank i)).length≤cap)
    (hdriver : ambient 28=List.replicate cap true)
    (hlog : ambient 127=List.replicate log false)
    (hleft : ambient 83=ZeroPadding.pad cap (frame left))
    (hright : ambient 84=ZeroPadding.pad cap (frame right))
    (hhbank : ∀ i,heads (bank i)=0) (hhpair : ∀ i,heads (pairSlots i)=0)
    (hhd : heads 28=0) (hhl : heads 127=0) :
    ∃ localOut : Fin 38 → List Bool,
      Path 5 7 (2*cap+PCPPairCanonical.budget left right+6) heads ambient heads
        (install pairSlots (cleared bank cap log ambient) localOut) ∧
      localOut 26=ZeroPadding.pad cap (frame (Nat.pair (value left) (value right)).bits) ∧
      ∀ i,(localOut i).length≤cap := by
  exact pair_clear_calls 5 6 7 rfl rfl (by intro q scanned; simp [next])
    (by intro q scanned; simp [next]) cap log left right heads ambient hpos hcap hb hdriver
    hlog hleft hright hhbank hhpair hhd hhl

end NearCubicWires.RepairOrdinary.PCPTraversal
