import Proof.MachineModel.ClockEmptyInput

/-! Total input-derived dyadic clock constructor. The first physical branch
reads the framed input marker, then calls either the fixed empty-input branch
or the accepted nonempty producer. Returns and final stop are charged. -/
namespace NearCubicWires.RepairOrdinary.ClockTotal
open LocalBitMultitape ClockJoin RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def marker : Machine 34 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none
def sizes (k c : ℕ) : Fin 3 → ℕ := ![1,k+1+2+14,50+ClockWordLayout.states k c]
def programs (k c : ℕ) : (j : Fin 3) → Machine 34 (sizes k c j)
  | ⟨0,_⟩ => marker
  | ⟨1,_⟩ => ClockEmptyInput.machine k
  | ⟨2,_⟩ => ClockFromInput.machine k c
  | ⟨n+3,h⟩ => False.elim (by omega)
def next (k c : ℕ) (j : Fin 3) (_ : Fin (sizes k c j))
    (bits : Fin 34 → Bool) : Option (Fin 3) :=
  if j.val=0 then some (if bits 12 then 2 else 1) else none
noncomputable def machine (k c : ℕ) := RecoveryCalls.machine (sizes k c) (programs k c) 0 (next k c)
def budget (k c : ℕ) (bits : List Bool) : ℕ :=
  402*(c+k+1)*(bits.length+1)*PCPResourceLedger.q bits.length^2

theorem selected_run (k c : ℕ) (bits : List Bool) (j : Fin 3) (fuel : ℕ)
    (hj : j.val≠0)
    (hselect : next k c 0 marker.start
      (initialConfiguration marker (ClockFromInput.input bits)).scanned=some j)
    (output : Fin 34 → List Bool)
    (hbody : ReadyRun (programs k c j) fuel (ClockFromInput.input bits) output) :
    ReadyRun (machine k c) (fuel+2) (ClockFromInput.input bits) output := by
  obtain ⟨body,hb,ht,hh,hs⟩ := hbody
  have hstart := RecoveryCalls.return_step (sizes k c) (programs k c) 0 (next k c)
    0 j (initialConfiguration marker (ClockFromInput.input bits)) (by rfl) hselect
  obtain ⟨hp,hhalt⟩ := prefix_of_run (programs k c j) fuel _ body hb
  have hrun := RecoveryCalls.body_timed (sizes k c) (programs k c) 0 (next k c) j
    ⟨body.peakTapeCells,hp⟩
  have hend := RecoveryCalls.stop_step (sizes k c) (programs k c) 0 (next k c) j
    body.final hhalt (by simp [next,hj])
  have hfirst := Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) hstart
  have hlast := Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) hend
  have hjoined := (hfirst.trans hrun).trans hlast
  have hhalted : (machine k c).halted
      (RecoveryCalls.stopped (sizes k c) body.final.heads body.final.tapes).control=true := by
    simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
  obtain ⟨r,hr,hf,hsteps⟩ := hjoined.run hhalted
  have htime : 1+body.steps+1≤fuel+2 := by omega
  have hmore := runFrom_moreFuel (machine k c) (1+body.steps+1)
    (fuel+2-(1+body.steps+1)) _ r hr
  rw [Nat.add_sub_of_le htime] at hmore
  refine ⟨r,hmore,?_,?_,hsteps.le.trans htime⟩
  · rw [hf]
    exact ht
  · rw [hf]
    exact hh

theorem input_marker (bits : List Bool) :
    (initialConfiguration marker (ClockFromInput.input bits)).scanned 12=
      !bits.isEmpty := by
  change readTapeBit (frame bits) 0= _
  cases bits <;> rfl

theorem budget_positive (k c : ℕ) (bits : List Bool) :
    1≤(c+k+1)*(bits.length+1)*PCPResourceLedger.q bits.length^2 := by
  have hq : 1≤PCPResourceLedger.q bits.length^2 :=
    Nat.one_le_pow _ _ (by simp [PCPResourceLedger.q])
  have hprod : 1≤(c+k+1)*(bits.length+1) := by nlinarith
  nlinarith

theorem nonempty_budget (k c : ℕ) (bits : List Bool) :
    ClockFromInput.budget k c bits+2≤budget k c bits := by
  have hp := budget_positive k c bits
  have he : budget k c bits=ClockFromInput.budget k c bits+
      2*((c+k+1)*(bits.length+1)*PCPResourceLedger.q bits.length^2) := by
    dsimp [budget,ClockFromInput.budget]
    ring
  rw [he]
  omega

theorem empty_budget (k c : ℕ) : 6*k+25+2≤budget k c [] := by
  simp [budget,PCPResourceLedger.q,PCPResourceLedger.ell]
  omega

theorem entry_run (k c : ℕ) (bits : List Bool) :
    ∃ r : ExecutionReceipt 34 (Fintype.card (RecoveryCalls.Control (sizes k c))),
      run (machine k c) (budget k c bits) (ClockFromInput.input bits)=some r ∧
      r.final.tapes 29=frame (SignedSortKey.binary (ClockEnvelope.exponent k c bits.length+1)
        (ClockEnvelope.clock k c bits.length)) ∧
      r.final.tapes 27=List.replicate (ClockEnvelope.exponent k c bits.length) true ∧
      r.final.tapes 12=frame bits ∧ (∀ i,r.final.heads i=0) ∧ r.steps≤budget k c bits := by
  cases bits with
  | nil =>
    have hchoose : next k c 0 marker.start
        (initialConfiguration marker (ClockFromInput.input [])).scanned=some 1 := by
      simp [next,input_marker]
    have h := selected_run k c [] 1 (6*k+25) (by decide) hchoose
      (ClockEmptyInput.output k) (ClockEmptyInput.empty_ready k)
    obtain ⟨r,hr,ht,hh,hs⟩ := ClockJoin.enlarge _ _ _ _ _ h (empty_budget k c)
    have hf := ClockEmptyInput.empty_fields k c
    exact ⟨r,hr,by rw [ht]; exact hf.1,by rw [ht]; exact hf.2.1,
      by rw [ht]; exact hf.2.2,hh,hs⟩
  | cons b bits =>
    have hchoose : next k c 0 marker.start
        (initialConfiguration marker (ClockFromInput.input (b::bits))).scanned=some 2 := by
      simp [next,input_marker]
    obtain ⟨carry,reset,degree,a,z,hbody⟩ := ClockFromInput.entry_ready k c (b::bits) (by simp)
    have h := selected_run k c (b::bits) 2 (ClockFromInput.budget k c (b::bits))
      (by decide) hchoose _ hbody
    obtain ⟨r,hr,ht,hh,hs⟩ := ClockJoin.enlarge _ _ _ _ _ h (nonempty_budget k c (b::bits))
    refine ⟨r,hr,?_,?_,?_,hh,hs⟩
    · rw [ht]
      change frame (List.replicate (ClockEnvelope.exponent k c (b::bits).length) false++[true])=_
      rw [ClockFromInput.clock_word_binary]
    · rw [ht]
      rfl
    · rw [ht]
      rfl

end NearCubicWires.RepairOrdinary.ClockTotal
