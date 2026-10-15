import Proof.MachineModel.ClockWord

/-! Full clock entry: framed input and blank workspace generate every numeric
field and the binary dyadic clock, retaining input and resetting all heads. -/
namespace NearCubicWires.RepairOrdinary.ClockFromInput
open LocalBitMultitape ClockJoin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def layout : Fin 34 ≃ Fin 34 where
  toFun := ![4,3,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,0,1,2,5,6,7,8,9,10,11,12,13]
  invFun := ![22,23,24,1,0,25,26,27,28,29,30,31,32,33,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def preparePhase : Machine 34 50 := ClockJoin.lifted (e:=20) (Equiv.refl _) ClockPreparation.machine
def clockPhase (k c : ℕ) : Machine 34 (ClockWordLayout.states k c) :=
  ClockJoin.lifted (e:=12) layout (ClockWordLayout.machine k c)
def machine (k c : ℕ) : Machine 34 (50+ClockWordLayout.states k c) := Composition.machine preparePhase (clockPhase k c)

def input (bits : List Bool) : Fin 34 → List Bool :=
  data (e:=20) (Equiv.refl (Fin 34)) (ClockPreparation.input bits) (fun _ => [])
def prepared (bits : List Bool) (carry reset degree : ℕ) : Fin 34 → List Bool :=
  data (e:=20) (Equiv.refl (Fin 34)) (ClockPreparation.output bits carry reset degree) (fun _ => [])
def retained (bits : List Bool) (carry reset degree : ℕ) : Fin 12 → List Bool :=
  fun i => prepared bits carry reset degree (layout (Fin.natAdd 22 i))
def output (k c : ℕ) (bits : List Bool) (carry reset degree a b : ℕ) : Fin 34 → List Bool :=
  data layout (ClockWordLayout.pack 7 k c bits.length a b) (retained bits carry reset degree)
def budget (k c : ℕ) (bits : List Bool) : ℕ := 400*(c+k+1)*(bits.length+1)*PCPResourceLedger.q bits.length^2

theorem budget_dominates (k c : ℕ) (bits : List Bool) :
    ClockPreparation.budget bits+1+200*(c+k+1)*PCPResourceLedger.q bits.length^2≤budget k c bits := by
  have hbase := ClockPreparation.budget_bound bits
  have hq : 1≤PCPResourceLedger.q bits.length^2 := Nat.one_le_pow _ _ (by simp [PCPResourceLedger.q])
  let scale := (c+k+1)*(bits.length+1)*PCPResourceLedger.q bits.length^2
  have h1 : (bits.length+1)*PCPResourceLedger.q bits.length^2≤ scale := by
    have hm := Nat.mul_le_mul_right ((bits.length+1)*PCPResourceLedger.q bits.length^2)
      (by omega : 1≤c+k+1)
    simpa only [one_mul,Nat.mul_assoc,scale] using hm
  have h2 : (c+k+1)*PCPResourceLedger.q bits.length^2≤ scale := by
    have hm := Nat.mul_le_mul_right ((c+k+1)*PCPResourceLedger.q bits.length^2)
      (by omega : 1≤bits.length+1)
    simpa only [one_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,scale] using hm
  have h3 : 1≤ scale := hq.trans ((by nlinarith : PCPResourceLedger.q bits.length^2≤
      (bits.length+1)*PCPResourceLedger.q bits.length^2).trans h1)
  have hb : ClockPreparation.budget bits≤100*scale := by nlinarith
  have hc : 200*(c+k+1)*PCPResourceLedger.q bits.length^2≤200*scale := by nlinarith
  have htarget : budget k c bits=400*scale := by dsimp [budget,scale]; ring
  rw [htarget]
  omega

theorem entry_ready (k c : ℕ) (bits : List Bool) (hn : 0<bits.length) :
    ∃ carry reset degree a b, ReadyRun (machine k c) (budget k c bits) (input bits)
      (output k c bits carry reset degree a b) := by
  obtain ⟨carry,reset,degree,_,_,_,hprep⟩ := ClockPreparation.prepare_run bits hn
  have hfirst := ClockJoin.lift (e:=20) (Equiv.refl (Fin 34)) ClockPreparation.machine
    (ClockPreparation.budget bits) _ _ (fun _ => []) hprep
  obtain ⟨a,b,hclock⟩ := ClockWord.word_ready k c bits.length hn
  have hsecond := ClockJoin.lift layout (ClockWordLayout.machine k c)
    (200*(c+k+1)*PCPResourceLedger.q bits.length^2) _ _ (retained bits carry reset degree) hclock
  have hi : data layout (ClockWordLayout.pack 0 k c bits.length 0 0) (retained bits carry reset degree)=
      prepared bits carry reset degree := by funext i; fin_cases i <;> rfl
  rw [hi] at hsecond
  have h := ClockJoin.join preparePhase (clockPhase k c) _ _ _ _ _ hfirst hsecond
  exact ⟨carry,reset,degree,a,b,ClockJoin.enlarge (machine k c) _ _ _ _ h (budget_dominates k c bits)⟩

theorem clock_word_binary (k c N : ℕ) :
    List.replicate (ClockEnvelope.exponent k c N) false++[true]=
      SignedSortKey.binary (ClockEnvelope.exponent k c N+1) (ClockEnvelope.clock k c N) := by
  have hv : RadixSemantics.value (List.replicate (ClockEnvelope.exponent k c N) false++[true])=
      ClockEnvelope.clock k c N := by simp [RadixSemantics.value_append,RadixSemantics.value,ClockEnvelope.clock]
  simpa [hv] using (BoundedCounter.binary_of_value (List.replicate (ClockEnvelope.exponent k c N) false++[true])).symm

theorem entry_run (k c : ℕ) (bits : List Bool) (hn : 0<bits.length) :
    ∃ r : ExecutionReceipt 34 (50+ClockWordLayout.states k c),
      run (machine k c) (budget k c bits) (input bits)=some r ∧
      r.final.tapes 29=frame (SignedSortKey.binary (ClockEnvelope.exponent k c bits.length+1)
        (ClockEnvelope.clock k c bits.length)) ∧
      r.final.tapes 27=List.replicate (ClockEnvelope.exponent k c bits.length) true ∧
      r.final.tapes 12=frame bits ∧ r.final.tapes 0=frame (ClockBinary.word bits.length) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps≤budget k c bits := by
  obtain ⟨carry,reset,degree,a,b,r,hr,hf,hh,hs⟩ := entry_ready k c bits hn
  refine ⟨r,hr,?_,?_,?_,?_,hh,hs⟩
  · rw [hf]
    change frame (List.replicate (ClockEnvelope.exponent k c bits.length) false++[true])=_
    rw [clock_word_binary]
  · rw [hf]
    rfl
  · rw [hf]
    rfl
  · rw [hf]
    rfl

end NearCubicWires.RepairOrdinary.ClockFromInput
