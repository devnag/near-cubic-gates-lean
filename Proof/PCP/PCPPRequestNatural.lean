import Proof.PCP.PCPPRequestNaturalSerializer

/-! Complete actual native natWord → canonical encodeNat field, including zero. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNatural
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private abbrev stateCount {t s : ℕ} (_ : Machine t s) := s
noncomputable def prepare := TapeEmbedding.machine 126 PCPPRequestNaturalReady.machine
def zeroMachine : Machine 136 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun i => if i=85 then some false else none,fun _ => .stay⟩
noncomputable def sizes : Fin 3 → ℕ := ![18,stateCount DecompositionMagnitudeSerializer.machine,2]
noncomputable def programs : (j : Fin 3) → Machine 136 (sizes j)
  | ⟨0,_⟩ => prepare
  | ⟨1,_⟩ => DecompositionMagnitudeSerializer.machine
  | ⟨2,_⟩ => zeroMachine
  | ⟨n+3,h⟩ => False.elim (by omega)
noncomputable def next (j : Fin 3) (_ : Fin (sizes j)) (bs : Fin 136 → Bool) : Option (Fin 3) :=
  ![some (if bs 8 then 1 else 2),none,none] j
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def initial (source : List Bool) (pos : ℕ) :=
  TapeEmbedding.config (fun _ : Fin 126 => 0) (fun _ => []) (PCPPRequestNaturalReady.entry source pos)
noncomputable def entry (source : List Bool) (pos : ℕ) :=
  controlConfig (RecoveryCalls.code sizes 0) (initial source pos)
def prepared (pre tail : List Bool) (n : ℕ) :=
  TapeEmbedding.config (fun _ : Fin 126 => 0) (fun _ => [])
    (PCPPRequestNaturalReady.prepared (pre++natWord n++tail) (pre.length+(natWord n).length) n)
def budget (n : ℕ) := 20*natBitLength n+PCPTraversal.budget (3*natBitLength n)+28

theorem prepare_run (pre tail : List Bool) (n : ℕ) :
    ∃ r,runFrom prepare (20*natBitLength n+24)
      (initial (pre++natWord n++tail) pre.length)=some r ∧
      r.final=prepared pre tail n ∧ r.steps=20*natBitLength n+24 := by
  obtain ⟨base,hb,bf,bs⟩ := PCPPRequestNaturalReady.ready_run pre tail n
  have h := TapeEmbedding.run_embed PCPPRequestNaturalReady.machine
    (fun _ : Fin 126 => 0) (fun _ => []) _ _ base hb
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 126 => 0) (fun _ => []) base,h,?_,bs⟩
  change TapeEmbedding.config (fun _ : Fin 126 => 0) (fun _ => []) base.final=_
  rw [bf]
  rfl

theorem prepared_flag (pre tail : List Bool) (n : ℕ) :
    (prepared pre tail n).scanned 8=decide (0<n) :=
  PCPPRequestNaturalReady.prepared_flag pre tail n

theorem positive_entry (pre tail : List Bool) (n : ℕ) :
    RecoveryCalls.restarted (programs 1) (prepared pre tail n).heads (prepared pre tail n).tapes=
      PCPPRequestNaturalSerializer.entry pre tail n := by
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

def zeroOutput (heads : Fin 136 → ℕ) (tapes : Fin 136 → List Bool) : Configuration 136 2 :=
  ⟨1,heads,Function.update tapes 85 [false]⟩

theorem zero_run (heads : Fin 136 → ℕ) (tapes : Fin 136 → List Bool)
    (hh : heads 85=0) (ht : tapes 85=[]) :
    ∃ r,runFrom zeroMachine 1 ⟨0,heads,tapes⟩=some r ∧
      r.final=zeroOutput heads tapes ∧ r.steps=1 := by
  have h : step zeroMachine ⟨0,heads,tapes⟩=some (zeroOutput heads tapes) := by
    simp only [step,zeroMachine,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i; rfl
    · funext i
      by_cases hi : i=85
      · subst i; simp [applyAction,zeroOutput,hh,ht,writeTapeBit]
      · simp [applyAction,zeroOutput,hi]
  exact (Timed.single (by rfl) h).run (by rfl)

theorem zero_code : CanonicalBinary.encodeNat 0=0 := by
  simp [CanonicalBinary.encodeNat,CanonicalBinary.encodeBits,
    CanonicalBinary.encodeBoolList,CanonicalBinary.encodeBalancedList]

theorem natural_run (pre tail : List Bool) (n : ℕ) :
    ∃ r,runFrom machine (budget n) (entry (pre++natWord n++tail) pre.length)=some r ∧
      (∃ padding,r.final.tapes 85=frame (CanonicalBinary.encodeNat n).bits++List.replicate padding false) ∧
      r.final.tapes 86=(CanonicalBinary.encodeNat n).bits ∧ r.final.heads 85=0 ∧
      r.final.tapes 0=pre++natWord n++tail ∧ r.final.heads 0=pre.length+(natWord n).length ∧
      r.steps ≤ budget n := by
  obtain ⟨base,hb,bf,_⟩ := prepare_run pre tail n
  have core : ∃ k≤budget n,∃ heads tapes,
      Timed machine k (entry (pre++natWord n++tail) pre.length)
        (RecoveryCalls.stopped sizes heads tapes) ∧
      (∃ padding,tapes 85=frame (CanonicalBinary.encodeNat n).bits++List.replicate padding false) ∧
      tapes 86=(CanonicalBinary.encodeNat n).bits ∧ heads 85=0 ∧
      tapes 0=pre++natWord n++tail ∧ heads 0=pre.length+(natWord n).length := by
    by_cases hn : 0<n
    · have hnext : next 0 base.final.control base.final.scanned=some 1 := by
        rw [bf]
        simp [next,prepared_flag,hn]
      obtain ⟨k,hk,hprefix⟩ := call_receipt sizes programs 0 next 0 1 _ _ base hb hnext
      rw [bf,positive_entry] at hprefix
      obtain ⟨last,hl,lt,lraw,lh,l0,lh0,_⟩ := PCPPRequestNaturalSerializer.serialized_run pre tail n hn
      obtain ⟨m,hm,hstop⟩ := stop_receipt sizes programs 0 next 1 _ _ last hl (by rfl)
      refine ⟨k+m,?_,last.final.heads,last.final.tapes,hprefix.trans hstop,?_,lraw,lh,l0,lh0⟩
      · unfold budget; omega
      · exact ⟨_,lt⟩
    · have hn0 : n=0 := by omega
      have hnext : next 0 base.final.control base.final.scanned=some 2 := by
        rw [bf]
        simp [next,prepared_flag,hn]
      obtain ⟨k,hk,hprefix⟩ := call_receipt sizes programs 0 next 0 2 _ _ base hb hnext
      rw [bf] at hprefix
      obtain ⟨last,hl,lf,ls⟩ := zero_run (prepared pre tail n).heads (prepared pre tail n).tapes
        (by rfl) (by rfl)
      obtain ⟨m,hm,hstop⟩ := stop_receipt sizes programs 0 next 2 _ _ last hl (by rfl)
      refine ⟨k+m,?_,last.final.heads,last.final.tapes,hprefix.trans hstop,?_,?_,?_,?_,?_⟩
      · unfold budget; omega
      · refine ⟨0,?_⟩
        rw [lf,hn0,zero_code]
        rfl
      · rw [lf,hn0,zero_code]; rfl
      · rw [lf]; rfl
      · rw [lf]; rfl
      · rw [lf]; rfl
  obtain ⟨k,hk,heads,tapes,path,ht,hraw,hh,h0,hh0⟩ := core
  obtain ⟨r,hr,rf,rs⟩ := path.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more := runFrom_moreFuel machine k (budget n-k) _ r hr
  rw [Nat.add_sub_of_le hk] at more
  refine ⟨r,more,?_,?_,?_,?_,?_,?_⟩
  · rw [rf]; exact ht
  · rw [rf]; exact hraw
  · rw [rf]; exact hh
  · rw [rf]; exact h0
  · rw [rf]; exact hh0
  · omega

theorem budget_envelope (n : ℕ) : budget n ≤ 1000000000000000000*(natBitLength n+1)^12 := by
  let w := natBitLength n
  have hpos : 1≤(w+1)^12 := Nat.one_le_pow _ _ (by omega)
  have hw : w≤(w+1)^12 := by
    calc
      w ≤ (w+1)^1 := by simp
      _ ≤ (w+1)^12 := Nat.pow_le_pow_right (by omega) (by omega)
  have hserializer : PCPTraversal.budget (3*w) ≤ 531441000000000000*(w+1)^12 := by
    unfold PCPTraversal.budget
    calc
      _ ≤ 1000000000000*(3*(w+1))^12 := by gcongr; omega
      _ = _ := by rw [mul_pow]; norm_num; ring
  change 20*w+PCPTraversal.budget (3*w)+28 ≤ 1000000000000000000*(w+1)^12
  omega

end NearCubicWires.RepairOrdinary.PCPPRequestNatural
