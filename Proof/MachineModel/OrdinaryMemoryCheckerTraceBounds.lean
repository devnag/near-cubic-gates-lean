import Proof.MachineModel.OrdinaryMemoryCheckerTrace

/-! The raw checker's finite-index and address premises follow from the
same successful symbolic walk and the scalar U ledger. Claimed reads may
be arbitrary here; no memory correctness is used to bound its events. -/
namespace NearCubicWires.RepairOrdinary.MemoryChecker
open LocalBitMultitape MemoryLog ClaimedTrace MemoryTransition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem writes_cells (tape start : ℕ) (bits : List Bool) (e : Event)
    (he : e ∈ MemoryInitialization.writes tape start bits) :
    e.cell.1 = tape ∧ start ≤ e.cell.2 ∧ e.cell.2 < start+bits.length := by
  induction bits generalizing start with
  | nil => simp only [MemoryInitialization.writes, List.not_mem_nil] at he
  | cons b bs ih =>
    simp only [MemoryInitialization.writes, List.mem_cons] at he
    rcases he with rfl | he
    · refine ⟨rfl,Nat.le_refl _,?_⟩
      simp only [List.length_cons]
      omega
    · obtain ⟨ht,hl,hu⟩ := ih (start+1) he
      refine ⟨ht,by omega,?_⟩
      simp only [List.length_cons]
      omega

theorem check_cells {t s : ℕ} (machine : Machine t s)
    (claims : List (Fin t → Bool)) (v finalView : View t s) (events : List Event)
    (H : ℕ) (hheads : ∀ i, v.heads i + claims.length ≤ H)
    (hcheck : check machine v claims = some (finalView,events)) :
    events.length = t*claims.length ∧
      ∀ e ∈ events, e.cell.1 < t ∧ e.cell.2 ≤ H := by
  induction claims generalizing v finalView events with
  | nil =>
    simp only [check, Option.some.injEq, Prod.mk.injEq] at hcheck
    obtain ⟨rfl,rfl⟩ := hcheck
    simp
  | cons reads rest ih =>
    cases hhalt : machine.halted v.control with
    | true => simp only [check, hhalt, ↓reduceIte] at hcheck; cases hcheck
    | false =>
      cases ha : machine.rule v.control reads with
      | none => simp only [check, hhalt, Bool.false_eq_true, ↓reduceIte, ha] at hcheck; cases hcheck
      | some action =>
        cases htail : check machine (advance v action) rest with
        | none =>
          simp only [check, hhalt, Bool.false_eq_true, ↓reduceIte, ha, htail, Option.map_none] at hcheck
          cases hcheck
        | some result =>
          obtain ⟨lastView,lastEvents⟩ := result
          have heq : (lastView,batch v.heads reads (fun i => (action.write i).getD (reads i)) ++ lastEvents) =
              (finalView,events) := by
            simpa only [check, hhalt, Bool.false_eq_true, ↓reduceIte, ha, htail,
              Option.map_some, Option.some.injEq] using hcheck
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj heq
          have hnext : ∀ i, (advance v action).heads i + rest.length ≤ H := by
            intro i
            have hi := hheads i
            simp only [List.length_cons] at hi
            change (action.move i).apply (v.heads i) + rest.length ≤ H
            cases action.move i <;> simp only [HeadMove.apply] <;> omega
          obtain ⟨hlen,hcells⟩ := ih (advance v action) lastView lastEvents hnext htail
          constructor
          · simp only [List.length_append, batch, List.length_map, List.length_finRange, hlen,
              List.length_cons, Nat.mul_add, Nat.mul_one]
            omega
          · intro e he
            rcases List.mem_append.mp he with he | he
            · obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
              refine ⟨i.isLt,?_⟩
              change v.heads i ≤ H
              have hi := hheads i
              omega
            · exact hcells e he

theorem initialized_cells (v : Verifier) (input witness : List Bool)
    (claims : List (Fin v.tapeCount → Bool)) (finalView : View v.tapeCount v.stateCount)
    (trace : List Event) (W : ℕ)
    (hcheck : check v.machine (view (initialConfiguration v.machine (v.inputTapes input witness)))
      claims = some (finalView,trace))
    (hinput : 2*input.length < 2^W) (hwitness : 2*witness.length < 2^W)
    (hsteps : claims.length < 2^W) :
    (MemoryInitialization.events input witness ++ trace).length =
      2*input.length+2*witness.length+2+v.tapeCount*claims.length ∧
    ∀ e ∈ MemoryInitialization.events input witness ++ trace,
      e.cell.1 < v.tapeCount ∧ e.cell.2 < 2^W := by
  obtain ⟨hlen,hcells⟩ := check_cells v.machine claims
    (view (initialConfiguration v.machine (v.inputTapes input witness))) finalView trace
    claims.length (by intro i; change 0+claims.length ≤ claims.length; omega) hcheck
  constructor
  · rw [List.length_append, MemoryInitialization.initial_count, hlen]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · simp only [MemoryInitialization.events, List.mem_append] at he
      rcases he with he | he
      · obtain ⟨ht,_,ha⟩ := writes_cells 0 0 (frame input) e he
        have htwo := v.twoTapes
        rw [frame_length] at ha
        exact ⟨by omega,by omega⟩
      · obtain ⟨ht,_,ha⟩ := writes_cells 1 0 (frame witness) e he
        have htwo := v.twoTapes
        rw [frame_length] at ha
        exact ⟨by omega,by omega⟩
    · obtain ⟨ht,ha⟩ := hcells e he
      exact ⟨ht,ha.trans_lt hsteps⟩

theorem initialized_ready (v : Verifier) (input witness : List Bool)
    (claims : List (Fin v.tapeCount → Bool)) (finalView : View v.tapeCount v.stateCount)
    (trace : List Event) (W : ℕ)
    (hcheck : check v.machine (view (initialConfiguration v.machine (v.inputTapes input witness)))
      claims = some (finalView,trace))
    (hcount : 2*input.length+2*witness.length+2+v.tapeCount*claims.length ≤ 2^(2*W))
    (htapes : v.tapeCount ≤ 2^W)
    (hinput : 2*input.length < 2^W) (hwitness : 2*witness.length < 2^W)
    (hsteps : claims.length < 2^W) :
    ListReady (2*W) W (MemoryInitialization.events input witness ++ trace) := by
  obtain ⟨hlen,hcells⟩ := initialized_cells v input witness claims finalView trace W
    hcheck hinput hwitness hsteps
  refine ⟨initialized_positive input witness trace,?_,?_,?_⟩
  · rw [hlen]
    exact hcount
  · intro e he
    obtain ⟨ht,ha⟩ := hcells e he
    have ht' := ht.trans_le htapes
    have hcode : MemorySort.cellCode W e.cell < 2^W*2^W := by
      unfold MemorySort.cellCode
      have hm := Nat.mul_le_mul_right (2^W) (Nat.succ_le_of_lt ht')
      nlinarith
    have hp : 2^W*2^W ≤ 2^(2*W+2) := by
      rw [← pow_add, ← two_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact hcode.trans_le hp
  · intro e he
    exact (hcells e he).2

end NearCubicWires.RepairOrdinary.MemoryChecker
