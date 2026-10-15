import Proof.MachineModel.ClockWordLayout

/-! Full ordinary execution producing the fixed-U dyadic binary clock.
The only initial nonblank fields are the already counted r and ell drivers. -/
namespace NearCubicWires.RepairOrdinary.ClockWord
open LocalBitMultitape ClockJoin ClockWordLayout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem log_phase (k c N : ℕ) (hn : 0<N) :
    ∃ a b, ReadyRun logPhase (logCost N) (pack 0 k c N 0 0) (pack 1 k c N a b) := by
  obtain ⟨a,b,h,he⟩ := ClockLogLog.clock_log_run N hn
  let extra : Fin 16 → List Bool := fun i => pack 0 k c N 0 0 (logLayout (Fin.natAdd 6 i))
  have hl := ClockJoin.lift logLayout ClockLogLog.machine (logCost N) _ _ extra h
  have hi : data logLayout (ClockLogLog.input (PCPResourceLedger.ell N)) extra=pack 0 k c N 0 0 := by
    funext i; fin_cases i <;> rfl
  have ho : data logLayout (ClockLogLog.output (PCPResourceLedger.ell N) a b) extra=pack 1 k c N a b := by
    funext i; fin_cases i <;> first | rfl | exact he
  rw [hi,ho] at hl
  exact ⟨a,b,hl⟩

theorem coefficient_phase (k c N a b : ℕ) :
    ReadyRun (coefficientPhase c) (2*c+2) (pack 1 k c N a b) (pack 2 k c N a b) := by
  obtain ⟨r,hr,hf,hh,hs⟩ := RecoveryEraseConstant.constant_ready c
  have h : ReadyRun (RecoveryEraseConstant.resetMachine c) (2*c+2) (fun _ : Fin 2 => [])
      ![List.replicate c true,List.replicate c false] := ⟨r,hr,hf,hh,hs.le⟩
  let extra : Fin 20 → List Bool := fun i => pack 1 k c N a b (coefficientLayout (Fin.natAdd 2 i))
  have hl := ClockJoin.lift coefficientLayout (RecoveryEraseConstant.resetMachine c) (2*c+2) _ _ extra h
  have hi : data coefficientLayout (fun _ : Fin 2 => []) extra=pack 1 k c N a b := by
    funext i; fin_cases i <;> rfl
  have ho : data coefficientLayout ![List.replicate c true,List.replicate c false] extra=pack 2 k c N a b := by
    funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact hl

theorem offset_phase (k c N a b : ℕ) :
    ReadyRun (offsetPhase k) (2*k+2) (pack 2 k c N a b) (pack 3 k c N a b) := by
  obtain ⟨r,hr,hf,hh,hs⟩ := RecoveryEraseConstant.constant_ready k
  have h : ReadyRun (RecoveryEraseConstant.resetMachine k) (2*k+2) (fun _ : Fin 2 => [])
      ![List.replicate k true,List.replicate k false] := ⟨r,hr,hf,hh,hs.le⟩
  let extra : Fin 20 → List Bool := fun i => pack 2 k c N a b (offsetLayout (Fin.natAdd 2 i))
  have hl := ClockJoin.lift offsetLayout (RecoveryEraseConstant.resetMachine k) (2*k+2) _ _ extra h
  have hi : data offsetLayout (fun _ : Fin 2 => []) extra=pack 2 k c N a b := by
    funext i; fin_cases i <;> rfl
  have ho : data offsetLayout ![List.replicate k true,List.replicate k false] extra=pack 3 k c N a b := by
    funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact hl

theorem product_phase (k c N a b : ℕ) :
    ReadyRun productPhase (productCost c N) (pack 3 k c N a b) (pack 4 k c N a b) := by
  let h := ClockEnvelope.logWidth N
  obtain ⟨r,hr,h0,h1,h2,h3,hh,hs⟩ := ClockUnaryProduct.product_run c h
  have hi0 : (Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      ![List.replicate c true,false::List.replicate h true,[]] (fun _ : Fin 1 => []))=
      ![List.replicate c true,false::List.replicate h true,[],[]] := by funext i; fin_cases i <;> rfl
  rw [hi0] at hr
  have hp : ReadyRun ClockUnaryProduct.machine (productCost c N)
      ![List.replicate c true,false::List.replicate h true,[],[]]
      ![List.replicate c true,false::List.replicate h true,List.replicate (c*h) true,
        List.replicate (c*(2*h+3)+2) false] := by
    refine ⟨r,hr,?_,hh,hs.le⟩
    funext i; fin_cases i <;> simp [h0,h1,h2,h3]
  let extra : Fin 18 → List Bool := fun i => pack 3 k c N a b (productLayout (Fin.natAdd 4 i))
  have hl := ClockJoin.lift productLayout ClockUnaryProduct.machine (productCost c N) _ _ extra hp
  have hi : data productLayout ![List.replicate c true,false::List.replicate h true,[],[]] extra=pack 3 k c N a b := by
    funext i; fin_cases i <;> rfl
  have ho : data productLayout
      ![List.replicate c true,false::List.replicate h true,List.replicate (c*h) true,
        List.replicate (c*(2*h+3)+2) false] extra=pack 4 k c N a b := by
    funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact hl

theorem first_sum_phase (k c N a b : ℕ) :
    ReadyRun firstSumPhase (firstSumCost c N) (pack 4 k c N a b) (pack 5 k c N a b) := by
  let r := ClockDyadicLedger.exponent N
  let p := product c N
  let extra : Fin 18 → List Bool := fun i => pack 4 k c N a b (firstSumLayout (Fin.natAdd 4 i))
  have hl := ClockJoin.lift firstSumLayout ClockUnarySum.machine (firstSumCost c N) _ _ extra (ClockUnarySum.sum_ready r p)
  have hi : data firstSumLayout ![List.replicate r true,List.replicate p true,[],[]] extra=pack 4 k c N a b := by
    funext i; fin_cases i <;> rfl
  have ho : data firstSumLayout
      ![List.replicate r true,List.replicate p true,List.replicate (r+p) true,List.replicate (r+p+2) false]
      extra=pack 5 k c N a b := by funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact hl

theorem second_sum_phase (k c N a b : ℕ) :
    ReadyRun secondSumPhase (secondSumCost k c N) (pack 5 k c N a b) (pack 6 k c N a b) := by
  let r := firstSum c N
  let extra : Fin 18 → List Bool := fun i => pack 5 k c N a b (secondSumLayout (Fin.natAdd 4 i))
  have hl := ClockJoin.lift secondSumLayout ClockUnarySum.machine (secondSumCost k c N) _ _ extra (ClockUnarySum.sum_ready r k)
  have hi : data secondSumLayout ![List.replicate r true,List.replicate k true,[],[]] extra=pack 5 k c N a b := by
    funext i; fin_cases i <;> rfl
  have ho : data secondSumLayout
      ![List.replicate r true,List.replicate k true,List.replicate (r+k) true,List.replicate (r+k+2) false]
      extra=pack 6 k c N a b := by funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact hl

theorem field_phase (k c N a b : ℕ) :
    ReadyRun fieldPhase (fieldCost k c N) (pack 6 k c N a b) (pack 7 k c N a b) := by
  let R := exponent k c N
  have hf := ClockInitialKey.field_ready R
  let extra : Fin 16 → List Bool := fun i => pack 6 k c N a b (fieldLayout (Fin.natAdd 6 i))
  have hl := ClockJoin.lift fieldLayout ClockFields.machine (fieldCost k c N) _ _ extra hf
  have hi : data fieldLayout (ClockInitialKey.fieldInput R) extra=pack 6 k c N a b := by
    funext i; fin_cases i <;> rfl
  have ho : data fieldLayout (ClockInitialKey.fieldOutput R) extra=pack 7 k c N a b := by
    funext i; fin_cases i <;> rfl
  rw [hi,ho] at hl
  exact hl

theorem word_ready (k c N : ℕ) (hn : 0<N) :
    ∃ a b, ReadyRun (machine k c) (200*(c+k+1)*(PCPResourceLedger.q N)^2)
      (pack 0 k c N 0 0) (pack 7 k c N a b) := by
  obtain ⟨a,b,hlog⟩ := log_phase k c N hn
  have h1 := ClockJoin.join logPhase (coefficientPhase c) _ _ _ _ _ hlog (coefficient_phase k c N a b)
  have h2 := ClockJoin.join (Composition.machine logPhase (coefficientPhase c)) (offsetPhase k) _ _ _ _ _ h1 (offset_phase k c N a b)
  have h3 := ClockJoin.join _ productPhase _ _ _ _ _ h2 (product_phase k c N a b)
  have h4 := ClockJoin.join _ firstSumPhase _ _ _ _ _ h3 (first_sum_phase k c N a b)
  have h5 := ClockJoin.join _ secondSumPhase _ _ _ _ _ h4 (second_sum_phase k c N a b)
  have h6 := ClockJoin.join _ fieldPhase _ _ _ _ _ h5 (field_phase k c N a b)
  exact ⟨a,b,ClockJoin.enlarge (machine k c) (budget k c N) _ _ _ h6 (budget_bound k c N)⟩

theorem word_run (k c N : ℕ) (hn : 0<N) :
    ∃ r : ExecutionReceipt 22 (states k c),
      run (machine k c) (200*(c+k+1)*(PCPResourceLedger.q N)^2) (pack 0 k c N 0 0)=some r ∧
      r.final.tapes 17=frame (List.replicate (ClockEnvelope.exponent k c N) false++[true]) ∧
      r.final.tapes 15=List.replicate (ClockEnvelope.exponent k c N) true ∧
      r.final.tapes 0=List.replicate (ClockDyadicLedger.exponent N) true ∧
      r.final.tapes 1=false::List.replicate (PCPResourceLedger.ell N) true ∧
      (∀ i,r.final.heads i=0) ∧ r.steps≤200*(c+k+1)*(PCPResourceLedger.q N)^2 := by
  obtain ⟨a,b,r,hr,hf,hh,hs⟩ := word_ready k c N hn
  exact ⟨r,hr,by simp [hf,pack,exponent],by simp [hf,pack,exponent],by simp [hf,pack],by simp [hf,pack],hh,hs⟩

end NearCubicWires.RepairOrdinary.ClockWord
