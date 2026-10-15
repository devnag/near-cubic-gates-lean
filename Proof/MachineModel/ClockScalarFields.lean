import Proof.MachineModel.ClockNormalize

/-! Numeric meaning and consumer endpoints for the physical width normalizer. -/
namespace NearCubicWires.RepairOrdinary.ClockScalarFields
open LocalBitMultitape RadixSemantics SignedSortKey ClockNormalize
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

@[simp] theorem zeros_value (n : ℕ) : value (List.replicate n false)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,value,ih]

theorem resize_value (w : ℕ) (bits : List Bool) (h : bits.length≤w) :
    value (resize w bits)=value bits := by rw [resize_eq w bits h,value_append]; simp

theorem resize_binary (w : ℕ) (bits : List Bool) (h : bits.length≤w) :
    resize w bits=binary w (value bits) := by
  have hb := BoundedCounter.binary_of_value (resize w bits)
  simpa [resize_value w bits h] using hb.symm

theorem scalar_run (w : ℕ) (bits : List Bool) (h : bits.length≤w) :
    ∃ r : ExecutionReceipt 5 6,
      run ClockNormalize.machine (4*w+4) (input w bits)=some r ∧
      r.final.tapes 0=List.replicate w true ∧ r.final.tapes 1=frame bits ∧
      r.final.tapes 2=frame (binary w (value bits)) ∧ r.final.tapes 3=[true] ∧
      r.final.tapes 4=List.replicate (2*w+1) false ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=4*w+4 := by
  simpa [resize_binary w bits h,h] using normalize_run w bits

theorem limit_run (N : ℕ) :
    ∃ r : ExecutionReceipt 5 6,
      run ClockNormalize.machine (4*ClockDyadicLedger.width N+4)
        (input (ClockDyadicLedger.width N) (List.replicate (ClockDyadicLedger.exponent N) false++[true]))=some r ∧
      r.final.tapes 2=frame (binary (ClockDyadicLedger.width N) (ClockDyadicLedger.limit N)) ∧
      r.final.tapes 3=[true] ∧ (∀ i,r.final.heads i=0) ∧ r.steps=4*ClockDyadicLedger.width N+4 := by
  have hlen : (List.replicate (ClockDyadicLedger.exponent N) false++[true]).length≤ClockDyadicLedger.width N := by
    simp [ClockDyadicLedger.width]
  have hv : value (List.replicate (ClockDyadicLedger.exponent N) false++[true])=ClockDyadicLedger.limit N := by
    simp [value_append,value,ClockDyadicLedger.limit]
  obtain ⟨r,hr,_,_,hout,hflag,_,hh,hs⟩ := scalar_run _ _ hlen
  exact ⟨r,hr,by simpa [hv] using hout,hflag,hh,hs⟩

def zeroInput (w : ℕ) : Fin 5 → List Bool := ![List.replicate w true,[],[],[],[]]
def zeroPad : Fin 5 → ℕ := ![0,1,0,0,0]

theorem zero_run (w : ℕ) :
    ∃ r : ExecutionReceipt 5 6,
      run ClockNormalize.machine (4*w+4) (zeroInput w)=some r ∧
      r.final.tapes 0=List.replicate w true ∧
      ZeroPadding.pad 1 (r.final.tapes 1)=[false] ∧
      r.final.tapes 2=frame (binary w 0) ∧ r.final.tapes 3=[true] ∧
      r.final.tapes 4=List.replicate (2*w+1) false ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=4*w+4 := by
  obtain ⟨base,hb,h0,h1,h2,h3,h4,hh,hs⟩ := scalar_run w [] (by simp)
  let c := initialConfiguration ClockNormalize.machine (zeroInput w)
  have hi : ZeroPadding.config zeroPad c=initialConfiguration ClockNormalize.machine (input w []) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,zeroPad,c,zeroInput,initialConfiguration,
        input,Fin.addCases,ZeroPadding.pad,frame]
  have hb' : runFrom ClockNormalize.machine (4*w+4) (ZeroPadding.config zeroPad c)=some base := by
    rw [hi]; exact hb
  obtain ⟨r,hr,hf,hrs,_⟩ := ZeroPadding.run_unpad ClockNormalize.machine zeroPad _ c base hb'
  have ht (i : Fin 5) : ZeroPadding.pad (zeroPad i) (r.final.tapes i)=base.final.tapes i :=
    congrArg (fun cfg : Configuration 5 6 => cfg.tapes i) hf
  have hheads := congrArg Configuration.heads hf
  change r.final.heads=base.final.heads at hheads
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_,hrs.trans hs⟩
  · simpa [zeroPad,ZeroPadding.pad] using (ht 0).trans h0
  · simpa [zeroPad,frame] using (ht 1).trans h1
  · simpa [zeroPad,ZeroPadding.pad,value] using (ht 2).trans h2
  · simpa [zeroPad,ZeroPadding.pad] using (ht 3).trans h3
  · simpa [zeroPad,ZeroPadding.pad] using (ht 4).trans h4
  · intro i; rw [hheads]; exact hh i

end NearCubicWires.RepairOrdinary.ClockScalarFields
