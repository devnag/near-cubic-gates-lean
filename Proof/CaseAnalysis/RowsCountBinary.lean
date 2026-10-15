import Proof.CaseAnalysis.RowsCircuitTaggedRun

/-! Total actual-count conversion, including zero. Two initial writes supply
only zero framing; the existing positive unary-to-binary converter runs under
the actual counter guard. No declared numeric value becomes a unary driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCountBinary
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CloseoutRowsGateColdPair
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (n : ℕ) : Fin 10→List Bool := fun i=>if i=0 then List.replicate n true else []
def capacity (i : Fin 10) : ℕ := if i=3 then 2 else if i=5 then 1 else 0
def prepared (n : ℕ) (i : Fin 10) := ZeroPadding.pad (capacity i) (input n i)
theorem prepared_zero (n : ℕ) : prepared n 0=List.replicate n true := by
  simp [prepared,capacity,input]
def boot : Machine 10 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q _=>if q.val=0 then
      some ⟨1,fun i=>if i=3 ∨ i=5 then some false else none,fun i=>if i=3 then .right else .stay⟩
    else if q.val=1 then
      some ⟨2,fun i=>if i=3 then some false else none,fun i=>if i=3 then .left else .stay⟩
    else none

theorem boot_run (n : ℕ) : ClockJoin.ReadyRun boot 2 (input n) (prepared n) := by
  let middle : Configuration 10 3 := ⟨1,fun i=>if i=3 then 1 else 0,
    fun i=>if i=3 ∨ i=5 then [false] else input n i⟩
  let final : Configuration 10 3 := ⟨2,fun _=>0,prepared n⟩
  have h1:step boot (initialConfiguration boot (input n))=some middle:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> simp [boot,initialConfiguration,applyAction,middle,input,writeTapeBit]
  have h2:step boot middle=some final:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> simp [applyAction,middle,final,prepared,capacity,input,ZeroPadding.pad,writeTapeBit]
  obtain ⟨r,hr,rf,rs⟩ := ((Timed.single (by rfl) h1).trans (Timed.single (by rfl) h2)).run (by rfl)
  exact ⟨r,hr,by rw [rf],by intro i;rw [rf],rs.le⟩

noncomputable def machine := CloseoutRowsGateColdPair.machine boot MatrixDimensionBinary.resetMachine (fun bits=>bits 0)
def budget (n : ℕ) := 16*n^2+72*n+36
def bits (n : ℕ) := if n=0 then [] else binary (natBitLength n) n

theorem positive_run (n : ℕ) (hn:0<n) : ∃ out,
    ClockJoin.ReadyRun MatrixDimensionBinary.resetMachine (16*n^2+72*n+32) (prepared n) out ∧
      out 1=List.replicate n true ∧ out 3=UnaryTemplate.tape n ∧ out 5=frame (bits n) := by
  obtain ⟨base,hbase,h1,_h2,h3,h5,_h8,hh,hs⟩ := MatrixDimensionBinary.reset_run n hn
  obtain ⟨r,hr,rf,rs,_⟩ := ZeroPadding.run_config MatrixDimensionBinary.resetMachine capacity _ _ base hbase
  have hi:ZeroPadding.config capacity (initialConfiguration MatrixDimensionBinary.resetMachine
      (MatrixDimensionBinary.resetInput n))=initialConfiguration MatrixDimensionBinary.resetMachine (prepared n) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r.final.tapes,⟨r,hr,rfl,?_,rs ▸ hs⟩,?_,?_,?_⟩
  · intro i;rw [rf];exact hh i
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 1)=_
    simpa only [ZeroPadding.pad_zero] using h1
  · rw [rf]
    change ZeroPadding.pad 2 (base.final.tapes 3)=_
    rw [h3]
    simp [ZeroPadding.pad,UnaryTemplate.tape]
  · rw [rf]
    change ZeroPadding.pad 1 (base.final.tapes 5)=_
    rw [h5]
    simp [ZeroPadding.pad,bits,Nat.ne_of_gt hn,frame_length]

theorem count_run (n : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget n) (input n) out ∧
      out 1=List.replicate n true ∧ out 3=UnaryTemplate.tape n ∧ out 5=frame (bits n) := by
  by_cases hn:n=0
  · subst n
    have h:=CloseoutRowsGateColdPair.rejected boot MatrixDimensionBinary.resetMachine (fun bs=>bs 0)
      2 _ _ (boot_run 0) (by rfl)
    exact ⟨prepared 0,ClockJoin.enlarge machine _ _ _ _ h (by unfold budget;omega),rfl,rfl,rfl⟩
  · obtain ⟨out,hr,h1,h3,h5⟩ := positive_run n (by omega)
    have h:=CloseoutRowsGateColdPair.joined boot MatrixDimensionBinary.resetMachine (fun bs=>bs 0)
      2 _ _ _ _ (boot_run n) hr (by
        change readTapeBit (prepared n 0) 0=true
        rw [prepared_zero]
        cases n with
        | zero=>contradiction
        | succ n=>rfl)
    have ht:2+1+(16*n^2+72*n+32)+1=budget n:=by unfold budget;omega
    rw [ht] at h
    exact ⟨out,h,h1,h3,h5⟩

theorem value_bits (n : ℕ) : value (bits n)=n := by
  by_cases hn:n=0
  · subst n;rfl
  · rw [bits,if_neg hn]
    exact binary_value _ _ (Nat.lt_pow_succ_log_self (by decide) _)

end NearCubicWires.RepairOrdinary.CloseoutRowsCountBinary
