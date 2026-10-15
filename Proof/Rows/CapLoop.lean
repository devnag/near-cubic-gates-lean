import Proof.Rows.CapBodies

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace CapDoublingBodies
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary RecoveryExecution
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound RadixSemantics

noncomputable def atCall (j : Fin 4) (H : Fin 7 → Nat) (A : Fin 7 → List Bool) :=
  controlConfig (RecoveryCalls.code sizes j)
    (⟨(programs j).start,H,A⟩ : Configuration 7 (sizes j))

/-- This is just the receipt application for the two actual doubling bodies. -/
theorem body_call (flip : Bool) (target : Fin 4) (fuel : Nat)
    (H A H' A') (h : Step (body flip) fuel H A H' A')
    (htarget : target=if readTapeBit (A' 3) (H' 3) then bodyIndex (!flip) else copyIndex flip) :
    ∃ time ≤ fuel+1, Timed machine time (atCall (bodyIndex flip) H A) (atCall target H' A') := by
  cases flip with
  | false =>
    obtain ⟨r,hr,hh,ht,_⟩ := h
    obtain ⟨time,hbound,path⟩ := call_receipt sizes programs 0 next 0 target fuel
      ⟨(programs 0).start,H,A⟩ r hr (by
        rw [htarget]
        by_cases hb : readTapeBit (A' 3) (H' 3)=true <;>
          simp [next,bodyIndex,copyIndex,Configuration.scanned,hh,ht,hb])
    rw [hh,ht] at path
    exact ⟨time,hbound,path⟩
  | true =>
    obtain ⟨r,hr,hh,ht,_⟩ := h
    obtain ⟨time,hbound,path⟩ := call_receipt sizes programs 0 next 1 target fuel
      ⟨(programs 1).start,H,A⟩ r hr (by
        rw [htarget]
        by_cases hb : readTapeBit (A' 3) (H' 3)=true <;>
          simp [next,bodyIndex,copyIndex,Configuration.scanned,hh,ht,hb])
    rw [hh,ht] at path
    exact ⟨time,hbound,path⟩

theorem copy_call (flip : Bool) (n m w pos k : Nat) (bits : List Bool) :
    ∃ time H O, time ≤ 2*n+4 ∧
      Timed machine time (atCall (copyIndex flip) (heads pos k) (bank (!flip) n m w bits))
        (RecoveryCalls.stopped sizes H O) ∧ copied n H O := by
  cases flip with
  | false =>
    obtain ⟨H,O,h,fields⟩ := copy_run false n m w pos k bits
    obtain ⟨r,hr,hh,ht,_⟩ := h
    obtain ⟨time,hbound,path⟩ := stop_receipt sizes programs 0 next 2 (2*n+3)
      ⟨(programs 2).start,heads pos k,bank true n m w bits⟩ r hr (by rfl)
    rw [hh,ht] at path
    exact ⟨time,H,O,by omega,path,fields⟩
  | true =>
    obtain ⟨H,O,h,fields⟩ := copy_run true n m w pos k bits
    obtain ⟨r,hr,hh,ht,_⟩ := h
    obtain ⟨time,hbound,path⟩ := stop_receipt sizes programs 0 next 3 (2*n+3)
      ⟨(programs 3).start,heads pos k,bank false n m w bits⟩ r hr (by rfl)
    rw [hh,ht] at path
    exact ⟨time,H,O,by omega,path,fields⟩

theorem remaining_read (lo hi : List Bool) (b : Bool) :
    readTapeBit (UnaryTemplate.tape (lo++b::hi).length) lo.length=decide (lo≠[]) := by
  cases lo with
  | nil => simp
  | cons a lo =>
    have h := UnaryTemplate.tape_mark ((a::lo)++b::hi).length lo.length (by
      simp only [List.length_append,List.length_cons]
      omega)
    simpa using h

/-- The stronger time invariant subtracts the already-built accumulator's
work. It telescopes over doubling, including arbitrarily many leading zeros. -/
theorem loop_timed (lo hi : List Bool) (flip : Bool) (old : Nat)
    (hne : lo≠[]) (hold : old ≤ value hi) :
    ∃ time H O,
      time+6*value hi ≤ 8*value (lo++hi)+12*lo.length+6 ∧
      Timed machine time
        (atCall (bodyIndex flip) (heads (2*lo.length-1) lo.length)
          (bank flip (value hi) old (lo++hi).length (lo++hi)))
        (RecoveryCalls.stopped sizes H O) ∧ copied (value (lo++hi)) H O := by
  induction lo using List.reverseRecOn generalizing hi flip old with
  | nil => exact (hne rfl).elim
  | append_singleton lo b ih =>
    let bits := lo++b::hi
    let n := value hi
    let nextValue := value (b::hi)
    have hn : nextValue=2*n+b.toNat := by simp [nextValue,n,value,Nat.add_comm]
    have hg : 2*n ≤ nextValue := by rw [hn];omega
    have he : (lo++[b])++hi=bits := by simp [bits,List.append_assoc]
    have hl : (lo++[b]).length=lo.length+1 := by simp
    have hp : 2*(lo.length+1)-1=2*lo.length+1 := by omega
    have hpos : (2*lo.length+1)-2=2*lo.length-1 := by omega
    have raw := body_run flip n old bits.length (2*lo.length+1) (lo.length+1)
      bits b hold (read_last lo hi b)
    have bodyStep : Step (body flip) (6*n+10)
        (heads (2*lo.length+1) (lo.length+1)) (bank flip n old bits.length bits)
        (heads (2*lo.length-1) lo.length) (bank (!flip) nextValue n bits.length bits) := by
      simpa only [hpos,Nat.add_sub_cancel,←hn] using raw
    have hr : readTapeBit (UnaryTemplate.tape bits.length) lo.length=decide (lo≠[]) :=
      remaining_read lo hi b
    by_cases empty : lo=[]
    · subst lo
      obtain ⟨t0,h0,p0⟩ := body_call flip (copyIndex flip) (6*n+10) _ _ _ _ bodyStep (by
        simp [heads,bank,bits,copyIndex])
      obtain ⟨t1,H,O,h1,p1,fields⟩ := copy_call flip nextValue n bits.length 0 0 bits
      have path := p0.trans p1
      refine ⟨t0+t1,H,O,?_,?_,?_⟩
      · change t0+t1+6*n ≤ 8*nextValue+12*1+6
        omega
      · simpa only [he,hl,hp,n] using path
      · simpa only [he,bits,List.nil_append,List.cons_append,nextValue] using fields
    · obtain ⟨t0,h0,p0⟩ := body_call flip (bodyIndex (!flip)) (6*n+10) _ _ _ _ bodyStep (by
        change bodyIndex (!flip) = if readTapeBit (UnaryTemplate.tape bits.length) lo.length
          then bodyIndex (!flip) else copyIndex flip
        rw [hr]
        simp [empty])
      have hnext : n ≤ nextValue := by omega
      obtain ⟨t1,H,O,h1,p1,fields⟩ := ih (b::hi) (!flip) n empty hnext
      have path := p0.trans p1
      refine ⟨t0+t1,H,O,?_,?_,?_⟩
      · rw [he,hl]
        change t0+t1+6*n ≤ 8*value bits+12*(lo.length+1)+6
        change t1+6*nextValue ≤ 8*value bits+12*lo.length+6 at h1
        omega
      · simpa only [he,hl,hp,n] using path
      · simpa only [he] using fields

theorem loop_run (bits : List Bool) (hne : bits≠[]) :
    ∃ H O, Step machine (8*value bits+12*bits.length+6)
      (heads (2*bits.length-1) bits.length) (bank false 0 0 bits.length bits) H O ∧
      copied (value bits) H O := by
  obtain ⟨time,H,O,hbound,path,fields⟩ := loop_timed bits [] false 0 hne (by rfl)
  simp only [List.append_nil,value,Nat.mul_zero,Nat.add_zero] at hbound path fields
  obtain ⟨r,hr,hf,_⟩ := path.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more := runFrom_moreFuel machine time
    (8*value bits+12*bits.length+6-time) _ r hr
  rw [Nat.add_sub_of_le hbound] at more
  have runStep := Step.of_run more (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  exact ⟨H,O,runStep,fields⟩

end CapDoublingBodies
