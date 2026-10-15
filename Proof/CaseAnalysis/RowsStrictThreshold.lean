import Proof.CaseAnalysis.RowsStrictSelector
import Proof.Hierarchy.HierarchyFixedWord

/-! The complete signed threshold-minus-one branch controller. The input
magnitude is the SAME canonical magnitude returned by the checked integer
decoder. Zero and one take literal finite branches; all other arithmetic
is binary. The sign field is retained for the native request append. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsStrictThreshold
open LocalBitMultitape RecoveryExecution RecoveryRootRound CloseoutRowsStrictSelector
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def arithmeticSlots (i : Fin 10) : Fin 13 := i.castAdd 3
def literalSlots : Fin 2 → Fin 13 := ![4,9]
theorem arithmetic_injective : Function.Injective arithmeticSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 13 => k.val) h)
theorem literal_injective : Function.Injective literalSlots := by decide
noncomputable def negativeMachine := RecoveryFocus.machine arithmeticSlots CloseoutRowsStrictArithmetic.negativeMachine
noncomputable def positiveMachine := RecoveryFocus.machine arithmeticSlots CloseoutRowsStrictArithmetic.positiveMachine
noncomputable def literalMachine (n : ℕ) := RecoveryFocus.machine literalSlots
  (HierarchyFixedWord.machine (RepairRepresentation.natWord n))
noncomputable def calls : Fin 5 → Σ s,Machine 13 s
  | ⟨0,_⟩ => ⟨_,CloseoutRowsStrictSelector.machine⟩
  | ⟨1,_⟩ => ⟨_,negativeMachine⟩
  | ⟨2,_⟩ => ⟨_,literalMachine 1⟩
  | ⟨3,_⟩ => ⟨_,literalMachine 0⟩
  | ⟨4,_⟩ => ⟨_,positiveMachine⟩
  | ⟨j+5,hj⟩ => False.elim (by omega)
noncomputable def sizes (j : Fin 5) := (calls j).1
noncomputable def programs (j : Fin 5) : Machine 13 (sizes j) := (calls j).2
def next (j : Fin 5) (q : Fin (sizes j)) (bits : Fin 13 → Bool) : Option (Fin 5) :=
  if j.val=0 then some (if bits 12 then 1 else if !bits 0 then 2 else if q.val=9 then 4 else 3)
  else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def selected (source bits : List Bool) : Fin 5 :=
  if negative source then 1 else if bits.isEmpty then 2 else if 2≤bits.length then 4 else 3
def magnitude (source : List Bool) (n : ℕ) := if negative source then n+1 else if n=0 then 1 else n-1
def budget (bits : List Bool) := 24*bits.length+58

theorem selected_nonzero (source bits : List Bool) : (selected source bits).val≠0 := by
  unfold selected
  split_ifs <;> decide

theorem bits_large (n : ℕ) : 2≤n.bits.length ↔ 2≤n := by
  constructor
  · intro h
    by_contra hn
    have he : n=0 ∨ n=1 := by omega
    rcases he with rfl | rfl <;> simp at h
  · intro h
    by_contra hn
    have hl : n.bits.length≤1 := by omega
    have hp : 2^n.bits.length≤2^1 := Nat.pow_le_pow_right (by decide) hl
    have hv := RadixSemantics.value_lt n.bits
    rw [CanonicalPositiveOutput.nat_bits_value] at hv
    norm_num at hp
    omega

theorem bits_nonempty (n : ℕ) (hn : 0<n) : n.bits.isEmpty=false := by
  cases hb : n.bits with
  | nil =>
    have hv := CanonicalPositiveOutput.nat_bits_value n
    rw [hb] at hv
    change 0=n at hv
    omega
  | cons b bits => rfl

theorem arithmetic_input (source bits : List Bool) : ∀ i,
    prepared source bits (arithmeticSlots i)=CloseoutRowsStrictArithmetic.input bits i := by
  intro i
  fin_cases i <;> rfl

theorem keep_sign (source bits : List Bool) (out : Fin 10 → List Bool) :
    install arithmeticSlots (prepared source bits) out 11=prepared source bits 11 := by
  apply install_other
  intro j h
  have hv := congrArg Fin.val h
  change j.val=11 at hv
  omega

theorem literal_run (source bits : List Bool) (n : ℕ) : ∃ out,
    ClockJoin.ReadyRun (literalMachine n) (2*(RepairRepresentation.natWord n).length+2)
      (prepared source bits) out ∧ out 4=RepairRepresentation.natWord n ∧
      out 11=prepared source bits 11 := by
  obtain ⟨r,hr,rt,rh,rs⟩ := HierarchyFixedWord.word_ready (RepairRepresentation.natWord n)
  have h : ClockJoin.ReadyRun (HierarchyFixedWord.machine (RepairRepresentation.natWord n))
      (2*(RepairRepresentation.natWord n).length+2) (fun _ => [])
      ![RepairRepresentation.natWord n,List.replicate (RepairRepresentation.natWord n).length false] :=
    ⟨r,hr,rt,rh,rs.le⟩
  have hf := h.focus literalSlots literal_injective (prepared source bits)
    (by intro i;fin_cases i <;> rfl)
  exact ⟨_,hf,install_slot _ literal_injective _ _ 0,install_other _ _ _ _ (by decide)⟩

theorem arm_run (source : List Bool) (n : ℕ) : ∃ out,
    ClockJoin.ReadyRun (programs (selected source n.bits)) (24*n.bits.length+49)
      (prepared source n.bits) out ∧ out 4=RepairRepresentation.natWord (magnitude source n) ∧
      out 11=prepared source n.bits 11 := by
  cases hneg : negative source with
  | true =>
    have hj : selected source n.bits=1 := by simp [selected,hneg]
    rw [hj]
    obtain ⟨out,ho,h4⟩ := CloseoutRowsStrictArithmetic.negative_run n
    have hf := ho.focus arithmeticSlots arithmetic_injective (prepared source n.bits) (arithmetic_input _ _)
    refine ⟨_,ClockJoin.enlarge _ _ _ _ _ hf (by omega),?_,keep_sign _ _ _⟩
    change install arithmeticSlots _ out (arithmeticSlots 4)=_
    rw [install_slot _ arithmetic_injective,h4]
    simp [magnitude,hneg]
  | false =>
    by_cases hz : n=0
    · subst n
      have hj : selected source (0 : ℕ).bits=2 := by simp [selected,hneg]
      rw [hj]
      obtain ⟨out,ho,h4,h11⟩ := literal_run source (0 : ℕ).bits 1
      refine ⟨out,ClockJoin.enlarge _ _ _ _ _ ho (by decide),?_,h11⟩
      simpa [magnitude,hneg] using h4
    · by_cases h1 : n=1
      · subst n
        have hj : selected source (1 : ℕ).bits=3 := by simp [selected,hneg]
        rw [hj]
        obtain ⟨out,ho,h4,h11⟩ := literal_run source (1 : ℕ).bits 0
        exact ⟨out,ClockJoin.enlarge _ _ _ _ _ ho (by decide),by simpa [magnitude,hneg] using h4,h11⟩
      · have hn : 2≤n := by omega
        have hj : selected source n.bits=4 := by simp [selected,hneg,bits_nonempty n (by omega),(bits_large n).2 hn]
        rw [hj]
        obtain ⟨out,ho,h4⟩ := CloseoutRowsStrictArithmetic.positive_run n hn
        have hf := ho.focus arithmeticSlots arithmetic_injective (prepared source n.bits) (arithmetic_input _ _)
        refine ⟨_,ClockJoin.enlarge _ _ _ _ _ hf (by omega),?_,keep_sign _ _ _⟩
        change install arithmeticSlots _ out (arithmeticSlots 4)=_
        rw [install_slot _ arithmetic_injective,h4]
        simp [magnitude,hneg,hz]

theorem threshold_run (source : List Bool) (n : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget n.bits) (input source n.bits) out ∧
      out 4=RepairRepresentation.natWord (magnitude source n) ∧
      out 11=prepared source n.bits 11 := by
  obtain ⟨first,hr,hf,hs⟩ := selector_run source n.bits
  have hn : next 0 first.final.control first.final.scanned=some (selected source n.bits) := by
    have hneg : first.final.scanned 12=negative source := by rw [hf];rfl
    have hzero : first.final.scanned 0 = !n.bits.isEmpty := by rw [hf];exact frame_start n.bits
    have hlarge : first.final.control.val=if 2≤n.bits.length then 9 else 8 := by
      rw [hf]
      split_ifs <;> rfl
    simp only [next,show (0 : Fin 5).val=0 from rfl,hneg,hzero,Bool.not_not,hlarge]
    unfold selected
    by_cases h : 2≤n.bits.length <;> simp [h]
  obtain ⟨a,ha,hcall⟩ := call_receipt sizes programs 0 next 0 (selected source n.bits) 7
    (initialConfiguration CloseoutRowsStrictSelector.machine (input source n.bits)) first hr hn
  have he : RecoveryCalls.restarted (programs (selected source n.bits)) first.final.heads first.final.tapes=
      initialConfiguration (programs (selected source n.bits)) (prepared source n.bits) := by
    rw [hf]
    rfl
  rw [he] at hcall
  obtain ⟨out,⟨last,hl,lt,lh,ls⟩,h4,h11⟩ := arm_run source n
  obtain ⟨b,hb,hstop⟩ := stop_receipt sizes programs 0 next (selected source n.bits) (24*n.bits.length+49)
    (initialConfiguration (programs (selected source n.bits)) (prepared source n.bits)) last hl
    (by simp only [next,if_neg (selected_nonzero source n.bits)])
  obtain ⟨r,hrun,rf,rs⟩ := (hcall.trans hstop).run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have hbound : a+b≤budget n.bits := by unfold budget;omega
  have more := runFrom_moreFuel machine (a+b) (budget n.bits-(a+b)) _ r hrun
  rw [Nat.add_sub_of_le hbound] at more
  refine ⟨out,⟨r,more,?_,?_,rs.le.trans hbound⟩,h4,h11⟩
  · rw [rf]
    exact lt
  · intro i
    rw [rf]
    exact lh i

end NearCubicWires.RepairOrdinary.CloseoutRowsStrictThreshold
