import Proof.Hierarchy.CompetitorSumLoop

/-! Actual construction of the zero/zero/one rational accumulator. The
unary wide and short widths are retained. All other native input tapes are
blank; fixed one is printed by the accepted clock-field writer at q=0. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumConstants
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (b : ℕ) : Fin 88 → List Bool := fun i =>
  if i.val=6 then List.replicate (width b) true else if i.val=84 then List.replicate b true else []
def zeroSlots (j : Fin 2) : Fin 5 → Fin 88 := if j.val=0 then ![6,2,0,3,5] else ![6,7,1,8,9]
def powerSlots : Fin 6 → Fin 88 := ![10,11,12,13,14,15]
def normalizeSlots : Fin 5 → Fin 88 := ![84,11,4,16,17]
noncomputable def zeroProgram (j : Fin 2) := RecoveryFocus.machine (zeroSlots j) ClockNormalize.machine
noncomputable def powerProgram := RecoveryFocus.machine powerSlots ClockFields.machine
noncomputable def normalizeProgram := RecoveryFocus.machine normalizeSlots ClockNormalize.machine
noncomputable def machine := Composition.machine (zeroProgram 0)
  (Composition.machine (zeroProgram 1) (Composition.machine powerProgram normalizeProgram))

theorem constants_run (b : ℕ) (hb : 1≤b) :
    ∃ out,ClockJoin.ReadyRun machine (20*b+53) (input b) out ∧
      out 0=frame (binary (width b) 0) ∧ out 1=frame (binary (width b) 0) ∧
      out 4=frame (binary b 1) ∧ out 6=List.replicate (width b) true ∧ out 84=List.replicate b true := by
  obtain ⟨zero,hzero,hz0,_,hz2,_,_,hzh,hzs⟩ := ClockScalarFields.zero_run (width b)
  have zeroReady : ClockJoin.ReadyRun ClockNormalize.machine (4*width b+4)
      (ClockScalarFields.zeroInput (width b)) zero.final.tapes := ⟨zero,hzero,rfl,hzh,hzs.le⟩
  let first := install (zeroSlots 0) (input b) zero.final.tapes
  have hfirst := bounded_focus (zeroSlots 0) (by decide) _ _ _ zeroReady (input b)
    (by intro i; fin_cases i <;> rfl)
  have hiSecond : ∀ i,first (zeroSlots 1 i)=ClockScalarFields.zeroInput (width b) i := by
    intro i
    fin_cases i
    · exact (install_slot (zeroSlots 0) (by decide) _ zero.final.tapes 0).trans hz0
    · exact install_other (zeroSlots 0) _ _ 7 (by decide)
    · exact install_other (zeroSlots 0) _ _ 1 (by decide)
    · exact install_other (zeroSlots 0) _ _ 8 (by decide)
    · exact install_other (zeroSlots 0) _ _ 9 (by decide)
  let second := install (zeroSlots 1) first zero.final.tapes
  have hsecond := bounded_focus (zeroSlots 1) (by decide) _ _ _ zeroReady first hiSecond
  obtain ⟨power,hpower,_,hp1,_,_,_,_,hph,hps⟩ := ClockFields.fields_run 0
  have powerReady : ClockJoin.ReadyRun ClockFields.machine 22
      (Fin.addCases (motive := fun _ : Fin (5+1) => List Bool)
        ![List.replicate 0 true,[],[],[],[]] (fun _ : Fin 1 => [])) power.final.tapes :=
    ⟨power,hpower,rfl,hph,hps.le⟩
  have hiPower : ∀ i,second (powerSlots i)=
      (Fin.addCases (motive := fun _ : Fin (5+1) => List Bool)
        ![List.replicate 0 true,[],[],[],[]] (fun _ : Fin 1 => [])) i := by
    intro i
    have hs : ∀ j,zeroSlots 1 j≠powerSlots i := by fin_cases i <;> decide
    have hf : ∀ j,zeroSlots 0 j≠powerSlots i := by fin_cases i <;> decide
    rw [show second (powerSlots i)=first (powerSlots i) from install_other _ _ _ _ hs,
      show first (powerSlots i)=input b (powerSlots i) from install_other _ _ _ _ hf]
    fin_cases i <;> rfl
  let powered := install powerSlots second power.final.tapes
  have hpowered := bounded_focus powerSlots (by decide) _ _ _ powerReady second hiPower
  obtain ⟨normalized,hn,hn0,_,hn2,_,_,hnh,hns⟩ := ClockScalarFields.scalar_run b [true] (by simpa using hb)
  have normalizeReady : ClockJoin.ReadyRun ClockNormalize.machine (4*b+4)
      (ClockNormalize.input b [true]) normalized.final.tapes := ⟨normalized,hn,rfl,hnh,hns.le⟩
  have hiNormalize : ∀ i,powered (normalizeSlots i)=ClockNormalize.input b [true] i := by
    intro i
    fin_cases i
    · exact (install_other powerSlots _ _ 84 (by decide)).trans
        ((install_other (zeroSlots 1) _ _ 84 (by decide)).trans
          (install_other (zeroSlots 0) _ _ 84 (by decide)))
    · exact (install_slot powerSlots (by decide) _ power.final.tapes 1).trans hp1
    · exact (install_other powerSlots _ _ 4 (by decide)).trans
        ((install_other (zeroSlots 1) _ _ 4 (by decide)).trans
          (install_other (zeroSlots 0) _ _ 4 (by decide)))
    · exact (install_other powerSlots _ _ 16 (by decide)).trans
        ((install_other (zeroSlots 1) _ _ 16 (by decide)).trans
          (install_other (zeroSlots 0) _ _ 16 (by decide)))
    · exact (install_other powerSlots _ _ 17 (by decide)).trans
        ((install_other (zeroSlots 1) _ _ 17 (by decide)).trans
          (install_other (zeroSlots 0) _ _ 17 (by decide)))
  let out := install normalizeSlots powered normalized.final.tapes
  have hnormalized := bounded_focus normalizeSlots (by decide) _ _ _ normalizeReady powered hiNormalize
  have htail := ClockJoin.join powerProgram normalizeProgram _ _ _ _ _ hpowered hnormalized
  have hmiddle := ClockJoin.join (zeroProgram 1) (Composition.machine powerProgram normalizeProgram) _ _ _ _ _ hsecond htail
  have hall := ClockJoin.join (zeroProgram 0) (Composition.machine (zeroProgram 1)
    (Composition.machine powerProgram normalizeProgram)) _ _ _ _ _ hfirst hmiddle
  have hcost : (4*width b+4)+1+((4*width b+4)+1+(22+1+(4*b+4)))=20*b+53 := by
    unfold width
    omega
  rw [hcost] at hall
  refine ⟨out,hall,?_,?_,?_,?_,?_⟩
  · exact (install_other normalizeSlots _ _ 0 (by decide)).trans
      ((install_other powerSlots _ _ 0 (by decide)).trans
        ((install_other (zeroSlots 1) _ _ 0 (by decide)).trans
          ((install_slot (zeroSlots 0) (by decide) _ zero.final.tapes 2).trans hz2)))
  · exact (install_other normalizeSlots _ _ 1 (by decide)).trans
      ((install_other powerSlots _ _ 1 (by decide)).trans
        ((install_slot (zeroSlots 1) (by decide) _ zero.final.tapes 2).trans hz2))
  · exact (install_slot normalizeSlots (by decide) _ normalized.final.tapes 2).trans hn2
  · exact (install_other normalizeSlots _ _ 6 (by decide)).trans
      ((install_other powerSlots _ _ 6 (by decide)).trans
        ((install_slot (zeroSlots 1) (by decide) _ zero.final.tapes 0).trans hz0))
  · exact (install_slot normalizeSlots (by decide) _ normalized.final.tapes 0).trans hn0

end NearCubicWires.RepairOrdinary.CompetitorSumConstants
