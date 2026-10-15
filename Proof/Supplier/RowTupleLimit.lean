import Proof.Supplier.RowTupleColdEnumeration
import Proof.Hierarchy.HierarchyFixedWord
import Proof.MachineModel.ClockInitialKey
import Proof.Supplier.EquationScalarArithmetic

/-! Construct the tuple loop's terminal field and its paid extent from the
runtime unary product. Both fields were supplied to the earlier cold loop. -/
namespace NearCubicWires.RepairOrdinary.RowTupleLimit
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (L : ℕ) : Fin 12→List Bool := fun i=>if i=0 then List.replicate L true else []
def oneSlots : Fin 2→Fin 12 := ![8,9]
def sumSlots : Fin 4→Fin 12 := ![0,8,10,11]
def fieldSlots : Fin 6→Fin 12 := ![0,1,2,3,4,5]
def predSlots : Fin 3→Fin 12 := ![1,6,7]
theorem one_injective : Function.Injective oneSlots := by decide
theorem sum_injective : Function.Injective sumSlots := by decide
theorem field_injective : Function.Injective fieldSlots := by decide
theorem pred_injective : Function.Injective predSlots := by decide
noncomputable def one := RecoveryFocus.machine oneSlots (HierarchyFixedWord.machine [true])
noncomputable def sum := RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def field := RecoveryFocus.machine fieldSlots ClockFields.machine
noncomputable def predecessor := RecoveryFocus.machine predSlots RecoveryListPredecessor.machine
noncomputable def first := Composition.machine one sum
noncomputable def second := Composition.machine first field
noncomputable def machine := Composition.machine second predecessor
def budget (L : ℕ) := 10*L+45
def predInput (L : ℕ) : Fin 3→List Bool := ![frame (binary (L+1) (2^L)),[],[]]
def predPad : Fin 3→ℕ := ![0,1,0]

theorem predecessor_ready (L : ℕ) : ∃ out,
    ClockJoin.ReadyRun RecoveryListPredecessor.machine (4*(L+1)+4) (predInput L) out ∧
      out 0=frame (binary (L+1) (2^L-1)) := by
  have hn : 2^L<2^(L+1) := by
    rw [pow_succ]
    have : 0<2^L := by positivity
    omega
  obtain ⟨base,hb,bt,bh,bs⟩ := EquationScalar.predecessor_cold (L+1) (2^L) hn (by positivity)
  let c := initialConfiguration RecoveryListPredecessor.machine (predInput L)
  have hi : ZeroPadding.config predPad c=initialConfiguration RecoveryListPredecessor.machine
      ![frame (binary (L+1) (2^L)),[false],[]] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,predPad,c,predInput,initialConfiguration,ZeroPadding.pad]
  have hb' : runFrom RecoveryListPredecessor.machine (4*(L+1)+4) (ZeroPadding.config predPad c)=some base := by
    rw [hi]; exact hb
  obtain ⟨r,hr,hf,hs,_⟩ := ZeroPadding.run_unpad RecoveryListPredecessor.machine predPad _ c base hb'
  have ht := congrArg (fun cfg : Configuration 3 7=>cfg.tapes 0) hf
  have hh := congrArg Configuration.heads hf
  change r.final.heads=base.final.heads at hh
  refine ⟨r.final.tapes,⟨r,hr,rfl,?_,hs.trans bs |>.le⟩,?_⟩
  · intro i; rw [hh]; exact bh i
  · simpa [ZeroPadding.config,predPad,ZeroPadding.pad,bt] using ht

theorem power_binary (L : ℕ) : ClockInitialKey.power L=binary (L+1) (2^L) := by
  have hv : RadixSemantics.value (ClockInitialKey.power L)=2^L := by
    simp [ClockInitialKey.power,RadixSemantics.value_append,RadixSemantics.value]
  have h := (BoundedCounter.binary_of_value (ClockInitialKey.power L)).symm
  rw [hv] at h
  simpa [ClockInitialKey.power] using h

theorem limit_run (L : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget L) (input L) out ∧
      out 0=List.replicate L true ∧
      out 1=frame (binary (L+1) (2^L-1)) ∧ out 10=List.replicate (L+1) true := by
  obtain ⟨a,ha,atapes,ah,as⟩ := HierarchyFixedWord.word_ready [true]
  have hone : ClockJoin.ReadyRun (HierarchyFixedWord.machine [true]) 4 (fun _=>[]) ![[true],[false]] :=
    ⟨a,ha,atapes,ah,as.le⟩
  have hsum := ClockUnarySum.sum_ready L 1
  have hfield := ClockInitialKey.field_ready L
  obtain ⟨p,hp,p0⟩ := predecessor_ready L
  have h1 := bounded_focus oneSlots one_injective _ _ _ hone (input L)
    (by intro i; fin_cases i <;> rfl)
  let a1 := install oneSlots (input L) ![[true],[false]]
  have h2 := bounded_focus sumSlots sum_injective _ _ _ hsum a1 (by
    intro i; fin_cases i
    · change install oneSlots (input L) ![[true],[false]] 0=List.replicate L true
      rw [install_other _ _ _ _ (by decide)]; rfl
    · exact install_slot oneSlots one_injective _ _ 0
    · change install oneSlots (input L) ![[true],[false]] 10=[]
      rw [install_other _ _ _ _ (by decide)]; rfl
    · change install oneSlots (input L) ![[true],[false]] 11=[]
      rw [install_other _ _ _ _ (by decide)]; rfl)
  let a2 := install sumSlots a1
    ![List.replicate L true,List.replicate 1 true,List.replicate (L+1) true,List.replicate (L+1+2) false]
  have h3 := bounded_focus fieldSlots field_injective _ _ _ hfield a2 (by
    intro i; fin_cases i
    · exact install_slot sumSlots sum_injective _ _ 0
    all_goals
      rw [show a2 (fieldSlots _)=install sumSlots a1 _ (fieldSlots _) from rfl]
      rw [install_other _ _ _ _ (by decide)]
      rw [show a1 (fieldSlots _)=install oneSlots (input L) _ (fieldSlots _) from rfl]
      rw [install_other _ _ _ _ (by decide)]
      rfl)
  let a3 := install fieldSlots a2 (ClockInitialKey.fieldOutput L)
  have h4 := bounded_focus predSlots pred_injective _ _ _ hp a3 (by
    intro i; fin_cases i
    · change install fieldSlots a2 (ClockInitialKey.fieldOutput L) (fieldSlots 1)=frame (binary (L+1) (2^L))
      rw [install_slot _ field_injective]
      change frame (ClockInitialKey.power L)=frame (binary (L+1) (2^L))
      rw [power_binary]
    all_goals
      rw [show a3 (predSlots _)=install fieldSlots a2 _ (predSlots _) from rfl]
      rw [install_other _ _ _ _ (by decide)]
      rw [show a2 (predSlots _)=install sumSlots a1 _ (predSlots _) from rfl]
      rw [install_other _ _ _ _ (by decide)]
      rw [show a1 (predSlots _)=install oneSlots (input L) _ (predSlots _) from rfl]
      rw [install_other _ _ _ _ (by decide)]
      rfl)
  have hwhole := ClockJoin.join second predecessor _ _ _ _ _
    (ClockJoin.join first field _ _ _ _ _ (ClockJoin.join one sum _ _ _ _ _ h1 h2) h3) h4
  have he : ((4+1+(2*(L+1)+6))+1+(4*L+22))+1+(4*(L+1)+4)=budget L := by unfold budget; omega
  rw [he] at hwhole
  refine ⟨install predSlots a3 p,hwhole,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide)]
    exact install_slot fieldSlots field_injective _ _ 0
  · exact (install_slot predSlots pred_injective _ _ 0).trans p0
  · rw [install_other _ _ _ _ (by decide)]
    rw [show a3 10=install fieldSlots a2 _ 10 from rfl,install_other _ _ _ _ (by decide)]
    exact install_slot sumSlots sum_injective _ _ 2

end NearCubicWires.RepairOrdinary.RowTupleLimit
