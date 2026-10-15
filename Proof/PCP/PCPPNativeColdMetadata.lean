import Proof.PCP.PCPPNativeArithmetic

/-! Native domain, padded size and exact padding are physically computed
from the measured width and the actual emitted-node counter. The source's
fixed minimum arity is printed by finite control; no size recount is used. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeColdMetadata
open LocalBitMultitape RecoveryRootRound SourceInterfaces ExecutableInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def fixedSlots : Fin 2 → Fin 10 := ![2,3]
def domainSlots : Fin 5 → Fin 10 := ![0,2,4,5,6]
def paddingSlots : Fin 5 → Fin 10 := ![4,1,7,8,9]
theorem fixed_injective : Function.Injective fixedSlots := by decide
theorem domain_injective : Function.Injective domainSlots := by decide
theorem padding_injective : Function.Injective paddingSlots := by decide
def input (width size : ℕ) : Fin 10 → List Bool :=
  ![List.replicate width true,List.replicate size true,[],[],[],[],[],[],[],[]]
def domain (minimum width : ℕ) := max width minimum
def padded (minimum width size : ℕ) := max (domain minimum width) size
def padding (minimum width size : ℕ) := domain minimum width-size
def afterFixed (minimum width size : ℕ) := install fixedSlots (input width size)
  ![List.replicate minimum true,List.replicate minimum false]
def afterDomain (minimum width size : ℕ) := install domainSlots (afterFixed minimum width size)
  (PCPPNativeColdArithmetic.output width minimum)
def output (minimum width size : ℕ) := install paddingSlots (afterDomain minimum width size)
  (PCPPNativeColdArithmetic.output (domain minimum width) size)
def fixed (minimum : ℕ) := RecoveryFocus.machine fixedSlots
  (HierarchyFixedWord.machine (List.replicate minimum true))
def domainMachine := RecoveryFocus.machine domainSlots PCPPNativeColdArithmetic.machine
def paddingMachine := RecoveryFocus.machine paddingSlots PCPPNativeColdArithmetic.machine
def machine (minimum : ℕ) := Composition.machine (Composition.machine (fixed minimum) domainMachine) paddingMachine
def budget (minimum width size : ℕ) :=
  2*minimum+2*domain minimum width+2*padded minimum width size+12

theorem fixed_local (minimum width size : ℕ) (i : Fin 2) :
    afterFixed minimum width size (fixedSlots i)=
      (![List.replicate minimum true,List.replicate minimum false] i) :=
  install_slot _ fixed_injective _ _ _
theorem domain_input (minimum width size : ℕ) (i : Fin 5) :
    afterFixed minimum width size (domainSlots i)=PCPPNativeColdArithmetic.input width minimum i := by
  fin_cases i
  · rw [afterFixed,install_other _ _ _ _ (by decide)]; rfl
  · exact fixed_local minimum width size 0
  · rw [afterFixed,install_other _ _ _ _ (by decide)]; rfl
  · rw [afterFixed,install_other _ _ _ _ (by decide)]; rfl
  · rw [afterFixed,install_other _ _ _ _ (by decide)]; rfl
theorem domain_local (minimum width size : ℕ) (i : Fin 5) :
    afterDomain minimum width size (domainSlots i)=PCPPNativeColdArithmetic.output width minimum i :=
  install_slot _ domain_injective _ _ _
theorem padding_input (minimum width size : ℕ) (i : Fin 5) :
    afterDomain minimum width size (paddingSlots i)=
      PCPPNativeColdArithmetic.input (domain minimum width) size i := by
  fin_cases i
  · exact domain_local minimum width size 2
  · rw [afterDomain,install_other _ _ _ _ (by decide),afterFixed,install_other _ _ _ _ (by decide)]; rfl
  · rw [afterDomain,install_other _ _ _ _ (by decide),afterFixed,install_other _ _ _ _ (by decide)]; rfl
  · rw [afterDomain,install_other _ _ _ _ (by decide),afterFixed,install_other _ _ _ _ (by decide)]; rfl
  · rw [afterDomain,install_other _ _ _ _ (by decide),afterFixed,install_other _ _ _ _ (by decide)]; rfl

private theorem bounded {t s b : ℕ} {p : Machine t s} {a z : Fin t → List Bool}
    (h : ReadyRun p b a z) : ClockJoin.ReadyRun p b a z := by
  obtain ⟨r,hr,ht,hh,hs⟩ := h
  exact ⟨r,hr,ht,hh,hs.le⟩

theorem ready (minimum width size : ℕ) :
    ClockJoin.ReadyRun (machine minimum) (budget minimum width size) (input width size) (output minimum width size) := by
  have first := (HierarchyFixedWord.word_ready (List.replicate minimum true)).focus
    fixedSlots fixed_injective (input width size) (by intro i; fin_cases i <;> rfl)
  simp only [List.length_replicate] at first
  have second := (PCPPNativeColdArithmetic.ready width minimum).focus domainSlots domain_injective
    (afterFixed minimum width size) (domain_input minimum width size)
  have last := (PCPPNativeColdArithmetic.ready (domain minimum width) size).focus paddingSlots padding_injective
    (afterDomain minimum width size) (padding_input minimum width size)
  have joined := ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ (bounded first) (bounded second)) (bounded last)
  have ht : ((2*minimum+2)+1+PCPPNativeColdArithmetic.budget width minimum)+1+
      PCPPNativeColdArithmetic.budget (domain minimum width) size=budget minimum width size := by
    simp only [PCPPNativeColdArithmetic.budget,budget,padded,domain]
    omega
  rw [ht] at joined
  exact joined

theorem fields (minimum width size : ℕ) :
    output minimum width size 0=List.replicate width true ∧
    output minimum width size 1=List.replicate size true ∧
    output minimum width size 4=List.replicate (domain minimum width) true ∧
    output minimum width size 7=List.replicate (padded minimum width size) true ∧
    output minimum width size 8=List.replicate (padding minimum width size) true := by
  have finalLocal (i : Fin 5) : output minimum width size (paddingSlots i)=
      PCPPNativeColdArithmetic.output (domain minimum width) size i :=
    install_slot _ padding_injective _ _ _
  refine ⟨?_,finalLocal 1,finalLocal 0,finalLocal 2,finalLocal 3⟩
  rw [output,install_other _ _ _ _ (by decide)]
  exact domain_local minimum width size 0

theorem source_fields (a : PointwisePCPPAlgorithm) (width size : ℕ) :
    output a.minimumArity width size 4=List.replicate (PCPPRequestBoundary.domain a width) true ∧
    output a.minimumArity width size 7=List.replicate (size+(PCPPRequestBoundary.domain a width-size)) true ∧
    output a.minimumArity width size 8=List.replicate (PCPPRequestBoundary.domain a width-size) true := by
  obtain ⟨_,_,hd,hs,hp⟩ := fields a.minimumArity width size
  refine ⟨hd,?_,hp⟩
  have he : padded a.minimumArity width size=size+(PCPPRequestBoundary.domain a width-size) := by
    unfold padded domain PCPPRequestBoundary.domain
    omega
  rw [he] at hs
  exact hs

end
end NearCubicWires.RepairOrdinary.PCPPNativeColdMetadata
