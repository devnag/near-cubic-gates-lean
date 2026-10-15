import Proof.MachineModel.OrdinaryMatrixPacketHeader
import Proof.MachineModel.OrdinaryMatrixPacketCapacityCost

/-! The source-fixed quadratic envelope includes the first capacity
bootstrap, every cold signed plane, and the actual p loop. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketBudget
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev exponent (a : WilliamsAlgorithm) := MatrixVariablePacketCapacity.exponent a
abbrev coefficient (a : WilliamsAlgorithm) := MatrixVariablePacketCapacity.coefficient a
abbrev capacity (a : WilliamsAlgorithm) (r : Request) := MatrixVariablePacketCapacity.capacity a r

theorem exponent_pos (a : WilliamsAlgorithm) : 1≤exponent a := by
  unfold exponent MatrixVariablePacketCapacity.exponent MatrixVariablePacketBounds.exponent MatrixWilliamsProductBounds.exponent
  omega
theorem coefficient_pos (a : WilliamsAlgorithm) : 1≤coefficient a := by
  unfold coefficient MatrixVariablePacketCapacity.coefficient
  omega
theorem q_le (a : WilliamsAlgorithm) (r : Request) : r.d+r.p+1≤capacity a r := by
  have hp:=Nat.le_self_pow (by have:=exponent_pos a; omega : exponent a≠0) (r.d+r.p+1)
  have h0 : 1≤coefficient a*(r.U+1)^2 := Nat.mul_pos (by have:=coefficient_pos a; omega) (pow_pos (by omega) _)
  exact hp.trans (Nat.le_mul_of_pos_left _ h0)
theorem bootstrap_eq (a : WilliamsAlgorithm) (r : Request) :
    MatrixPacketBootstrapState.capacity (exponent a) (coefficient a) r=capacity a r := rfl

theorem input_header_le (a : WilliamsAlgorithm) (r : Request) :
    (physicalInput r).length≤capacity a r ∧ MatrixPacketHeader.budget r≤capacity a r := by
  have hi:=MatrixVariableCapacity.input_bound r
  have hh : MatrixPacketHeader.budget r≤MatrixWilliamsInput.budget r := by
    rw [MatrixWilliamsProductBounds.preparation_eq]
    unfold MatrixBatchCoefficientPlanes.budget MatrixCoefficientCold.budget MatrixCoefficientCold.forwardBudget
      MatrixCoefficientHeaders.budget MatrixPacketHeader.budget MatrixPacketHeader.suffix
    omega
  have hp : MatrixWilliamsInput.budget r≤MatrixVariableProduct.budget a r := by
    unfold MatrixVariableProduct.budget
    rw [MatrixVariableInput.budget_eq]
    omega
  have hb:=MatrixWilliamsProductBounds.budget_bound a r
  rw [←MatrixVariableProduct.budget_eq] at hb
  have hc : MatrixWilliamsProductBounds.coefficient a≤coefficient a := by
    unfold coefficient MatrixVariablePacketCapacity.coefficient MatrixVariablePacketBounds.coefficient
    omega
  have hcap : MatrixVariableProduct.budget a r≤capacity a r := hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc))
  exact ⟨hi.trans (hp.trans hcap),hh.trans (hp.trans hcap)⟩

theorem positive_arithmetic (p q w cap entry E rf rt : ℕ)
    (hq : 1≤q) (hc : 1≤cap) (hp : p≤q) (hw : w≤cap) (hpc : p≤cap)
    (he : entry≤(20*E+148)*cap) (hf : rf≤cap) (ht : rt≤cap) :
    (16*w+rf+rt+entry+4*cap+51)+1+
      ((p-1)*(6*cap+16*w+8*p+49)+p+3)≤(20*E+400)*cap*q := by
  have hbody : 6*cap+16*w+8*p+49≤79*cap := by omega
  have hfirst : 16*w+rf+rt+entry+4*cap+51+1≤(20*E+222)*cap := by nlinarith only [hw,hf,ht,he,hc]
  have hloop:=Nat.mul_le_mul (by omega : p-1≤q) hbody
  have htail : p+3≤4*cap*q := by
    have hb:=Nat.le_mul_of_pos_right cap hq
    nlinarith only [hb,hpc,hc]
  have hraise:=Nat.le_mul_of_pos_right ((20*E+222)*cap) hq
  nlinarith only [hfirst,hloop,htail,hraise]

theorem positive_bound (a : WilliamsAlgorithm) (r : Request) (hp : 0<r.p) :
    MatrixPacketPositive.budget a (exponent a) (coefficient a) r≤
      (20*exponent a+400)*capacity a r*(r.d+r.p+1) := by
  have hcap (negative : Bool) : MatrixVariablePacketWorkspace.footprint a r 0 negative≤capacity a r :=
    MatrixVariablePacketCapacity.capacity_bound a r negative 0 hp
  have hw : (word r).length≤capacity a r := by
    have h:=(input_header_le a r).1
    simp only [physicalInput,frame_length] at h
    omega
  have hf : MatrixVariablePacketReset.budget a r 0 false≤capacity a r := by
    have h:=hcap false
    unfold MatrixVariablePacketWorkspace.footprint at h
    omega
  have ht : MatrixVariablePacketReset.budget a r 0 true≤capacity a r := by
    have h:=hcap true
    unfold MatrixVariablePacketWorkspace.footprint at h
    omega
  have hq:=q_le a r
  have hc : 1≤capacity a r := by omega
  have he:=MatrixPacketCapacityCost.budget_bound (exponent a) (coefficient a) r.U r.d r.p
    (exponent_pos a) (coefficient_pos a)
  have he' : MatrixPacketCapacityEntry.budget (exponent a) (coefficient a) r.U r.d r.p≤(20*exponent a+148)*capacity a r := by
    simpa only [MatrixVariablePacketCapacity.capacity,Nat.mul_assoc] using he
  have harith:=positive_arithmetic r.p (r.d+r.p+1) (word r).length (capacity a r)
    (MatrixPacketCapacityEntry.budget (exponent a) (coefficient a) r.U r.d r.p) (exponent a)
    (MatrixVariablePacketReset.budget a r 0 false) (MatrixVariablePacketReset.budget a r 0 true)
    (by omega) hc (by omega) hw (by omega) he' hf ht
  convert harith using 1
  unfold MatrixPacketPositive.budget MatrixPacketFirstBit.budget MatrixPacketColdBootstrap.budget
    MatrixPacketColdPrepare.budget MatrixPacketBootstrapErase.budget MatrixPacketCapacityNative.budget
    MatrixPacketReuse.budget MatrixPacketRestore.budget MatrixPacketOffset.budget
    MatrixPacketLoop.budget MatrixPacketLoop.bodyBudget
  rw [bootstrap_eq]
  unfold capacity MatrixVariablePacketCapacity.capacity
  ring

end NearCubicWires.RepairOrdinary.MatrixPacketBudget
