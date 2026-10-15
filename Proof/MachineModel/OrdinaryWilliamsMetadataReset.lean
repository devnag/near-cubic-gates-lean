import Proof.MachineModel.OrdinaryWilliamsMetadata

/-! Paid whole-phase cursor restoration for the metadata producer. The
external frame, raw matrix word, U and the payload-derived c are retained.
The quadratic estimate includes the complete input scan and actual rewind. -/
namespace NearCubicWires.RepairOrdinary.WilliamsMetadata
open LocalBitMultitape SourceInterfaces ExecutableInterfaces RepairRepresentation SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_quadratic (r : RectangularProductRequest) : budget r≤128*(r.dimension+1)^2 := by
  let u := r.dimension
  let w := natBitLength u
  let c := rectangularInnerDimension u
  have hw : w≤u+1 := Nat.add_le_add_right (Nat.log_le_self 2 u) 1
  have hc : c≤u := WilliamsPaddedRequest.inner_le u
  have huc : u*c≤u*u := Nat.mul_le_mul_left u hc
  have huw : u*w≤u*(u+1) := Nat.mul_le_mul_left u hw
  have hlen : (natWord u++WilliamsPayloadCount.payload r).length=2*w+1+2*u*c := by
    rw [List.length_append]
    have hn : (natWord u).length=2*w+1 := WilliamsLoader.nat_frame_length u
    rw [hn,WilliamsPayloadCount.payload_length]
  change WilliamsInputHeader.budget u (WilliamsPayloadCount.payload r)+6*w+c*(6*u+15)+23≤128*(u+1)^2
  unfold WilliamsInputHeader.budget
  rw [hlen]
  change 4*(2*w+1+2*u*c)+3+MatrixDimensionPrepare.budget w u+6*w+c*(6*u+15)+23≤_
  unfold MatrixDimensionPrepare.budget
  nlinarith

noncomputable def resetMachine := Rewind.machine machine
def resetInput (r : RectangularProductRequest) : Fin 15 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (14+1) => List Bool) (input r) (fun _ : Fin 1 => [])

theorem reset_run (r : RectangularProductRequest) (hr : 1≤r.dimension) :
    ∃ actual : ExecutionReceipt 15 (headerStates+15+countStates+2),
      run resetMachine (258*(r.dimension+1)^2) (resetInput r)=some actual ∧
      actual.final.tapes 0=frame (word r) ∧ actual.final.tapes 1=word r ∧
      actual.final.tapes 3=List.replicate (natBitLength r.dimension) true ∧
      actual.final.tapes 5=UnaryTemplate.tape (natBitLength r.dimension) ∧
      actual.final.tapes 6=frame (binary (natBitLength r.dimension) r.dimension) ∧
      actual.final.tapes 12=UnaryTemplate.tape r.dimension ∧
      actual.final.tapes 13=UnaryTemplate.tape (rectangularInnerDimension r.dimension) ∧
      (∀ i,actual.final.heads i=0) ∧ actual.steps≤258*(r.dimension+1)^2 := by
  obtain ⟨base,hb,hd,hs⟩ := metadata_run r hr
  obtain ⟨actual,ha,ht,hh,hsteps,_⟩ := Rewind.reset_run machine (budget r) (input r) base hb
  have hbudget := budget_quadratic r
  have hone : 1≤(r.dimension+1)^2 := by nlinarith
  have hbound : 2*base.steps+2≤258*(r.dimension+1)^2 := by nlinarith
  have hm := run_moreFuel resetMachine (2*base.steps+2)
    (258*(r.dimension+1)^2-(2*base.steps+2)) (resetInput r) actual ha
  rw [Nat.add_sub_of_le hbound] at hm
  rcases hd with ⟨h0,h1,h3,h5,h6,h12,h13⟩
  exact ⟨actual,hm,(ht 0).trans h0,(ht 1).trans h1,(ht 3).trans h3,(ht 5).trans h5,
    (ht 6).trans h6,(ht 12).trans h12,(ht 13).trans h13,hh,hsteps.trans_le hbound⟩

end NearCubicWires.RepairOrdinary.WilliamsMetadata
