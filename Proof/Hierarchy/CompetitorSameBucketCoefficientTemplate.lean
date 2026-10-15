import Proof.Hierarchy.CompetitorSameBucketBlocks

/-! The scalar-state zero coefficient is physically generated from raw p.
Its sign plus p magnitude bits are all zero; no framed template is supplied. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketCoefficientTemplate
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bootSlots (j : Fin 13) : Fin 17 := j.castAdd 4
def zeroSlots : Fin 5 → Fin 17 := ![9,13,14,15,16]
theorem boot_injective : Function.Injective bootSlots := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 17 => x.val) h)
noncomputable def first:=RecoveryFocus.machine bootSlots CompetitorDimensions.bootstrapProgram
noncomputable def last:=RecoveryFocus.machine zeroSlots ClockNormalize.machine
noncomputable def machine:=Composition.machine first last
def input (p : ℕ) : Fin 17 → List Bool := fun i => if i=0 then List.replicate p true else []
def budget (p : ℕ) := CompetitorDimensions.bootstrapBudget p+1+(4*(p+1)+4)

theorem template_run (p : ℕ) : ∃ out,ClockJoin.ReadyRun machine (budget p) (input p) out ∧
    out 0=List.replicate p true ∧ out 14=frame (List.replicate (p+1) false) := by
  obtain ⟨boot,hr,b0,_,_,b9,_,_⟩:=CompetitorDimensions.bootstrap_run p
  have hboot:=bounded_focus bootSlots boot_injective _ _ _ hr (input p)
    (by intro i; fin_cases i <;> rfl)
  let prepared:=install bootSlots (input p) boot
  have fresh (j : Fin 17) (hj : 13≤j.val) : prepared j=[] := by
    apply (install_other bootSlots (input p) boot j ?_).trans
    · have h0 : j≠0 := by intro h; subst j; simp at hj
      simp [input,h0]
    · intro k hk
      have hv:=congrArg Fin.val hk
      change k.val=j.val at hv
      omega
  obtain ⟨z,hz,z0,_,z2,_,_,zh,zs⟩:=ClockScalarFields.zero_run (p+1)
  have ready : ClockJoin.ReadyRun ClockNormalize.machine (4*(p+1)+4) (ClockScalarFields.zeroInput (p+1)) z.final.tapes :=
    ⟨z,hz,rfl,zh,zs.le⟩
  have hzero:=bounded_focus zeroSlots (by decide) _ _ _ ready prepared (by
    intro i
    fin_cases i
    · exact (install_slot bootSlots boot_injective (input p) boot 9).trans b9
    all_goals exact fresh _ (by decide))
  have joined:=ClockJoin.join first last _ _ _ _ _ hboot hzero
  refine ⟨install zeroSlots prepared z.final.tapes,joined,?_,?_⟩
  · exact (install_other zeroSlots prepared z.final.tapes 0 (by decide)).trans
      ((install_slot bootSlots boot_injective (input p) boot 0).trans b0)
  · have h:=(install_slot zeroSlots (by decide) prepared z.final.tapes 2).trans z2
    simpa [RankCarrier.binary_zero,zeroSlots] using h

theorem budget_eq (p : ℕ) : budget p=10*p+8245 := by
  unfold budget CompetitorDimensions.bootstrapBudget
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketCoefficientTemplate
