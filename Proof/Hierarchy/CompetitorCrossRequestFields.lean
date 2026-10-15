import Proof.Hierarchy.CompetitorCrossRequestDimensions

/-! Original framed Request to all literal cross-table input dimensions.
The actual unary products allocate U²; the short widths remain d+1 and
d+2p+3. No dimension word is supplied by the caller. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossRequestFields
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
open RepairSource.ProjectionNormalization
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (r : Request) : Fin 61 → List Bool :=
  Fin.addCases (m := 46) (n := 15) (motive := fun _ => List Bool) (CompetitorCrossRequestDimensions.input r) (fun _ => [])
def oneSlots : Fin 2 → Fin 61 := ![46,47]
def bSlots : Fin 4 → Fin 61 := ![24,46,48,49]
def pSlots : Fin 4 → Fin 61 := ![28,29,50,51]
def wSlots : Fin 4 → Fin 61 := ![33,50,52,53]
def nSlots (i : Fin 7) : Fin 61 := if i.val=0 then 44 else if i.val=5 then 54 else ⟨i.val+54,by omega⟩
theorem n_injective : Function.Injective nSlots := by decide
noncomputable def first := ClockJoin.lifted (e := 15) (Equiv.refl (Fin 61)) CompetitorCrossRequestDimensions.machine
noncomputable def one := RecoveryFocus.machine oneSlots (HierarchyFixedWord.machine [true])
noncomputable def bSum := RecoveryFocus.machine bSlots ClockUnarySum.machine
noncomputable def pSum := RecoveryFocus.machine pSlots ClockUnarySum.machine
noncomputable def wSum := RecoveryFocus.machine wSlots ClockUnarySum.machine
noncomputable def nPower := RecoveryFocus.machine nSlots (DimensionPower.machine 2 1)
noncomputable def tail := Composition.machine one (Composition.machine bSum (Composition.machine pSum (Composition.machine wSum nPower)))
noncomputable def machine := Composition.machine first tail
def budget (r : Request) := CompetitorCrossRequestDimensions.budget r+1+
  (4+1+((2*(r.d+1)+6)+1+((2*(r.p+r.p)+6)+1+((2*(r.d+3+(r.p+r.p))+6)+1+DimensionPower.cost 1 r.U 2))))

theorem fields_run (r : Request) : ∃ out,ClockJoin.ReadyRun machine (budget r) (input r) out ∧
    out 0=MatrixScoreBatch.physicalInput r ∧ out 28=List.replicate r.p true ∧
    out 44=UnaryTemplate.tape r.U ∧ out 48=List.replicate (natBitLength r.U) true ∧
    out 52=List.replicate (CompetitorPlaneWidth.width (natBitLength r.U) r.p) true ∧
    out 54=List.replicate (r.U*r.U) true := by
  obtain ⟨a,ha,h0,h24,h28,h29,h33,h44⟩ := CompetitorCrossRequestDimensions.dimensions_run r
  let atapes : Fin 61 → List Bool := Fin.addCases (m := 46) (n := 15) (motive := fun _ => List Bool) a (fun _ => [])
  have hfirst : ClockJoin.ReadyRun first (CompetitorCrossRequestDimensions.budget r) (input r) atapes :=
    ClockJoin.lift (e := 15) (Equiv.refl (Fin 61)) _ _ _ _ (fun _ : Fin 15 => []) ha
  have hone := bounded_focus oneSlots (by decide) _ _ _ (CompetitorCrossAffineDimensions.constant_ready 1) atapes
    (by intro i;fin_cases i <;> rfl)
  let btapes := install oneSlots atapes (![List.replicate 1 true,List.replicate 1 false])
  have hb := bounded_focus bSlots (by decide) _ _ _
    (CompetitorSameBucketGroupColdDimensions.sum_ready r.d 1) btapes (by
      intro i
      fin_cases i
      · exact (install_other oneSlots _ _ _ (by decide)).trans h24
      · exact install_slot oneSlots (by decide) _ _ 0
      all_goals exact install_other oneSlots _ _ _ (by decide))
  let ctapes := install bSlots btapes (CompetitorSameBucketGroupColdDimensions.sumOutput r.d 1)
  have hp := bounded_focus pSlots (by decide) _ _ _
    (CompetitorSameBucketGroupColdDimensions.sum_ready r.p r.p) ctapes (by
      intro i
      fin_cases i
      · exact (install_other bSlots _ _ _ (by decide)).trans ((install_other oneSlots _ _ _ (by decide)).trans h28)
      · exact (install_other bSlots _ _ _ (by decide)).trans ((install_other oneSlots _ _ _ (by decide)).trans h29)
      all_goals exact (install_other bSlots _ _ _ (by decide)).trans (install_other oneSlots _ _ _ (by decide)))
  let dtapes := install pSlots ctapes (CompetitorSameBucketGroupColdDimensions.sumOutput r.p r.p)
  have hw := bounded_focus wSlots (by decide) _ _ _
    (CompetitorSameBucketGroupColdDimensions.sum_ready (r.d+3) (r.p+r.p)) dtapes (by
      intro i
      fin_cases i
      · exact (install_other pSlots _ _ _ (by decide)).trans
          ((install_other bSlots _ _ _ (by decide)).trans ((install_other oneSlots _ _ _ (by decide)).trans h33))
      · exact install_slot pSlots (by decide) _ _ 2
      all_goals
        exact (install_other pSlots _ _ _ (by decide)).trans
          ((install_other bSlots _ _ _ (by decide)).trans (install_other oneSlots _ _ _ (by decide))))
  let etapes := install wSlots dtapes (CompetitorSameBucketGroupColdDimensions.sumOutput (r.d+3) (r.p+r.p))
  obtain ⟨pow,hpow,p0,p5⟩ := DimensionPower.power_run 2 1 r.U
  have hn := bounded_focus nSlots n_injective _ _ _ hpow etapes (by
    intro i
    fin_cases i
    · exact (install_other wSlots _ _ _ (by decide)).trans
        ((install_other pSlots _ _ _ (by decide)).trans
          ((install_other bSlots _ _ _ (by decide)).trans ((install_other oneSlots _ _ _ (by decide)).trans h44)))
    all_goals
      exact (install_other wSlots _ _ _ (by decide)).trans
        ((install_other pSlots _ _ _ (by decide)).trans
          ((install_other bSlots _ _ _ (by decide)).trans (install_other oneSlots _ _ _ (by decide)))))
  let out := install nSlots etapes pow
  have hnTail := ClockJoin.join _ _ _ _ _ _ _ hw hn
  have hwTail := ClockJoin.join _ _ _ _ _ _ _ hp hnTail
  have hpTail := ClockJoin.join _ _ _ _ _ _ _ hb hwTail
  have htail := ClockJoin.join _ _ _ _ _ _ _ hone hpTail
  have bitWidth : natBitLength r.U=r.d+1 := by simp [MatrixScoreBatch.Request.U,natBitLength,Nat.log_pow]
  refine ⟨out,ClockJoin.join _ _ _ _ _ _ _ hfirst htail,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other nSlots _ _ _ (by decide)).trans
      ((install_other wSlots _ _ _ (by decide)).trans
        ((install_other pSlots _ _ _ (by decide)).trans
          ((install_other bSlots _ _ _ (by decide)).trans ((install_other oneSlots _ _ _ (by decide)).trans h0))))
  · exact (install_other nSlots _ _ _ (by decide)).trans
      ((install_other wSlots _ _ _ (by decide)).trans (install_slot pSlots (by decide) _ _ 0))
  · exact (install_slot nSlots n_injective _ pow 0).trans p0
  · rw [bitWidth]
    exact (install_other nSlots _ _ _ (by decide)).trans
      ((install_other wSlots _ _ _ (by decide)).trans
        ((install_other pSlots _ _ _ (by decide)).trans (install_slot bSlots (by decide) _ _ 2)))
  · have he : r.d+3+(r.p+r.p)=CompetitorPlaneWidth.width (natBitLength r.U) r.p := by
      rw [bitWidth]
      unfold CompetitorPlaneWidth.width
      omega
    rw [←he]
    exact (install_other nSlots _ _ _ (by decide)).trans (install_slot wSlots (by decide) _ _ 2)
  · change install nSlots etapes pow (nSlots 5)=_
    rw [install_slot nSlots n_injective]
    change pow (5 : Fin 7)=List.replicate (1*r.U^2) true at p5
    simpa only [Nat.one_mul,pow_two] using p5

end NearCubicWires.RepairOrdinary.CompetitorCrossRequestFields
