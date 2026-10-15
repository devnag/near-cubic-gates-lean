import Proof.Hierarchy.HierarchyBinaryPowerEntry

/-! End-to-end fixed-degree binary powering, including the paid initialization
of one. The only scalar inputs are the framed binary n and the paid unary
field width; the program never traverses a unary copy of n^D. -/
namespace NearCubicWires.RepairOrdinary
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ClockJoin.ReadyRun.focus {t u s n : Nat} {p : Machine t s}
    {input output : Fin t → List Bool} (h : ClockJoin.ReadyRun p n input output)
    (slot : Fin t → Fin u) (hi : Function.Injective slot) (ambient : Fin u → List Bool)
    (hin : ∀ j,ambient (slot j)=input j) :
    ClockJoin.ReadyRun (RecoveryFocus.machine slot p) n ambient (install slot ambient output) := by
  obtain ⟨base,hr,ht,hh,hs⟩ := h
  obtain ⟨r,hrun,hf,hsteps⟩ := RecoveryFocus.run_config slot hi p (fun _ => 0) ambient n
    (initialConfiguration p input) base hr
  have hinit : RecoveryFocus.config slot (fun _ => 0) ambient (initialConfiguration p input)=
      initialConfiguration (RecoveryFocus.machine slot p) ambient := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick slot i <;> simp [RecoveryFocus.config,hp,initialConfiguration]
    · exact install_existing slot ambient input hin
  rw [hinit] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans_le hs⟩
  · rw [hf]
    change install slot ambient base.final.tapes=install slot ambient output
    rw [ht]
  · intro i
    cases hp : RecoveryFocus.pick slot i <;> simp [hf,RecoveryFocus.config,hp,hh]

namespace HierarchyPower
noncomputable def fullMachine (D : ℕ) (hD : 0<D) :=
  Composition.machine (bootstrap D) (machine D hD)
def fullBudget (D C n : ℕ) := 4*HierarchyBinary.width C D n+14+budget D C n

theorem full_run (D C n : ℕ) (hD : 0<D) :
    ∃ r : ExecutionReceipt (tapes D) (6+6+Fintype.card (RecoveryCalls.Control (sizes D))),
      run (fullMachine D hD) (fullBudget D C n)
        (initialData D (HierarchyBinary.width C D n) (ClockBinary.word n))=some r ∧
      Fields D C n hD r.final.tapes ∧ (∀ i,r.final.heads i=0) ∧
      r.steps ≤ fullBudget D C n := by
  obtain ⟨first,hfirst,ht,hh,hs⟩ := bootstrap_ready D (HierarchyBinary.width C D n)
    (ClockBinary.word n) (by dsimp [HierarchyBinary.width]; omega)
  obtain ⟨last,hlast,hfields,hlh,hls⟩ := power_run D C n hD _ (initialized_input D C n hD)
  have h := ClockJoin.join (bootstrap D) (machine D hD)
    (4*HierarchyBinary.width C D n+13) (budget D C n) _ _ _
    ⟨first,hfirst,ht,hh,hs.le⟩ ⟨last,hlast,rfl,hlh,hls⟩
  have he : 4*HierarchyBinary.width C D n+13+1+budget D C n=fullBudget D C n := by
    simp [fullBudget]
  rw [he] at h
  obtain ⟨r,hr,hrt,hrh,hrs⟩ := h
  exact ⟨r,hr,by rw [hrt]; exact hfields,hrh,hrs⟩

end HierarchyPower
end NearCubicWires.RepairOrdinary
