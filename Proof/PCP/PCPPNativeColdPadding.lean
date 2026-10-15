import Proof.PCP.PCPPNativeDescriptorEntry
import Proof.PCP.PCPPNativePadding

/-! Exact false-node padding from the raw count returned by cold metadata.
Template production, the paid sentinel-head shift and the whole padding
loop execute while the existing native node stream stays at its cursor. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeColdPadding
open LocalBitMultitape RecoveryRootRound RecoveryExecution RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def templateSlots : Fin 3 → Fin 4 := ![0,1,2]
def paddingSlots : Fin 2 → Fin 4 := ![3,1]
def heads (out : List Bool) : Fin 4 → ℕ := ![0,0,0,out.length]
def positioned (out : List Bool) : Fin 4 → ℕ := ![0,1,0,out.length]
def data (count : ℕ) (out : List Bool) : Fin 4 → List Bool := ![List.replicate count true,[],[],out]
def prepared (count : ℕ) (out : List Bool) : Fin 4 → List Bool :=
  ![List.replicate count true,UnaryTemplate.tape count,List.replicate (count+3) false,out]
noncomputable def first := RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def position : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,![.stay,.right,.stay,.stay]⟩ else none
noncomputable def last := RecoveryFocus.machine paddingSlots PCPPNativePadding.machine
noncomputable def machine := Composition.machine (Composition.machine first position) last
noncomputable def entry (count : ℕ) (out : List Bool) :=
  (⟨machine.start,heads out,data count out⟩ : Configuration 4 _)
def budget (count : ℕ) := 14*count+14

theorem template_run (count : ℕ) (out : List Bool) :
    ∃ r,runFrom first (2*count+8) ⟨first.start,heads out,data count out⟩=some r ∧
      r.final.heads=heads out ∧ r.final.tapes=prepared count out ∧ r.steps ≤ 2*count+8 := by
  obtain ⟨r,hr,rh,rt,rs⟩ := (DimensionTemplate.ready false count).focus_at templateSlots
    (by decide) (heads out) (data count out) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  refine ⟨r,hr,rh,?_,rs⟩
  rw [rt]
  funext i
  fin_cases i
  · exact install_slot _ (by decide) _ _ 0
  · exact install_slot _ (by decide) _ _ 1
  · exact install_slot _ (by decide) _ _ 2
  · rw [install_other _ _ _ _ (by decide)]; rfl

theorem position_run (out : List Bool) (tapes : Fin 4 → List Bool) :
    ∃ r,runFrom position 1 ⟨0,heads out,tapes⟩=some r ∧
      r.final=⟨1,positioned out,tapes⟩ ∧ r.steps=1 := by
  have hs : step position ⟨0,heads out,tapes⟩=some ⟨1,positioned out,tapes⟩ := by
    simp [step,position]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem append_run (count : ℕ) (out : List Bool) :
    ∃ result,runFrom machine (budget count) (entry count out)=some result ∧
      result.steps ≤ budget count ∧
      result.final.heads=positioned (out++PCPPNativePadding.emitted count) ∧
      result.final.tapes=prepared count (out++PCPPNativePadding.emitted count) := by
  obtain ⟨a,ha,ah,atapes,as⟩ := template_run count out
  obtain ⟨b,hb,bf,bs⟩ := position_run out (prepared count out)
  have mid : Composition.restart a.final position.start=⟨0,heads out,prepared count out⟩ := by
    apply configuration_ext
    · rfl
    · exact ah
    · exact atapes
  rw [←mid] at hb
  have hab := Composition.run_join first position _ _ _ a b ha hb
  obtain ⟨base,hbase,baseSteps,baseFinal⟩ := PCPPNativePadding.pad_run out count
  obtain ⟨c,hc,_,cs,ch,ct,ck⟩ := RecoveryFocus.dock paddingSlots (by decide) PCPPNativePadding.machine _
    b.final.heads b.final.tapes _
    (by intro j; rw [bf,PCPPNativePadding.template_heads]; fin_cases j <;> rfl)
    (by intro j; rw [bf,PCPPNativePadding.template_tapes]; fin_cases j <;> rfl) base hbase
  have joined := Composition.run_join (Composition.machine first position) last _ _ _
    (Composition.joinedReceipt a b) c hab hc
  have ht : ((2*count+8)+1+1)+1+(12*count+3)=budget count := by unfold budget; omega
  rw [ht] at joined
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt a b) c,joined,?_,?_,?_⟩
  · change a.steps+1+b.steps+1+c.steps ≤ _
    unfold budget
    omega
  · funext i
    fin_cases i
    · exact ((ck 0 (by decide)).1).trans (by rw [bf]; rfl)
    · exact (ch 1).trans (by rw [baseFinal,PCPPNativePadding.template_heads]; rfl)
    · exact ((ck 2 (by decide)).1).trans (by rw [bf]; rfl)
    · exact (ch 0).trans (by rw [baseFinal,PCPPNativePadding.template_heads]; rfl)
  · funext i
    fin_cases i
    · exact ((ck 0 (by decide)).2).trans (by rw [bf]; rfl)
    · exact (ct 1).trans (by rw [baseFinal,PCPPNativePadding.template_tapes]; rfl)
    · exact ((ck 2 (by decide)).2).trans (by rw [bf]; rfl)
    · exact (ct 0).trans (by rw [baseFinal,PCPPNativePadding.template_tapes]; rfl)

end NearCubicWires.RepairOrdinary.PCPPNativeColdPadding
