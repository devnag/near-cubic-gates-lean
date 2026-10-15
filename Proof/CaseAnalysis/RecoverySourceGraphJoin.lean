import Proof.CaseAnalysis.RecoverySourceGraphMeaning

/-! The one source-to-graph composition keeps state counts symbolic while
using the original sparse bank. All source and graph calls remain charged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSourceGraph.Join
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (k d : ℕ)

def machine {s t : ℕ} (first : Machine (tapes source k d) s) (last : Machine 1664 t):=
  Composition.machine first (RecoveryFocus.machine (graphSlots source k d) last)

theorem run {s t : ℕ} (first : Machine (tapes source k d) s) (last : Machine 1664 t)
    (u v : ℕ) (word : List Bool) (W : ℕ) (A : Fin 158→List Bool)
    (payload arity : List Bool) (E : Fin 5→List Bool)
    (hp : ∃ r,LocalBitMultitape.run first u (input source k d word W)=some r ∧ r.steps ≤ u ∧
      (∀ i : Fin 1664,r.final.heads (graphSlots source k d i)=0) ∧
      (∀ i : Fin 1664,r.final.tapes (graphSlots source k d i)=RecoveryBoundedColdGraph.insert [] A i) ∧
      r.final.tapes (hierarchyPort source k d)=word ∧ r.final.heads (hierarchyPort source k d)=0 ∧
      r.final.tapes (wPort source k d)=List.replicate W true ∧ r.final.heads (wPort source k d)=0)
    (hq : ∃ r,LocalBitMultitape.run last v (RecoveryBoundedColdGraph.insert [] A)=some r ∧ r.steps ≤ v ∧
      r.final.tapes 1657=payload ∧ r.final.heads 1657=0 ∧
      r.final.tapes 144=arity ∧ r.final.heads 144=0 ∧
      (∀ j : Fin 5,r.final.tapes (j.natAdd 1659)=E j ∧ r.final.heads (j.natAdd 1659)=0)) :
    ∃ r,LocalBitMultitape.run (machine source k d first last) (u+1+v) (input source k d word W)=some r ∧
      r.steps ≤ u+1+v ∧ r.final.tapes (graphSlots source k d 1657)=payload ∧
      r.final.heads (graphSlots source k d 1657)=0 ∧ r.final.tapes (graphSlots source k d 144)=arity ∧
      r.final.heads (graphSlots source k d 144)=0 ∧
      (∀ j : Fin 5,r.final.tapes (graphSlots source k d (j.natAdd 1659))=E j ∧
        r.final.heads (graphSlots source k d (j.natAdd 1659))=0) ∧
      r.final.tapes (hierarchyPort source k d)=word ∧ r.final.heads (hierarchyPort source k d)=0 ∧
      r.final.tapes (wPort source k d)=List.replicate W true ∧ r.final.heads (wPort source k d)=0:=by
  obtain ⟨r0,h0,hs0,hheads,htapes,hinput,hihead,hrawW,hrawWh⟩:=hp
  obtain ⟨rg,hg,hgs,hgt,hgh,hw,hwh,hscalars⟩:=hq
  obtain ⟨r1,h1,_hcontrol,hsteps,hhead,htape,hkeep⟩:=RecoveryFocus.dock
    (graphSlots source k d) (graph_injective source k d) last v r0.final.heads r0.final.tapes _ hheads htapes rg hg
  have whole:=Composition.run_join first (RecoveryFocus.machine (graphSlots source k d) last) u v _ r0 r1 h0 h1
  have hhi : ∀ j,graphSlots source k d j≠hierarchyPort source k d:=by
    intro j
    rw [hierarchy_fresh]
    exact graph_fresh source k d j _
  have hwi : ∀ j,graphSlots source k d j≠wPort source k d:=by
    intro j
    rw [w_fresh]
    exact graph_fresh source k d j _
  refine ⟨Composition.joinedReceipt r0 r1,whole,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change r0.steps+1+r1.steps ≤ u+1+v
    omega
  · change r1.final.tapes (graphSlots source k d 1657)=payload
    exact (htape 1657).trans hgt
  · change r1.final.heads (graphSlots source k d 1657)=0
    exact (hhead 1657).trans hgh
  · change r1.final.tapes (graphSlots source k d 144)=arity
    exact (htape 144).trans hw
  · change r1.final.heads (graphSlots source k d 144)=0
    exact (hhead 144).trans hwh
  · intro j
    change r1.final.tapes (graphSlots source k d (j.natAdd 1659))=E j ∧
      r1.final.heads (graphSlots source k d (j.natAdd 1659))=0
    exact ⟨(htape _).trans (hscalars j).1,(hhead _).trans (hscalars j).2⟩
  · change r1.final.tapes (hierarchyPort source k d)=word
    exact (hkeep _ hhi).2.trans hinput
  · change r1.final.heads (hierarchyPort source k d)=0
    exact (hkeep _ hhi).1.trans hihead
  · change r1.final.tapes (wPort source k d)=List.replicate W true
    exact (hkeep _ hwi).2.trans hrawW
  · change r1.final.heads (wPort source k d)=0
    exact (hkeep _ hwi).1.trans hrawWh

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSourceGraph.Join
