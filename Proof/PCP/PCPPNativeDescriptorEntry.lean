import Proof.PCP.PCPPNativeHeader

/-! A cold native descriptor entry computes and prints both header fields
from the actual retained width and emitted-node count. Exact padding and
raw source/cache parameters survive the header conversion. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeDescriptorEntry
open LocalBitMultitape RecoveryRootRound PCPPNativeColdMetadata RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def metadataSlots (i : Fin 10) : Fin 43 := i.castAdd 33
def headerSlots (i : Fin 35) : Fin 43 :=
  if i=0 then 4 else if i=1 then 7 else ⟨i.val+8,by omega⟩
theorem metadata_injective : Function.Injective metadataSlots := by decide
theorem header_injective : Function.Injective headerSlots := by decide
def input (width size : ℕ) (i : Fin 43) : List Bool :=
  if i=0 then List.replicate width true else if i=1 then List.replicate size true else []
def prepared (minimum width size : ℕ) := install metadataSlots (input width size)
  (PCPPNativeColdMetadata.output minimum width size)
def first (minimum : ℕ) := RecoveryFocus.machine metadataSlots (PCPPNativeColdMetadata.machine minimum)
def last := RecoveryFocus.machine headerSlots PCPPNativeColdHeader.machine
def machine (minimum : ℕ) := Composition.machine (first minimum) last
def budget (minimum width size : ℕ) := PCPPNativeColdMetadata.budget minimum width size+1+
  PCPPNativeColdHeader.budget (domain minimum width) (padded minimum width size)

theorem metadata_input (width size : ℕ) (i : Fin 10) :
    input width size (metadataSlots i)=PCPPNativeColdMetadata.input width size i := by
  fin_cases i <;> rfl
theorem prepared_local (minimum width size : ℕ) (i : Fin 10) :
    prepared minimum width size (metadataSlots i)=PCPPNativeColdMetadata.output minimum width size i :=
  install_slot _ metadata_injective _ _ _
theorem prepared_fresh (minimum width size : ℕ) (i : Fin 43) (hi : 10 ≤ i.val) :
    prepared minimum width size i=[] := by
  rw [prepared,install_other _ _ _ _ (by
    intro j he
    have hj := j.isLt
    have h := congrArg Fin.val he
    change j.val=i.val at h
    omega)]
  have h0 : i≠0 := fun h => by subst i; contradiction
  have h1 : i≠1 := fun h => by subst i; contradiction
  simp [input,h0,h1]
theorem header_input (minimum width size : ℕ) (i : Fin 35) :
    prepared minimum width size (headerSlots i)=
      PCPPNativeColdHeader.data (domain minimum width) (padded minimum width size) [] i := by
  obtain ⟨_,_,hd,hs,_⟩ := PCPPNativeColdMetadata.fields minimum width size
  by_cases h0 : i=0
  · subst i
    exact (prepared_local minimum width size 4).trans hd
  by_cases h1 : i=1
  · subst i
    exact (prepared_local minimum width size 7).trans hs
  have hi : 10 ≤ (headerSlots i).val := by
    have hv0 : i.val≠0 := fun h => h0 (Fin.ext h)
    have hv1 : i.val≠1 := fun h => h1 (Fin.ext h)
    simp only [headerSlots,h0,h1,if_false,Fin.val_mk]
    omega
  rw [prepared_fresh _ _ _ _ hi]
  simp [PCPPNativeColdHeader.data,h0,h1]

theorem entry_run (minimum width size : ℕ) :
    ∃ result,run (machine minimum) (budget minimum width size) (input width size)=some result ∧
      result.steps ≤ budget minimum width size ∧
      result.final.tapes 26=natWord (domain minimum width)++natWord (padded minimum width size) ∧
      result.final.heads 26=(natWord (domain minimum width)++natWord (padded minimum width size)).length ∧
      result.final.tapes 10=List.replicate (domain minimum width) true ∧ result.final.heads 10=0 ∧
      result.final.tapes 27=List.replicate (padded minimum width size) true ∧ result.final.heads 27=0 ∧
      result.final.tapes 8=List.replicate (padding minimum width size) true ∧ result.final.heads 8=0 ∧
      result.final.tapes 0=List.replicate width true ∧ result.final.heads 0=0 ∧
      result.final.tapes 1=List.replicate size true ∧ result.final.heads 1=0 := by
  obtain ⟨a,ha,atapes,ah,as⟩ := (PCPPNativeColdMetadata.ready minimum width size).focus
    metadataSlots metadata_injective (input width size) (metadata_input width size)
  obtain ⟨base,hbase,baseSteps,bo,bh,bd,bdh,bs,bsh⟩ := PCPPNativeColdHeader.append_run
    (domain minimum width) (padded minimum width size) []
  obtain ⟨b,hb,_,bst,bheads,btapes,bkeep⟩ := RecoveryFocus.dock headerSlots header_injective
    PCPPNativeColdHeader.machine _ a.final.heads a.final.tapes _
    (by intro j; rw [ah]; simp [PCPPNativeColdHeader.entry,PCPPNativeColdHeader.heads])
    (by intro j; rw [atapes]; exact header_input minimum width size j) base hbase
  have keep (i : Fin 10) (hi : i≠4 ∧ i≠7) :
      b.final.tapes (metadataSlots i)=PCPPNativeColdMetadata.output minimum width size i ∧
      b.final.heads (metadataSlots i)=0 := by
    have away : ∀ j,headerSlots j≠metadataSlots i := by
      intro j he
      have h := congrArg Fin.val he
      have hi4 : i.val≠4 := fun h => hi.1 (Fin.ext h)
      have hi7 : i.val≠7 := fun h => hi.2 (Fin.ext h)
      have hij := i.isLt
      dsimp [headerSlots,metadataSlots] at h
      split_ifs at h <;> dsimp at h <;> omega
    have hk := bkeep (metadataSlots i) away
    refine ⟨hk.2.trans ?_,hk.1.trans (ah _)⟩
    rw [atapes]
    exact prepared_local minimum width size i
  obtain ⟨hw,hn,_,_,hp⟩ := PCPPNativeColdMetadata.fields minimum width size
  have joined := Composition.run_join (first minimum) last _ _ _ a b ha hb
  refine ⟨Composition.joinedReceipt a b,joined,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ _
    unfold budget
    omega
  · exact (btapes 18).trans (by simpa only [PCPPNativeColdHeader.emitted,List.nil_append] using bo)
  · exact (bheads 18).trans (by simpa only [PCPPNativeColdHeader.emitted,List.nil_append] using bh)
  · exact (btapes 2).trans bd
  · exact (bheads 2).trans bdh
  · exact (btapes 19).trans bs
  · exact (bheads 19).trans bsh
  · exact ((keep 8 (by decide)).1).trans hp
  · exact (keep 8 (by decide)).2
  · exact ((keep 0 (by decide)).1).trans hw
  · exact (keep 0 (by decide)).2
  · exact ((keep 1 (by decide)).1).trans hn
  · exact (keep 1 (by decide)).2

end
end NearCubicWires.RepairOrdinary.PCPPNativeDescriptorEntry
