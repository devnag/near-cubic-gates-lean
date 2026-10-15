import Proof.PCP.PCPPNativeClauseQueryForward
import Proof.PCP.PCPPNativeDescriptorTail
import Proof.MachineModel.GeneratedAmplifierCopy

/-! Actual header, native-node bytes and padding/footer form the source
descriptor. The framed node stream is copied physically at the header's
live append cursor; actual domain and padded size remain available. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseDescriptor
open LocalBitMultitape RepairRepresentation PCPPNativeColdMetadata
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 2→Fin 65 := ![44,26]
def tailSlots (i : Fin 21) : Fin 65 :=
  if i=0 then 8 else if i=1 then 43 else if i=4 then 26 else i.natAdd 44
theorem tail_injective : Function.Injective tailSlots := by decide
def extra (index : ℕ) (bits : List Bool) (i : Fin 22) : List Bool :=
  if i=0 then List.replicate index true else if i=1 then frame bits else []
def input (width size index : ℕ) (bits : List Bool) : Fin 65→List Bool :=
  Fin.addCases (m:=43) (n:=22) (motive:=fun _=>List Bool) (PCPPNativeDescriptorEntry.input width size) (extra index bits)
noncomputable def first (minimum : ℕ) := TapeEmbedding.machine 22 (PCPPNativeDescriptorEntry.machine minimum)
noncomputable def second := RecoveryFocus.machine copySlots GeneratedAmplifier.Copy.machine
noncomputable def last := RecoveryFocus.machine tailSlots PCPPNativeDescriptorTail.machine
noncomputable def machine (minimum : ℕ) := Composition.machine (Composition.machine (first minimum) second) last
def emitted (minimum width size index : ℕ) (bits : List Bool) :=
  natWord (domain minimum width)++natWord (padded minimum width size)++bits++
    PCPPNativeDescriptorTail.emitted (padding minimum width size) index
def budget (minimum width size index : ℕ) (bits : List Bool) :=
  PCPPNativeDescriptorEntry.budget minimum width size+1+(2*bits.length+1)+1+
    PCPPNativeDescriptorTail.budget (padding minimum width size) index

theorem assemble_run (minimum width size index : ℕ) (bits : List Bool) : ∃ result,
    run (machine minimum) (budget minimum width size index bits) (input width size index bits)=some result ∧
    result.steps≤budget minimum width size index bits ∧
    result.final.tapes 26=emitted minimum width size index bits ∧
    result.final.heads 26=(emitted minimum width size index bits).length ∧
    result.final.heads 10=0 ∧ result.final.tapes 10=List.replicate (domain minimum width) true ∧
    result.final.heads 27=0 ∧ result.final.tapes 27=List.replicate (padded minimum width size) true := by
  obtain ⟨a,ar,as,atapes,ah,ad,adh,az,azh,ap,aph,_,_,_,_⟩:=PCPPNativeDescriptorEntry.entry_run minimum width size
  let lifted:=TapeEmbedding.receipt (fun _ : Fin 22=>0) (extra index bits) a
  have firstRun:=TapeEmbedding.run_embed (PCPPNativeDescriptorEntry.machine minimum) (fun _ : Fin 22=>0)
    (extra index bits) _ _ a ar
  let header:=natWord (domain minimum width)++natWord (padded minimum width size)
  obtain ⟨b,br,bf,bs⟩:=GeneratedAmplifier.Copy.copy_run [] bits [] header
  simp only [List.nil_append,List.append_nil,List.length_nil] at br bf
  obtain ⟨c,cr,_,cs,ch,ct,keep⟩:=RecoveryFocus.dock copySlots (by decide) GeneratedAmplifier.Copy.machine _
    lifted.final.heads lifted.final.tapes (GeneratedAmplifier.Copy.cfg 0 (frame bits) 0 header)
    (by intro i; fin_cases i; rfl; exact ah)
    (by intro i; fin_cases i; rfl; exact atapes) b br
  have c26h : c.final.heads 26=(header++bits).length := (ch 1).trans (by rw [bf]; rfl)
  have c26t : c.final.tapes 26=header++bits := (ct 1).trans (by rw [bf]; rfl)
  obtain ⟨d,dr,ds,dt,dh,_,_,_,_⟩:=PCPPNativeDescriptorTail.append_run (padding minimum width size) index (header++bits)
  have tail_input (j : Fin 21) :
      c.final.heads (tailSlots j)=PCPPNativeDescriptorTail.heads (header++bits) j ∧
      c.final.tapes (tailSlots j)=PCPPNativeDescriptorTail.data (padding minimum width size) index (header++bits) j := by
    by_cases j0 : j=0
    · subst j
      exact ⟨((keep 8 (by decide)).1).trans aph,((keep 8 (by decide)).2).trans ap⟩
    by_cases j1 : j=1
    · subst j
      exact keep 43 (by decide)
    by_cases j4 : j=4
    · subst j
      exact ⟨c26h,c26t⟩
    have jv0 : j.val≠0:=fun h=>j0 (Fin.ext h)
    have away : ∀ i,copySlots i≠tailSlots j := by
      intro i hi
      have hv:=congrArg Fin.val hi
      fin_cases i
      · norm_num [copySlots,tailSlots,j0,j1,j4] at hv
      · norm_num [copySlots,tailSlots,j0,j1,j4] at hv
        omega
    have hk:=keep (tailSlots j) away
    let k : Fin 22:=⟨j.val+1,by omega⟩
    have high : tailSlots j=k.natAdd 43 := by
      apply Fin.ext
      simp only [tailSlots,j0,j1,j4,ite_false,Fin.val_natAdd,k]
      omega
    have highH : lifted.final.heads (tailSlots j)=0 := by
      rw [high]
      exact TapeEmbedding.receipt_heads_new _ _ _ _
    have highT : lifted.final.tapes (tailSlots j)=[] := by
      rw [high]
      change (TapeEmbedding.receipt (fun _ : Fin 22=>0) (extra index bits) a).final.tapes (k.natAdd 43)=[]
      rw [TapeEmbedding.receipt_tapes_new]
      simp [extra,k,Fin.ext_iff,jv0]
    simpa only [PCPPNativeDescriptorTail.heads,PCPPNativeDescriptorTail.data,j0,j1,j4,ite_false] using
      And.intro (hk.1.trans highH) (hk.2.trans highT)
  obtain ⟨e,er,_,es,eh,et,other⟩:=RecoveryFocus.dock tailSlots tail_injective PCPPNativeDescriptorTail.machine _
    c.final.heads c.final.tapes _ (fun j=>(tail_input j).1) (fun j=>(tail_input j).2) d dr
  have ab:=Composition.run_join (first minimum) second _ _ _ lifted c firstRun cr
  have joined:=Composition.run_join (Composition.machine (first minimum) second) last _ _ _
    (Composition.joinedReceipt lifted c) e ab er
  have init : Composition.leftConfig _ (Composition.leftConfig _
      (TapeEmbedding.config (fun _ : Fin 22=>0) (extra index bits)
        (initialConfiguration (PCPPNativeDescriptorEntry.machine minimum) (PCPPNativeDescriptorEntry.input width size))))=
      initialConfiguration (machine minimum) (input width size index bits) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=43) (n:=22) (fun _=>?_) (fun _=>?_) i <;>
        simp only [Composition.leftConfig,TapeEmbedding.config,initialConfiguration,Fin.addCases_left,Fin.addCases_right]
    · rfl
  rw [init] at joined
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt lifted c) e,joined,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+c.steps+1+e.steps≤budget minimum width size index bits
    rw [cs,es,bs]
    unfold budget
    omega
  · exact (et 4).trans dt
  · exact (eh 4).trans dh
  · exact ((other 10 (by decide)).1).trans (((keep 10 (by decide)).1).trans adh)
  · exact ((other 10 (by decide)).2).trans (((keep 10 (by decide)).2).trans ad)
  · exact ((other 27 (by decide)).1).trans (((keep 27 (by decide)).1).trans azh)
  · exact ((other 27 (by decide)).2).trans (((keep 27 (by decide)).2).trans az)

end NearCubicWires.RepairOrdinary.PCPPNativeClauseDescriptor
