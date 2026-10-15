import Proof.Amplification.RecoveryTseitinNativeTagDock

/-! Paid native tag dispatch reaches the actual original node-clause branch
and retains all kernel heads and tapes supplied by the physical preparer. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.NodeController
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nodeStage (k : Fin 6) : Fin 8 := k.natAdd 2
def tagKind (tag : Fin 5) : Fin 6 := ⟨tag.val+1,by have ht:=tag.isLt; omega⟩

theorem nonconstant_dispatch {z : Nat} (tag : Fin 5) (ht : 0 < tag.val) (ambient : Configuration 1335 z)
    (hh : ambient.heads 1072=1) (hd : ambient.tapes 1072=UnaryTemplate.tape tag.val) :
    ∃ head,Timed machine (tag.val+2) (boundary 0 ambient.heads ambient.tapes)
      (boundary (nodeStage (tagKind tag)) head ambient.tapes) ∧
      (∀ flag i,head (kernelSlots flag i)=ambient.heads (kernelSlots flag i)) ∧
      (∀ i,i≠1072 → i≠1082 → head i=ambient.heads i) := by
  obtain ⟨r,hr,rc,rs,rt,rkeep⟩:=tag_run false tag ambient hh hd
  have hn : next 0 r.final.control r.final.scanned=some (nodeStage (tagKind tag)) := by
    fin_cases tag
    · norm_num at ht
    all_goals simp [next,rc,nodeStage,tagKind]
  have h:=call_run 0 (nodeStage (tagKind tag)) _ ambient.heads ambient.tapes r hr hn
  rw [rs,rt] at h
  have he : tag.val+1+1=tag.val+2 := by omega
  rw [he] at h
  exact ⟨r.final.heads,h,(fun flag i=>rkeep _ (kernel_tag_disjoint flag false i)),fun i hi _=>rkeep i hi⟩

theorem constant_dispatch {z : Nat} (b : Bool) (ambient : Configuration 1335 z)
    (hh : ambient.heads 1072=1) (hd : ambient.tapes 1072=UnaryTemplate.tape 0)
    (hv : ambient.heads 1082=1) (dv : ambient.tapes 1082=UnaryTemplate.tape b.toNat) :
    ∃ head,Timed machine (b.toNat+4) (boundary 0 ambient.heads ambient.tapes)
      (boundary (nodeStage (if b then 1 else 0)) head ambient.tapes) ∧
      (∀ flag i,head (kernelSlots flag i)=ambient.heads (kernelSlots flag i)) ∧
      (∀ i,i≠1072 → i≠1082 → head i=ambient.heads i) := by
  obtain ⟨first,hf,fc,fs,ft,fkeep⟩:=tag_run false 0 ambient hh hd
  have hvalue : first.final.heads 1082=1 := (fkeep 1082 (by decide)).trans hv
  have dvalue : first.final.tapes 1082=UnaryTemplate.tape b.toNat := by rw [ft]; exact dv
  let v : Fin 5 := ⟨b.toNat,by cases b <;> decide⟩
  obtain ⟨last,hl,lc,ls,lt,lkeep⟩:=tag_run true v first.final hvalue dvalue
  have hn0 : next 0 first.final.control first.final.scanned=some 1 := parsed_next 0 _ _ fc
  have hn1 : next 1 last.final.control last.final.scanned=some (nodeStage (if b then 1 else 0)) := by
    have lc' : last.final.control.val=b.toNat+5 := lc
    have h:=const_next b last.final.control last.final.scanned lc'
    cases b <;> simpa [nodeStage] using h
  have h0:=call_run 0 1 _ ambient.heads ambient.tapes first hf hn0
  have h1:=call_run 1 (nodeStage (if b then 1 else 0)) _ first.final.heads first.final.tapes last hl hn1
  have h:=h0.trans h1
  change Timed machine (first.steps+1+(last.steps+1)) (boundary 0 ambient.heads ambient.tapes)
    (boundary (nodeStage (if b then 1 else 0)) last.final.heads last.final.tapes) at h
  rw [fs,ls,lt,ft] at h
  have he : ((0 : Fin 5).val+1+1)+(v.val+1+1)=b.toNat+4 := by dsimp [v]; omega
  rw [he] at h
  exact ⟨last.final.heads,h,(fun flag i=>(lkeep _ (kernel_tag_disjoint flag true i)).trans
    (fkeep _ (kernel_tag_disjoint flag false i))),fun i hi hv=>(lkeep i hv).trans (fkeep i hi)⟩

end NearCubicWires.RepairSource.RecoveryTseitinNative.NodeController
