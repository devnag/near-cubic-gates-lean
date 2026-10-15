import Proof.CaseAnalysis.CaseTwoTraversalFits
import Proof.PCP.PCPPRequestNodeSchema

/-! One fixed finite controller observes a tag, executes either the original
node row or output reference, and stops immediately after that reference.
Padding rows are never visited. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
open LocalBitMultitape RepairRepresentation OuterPCPRecovery RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def workers : Fin 3→(Σ s,Machine 30 s):=![⟨_,tag⟩,⟨_,node⟩,⟨_,field⟩]
noncomputable def sizes (j : Fin 3):=(workers j).1
noncomputable def programs (j : Fin 3) : Machine 30 (sizes j):=(workers j).2
def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 30→Bool) : Option (Fin 3):=
  if j=0 then some (if bits 25 then 2 else 1) else if j=1 then some 0 else none
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next
noncomputable def cfg (j : Fin 3) (H : Fin 30→ℕ) (A : Fin 30→List Bool):=
  controlConfig (RecoveryCalls.code sizes j) (⟨(programs j).start,H,A⟩ : Configuration 30 (sizes j))

theorem call (j l : Fin 3) (fuel : ℕ) (H H' : Fin 30→ℕ) (A A' : Fin 30→List Bool)
    (r : ExecutionReceipt 30 (sizes j))
    (hr : runFrom (programs j) fuel ⟨(programs j).start,H,A⟩=some r)
    (hh : r.final.heads=H') (ht : r.final.tapes=A')
    (hn : ∀ q,next j q (fun i=>readTapeBit (A' i) (H' i))=some l) :
    Timed machine (r.steps+1) (cfg j H A) (cfg l H' A') := by
  obtain ⟨hp,hhalt⟩:=prefix_of_run (programs j) fuel _ r hr
  have hbody:=RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have hscan : r.final.scanned=(fun i=>readTapeBit (A' i) (H' i)):=by
    funext i;simp only [Configuration.scanned,hh,ht]
  have hret:=RecoveryCalls.return_step sizes programs 0 next j l r.final hhalt (by rw [hscan];exact hn _)
  have he : RecoveryCalls.restarted (programs l) r.final.heads r.final.tapes=
      (⟨(programs l).start,H',A'⟩ : Configuration 30 (sizes l)):=by
    apply configuration_ext
    · rfl
    · exact hh
    · exact ht
  have hfull:=hbody.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) hret)
  rw [he] at hfull
  exact hfull

theorem stop (fuel : ℕ) (H H' : Fin 30→ℕ) (A A' : Fin 30→List Bool)
    (r : ExecutionReceipt 30 (sizes 2))
    (hr : runFrom (programs 2) fuel ⟨(programs 2).start,H,A⟩=some r)
    (hh : r.final.heads=H') (ht : r.final.tapes=A') :
    Timed machine (r.steps+1) (cfg 2 H A) (RecoveryCalls.stopped sizes H' A') := by
  obtain ⟨hp,hhalt⟩:=prefix_of_run (programs 2) fuel _ r hr
  have hbody:=RecoveryCalls.body_timed sizes programs 0 next 2 ⟨r.peakTapeCells,hp⟩
  have hret:=RecoveryCalls.stop_step sizes programs 0 next 2 r.final hhalt (by rfl)
  have he : RecoveryCalls.stopped sizes r.final.heads r.final.tapes=RecoveryCalls.stopped sizes H' A':=by
    rw [hh,ht]
  rw [he] at hret
  exact hbody.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) hret)

theorem flag_scan (C F count offset : ℕ) (source tagWord out : List Bool) (flag : Bool) :
    readTapeBit (data C F count source offset tagWord out flag 25) (heads out 25)=flag:=by
  change readTapeBit (ZeroPadding.pad 0 (ZeroPadding.pad C [flag])) 0=flag
  rw [ZeroPadding.pad_zero,ZeroPadding.read_pad]
  rfl

def rowBits {n : ℕ} (F : ℕ) (x : BooleanNode n):=
  orderedNatBits 6 (PCPPRequestNodeSchema.fields x 0)++
    orderedNatBits F (PCPPRequestNodeSchema.fields x 1)++orderedNatBits F (PCPPRequestNodeSchema.fields x 2)
def word {n : ℕ} (F : ℕ) (nodes : List (BooleanNode n)) (output : ℕ) (tail : List Bool):=
  nodes.flatMap (rowBits F)++orderedNatBits 6 5++orderedNatBits F output++tail
@[simp] theorem row_length {n : ℕ} (F : ℕ) (x : BooleanNode n) : (rowBits F x).length=6+2*F:=by
  simp [rowBits]
  omega

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
