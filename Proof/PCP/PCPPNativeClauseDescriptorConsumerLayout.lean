import Proof.PCP.PCPPNativeClauseDescriptorTyped
import Proof.PCP.PCPPNativeClauseDescriptorForward
import Proof.PCP.PCPPNativeSource

/-! Dock the actual original node producer through paid node framing into
its faithful typed descriptor assembler. The retained scalar ports belong
to that producer; every descriptor scratch tape starts empty. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseDescriptorConsumer
open LocalBitMultitape SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (t : ℕ) := ((t+2)+2)+65
def oldSlot {t : ℕ} (i : Fin t) : Fin (tapes t) := (PCPPNativeFrame.old i).castAdd 65
def frameSlot (t : ℕ) : Fin (tapes t) := ((0 : Fin 2).natAdd (t+2)).castAdd 65
def slots {t : ℕ} (width size index : Fin t) (j : Fin 65) : Fin (tapes t) :=
  if j=0 then oldSlot width else if j=1 then oldSlot size else if j=43 then oldSlot index
  else if j=44 then frameSlot t else j.natAdd ((t+2)+2)
theorem slots_injective {t : ℕ} (width size index : Fin t)
    (ws : width≠size) (wi : width≠index) (si : size≠index) : Function.Injective (slots width size index) := by
  intro i j he
  apply Fin.ext
  have hv:=congrArg Fin.val he
  have hw:=width.isLt
  have hs:=size.isLt
  have hi:=index.isLt
  have hws : width.val≠size.val:=fun h=>ws (Fin.ext h)
  have hwi : width.val≠index.val:=fun h=>wi (Fin.ext h)
  have hsi : size.val≠index.val:=fun h=>si (Fin.ext h)
  dsimp only [slots,oldSlot,frameSlot,PCPPNativeFrame.old] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;> simp_all only [Fin.ext_iff] <;> omega

def input {t : ℕ} (native : Fin t→List Bool) : Fin (tapes t)→List Bool :=
  Fin.addCases (m:=(t+2)+2) (n:=65) (motive:=fun _=>List Bool) (AppendOutputFrame.input native) (fun _=>[])
noncomputable def first {t s : ℕ} (p : Machine t s) (target : Fin t) :=
  TapeEmbedding.machine 65 (AppendOutputFrame.machine p target)
noncomputable def last (a : PointwisePCPPAlgorithm) {t : ℕ} (width size index : Fin t) :=
  RecoveryFocus.machine (slots width size index) (PCPPNativeClauseDescriptor.machine a.minimumArity)
noncomputable def machine (a : PointwisePCPPAlgorithm) {t s : ℕ} (p : Machine t s)
    (target width size index : Fin t) := Composition.machine (first p target) (last a width size index)

theorem descriptor_input {t : ℕ} (width size index : Fin t) (n sz idx : ℕ) (bits : List Bool)
    (data : Fin (tapes t)→List Bool)
    (hw : data (oldSlot width)=List.replicate n true)
    (hs : data (oldSlot size)=List.replicate sz true)
    (hi : data (oldSlot index)=List.replicate idx true)
    (hf : data (frameSlot t)=frame bits)
    (hn : ∀ j : Fin 65,data (j.natAdd ((t+2)+2))=[]) :
    ∀ j,data (slots width size index j)=PCPPNativeClauseDescriptor.input n sz idx bits j := by
  intro j
  fin_cases j <;> simp [slots,PCPPNativeClauseDescriptor.input,hw,hs,hi,hf,hn] <;> rfl

end NearCubicWires.RepairOrdinary.PCPPNativeClauseDescriptorConsumer
