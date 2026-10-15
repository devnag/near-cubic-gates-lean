import Proof.PCP.PCPPNativeFrame
import Proof.PCP.PCPPSourceCacheBounds

/-! Static docking of the actual framed native descriptor and its retained
raw size/domain into the one-source shared-cache producer. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeSource
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (a : PointwisePCPPAlgorithm) (t : ℕ) := ((t+2)+2)+PCPPSourceCache.tapes a
def oldSlot (a : PointwisePCPPAlgorithm) {t : ℕ} (i : Fin t) : Fin (tapes a t) :=
  (PCPPNativeFrame.old i).castAdd (PCPPSourceCache.tapes a)
def frameSlot (a : PointwisePCPPAlgorithm) (t : ℕ) : Fin (tapes a t) :=
  ((0 : Fin 2).natAdd (t+2)).castAdd (PCPPSourceCache.tapes a)
def sourceSlots (a : PointwisePCPPAlgorithm) {t : ℕ} (size domain : Fin t)
    (j : Fin (PCPPSourceCache.tapes a)) : Fin (tapes a t) :=
  if j.val=PCPPSourceCache.coldTapes a then frameSlot a t
  else if j.val=21 then oldSlot a size else if j.val=19 then oldSlot a domain
  else j.natAdd ((t+2)+2)

theorem source_injective (a : PointwisePCPPAlgorithm) {t : ℕ} (size domain : Fin t)
    (distinct : size≠domain) : Function.Injective (sourceSlots a size domain) := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  have hs : size.val<t := size.isLt
  have hd : domain.val<t := domain.isLt
  have hsd : size.val≠domain.val := fun h => distinct (Fin.ext h)
  have hc := PCPPSourceCache.cold_lower a
  dsimp only [sourceSlots,frameSlot,oldSlot,PCPPNativeFrame.old] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;> omega

def input (a : PointwisePCPPAlgorithm) {t : ℕ} (native : Fin t → List Bool) : Fin (tapes a t) → List Bool :=
  Fin.addCases (m := (t+2)+2) (n := PCPPSourceCache.tapes a) (motive := fun _ => List Bool)
    (AppendOutputFrame.input native) (fun _ => [])
noncomputable def first (a : PointwisePCPPAlgorithm) {t s : ℕ} (p : Machine t s) (target : Fin t) :=
  TapeEmbedding.machine (PCPPSourceCache.tapes a) (AppendOutputFrame.machine p target)
noncomputable def last (a : PointwisePCPPAlgorithm) {t : ℕ} (size domain : Fin t) :=
  RecoveryFocus.machine (sourceSlots a size domain) (PCPPSourceCache.machine a)
noncomputable def machine (a : PointwisePCPPAlgorithm) {t s : ℕ} (p : Machine t s)
    (target size domain : Fin t) := Composition.machine (first a p target) (last a size domain)

theorem source_input (a : PointwisePCPPAlgorithm) {t : ℕ} (size domain : Fin t)
    (request : PCPPRequest a.minimumArity) (data : Fin (tapes a t) → List Bool)
    (hf : data (frameSlot a t)=frame (PCPPNative.descriptor request.circuit))
    (hs : data (oldSlot a size)=List.replicate request.circuit.size true)
    (hd : data (oldSlot a domain)=List.replicate request.arity true)
    (hn : ∀ i : Fin (PCPPSourceCache.tapes a),data (i.natAdd ((t+2)+2))=[]) :
    ∀ j,data (sourceSlots a size domain j)=PCPPSourceCache.input a request j := by
  intro j
  have hc := PCPPSourceCache.cold_lower a
  by_cases hj : j.val=PCPPSourceCache.coldTapes a
  · simp only [sourceSlots,PCPPSourceCache.input,hj,ite_true,hf]
    rfl
  · simp only [sourceSlots,PCPPSourceCache.input,if_neg hj]
    by_cases hs21 : j.val=21
    · simp only [if_pos hs21,hs]
    · simp only [if_neg hs21]
      by_cases hd19 : j.val=19
      · simp only [if_pos hd19,hd]
      · simp only [if_neg hd19,hn]

end NearCubicWires.RepairOrdinary.PCPPNativeSource
