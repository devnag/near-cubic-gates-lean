import Proof.Hierarchy.HierarchyStreamScalars
import Proof.Amplification.RecoveryFocusDock

/-! The original padded hierarchy source and normalized streams dock directly
at the existing graph ports. All other source work is fresh beyond tape157. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdHierarchyDock
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def tapes (k : ℕ):=158+HierarchyStreams.tapes source k
def old (k : ℕ) (i : Fin 158) : Fin (tapes source k):=i.castAdd (HierarchyStreams.tapes source k)
def fresh (k : ℕ) (i : Fin (HierarchyStreams.tapes source k)) : Fin (tapes source k):=i.natAdd 158
def slots (k : ℕ) (i : Fin (HierarchyStreams.tapes source k)) : Fin (tapes source k):=
  if i=HierarchyStreams.slots source k 38 then old source k 70
  else if i=HierarchyStreams.slots source k 29 then old source k 106
  else fresh source k i
def input (k : ℕ) (A : Fin 158→List Bool) (word : List Bool) : Fin (tapes source k)→List Bool:=
  Fin.addCases A (SourceHandoff.sourceTapes word)
def heads (k : ℕ) (H : Fin 158→ℕ) : Fin (tapes source k)→ℕ:=Fin.addCases H (fun _=>0)
def machine (k CH Cpad : ℕ) (code : List Bool):=
  RecoveryFocus.machine (slots source k) (HierarchyStreams.machine source k CH Cpad code)

theorem stream_distinct (k : ℕ) :
    HierarchyStreams.slots source k 29≠HierarchyStreams.slots source k 38:=by
  intro he
  have hh:=HierarchyStreams.slots_injective source k he
  exact (by decide : (29 : Fin 48)≠38) hh

theorem slots_injective (k : ℕ) : Function.Injective (slots source k):=by
  intro i j he
  have hv:=congrArg Fin.val he
  apply Fin.ext
  dsimp only [slots,old,fresh] at hv
  split_ifs at hv <;>dsimp at hv <;>subst_vars <;>omega

theorem clause_slot (k : ℕ) : slots source k (HierarchyStreams.slots source k 38)=old source k 70:=by
  simp only [slots,if_pos]
theorem query_slot (k : ℕ) : slots source k (HierarchyStreams.slots source k 29)=old source k 106:=by
  simp only [slots,if_neg (stream_distinct source k),if_pos]

theorem slots_other (k : ℕ) (i : Fin 158) (h70 : i≠70) (h106 : i≠106) :
    ∀ j,slots source k j≠old source k i:=by
  intro j he
  have hi:=i.isLt
  have hv:=congrArg Fin.val he
  have hi70 : i.val≠70:=fun h=>h70 (Fin.ext h)
  have hi106 : i.val≠106:=fun h=>h106 (Fin.ext h)
  dsimp only [slots,old,fresh] at hv
  split_ifs at hv <;>dsimp at hv <;>omega

theorem input_projection (k : ℕ) (A : Fin 158→List Bool) (word : List Bool)
    (h70 : A 70=[]) (h106 : A 106=[]) (j : Fin (HierarchyStreams.tapes source k)) :
    input source k A word (slots source k j)=SourceHandoff.sourceTapes word j:=by
  by_cases hc : j=HierarchyStreams.slots source k 38
  · subst j
    rw [clause_slot]
    simp only [input,old,Fin.addCases_left]
    simpa [SourceHandoff.sourceTapes,HierarchyStreams.slots] using h70
  by_cases hq : j=HierarchyStreams.slots source k 29
  · subst j
    rw [query_slot]
    simp only [input,old,Fin.addCases_left]
    simpa [SourceHandoff.sourceTapes,HierarchyStreams.slots] using h106
  · simp only [slots,if_neg hc,if_neg hq,input,fresh,Fin.addCases_right]

theorem heads_projection (k : ℕ) (H : Fin 158→ℕ) (h70 : H 70=0) (h106 : H 106=0)
    (j : Fin (HierarchyStreams.tapes source k)) : heads source k H (slots source k j)=0:=by
  by_cases hc : j=HierarchyStreams.slots source k 38
  · subst j
    rw [clause_slot]
    exact (Fin.addCases_left (motive:=fun _ : Fin (tapes source k)=>ℕ) (70 : Fin 158)).trans h70
  by_cases hq : j=HierarchyStreams.slots source k 29
  · subst j
    rw [query_slot]
    exact (Fin.addCases_left (motive:=fun _ : Fin (tapes source k)=>ℕ) (106 : Fin 158)).trans h106
  · simp only [slots,if_neg hc,if_neg hq,heads,fresh,Fin.addCases_right]

def project {k s : ℕ} (c : Configuration (tapes source k) s) :
    Configuration (HierarchyStreams.tapes source k) s:=
  ⟨c.control,c.heads∘slots source k,c.tapes∘slots source k⟩
def inputPort (k : ℕ):=slots source k (HierarchyStreams.old source k
  ⟨0,by dsimp [HierarchyStreams.base,HierarchySourceInput.tapes];omega⟩)
def rBitsPort (k : ℕ):=slots source k (HierarchyStreams.old source k (HierarchyStreams.bitsR source k))
def qBitsPort (k : ℕ):=slots source k (HierarchyStreams.old source k (HierarchyStreams.bitsQ source k))
def queryCountPort (k : ℕ):=slots source k (HierarchyStreams.slots source k 25)
def clauseCountPort (k : ℕ):=slots source k (HierarchyStreams.slots source k 46)

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdHierarchyDock
