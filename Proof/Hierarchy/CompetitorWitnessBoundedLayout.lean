import Proof.Hierarchy.CompetitorWitnessCap

/-! The cap and canonical-header consumers share their actual input/witness
tapes. The two cap outputs sit outside all 148 header tapes. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessBounded
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4→Fin 150 := ![0,1,148,149]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def cap := RecoveryFocus.machine slots CompetitorWitnessCap.guard
noncomputable def header := TapeEmbedding.machine 2 CompetitorWitnessHeader.machine
def input (x w : List Bool) : Fin 150→List Bool :=
  Fin.addCases (m:=148) (n:=2) (motive:=fun _=>List Bool) (CompetitorWitnessHeader.input x w) (fun _=>[])
def bank (core : Fin 148→List Bool) (flag : Bool) (scratch : ℕ) : Fin 150→List Bool :=
  Fin.addCases (m:=148) (n:=2) (motive:=fun _=>List Bool) core ![[flag],List.replicate scratch false]
def capped (x w : List Bool) (scratch : ℕ) :=
  bank (CompetitorWitnessHeader.input x w) (decide (16*w.length≤x.length)) scratch

theorem input_slots (x w : List Bool) (j : Fin 4) :
    input x w (slots j)=CompetitorWitnessCap.input x w j := by
  fin_cases j
  · change CompetitorWitnessHeader.input x w 0=_
    rw [CompetitorWitnessHeader.input_eq]; rfl
  · change CompetitorWitnessHeader.input x w 1=_
    rw [CompetitorWitnessHeader.input_eq]; rfl
  · rfl
  · rfl

theorem capped_slots (x w : List Bool) (scratch : ℕ) (j : Fin 4) :
    capped x w scratch (slots j)=CompetitorWitnessCap.output x w scratch j := by
  fin_cases j
  · change CompetitorWitnessHeader.input x w 0=_
    rw [CompetitorWitnessHeader.input_eq]; rfl
  · change CompetitorWitnessHeader.input x w 1=_
    rw [CompetitorWitnessHeader.input_eq]; rfl
  · rfl
  · rfl

theorem cap_install (x w : List Bool) (scratch : ℕ) :
    install slots (input x w) (CompetitorWitnessCap.output x w scratch)=capped x w scratch := by
  funext i
  by_cases hi : ∃ j,slots j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [install_slot slots slots_injective]
    exact (capped_slots x w scratch j).symm
  · rw [install_other slots _ _ _ (by intro j hj; exact hi ⟨j,hj⟩)]
    refine Fin.addCases (m:=148) (n:=2) (motive:=fun k=>(¬∃ j,slots j=k) →
      input x w k=capped x w scratch k) ?_ ?_ i hi
    · intro j _
      simp only [input,capped,bank,Fin.addCases_left]
    · intro j hj
      fin_cases j
      · exact False.elim (hj ⟨2,rfl⟩)
      · exact False.elim (hj ⟨3,rfl⟩)

theorem cap_ready (x w : List Bool) :
    ∃ scratch,scratch≤3*x.length+2 ∧ ReadyRun cap (2*scratch+2) (input x w) (capped x w scratch) := by
  obtain ⟨scratch,hs,h⟩ := CompetitorWitnessCap.cap_ready x w
  have hp := h.focus slots slots_injective (input x w) (input_slots x w)
  rw [cap_install] at hp
  exact ⟨scratch,hs,hp⟩

theorem header_ready (x w : List Bool) (scratch : ℕ) :
    ReadyRun header (CompetitorWitnessHeader.time w) (capped x w scratch)
      (bank (CompetitorWitnessHeader.output x w) (decide (16*w.length≤x.length)) scratch) :=
  (CompetitorWitnessHeader.header_ready x w).embed ![[decide (16*w.length≤x.length)],List.replicate scratch false]

theorem input_eq (x w : List Bool) (i : Fin 150) : input x w i=
    if i.val=0 then frame x else if i.val=1 then frame w else [] := by
  refine Fin.addCases (m:=148) (n:=2) ?_ ?_ i
  · intro j
    rw [input,Fin.addCases_left,CompetitorWitnessHeader.input_eq]
    rfl
  · intro j
    rw [input,Fin.addCases_right]
    have h0 : (j.natAdd 148).val≠0 := by simp only [Fin.val_natAdd];omega
    have h1 : (j.natAdd 148).val≠1 := by simp only [Fin.val_natAdd];omega
    rw [if_neg h0,if_neg h1]

end NearCubicWires.RepairOrdinary.CompetitorWitnessBounded
