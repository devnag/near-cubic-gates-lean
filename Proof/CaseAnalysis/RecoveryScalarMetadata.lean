import Proof.CaseAnalysis.RecoveryScalarLoad
import Proof.CaseAnalysis.RecoveryMetadataPrepare
import Proof.CaseAnalysis.RecoveryCountScalarDock

/-! Pay the five scalar loads, then the existing complete cold metadata
producer in the original count bank. All outside words and heads remain. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdScalarMetadata
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def sourceSlot (j : Fin 5) : Fin 158:=j.natAdd 153
def loadSlots : Fin 12→Fin 158:=Fin.addCases (m:=5) (n:=7) sourceSlot ![135,137,140,141,142,76,77]
def metadataSlots (j : Fin 37) : Fin 158:=(RecoveryBoundedCountScalarDock.slots j).castAdd 6
def values (q bound C Q clauses : ℕ) : Fin 5→ℕ:=![q,C,bound,Q,clauses]
def blank (B : ℕ) : Fin 37→List Bool:=
  Fin.addCases (m:=33) (n:=4) (fun _=>[]) ![[],[],List.replicate B true,List.replicate (B+1) false]
def loaded (A : Fin 158→List Bool) (q bound C Q clauses B : ℕ):=
  install loadSlots A (RecoveryBoundedColdScalarLoad.bank (values q bound C Q clauses) B 5)
def output (A : Fin 158→List Bool) (q bound C Q clauses B : ℕ):=
  install metadataSlots (loaded A q bound C Q clauses B) (RecoveryBoundedColdMetadata.output q bound C Q clauses B)
def first:=RecoveryFocus.machine loadSlots RecoveryBoundedColdScalarLoad.machine
def last:=RecoveryFocus.machine metadataSlots RecoveryBoundedColdMetadata.freshMachine
def machine:=Composition.machine first last
def budget (B : ℕ):=2048*(B+2)

theorem load_injective : Function.Injective loadSlots:=by decide
theorem metadata_injective : Function.Injective metadataSlots:=
  (Fin.castAdd_injective 152 6).comp RecoveryBoundedCountScalarDock.injective

theorem load_input (A : Fin 158→List Bool) (q bound C Q clauses B : ℕ)
    (hs : ∀ j,A (sourceSlot j)=List.replicate (values q bound C Q clauses j) true)
    (hm : ∀ j,A (metadataSlots j)=blank B j) (j : Fin 12) :
    A (loadSlots j)=RecoveryBoundedColdScalarLoad.input (values q bound C Q clauses) B j := by
  fin_cases j
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · exact hs 3
  · exact hs 4
  · exact hm 18
  · exact hm 20
  · exact hm 23
  · exact hm 24
  · exact hm 25
  · exact hm 35
  · exact hm 36

theorem loaded_input (A : Fin 158→List Bool) (q bound C Q clauses B : ℕ)
    (hm : ∀ j,A (metadataSlots j)=blank B j) (j : Fin 37) :
    loaded A q bound C Q clauses B (metadataSlots j)=
      RecoveryBoundedColdMetadata.freshInput q bound C Q clauses B j := by
  fin_cases j
  all_goals first
    | exact install_slot loadSlots load_injective A _ 5
    | exact install_slot loadSlots load_injective A _ 6
    | exact install_slot loadSlots load_injective A _ 7
    | exact install_slot loadSlots load_injective A _ 8
    | exact install_slot loadSlots load_injective A _ 9
    | exact install_slot loadSlots load_injective A _ 10
    | exact install_slot loadSlots load_injective A _ 11
    | (rw [show loaded A q bound C Q clauses B (metadataSlots _)=A (metadataSlots _) from
        install_other loadSlots A _ _ (by decide)]
       exact hm _)

theorem metadata_run (A : Fin 158→List Bool) (H : Fin 158→ℕ) (q bound C Q clauses B : ℕ)
    (hs : ∀ j,A (sourceSlot j)=List.replicate (values q bound C Q clauses j) true)
    (hm : ∀ j,A (metadataSlots j)=blank B j)
    (hhs : ∀ j,H (sourceSlot j)=0) (hhm : ∀ j,H (metadataSlots j)=0)
    (hn : ∀ j,values q bound C Q clauses j≤B) (hB : 2*(q+bound+1)+8≤B) :
    ∃ r,runFrom machine (budget B) ⟨machine.start,H,A⟩=some r ∧
      r.steps≤budget B ∧ r.final.heads=H ∧ r.final.tapes=output A q bound C Q clauses B := by
  have hloadHeads (j : Fin 12) : H (loadSlots j)=0 := by
    fin_cases j
    · exact hhs 0
    · exact hhs 1
    · exact hhs 2
    · exact hhs 3
    · exact hhs 4
    · exact hhm 18
    · exact hhm 20
    · exact hhm 23
    · exact hhm 24
    · exact hhm 25
    · exact hhm 35
    · exact hhm 36
  obtain ⟨a,ha,ah,aT,as⟩:=(RecoveryBoundedColdScalarLoad.load_ready (values q bound C Q clauses) B hn).focus_at
    loadSlots load_injective H A (load_input A q bound C Q clauses B hs hm) hloadHeads
  obtain ⟨b,hb,bh,bT,bs⟩:=(RecoveryBoundedColdMetadata.fresh_ready q bound C Q clauses B hB).focus_at
    metadataSlots metadata_injective H (loaded A q bound C Q clauses B)
    (loaded_input A q bound C Q clauses B hm) hhm
  have hb' : runFrom last (RecoveryBoundedColdMetadata.freshBudget B)
      (Composition.restart a.final last.start)=some b := by
    change runFrom last _ ⟨last.start,a.final.heads,a.final.tapes⟩=some b
    rw [ah,aT]
    exact hb
  have h:=Composition.run_join first last _ _ _ a b ha hb'
  have hu : RecoveryBoundedColdScalarLoad.budget B+1+RecoveryBoundedColdMetadata.freshBudget B≤budget B := by
    unfold RecoveryBoundedColdScalarLoad.budget RecoveryBoundedColdMetadata.freshBudget budget
    omega
  have hh:=runFrom_moreFuel machine _ (budget B-(RecoveryBoundedColdScalarLoad.budget B+1+
    RecoveryBoundedColdMetadata.freshBudget B)) _ _ h
  rw [Nat.add_sub_of_le hu] at hh
  exact ⟨Composition.joinedReceipt a b,hh,by change a.steps+1+b.steps≤budget B;omega,bh,bT⟩

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdScalarMetadata
