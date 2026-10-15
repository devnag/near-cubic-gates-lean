import Proof.CaseAnalysis.WitnessSupportDock
import Proof.CaseAnalysis.WitnessFamilyCallDock

/-! Physical docking for the pinned3244-tape family supplier. This lemma
transports an actual supplier receipt; it does not assume that supplier exists. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySupportCall
open LocalBitMultitape FamilySparse
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def slots {t : ℕ} (fields : Fin 104→Fin t):=SupportDock.slots (FamilyCold.Call.slots fields)
def old {t : ℕ} (i : Fin t):=(FamilyCold.Call.old i).castAdd 1
def input {t : ℕ} (data : Fin t→List Bool) (supports : List Bool):=SupportDock.lift (FamilyCold.Call.input data) supports
def heads {t : ℕ} (cursor : Fin t→ℕ) (supports : List Bool):=SupportDock.lift (FamilyCold.Call.heads cursor) supports.length
def machine {t s : ℕ} (supplier : Machine 3244 s) (fields : Fin 104→Fin t):=RecoveryFocus.machine (slots fields) supplier

theorem slots_old {t : ℕ} (fields : Fin 104→Fin t) (i : Fin 3243) :
    slots fields (i.castAdd 1)=(FamilyCold.Call.slots fields i).castAdd 1:=SupportDock.slots_old _ _
theorem slots_support {t : ℕ} (fields : Fin 104→Fin t) :
    slots fields 3243=(0 : Fin 1).natAdd (t+3243):=SupportDock.slots_new _ 0

theorem call_run {t s : ℕ} (supplier : Machine 3244 s) (fields : Fin 104→Fin t) (hf:Function.Injective fields)
    (P H V C T core W L fuel : ℕ) (bits arity supports : List Bool) (ambient : Fin 94→List Bool)
    (data : Fin t→List Bool) (cursor : Fin t→ℕ)
    (hdata:∀ j,data (fields j)=values P H V C T core W L bits arity ambient j)
    (hheads:∀ j,cursor (fields j)=cursors j)
    (inner : ExecutionReceipt 3244 s)
    (hr:runFrom supplier fuel ⟨supplier.start,SupportDock.lift (FamilyPrepare.heads FamilyHeads.heads) supports.length,
      SupportDock.lift (FamilyCold.input P H V C T core W L bits arity ambient) supports⟩=some inner) :
    ∃ actual,runFrom (machine supplier fields) fuel ⟨(machine supplier fields).start,heads cursor supports,input data supports⟩=some actual ∧
      actual.steps=inner.steps ∧
      (∀ i,actual.final.heads (slots fields i)=inner.final.heads i ∧ actual.final.tapes (slots fields i)=inner.final.tapes i) ∧
      (∀ i,(∀ j,fields j≠i)→actual.final.heads (old i)=cursor i ∧ actual.final.tapes (old i)=data i) := by
  have injective:=SupportDock.injective (FamilyCold.Call.slots fields) (FamilyCold.Call.slots_injective fields hf)
  have localHeads:=SupportDock.local_fields (FamilyCold.Call.slots fields) (FamilyCold.Call.heads cursor)
    (FamilyPrepare.heads FamilyHeads.heads) supports.length (FamilyCold.Call.heads_local fields cursor hheads)
  have localTapes:=SupportDock.local_fields (FamilyCold.Call.slots fields) (FamilyCold.Call.input data)
    (FamilyCold.input P H V C T core W L bits arity ambient) supports
    (FamilyCold.Call.input_local fields data P H V C T core W L bits arity ambient hdata)
  obtain ⟨actual,run,_control,steps,ah,atape,away⟩:=RecoveryFocus.dock (slots fields) injective supplier fuel
    (heads cursor supports) (input data supports)
    ⟨supplier.start,SupportDock.lift (FamilyPrepare.heads FamilyHeads.heads) supports.length,
      SupportDock.lift (FamilyCold.input P H V C T core W L bits arity ambient) supports⟩
    localHeads localTapes inner hr
  refine ⟨actual,run,steps,fun i=>⟨ah i,atape i⟩,?_⟩
  intro i hi
  have kept:=away (old i) (SupportDock.outside (FamilyCold.Call.slots fields) (FamilyCold.Call.old i)
    (FamilyCold.Call.outside fields i hi))
  simpa only [heads,input,old,SupportDock.lift,FamilyCold.Call.heads,FamilyCold.Call.input,
    FamilyCold.Call.old,Fin.addCases_left] using kept

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySupportCall
