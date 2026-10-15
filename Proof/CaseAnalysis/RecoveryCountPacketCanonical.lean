import Proof.CaseAnalysis.RecoveryCountBank

/-! The actual shared-candidate increment and row-packet installer return
one canonical bank. Scalar padding and stack padding are retained explicitly. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountPacketCanonical
open LocalBitMultitape RecoveryRootRound
open RecoveryBoundedRowPacketAppend (values Loaded scalarPort)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data (A : Fin 78→List Bool) (v : Fin 10→ℕ) : Fin 88→List Bool:=
  Fin.addCases (m:=78) (n:=10) A (fun j=>List.replicate (v j) true)
def heads (out stack : List Bool) : Fin 88→ℕ:=
  Fin.addCases (m:=78) (n:=10) (RecoveryBoundedGrammarWorker.heads out stack) (fun _=>0)

theorem loaded (current : Fin 78→List Bool) (node B : ℕ) (out stack packet source : List Bool)
    (v : Fin 10→ℕ) (h : ∀ j,2*v j+4≤B) :
    Loaded v B (heads out stack)
      (data (RecoveryBoundedGrammarBank.ready current node B out stack packet source) v) := by
  refine ⟨?_,?_,rfl,?_,h⟩
  · intro j
    change heads out stack (j.natAdd 78)=0
    simp only [heads,Fin.addCases_right]
  · intro j
    change data (RecoveryBoundedGrammarBank.ready current node B out stack packet source) v
      (j.natAdd 78)=List.replicate (v j) true
    simp only [data,Fin.addCases_right]
  · change RecoveryBoundedGrammarBank.ready current node B out stack packet source 73=List.replicate B false
    rw [RecoveryBoundedGrammarBank.ready_kept _ _ _ _ _ _ _ _ (by decide)]
    rfl

theorem load_output (fields : Fin 78→List Bool) (node B : ℕ) (A : Fin 78→List Bool)
    (out stack packet source : List Bool)
    (h20 : A 20=out) (h25 : A 25=List.replicate node true) (h70 : A 70=source)
    (h73 : A 73=List.replicate B false) (h74 : A 74=stack) (h75 : A 75=packet)
    (h76 : A 76=List.replicate B true) (h77 : A 77=List.replicate (B+1) false) :
    RecoveryBoundedRowPacketLoad.output fields B A=
      RecoveryBoundedGrammarBank.ready fields node B out stack packet source := by
  apply congrArg (RecoveryBoundedRowReload.loaded fields B)
  funext i
  fin_cases i <;> simp [RecoveryBoundedRowErase.data,RecoveryBoundedGrammarBank.base,
    h20,h25,h70,h73,h74,h75,h76,h77]

theorem result (C D F L R count Q clauses B node : ℕ) (current : Fin 78→List Bool)
    (out stack packet source : List Bool)
    (hb : ∀ j,2*values C F R count Q clauses j+4≤B) (hn : 2*(count+1)+4≤B) :
    RecoveryBoundedCountRowEntry.result C D F L R count Q clauses B
      (data (RecoveryBoundedGrammarBank.ready current node B out stack packet source) (values C F R count Q clauses))=
    data (RecoveryBoundedGrammarBank.ready (RecoveryBoundedRowPrototype.fields C D F L R (count+1) Q clauses)
      node B out stack
      (ZeroPadding.pad B (RecoveryBoundedRowReload.word (RecoveryBoundedRowPrototype.fields C D F L R (count+1) Q clauses))) source)
      (values C F R (count+1) Q clauses) := by
  let A:=data (RecoveryBoundedGrammarBank.ready current node B out stack packet source) (values C F R count Q clauses)
  let next:=RecoveryBoundedCountIncrement.next A count
  let printed:=RecoveryBoundedRowPacketInstall.printed C D F L R (count+1) Q clauses B next
  let fields:=RecoveryBoundedRowPrototype.fields C D F L R (count+1) Q clauses
  let newPacket:=ZeroPadding.pad B (RecoveryBoundedRowReload.word fields)
  have clean : RecoveryBoundedRowPacketLoad.output fields B (fun i=>printed (RecoveryBoundedRowPacketLoad.slots i))=
      RecoveryBoundedGrammarBank.ready fields node B out stack newPacket source := by
    apply load_output fields node B _ out stack newPacket source
    all_goals rfl
  have hnxt:=RecoveryBoundedCountIncrement.loaded_next (loaded current node B out stack packet source
    (values C F R count Q clauses) hb) hn
  funext i
  refine Fin.addCases (m:=78) (n:=10) ?_ ?_ i
  · intro j
    change install RecoveryBoundedRowPacketLoad.slots printed
      (RecoveryBoundedRowPacketLoad.output fields B (fun k=>printed (RecoveryBoundedRowPacketLoad.slots k)))
      (RecoveryBoundedRowPacketLoad.slots j)=_
    have hinj : Function.Injective RecoveryBoundedRowPacketLoad.slots:=Fin.castAdd_injective 78 10
    rw [install_slot RecoveryBoundedRowPacketLoad.slots hinj,clean]
    simp only [data,Fin.addCases_left,fields,newPacket]
  · intro j
    have hj75 : scalarPort j≠75:=RecoveryBoundedRowPacketAppend.scalar_ne_output j
    have hjSlots : ∀ k,RecoveryBoundedRowPacketLoad.slots k≠scalarPort j:=by
      intro k he
      have hv:=congrArg Fin.val he
      change k.val=78+j.val at hv
      omega
    change install RecoveryBoundedRowPacketLoad.slots printed _ (scalarPort j)=_
    rw [install_other _ _ _ _ hjSlots]
    change Function.update next 75 newPacket (scalarPort j)=_
    rw [Function.update_of_ne hj75]
    simpa only [data,Fin.addCases_right] using hnxt.tapes j

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountPacketCanonical
