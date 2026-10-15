import Proof.CaseAnalysis.WitnessFamilyCallDock
import Proof.CaseAnalysis.CloseoutWitnessFamilyResources

/-! The actual whole family supplier consumes the paid retained policy and
mass store. The literal numerical and circuit premises are discharged by
the checked uniform resource consumer, with one unchanged machine. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCold.Call
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth FamilySparse FamilyResources
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem call_run (sym : Bool) (S P V C T core W L k : ℕ) (q : ℚ)
    (bits arity : List Bool) (ambient : Fin 94→List Bool)
    {t : ℕ} (fields : Fin 104→Fin t) (injective : Function.Injective fields)
    (data : Fin t→List Bool) (cursor : Fin t→ℕ)
    (hdata : ∀ j,data (fields j)=values P (P+1) V C T core W L bits arity ambient j)
    (hheads : ∀ j,cursor (fields j)=cursors j)
    (hf : Fits P V C T k bits arity) (hlen : bits.length ≤ S) (hv : V ≤ S)
    (hC : 0<C) (hstore : Store (width T (natBitLength C)) zero [] ambient)
    (hq : 0≤q) (hk : k≤width T (natBitLength C))
    (hp : CompetitorThresholdDecision.numerator q<2^k) (hd : q.den<2^k) :
    ∃ extra actual,runFrom (machine sym k q fields)
      (FamilyCold.budget P (P+1) V (sumCost S P) bits)
      ⟨(machine sym k q fields).start,heads cursor,input data⟩=some actual ∧
      actual.steps≤totalCost S P ∧ actual.final.heads (slots fields 724)=0 ∧
      actual.final.tapes (slots fields 724)=[FamilyCold.passed sym V C T core W L q bits arity] ∧
      extra 174=List.replicate V true ∧
      (∀ i,(∀ j,fields j≠i)→actual.final.heads (old i)=cursor i ∧ actual.final.tapes (old i)=data i) ∧
      (FamilyCold.passed sym V C T core W L q bits arity=true→∃ after,
        actual.final.heads ∘ slots fields=FamilyPrepare.heads (FamilyWork.heads
          (FamilyLoop.entry (FamilyMode.machine sym) P (P+1) C T core W L k q
            (FamilyFields.words bits) arity [] (FamilyFields.tail (P+1) bits)
            [] [] [] (FamilyMode.native sym core) V after) 1) ∧
        actual.final.tapes ∘ slots fields=FamilyPrepare.tapes (natBitLength C) bits (FamilyWork.tapes (P+1) V
          (FamilyLoop.entry (FamilyMode.machine sym) P (P+1) C T core W L k q
            (FamilyFields.words bits) arity [] (FamilyFields.tail (P+1) bits)
            [] [] [] (FamilyMode.native sym core) V after) extra) ∧
        Store (width T (natBitLength C)) zero [] after):=by
  obtain ⟨extra,inner,ir,is,ih,it,iv,good⟩:=FamilyResources.consumer_run sym S P V C T core W L k q
    bits arity ambient hf hlen hv hC hstore hq hk hp hd
  have dock:=RecoveryFocus.dock (slots fields) (slots_injective fields injective)
    (FamilyCold.machine sym k q) _ (heads cursor) (input data)
    ⟨(FamilyCold.machine sym k q).start,FamilyPrepare.heads FamilyHeads.heads,
      FamilyCold.input P (P+1) V C T core W L bits arity ambient⟩
    (heads_local fields cursor hheads) (input_local fields data P (P+1) V C T core W L bits arity ambient hdata) inner ir
  let actual:=Classical.choose dock
  have facts:=Classical.choose_spec dock
  have ah:=facts.2.2.2.1
  have atapes:=facts.2.2.2.2.1
  have away:=facts.2.2.2.2.2
  refine ⟨extra,actual,facts.1,facts.2.2.1.trans_le is,(ah _).trans ih,(atapes _).trans it,iv,?_,?_⟩
  · intro i hi
    have keep:=away (old i) (outside fields i hi)
    exact ⟨keep.1.trans (by simp only [heads,old,Fin.addCases_left]),
      keep.2.trans (by simp only [input,old,Fin.addCases_left])⟩
  · intro accepted
    obtain ⟨after,ah',at',store⟩:=good accepted
    exact ⟨after,(funext ah).trans ah',(funext atapes).trans at',store⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCold.Call
