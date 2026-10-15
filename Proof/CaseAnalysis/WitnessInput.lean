import Proof.CaseAnalysis.WitnessFamilyCacheRun

/-! The complete cold family has exactly three original input tapes.
All other tapes start blank and can be supplied by the existing header's
fresh bank without a copy or a second source execution. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdInput
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem blank {t u : ℕ} (data : Fin t→List Bool) (f : ℕ→List Bool)
    (hd:∀i,data i=f i.val) (hz:∀i,t ≤ i →f i=[]) :
    ∀i : Fin (t+u),Fin.addCases (motive:=fun _=>List Bool) data (fun _=>[]) i=f i.val:=by
  intro i
  refine Fin.addCases (m:=t) (n:=u) (fun j=>?_) (fun j=>?_) i
  · simpa only [Fin.addCases_left,Fin.val_castAdd] using hd j
  · rw [Fin.addCases_right,Fin.val_natAdd,hz (t+j.val) (by omega)]

private theorem append {t u : ℕ} (data : Fin t→List Bool) (f : ℕ→List Bool)
    (hd:∀i,data i=f i.val) (hz:∀i,t ≤ i →f i=[]) (p : ℕ) (word : List Bool) :
    ∀i : Fin (t+u),Fin.addCases (motive:=fun _=>List Bool) data
      (fun j=>if j.val=p then word else []) i=
      if i.val=t+p then word else f i.val:=by
  intro i
  refine Fin.addCases (m:=t) (n:=u) (fun j=>?_) (fun j=>?_) i
  · rw [Fin.addCases_left,Fin.val_castAdd,if_neg (by have h:=j.isLt;omega)]
    exact hd j
  · rw [Fin.addCases_right,Fin.val_natAdd,hz (t+j.val) (by omega)]
    by_cases hj:j.val=p
    · rw [if_pos hj,if_pos (by omega)]
    · rw [if_neg hj,if_neg (by omega)]

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def oracleIndex (k : ℕ):=ColdSource.tapes source k+4+1

theorem source_input (k : ℕ) (x : List Bool) :
    ∀i,ColdSource.input source k x i=if i.val=2 then frame x else []:=by
  have lo:2<HierarchySelectedSource.base source k:=
    (HierarchyPrefix.old k (HierarchySelectedSource.p source) (HierarchySelectedSource.q source)
      (HierarchyFramedInput.old k (HierarchyReduction.xTape k))).isLt
  have hs:∀i,HierarchySelectedSource.input source k x i=if i.val=2 then frame x else []:=
    blank (t:=HierarchySelectedSource.base source k) (u:=SourceCall.tapes source)
      (HierarchyPrefix.input k (HierarchySelectedSource.p source) (HierarchySelectedSource.q source) x)
      (fun i=>if i=2 then frame x else []) (fun _=>rfl) (fun i hi=>if_neg (by omega))
  exact blank (t:=HierarchySelectedSource.tapes source k) (u:=8)
    (HierarchySelectedSource.input source k x) (fun i=>if i=2 then frame x else [])
    hs (fun i hi=>if_neg (by dsimp [HierarchySelectedSource.tapes] at hi;omega))

theorem oracle_input (k : ℕ) (x raw : List Bool) :
    ∀i,ColdOracle.input source k x raw i=
      if i.val=oracleIndex source k then frame raw else if i.val=2 then frame x else []:=by
  have lo:2<ColdSource.tapes source k:=by
    have h:=(SelectedOracle.fields source k 0).isLt
    change 2<HierarchySelectedSource.tapes source k at h
    dsimp [ColdSource.tapes];omega
  have hg:∀i,NativeGuard.input (ColdSource.input source k x) i=if i.val=2 then frame x else []:=
    blank (t:=ColdSource.tapes source k) (u:=4) (ColdSource.input source k x)
      (fun i=>if i=2 then frame x else []) (source_input source k x) (fun i hi=>if_neg (by omega))
  exact append (t:=ColdSource.tapes source k+4) (u:=1385)
    (NativeGuard.input (ColdSource.input source k x)) (fun i=>if i=2 then frame x else [])
    hg (fun i hi=>if_neg (by omega)) 1 (frame raw)

theorem legal_input (a : PointwisePCPPAlgorithm) (k D G e : ℕ) (x raw : List Bool) :
    ∀i,ColdLegal.input source a k D G e x raw i=
      if i.val=oracleIndex source k then frame raw else if i.val=2 then frame x else []:=by
  have lo:2<oracleIndex source k:=by dsimp [oracleIndex];omega
  have bound:oracleIndex source k<ColdNative.base source k:=by
    change ColdSource.tapes source k+4+1<ColdSource.tapes source k+4+1385
    omega
  have hn:∀i,ColdNative.input source a k D G x raw i=
      if i.val=oracleIndex source k then frame raw else if i.val=2 then frame x else []:=
    blank (t:=ColdNative.base source k) (u:=NativePipeline.Dock.extra a D G)
      (ColdOracle.input source k x raw)
      (fun i=>if i=oracleIndex source k then frame raw else if i=2 then frame x else [])
      (oracle_input source k x raw) (fun i hi=>by rw [if_neg (by omega),if_neg (by omega)])
  exact blank (t:=ColdNative.tapes source a k D G) (u:=LegalTemplate.Call.extra e)
    (ColdNative.input source a k D G x raw)
    (fun i=>if i=oracleIndex source k then frame raw else if i=2 then frame x else []) hn (fun i hi=>by
    have more:ColdNative.base source k≤ColdNative.tapes source a k D G:=by
      change ColdNative.base source k≤ColdNative.base source k+NativePipeline.Dock.extra a D G
      omega
    rw [if_neg (by omega),if_neg (by omega)])

def data (a : PointwisePCPPAlgorithm) (k D G e : ℕ) (x raw bits : List Bool) (i : ℕ):=
  if i=ColdLegal.tapes source a k D G e then frame bits
  else if i=oracleIndex source k then frame raw else if i=2 then frame x else []

theorem family_input (a : PointwisePCPPAlgorithm) (k D G e E : ℕ) (x raw bits : List Bool) :
    ∀i,ColdFamily.input source a k D G e E x raw bits i=data source a k D G e x raw bits i.val:=by
  have lo:2<oracleIndex source k:=by dsimp [oracleIndex];omega
  have bound:oracleIndex source k<ColdLegal.tapes source a k D G e:=by
    change ColdSource.tapes source k+4+1<
      ColdSource.tapes source k+4+1385+NativePipeline.Dock.extra a D G+LegalTemplate.Call.extra e
    omega
  have first:∀i,ColdFamily.baseInput source a k D G e x raw bits i=data source a k D G e x raw bits i.val:=by
    have same:=append (t:=ColdLegal.tapes source a k D G e) (u:=1)
      (ColdLegal.input source a k D G e x raw)
      (fun i=>if i=oracleIndex source k then frame raw else if i=2 then frame x else [])
      (legal_input source a k D G e x raw)
      (fun i hi=>by rw [if_neg (by omega),if_neg (by omega)]) 0 (frame bits)
    have one:(fun j : Fin 1=>if j.val=0 then frame bits else [])=(fun _=>frame bits):=by
      funext j
      exact if_pos (by have h:=j.isLt;omega)
    rw [one] at same
    simpa only [Nat.add_zero,ColdFamily.baseInput,data] using same
  have second:∀i,FamilyCapacity.Call.input E (ColdFamily.baseInput source a k D G e x raw bits) i=
      data source a k D G e x raw bits i.val:=
    blank (t:=ColdFamily.base source a k D G e) (u:=FamilyCapacity.Call.extra E)
      (ColdFamily.baseInput source a k D G e x raw bits) (data source a k D G e x raw bits) first (fun i hi=>by
      dsimp only [ColdFamily.base] at hi
      rw [data,if_neg (by omega),if_neg (by omega),if_neg (by omega)])
  exact blank (t:=ColdFamily.base source a k D G e+FamilyCapacity.Call.extra E) (u:=FamilyCold.Call.extra)
    (FamilyCapacity.Call.input E (ColdFamily.baseInput source a k D G e x raw bits))
    (data source a k D G e x raw bits) second (fun i hi=>by
    dsimp only [ColdFamily.base] at hi
    rw [data,if_neg (by omega),if_neg (by omega),if_neg (by omega)])

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdInput
