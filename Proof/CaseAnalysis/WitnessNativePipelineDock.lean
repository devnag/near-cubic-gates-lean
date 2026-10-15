import Proof.CaseAnalysis.WitnessNativePipeline

/-! Five retained outputs of the original cold oracle prefix are the only
live inputs to the complete guarded native pipeline. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativePipeline.Dock
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev extra (a : PointwisePCPPAlgorithm) (D G : ℕ):=NativePipeline.base G+NativePolicy.Call.extra a D
def values {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ) : Fin 5→List Bool:=
  ![p.word,List.replicate R true,List.replicate Q true,frame Q.bits,PCPPNative.descriptor oracle]
def initialData {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q i : ℕ):=
  if i=0 then values oracle p Q 0 else if i=13 then values oracle p Q 1
  else if i=14 then values oracle p Q 2 else if i=48 then values oracle p Q 3
  else if i=49 then values oracle p Q 4 else []
private theorem extend_data {R m : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q n : ℕ)
    (data : Fin m→List Bool) (hd : ∀ i,data i=initialData oracle p Q i.val) (hm : 125 ≤ m) :
    ∀ i : Fin (m+n),Fin.addCases (motive:=fun _=>List Bool) data (fun _=>[]) i=
      initialData oracle p Q i.val:=by
  intro i
  refine Fin.addCases (m:=m) (n:=n) (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left,Fin.val_castAdd,hd]
  · rw [Fin.addCases_right]
    simp only [initialData,Fin.val_natAdd,if_neg (show m+j.val≠0 by omega),
      if_neg (show m+j.val≠13 by omega),if_neg (show m+j.val≠14 by omega),
      if_neg (show m+j.val≠48 by omega),if_neg (show m+j.val≠49 by omega)]
theorem input_fields (a : PointwisePCPPAlgorithm) (D G : ℕ) {R : ℕ}
    (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ) :
    ∀ i,NativePipeline.input a D G oracle p Q i=initialData oracle p Q i.val:=by
  have h : ∀ i,NativeMeasured.input oracle p Q i=initialData oracle p Q i.val:=by
    intro i
    rw [NativeMeasured.input_fields]
    simp only [Fin.ext_iff]
    rfl
  have h0:=extend_data oracle p Q (OracleCap.Call.extra G) _ h (by decide)
  exact extend_data oracle p Q (NativePolicy.Call.extra a D) _ h0 (by omega)

def old (a : PointwisePCPPAlgorithm) (D G : ℕ) {t : ℕ} (i : Fin t) : Fin (t+extra a D G):=i.castAdd _
def remap (a : PointwisePCPPAlgorithm) (D G : ℕ) (i : Fin (extra a D G)) : Fin (5+extra a D G):=
  if i.val=0 then (0 : Fin 5).castAdd _ else if i.val=13 then (1 : Fin 5).castAdd _
  else if i.val=14 then (2 : Fin 5).castAdd _ else if i.val=48 then (3 : Fin 5).castAdd _
  else if i.val=49 then (4 : Fin 5).castAdd _ else i.natAdd 5
def bank (a : PointwisePCPPAlgorithm) (D G : ℕ) {t : ℕ} (fields : Fin 5→Fin t) :
    Fin (5+extra a D G)→Fin (t+extra a D G):=
  Fin.addCases (motive:=fun _=>Fin (t+extra a D G)) (fun i=>old a D G (fields i)) (fun i=>i.natAdd t)
def slots (a : PointwisePCPPAlgorithm) (D G : ℕ) {t : ℕ} (fields : Fin 5→Fin t):=
  bank a D G fields ∘ remap a D G
def input (a : PointwisePCPPAlgorithm) (D G : ℕ) {t : ℕ} (data : Fin t→List Bool) :
    Fin (t+extra a D G)→List Bool:=Fin.addCases data (fun _=>[])
def machine (a : PointwisePCPPAlgorithm) (D G copies : ℕ) (delta : ℚ) {t : ℕ} (fields : Fin 5→Fin t):=
  RecoveryFocus.machine (slots a D G fields) (NativePipeline.machine a D G copies delta)
theorem remap_injective (a : PointwisePCPPAlgorithm) (D G : ℕ) : Function.Injective (remap a D G):=by
  intro i j he
  have hv:=congrArg Fin.val he
  dsimp only [remap] at hv
  split_ifs at hv <;> dsimp at hv <;> apply Fin.ext <;> omega
theorem slots_injective (a : PointwisePCPPAlgorithm) (D G : ℕ) {t : ℕ} (fields : Fin 5→Fin t)
    (hf : Function.Injective fields) : Function.Injective (slots a D G fields):=by
  apply Function.Injective.comp (g:=bank a D G fields) _ (remap_injective a D G)
  apply RecoveryColdAllCode.join_injective
  · intro i j he
    have hv:=congrArg Fin.val he
    exact hf (Fin.ext hv)
  · intro i j he
    have hv:=congrArg Fin.val he
    simp only [Fin.val_natAdd] at hv
    exact Fin.ext (by omega)
  · intro i j he
    have hv:=congrArg Fin.val he
    have ht:=(fields i).isLt
    dsimp only [old,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
theorem input_local (a : PointwisePCPPAlgorithm) (D G : ℕ) {t R : ℕ} (fields : Fin 5→Fin t)
    (data : Fin t→List Bool) (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ)
    (hf : ∀ i,data (fields i)=values oracle p Q i) (i : Fin (extra a D G)) :
    input a D G data (slots a D G fields i)=NativePipeline.input a D G oracle p Q i:=by
  rw [input_fields]
  by_cases h0:i.val=0
  · simpa [input,slots,bank,remap,old,initialData,h0] using hf 0
  by_cases h13:i.val=13
  · simpa [input,slots,bank,remap,old,initialData,h0,h13] using hf 1
  by_cases h14:i.val=14
  · simpa [input,slots,bank,remap,old,initialData,h0,h13,h14] using hf 2
  by_cases h48:i.val=48
  · simpa [input,slots,bank,remap,old,initialData,h0,h13,h14,h48] using hf 3
  by_cases h49:i.val=49
  · simpa [input,slots,bank,remap,old,initialData,h0,h13,h14,h48,h49] using hf 4
  simp [input,slots,bank,remap,initialData,h0,h13,h14,h48,h49]

theorem outside (a : PointwisePCPPAlgorithm) (D G : ℕ) {t : ℕ} (fields : Fin 5→Fin t)
    (i : Fin t) (hi : ∀ j,fields j≠i) : ∀ j,slots a D G fields j≠old a D G i:=by
  have away : ∀ k,bank a D G fields k≠old a D G i:=by
    intro k
    refine Fin.addCases (m:=5) (n:=extra a D G) (fun j=>?_) (fun j=>?_) k
    · intro he
      have hv:=congrArg Fin.val he
      simp only [bank,Fin.addCases_left,old,Fin.val_castAdd] at hv
      exact hi j (Fin.ext hv)
    · intro he
      have hv:=congrArg Fin.val he
      simp only [bank,Fin.addCases_right,old,Fin.val_castAdd,Fin.val_natAdd] at hv
      have ht:=i.isLt
      omega
  exact fun j=>away (remap a D G j)

theorem flag_index (a : PointwisePCPPAlgorithm) (D G : ℕ) :
    125 ≤ (NativePipeline.flagSlot a D G).val:=by
  change 125 ≤ (NativeScreen.flagSlot G).val
  have h0:(OracleCap.Core.flagSlot (OracleCap.degree G)).val≠0:=by
    change OracleCap.Core.P (OracleCap.degree G)+4≠0
    omega
  have h1:(OracleCap.Core.flagSlot (OracleCap.degree G)).val≠1:=by
    change OracleCap.Core.P (OracleCap.degree G)+4≠1
    omega
  simp only [NativeScreen.flagSlot,OracleCap.Call.flagSlot,OracleCap.Call.slots,
    if_neg h0,if_neg h1,Fin.val_natAdd]
  omega
theorem initial_flag (a : PointwisePCPPAlgorithm) (D G : ℕ) {t : ℕ} (fields : Fin 5→Fin t)
    (data : Fin t→List Bool) :
    input a D G data (slots a D G fields (NativePipeline.flagSlot a D G))=[]:=by
  have hi:=flag_index a D G
  simp only [slots,Function.comp_apply,remap,
    if_neg (show (NativePipeline.flagSlot a D G).val≠0 by omega),
    if_neg (show (NativePipeline.flagSlot a D G).val≠13 by omega),
    if_neg (show (NativePipeline.flagSlot a D G).val≠14 by omega),
    if_neg (show (NativePipeline.flagSlot a D G).val≠48 by omega),
    if_neg (show (NativePipeline.flagSlot a D G).val≠49 by omega),
    bank,Fin.addCases_right,input]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativePipeline.Dock
