import Proof.CaseAnalysis.WitnessNativePolicyInput
import Proof.Amplification.RecoveryAllCodeLayout

/-! Alias the ten measured fields into the complete cache and policy worker.
The unrelated stream/counter heads stay outside this local cold workspace. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativePolicy.Call
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev extra (a : PointwisePCPPAlgorithm) (D : ℕ):=NativePolicy.tapes a D
def remap (a : PointwisePCPPAlgorithm) (D : ℕ) (i : Fin (extra a D)) : Fin (75+extra a D):=
  if i.val=0 then (45 : Fin 75).castAdd _ else if i.val=1 then (32 : Fin 75).castAdd _
  else if i.val=2 then (48 : Fin 75).castAdd _ else if i.val=18 then (71 : Fin 75).castAdd _
  else if i.val=19 then (53 : Fin 75).castAdd _ else if i.val=20 then (58 : Fin 75).castAdd _
  else if i.val=95 then (0 : Fin 75).castAdd _ else if i.val=96 then (52 : Fin 75).castAdd _
  else if i.val=291 then (57 : Fin 75).castAdd _ else if i.val=363 then (72 : Fin 75).castAdd _
  else i.natAdd 75
def old (a : PointwisePCPPAlgorithm) (D : ℕ) {t : ℕ} (i : Fin t) : Fin (t+extra a D):=i.castAdd _
def bank (a : PointwisePCPPAlgorithm) (D : ℕ) {t : ℕ} (counter : Fin 75→Fin t) :
    Fin (75+extra a D)→Fin (t+extra a D):=
  Fin.addCases (motive:=fun _=>Fin (t+extra a D)) (fun i=>old a D (counter i)) (fun i=>i.natAdd t)
def slots (a : PointwisePCPPAlgorithm) (D : ℕ) {t : ℕ} (counter : Fin 75→Fin t):=
  bank a D counter ∘ remap a D
def input (a : PointwisePCPPAlgorithm) (D : ℕ) {t : ℕ} (data : Fin t→List Bool) :
    Fin (t+extra a D)→List Bool:=Fin.addCases data (fun _=>[])
def heads (a : PointwisePCPPAlgorithm) (D : ℕ) {t : ℕ} (cursor : Fin t→ℕ) :
    Fin (t+extra a D)→ℕ:=Fin.addCases cursor (fun _=>0)
def machine (a : PointwisePCPPAlgorithm) (D copies : ℕ) (delta : ℚ) {t : ℕ}
    (counter : Fin 75→Fin t):=RecoveryFocus.machine (slots a D counter) (NativePolicy.machine a D copies delta)

private def index (i : ℕ):=
  if i=0 then 45 else if i=1 then 32 else if i=2 then 48 else if i=18 then 71
  else if i=19 then 53 else if i=20 then 58 else if i=95 then 0 else if i=96 then 52
  else if i=291 then 57 else if i=363 then 72 else 75+i
private def inverse (i : ℕ):=
  if i=45 then 0 else if i=32 then 1 else if i=48 then 2 else if i=71 then 18
  else if i=53 then 19 else if i=58 then 20 else if i=0 then 95 else if i=52 then 96
  else if i=57 then 291 else if i=72 then 363 else i-75
private theorem inverse_index (i : ℕ) : inverse (index i)=i:=by
  unfold index
  split_ifs with h0 h1 h2 h18 h19 h20 h95 h96 h291 h363
  all_goals try (subst i; rfl)
  simp only [inverse,if_neg (show 75+i≠45 by omega),if_neg (show 75+i≠32 by omega),
    if_neg (show 75+i≠48 by omega),if_neg (show 75+i≠71 by omega),
    if_neg (show 75+i≠53 by omega),if_neg (show 75+i≠58 by omega),
    if_neg (show 75+i≠0 by omega),if_neg (show 75+i≠52 by omega),
    if_neg (show 75+i≠57 by omega),if_neg (show 75+i≠72 by omega)]
  omega
private theorem index_injective : Function.Injective index:=by
  intro i j he
  exact (inverse_index i).symm.trans ((congrArg inverse he).trans (inverse_index j))
private theorem remap_val (a : PointwisePCPPAlgorithm) (D : ℕ) (i : Fin (extra a D)) :
    (remap a D i).val=index i.val:=by
  unfold remap index
  split_ifs <;> rfl
theorem remap_injective (a : PointwisePCPPAlgorithm) (D : ℕ) : Function.Injective (remap a D):=by
  intro i j he
  have hv:=congrArg Fin.val he
  rw [remap_val,remap_val] at hv
  exact Fin.ext (index_injective hv)
theorem bank_injective (a : PointwisePCPPAlgorithm) (D : ℕ) {t : ℕ} (counter : Fin 75→Fin t)
    (hc : Function.Injective counter) : Function.Injective (bank a D counter):=by
  apply RecoveryColdAllCode.join_injective
  · intro i j he
    have hv:=congrArg Fin.val he
    exact hc (Fin.ext hv)
  · intro i j he
    apply Fin.ext
    have hv:=congrArg Fin.val he
    simp only [Fin.val_natAdd] at hv
    omega
  · intro i j he
    have hv:=congrArg Fin.val he
    have hi:=(counter i).isLt
    dsimp only [old,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
theorem slots_injective (a : PointwisePCPPAlgorithm) (D : ℕ) {t : ℕ} (counter : Fin 75→Fin t)
    (hc : Function.Injective counter) : Function.Injective (slots a D counter):=
  (bank_injective a D counter hc).comp (remap_injective a D)

theorem input_fields (a : PointwisePCPPAlgorithm) (D : ℕ) {t R : ℕ} (counter : Fin 75→Fin t)
    (data : Fin t→List Bool) (cursor : Fin t→ℕ) (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ)
    (hf : ∀ j,cursor (counter (PCPPNativeColdCounters.ports j))=0 ∧
      data (counter (PCPPNativeColdCounters.ports j))=PCPPNativeMetadataMass.values oracle p Q j)
    (hrh : cursor (counter 72)=0) (hrt : data (counter 72)=List.replicate R true)
    (i : Fin (extra a D)) :
    heads a D cursor (slots a D counter i)=0 ∧
      input a D data (slots a D counter i)=NativePolicy.input a D oracle p Q i:=by
  rw [NativePolicy.input_fields]
  by_cases h0:i.val=0
  · simpa [heads,input,slots,bank,remap,old,NativePolicy.initialData,PCPPNativeColdCounters.ports,
      PCPPNativeMetadataMass.values,h0] using hf 3
  by_cases h1:i.val=1
  · simpa [heads,input,slots,bank,remap,old,NativePolicy.initialData,PCPPNativeColdCounters.ports,
      PCPPNativeMetadataMass.values,h0,h1] using hf 1
  by_cases h2:i.val=2
  · simpa [heads,input,slots,bank,remap,old,NativePolicy.initialData,PCPPNativeColdCounters.ports,
      PCPPNativeMetadataMass.values,h0,h1,h2] using hf 4
  by_cases h18:i.val=18
  · simpa [heads,input,slots,bank,remap,old,NativePolicy.initialData,PCPPNativeColdCounters.ports,
      PCPPNativeMetadataMass.values,h0,h1,h2,h18] using hf 2
  by_cases h19:i.val=19
  · simpa [heads,input,slots,bank,remap,old,NativePolicy.initialData,PCPPNativeColdCounters.ports,
      PCPPNativeMetadataMass.values,h0,h1,h2,h18,h19] using hf 6
  by_cases h20:i.val=20
  · simpa [heads,input,slots,bank,remap,old,NativePolicy.initialData,PCPPNativeColdCounters.ports,
      PCPPNativeMetadataMass.values,h0,h1,h2,h18,h19,h20] using hf 8
  by_cases h95:i.val=95
  · simpa [heads,input,slots,bank,remap,old,NativePolicy.initialData,PCPPNativeColdCounters.ports,
      PCPPNativeMetadataMass.values,h0,h1,h2,h18,h19,h20,h95] using hf 0
  by_cases h96:i.val=96
  · simpa [heads,input,slots,bank,remap,old,NativePolicy.initialData,PCPPNativeColdCounters.ports,
      PCPPNativeMetadataMass.values,h0,h1,h2,h18,h19,h20,h95,h96] using hf 5
  by_cases h291:i.val=291
  · simpa [heads,input,slots,bank,remap,old,NativePolicy.initialData,PCPPNativeColdCounters.ports,
      PCPPNativeMetadataMass.values,h0,h1,h2,h18,h19,h20,h95,h96,h291] using hf 7
  by_cases h363:i.val=363
  · simpa [heads,input,slots,bank,remap,old,NativePolicy.initialData,PCPPNativeColdCounters.ports,
      PCPPNativeMetadataMass.values,h0,h1,h2,h18,h19,h20,h95,h96,h291,h363] using And.intro hrh hrt
  simp [heads,input,slots,bank,remap,NativePolicy.initialData,h0,h1,h2,h18,h19,h20,h95,h96,h291,h363]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativePolicy.Call
