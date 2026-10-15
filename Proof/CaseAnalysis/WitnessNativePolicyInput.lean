import Proof.CaseAnalysis.WitnessNativePolicy

/-! The native cache/policy continuation has exactly ten live initial
fields. All framing and source workspaces are physically fresh; the caller
aliases the already-produced counters and streams without copying them. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativePolicy
open LocalBitMultitape RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev tapes (a : PointwisePCPPAlgorithm) (D : ℕ):=base a+SourcePolicy.Call.extra D
def initialData {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q i : ℕ):=
  if i=0 then List.replicate Q true else if i=1 then List.replicate oracle.size true
  else if i=2 then List.replicate (Codec.clauses p).length true else if i=18 then List.replicate R true
  else if i=19 then List.replicate (PCPPNativeMetadataMass.queryBytes p R Q).length true
  else if i=20 then List.replicate (DedupBytes.fields p).length true
  else if i=95 then PCPPNative.descriptor oracle
  else if i=96 then PCPPNativeMetadataMass.queryBytes p R Q
  else if i=291 then DedupBytes.fields p else if i=363 then List.replicate R true else []

theorem initialData_fresh {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q i : ℕ)
    (hi : 364 ≤ i) : initialData oracle p Q i=[]:=by
  simp only [initialData,if_neg (show i≠0 by omega),if_neg (show i≠1 by omega),
    if_neg (show i≠2 by omega),if_neg (show i≠18 by omega),if_neg (show i≠19 by omega),
    if_neg (show i≠20 by omega),if_neg (show i≠95 by omega),if_neg (show i≠96 by omega),
    if_neg (show i≠291 by omega),if_neg (show i≠363 by omega)]

private theorem extend_data {R m : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q n : ℕ)
    (data : Fin m→List Bool) (hdata : ∀ i,data i=initialData oracle p Q i.val) (hm : 364 ≤ m) :
    ∀ i : Fin (m+n),Fin.addCases (motive:=fun _=>List Bool) data (fun _=>[]) i=
      initialData oracle p Q i.val:=by
  intro i
  refine Fin.addCases (m:=m) (n:=n) (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left,Fin.val_castAdd,hdata]
  · rw [Fin.addCases_right,initialData_fresh oracle p Q _ (by simp only [Fin.val_natAdd];omega)]

theorem native_input_fields {R : ℕ} (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ) :
    ∀ i,NativeCache.nativeInput oracle p Q i=initialData oracle p Q i.val:=by
  intro i
  refine Fin.addCases (m:=363) (n:=1) (fun j=>?_) (fun j=>?_) i
  · fin_cases j <;> rfl
  · fin_cases j
    rfl

theorem input_fields (a : PointwisePCPPAlgorithm) (D : ℕ) {R : ℕ}
    (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ) :
    ∀ i,input a D oracle p Q i=initialData oracle p Q i.val:=by
  have h0:=native_input_fields oracle p Q
  have h1:=extend_data oracle p Q 1 _ h0 (by decide)
  have h2:=extend_data oracle p Q 1 _ h1 (by decide)
  have h3:=extend_data oracle p Q 2 _ h2 (by decide)
  have h4:=extend_data oracle p Q 65 _ h3 (by decide)
  have h5:=extend_data oracle p Q 1 _ h4 (by decide)
  have h6:=extend_data oracle p Q 1 _ h5 (by decide)
  have h7:=extend_data oracle p Q 2 _ h6 (by decide)
  have h8:=extend_data oracle p Q (PCPPSourceCache.tapes a) _ h7 (by decide)
  exact extend_data oracle p Q (SourcePolicy.Call.extra D) _ h8 (by
    change 364 ≤ 437+PCPPSourceCache.tapes a
    omega)

end NearCubicWires.RepairOrdinary.CloseoutWitness.NativePolicy
