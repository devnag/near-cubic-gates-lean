import Proof.Amplification.RecoveryTseitinNativeSerialize

/-! The cold serializer consumes three finished graph ports and a paid
fresh arity copy. All hierarchy/search metadata lies outside this focus. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGraphSerialize
open LocalBitMultitape RecoveryRootRound
open RepairSource.RecoveryTseitinNative RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prepareSlots : Fin 7→Fin 1659 := ![20,25,144,145,76,116,153]
def serializerSlots (i : Fin 1506) : Fin 1659 :=
  if i=1062 then 20 else if i=1339 then 25 else if i=1342 then 145 else i.natAdd 153
def serializerCaps (B : ℕ) (i : Fin 1506) := if i=1342 then B else 0
def graph {n : ℕ} (c : BooleanCircuit n) := c.nodes.flatMap PCPPRequestNodeSchema.native
def coldData (n count output : ℕ) (word : List Bool) (i : Fin 1506) : List Bool :=
  if i=0 then List.replicate n true else if i=1062 then word else
    if i=1339 then List.replicate output true else if i=1342 then List.replicate count true else []

theorem prepare_injective : Function.Injective prepareSlots := by decide
theorem serializer_injective : Function.Injective serializerSlots := by
  intro i j he
  have hv := congrArg Fin.val he
  apply Fin.ext
  dsimp only [serializerSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem serializer_old (i : Fin 1659) (hi : i.val<153) (h20 : i≠20) (h25 : i≠25) (h145 : i≠145) :
    ∀ j,serializerSlots j≠i := by
  intro j he
  have hv := congrArg Fin.val he
  have n20 : i.val≠20 := fun h=>h20 (Fin.ext h)
  have n25 : i.val≠25 := fun h=>h25 (Fin.ext h)
  have n145 : i.val≠145 := fun h=>h145 (Fin.ext h)
  dsimp only [serializerSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem serializer_input {n : ℕ} (c : BooleanCircuit n) :
    Serialize.input c=coldData n c.nodes.length c.output.val (graph c) := by
  funext i
  refine Fin.addCases (m:=1374) (n:=132) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=1372) (n:=2) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=1371) (n:=1) (fun l=>?_) (fun l=>?_) k
      · refine Fin.addCases (m:=1370) (n:=1) (fun m=>?_) (fun m=>?_) l
        · simp only [Serialize.input,Cold.framedInput,AppendOutputFrame.input,
            AppendOutputLength.input,Cold.circuitInput,Fin.addCases_left,Cold.input,
            Reuse.source,Reuse.nativeWords,List.nil_append,List.append_nil,graph,coldData]
          simp only [Fin.ext_iff,Fin.val_castAdd]
          norm_num
        · have hm : m=0 := Fin.eq_zero m
          subst hm
          rfl
      · have hl : l=0 := Fin.eq_zero l
        subst hl
        rfl
    · fin_cases k <;> rfl
  · have hj := j.isLt
    have h0 : (j.natAdd 1374 : Fin 1506)≠0 := by
      intro he;have hv:=congrArg Fin.val he;change 1374+j.val=0 at hv;omega
    have h1062 : (j.natAdd 1374 : Fin 1506)≠1062 := by
      intro he;have hv:=congrArg Fin.val he;change 1374+j.val=1062 at hv;omega
    have h1339 : (j.natAdd 1374 : Fin 1506)≠1339 := by
      intro he;have hv:=congrArg Fin.val he;change 1374+j.val=1339 at hv;omega
    have h1342 : (j.natAdd 1374 : Fin 1506)≠1342 := by
      intro he;have hv:=congrArg Fin.val he;change 1374+j.val=1342 at hv;omega
    simp only [Serialize.input,Fin.addCases_right,coldData,if_neg h0,if_neg h1062,if_neg h1339,if_neg h1342]

theorem padded_input {n : ℕ} (B : ℕ) (c : BooleanCircuit n) (i : Fin 1506) :
    ZeroPadding.pad (serializerCaps B i) (Serialize.input c i)=
      (if i=0 then List.replicate n true else if i=1062 then graph c else
        if i=1339 then List.replicate c.output.val true else if i=1342 then
          ZeroPadding.pad B (List.replicate c.nodes.length true) else []) := by
  rw [serializer_input]
  by_cases hi : i=1342
  · subst i
    rfl
  · simp only [serializerCaps,if_neg hi,ZeroPadding.pad_zero,coldData]

end NearCubicWires.RepairOrdinary.RecoveryBoundedGraphSerialize
