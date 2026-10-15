import Proof.SourceAssembly.SourceRequestThrParity
import Proof.SourceAssembly.SourceRequestFactorLoop
import Proof.SourceAssembly.SourceFrameOuter
import Proof.SourceAssembly.SourceTopNative
import Proof.SourceAssembly.SourceSingletonRequest

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity RepairSource.VerifierDecoding
open RepairSource.ProjectionNormalization SupplierPipeline CompilerSemantics
noncomputable section

namespace NearCubicWires.SourceRequest.Gen.SupportFrame

theorem pair_support_forward : CursorRestore.NoLeft (CloseoutRowsTupleSeek.pairMachine true) 3 :=
  CursorRestore.composition_forward _ _ _
    (SourceAssemblyCircuitFrame.fresh_forward _ (1 : Fin 2))
    (CursorRestore.focus_forward CloseoutRowsTupleSeek.supportSlots (by decide) _ 1
      SourceAssemblyCircuitFrame.frame_forward)

theorem assembler_support_forward :
    CursorRestore.NoLeft SourceAssemblySymmetricAssemble.machine 6 :=
  CursorRestore.composition_forward _ _ _
    (EquationRowCuts.unselected_forward _ _ 6 (by decide))
    (CursorRestore.composition_forward _ _ _
      (EquationRowCuts.unselected_forward _ _ 6 (by decide))
      (CursorRestore.focus_forward _ (by decide) _ 3 (CursorRestore.repeat_forward _ _ 3 pair_support_forward)))

theorem support_forward : CursorRestore.NoLeft Gen.ThresholdPhysical.machine 208 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.composition_forward _ _ _
      (SourceAssemblyCircuitFrame.fresh_forward _ (2 : Fin 4))
      (EquationRowCuts.unselected_forward _ _ 208 (by decide)))
    (CursorRestore.focus_forward _ SourceAssemblyThresholdPhysical.slots_inj _ 6
      assembler_support_forward)

def machine:=AppendOutputFrame.machine Gen.ThresholdPhysical.machine 208

/-- The support stream of the parity circuit, framed, on tape 212; every head `0`. -/
theorem run {q : Nat} (S : Finset (Fin q)) (Q : Nat) :
    let bm:=SourceAssemblySymmetricMeaning.bitmap S
    let w:=CloseoutRowsTupleSeek.supportWord (SourceAssemblyThresholdPhysical.gates q S.card bm)
    ∃ A,Step machine (2*Gen.ThresholdPhysical.budget q Q bm (Gen.ThresholdCanonical.bitmap_length S)+
        4*w.length+7) (fun _=>0)
      (AppendOutputFrame.input (Gen.ThresholdReady.input q Q bm)) (fun _=>0) A ∧
      A 212=frame w := by
  intro bm w
  have hbm : bm.length = q := Gen.ThresholdCanonical.bitmap_length S
  obtain ⟨A,⟨source,hr,rh,rt,rs⟩,hn,hs,h131⟩:=Gen.ThresholdPhysical.run_retained q Q bm hbm
  have hcount : Gen.SymmetricHeaderQuery.count q Q bm = S.card :=
    SourceAssemblySymmetricMeaning.count_eq S Q
  have hs' : A 208 = w := by rw [hs, hcount]; rfl
  have hh : source.final.heads 208 = w.length := by
    rw [rh]
    change Gen.ThresholdPhysical.finalHeads q Q bm hbm (SourceAssemblyThresholdPhysical.slots 6)=_
    rw [Gen.ThresholdPhysical.finalHeads,dockH_slot _ SourceAssemblyThresholdPhysical.slots_inj _ _ 6]
    change (CloseoutRowsTupleSeek.supportWord (SourceAssemblyThresholdPhysical.gates q
      (Gen.SymmetricHeaderQuery.count q Q bm) (Gen.ThresholdCache.bits q Q bm hbm))).length=_
    rw [hcount]; rfl
  obtain ⟨s,sr,st,sh,sk,ss⟩:=PCPPNativeFrame.frame_run
    Gen.ThresholdPhysical.machine 208 support_forward
    (Gen.ThresholdPhysical.budget q Q bm hbm) (Gen.ThresholdReady.input q Q bm) source hr w
    (by rw [rt];exact hs') hh
  exact ⟨s.final.tapes,(Step.of_run sr (funext sh) rfl).enlarge (by omega),st⟩

end NearCubicWires.SourceRequest.Gen.SupportFrame

namespace NearCubicWires.SourceRequest.Gen.ChainIn

theorem addCases_nil {m n : Nat} (f : Fin m → List Bool) (i : Fin (m + n)) :
    Fin.addCases (motive := fun _ => List Bool) f (fun _ : Fin n => []) i
      = if h : i.val < m then f ⟨i.val, h⟩ else [] := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left, dif_pos (by simp)]; rfl
  · rw [Fin.addCases_right, dif_neg (by simp)]

/-- The generic chain's entry value at tape number `n`: bitmap on 3, arity template on 13, blank. -/
def chainAt (q Q : Nat) (bm : List Bool) (n : Nat) : List Bool :=
  if n = 3 then ZeroPadding.pad Q bm else if n = 13 then UnaryTemplate.tape q else []

theorem chainAt_high (q Q : Nat) (bm : List Bool) (n : Nat) (h : 137 ≤ n) : chainAt q Q bm n = [] := by
  unfold chainAt; rw [if_neg (by omega), if_neg (by omega)]

theorem lvl0 (q Q : Nat) (bm : List Bool) (i : Fin 137) :
    Gen.ParityQuery.input q Q bm i = chainAt q Q bm i.val := by
  unfold Gen.ParityQuery.input chainAt
  by_cases h3 : i.val = 3
  · rw [if_pos (Fin.ext h3), if_pos h3]
  · rw [if_neg (fun e => h3 (by rw [e]; rfl)), if_neg h3]
    by_cases h13 : i.val = 13
    · rw [if_pos (Fin.ext h13), if_pos h13]
    · rw [if_neg (fun e => h13 (by rw [e]; rfl)), if_neg h13]

theorem step {m n : Nat} (f : Fin m → List Bool) (q Q : Nat) (bm : List Bool) (hm : 137 ≤ m)
    (hf : ∀ j : Fin m, f j = chainAt q Q bm j.val) (i : Fin (m + n)) :
    Fin.addCases (motive := fun _ => List Bool) f (fun _ : Fin n => []) i = chainAt q Q bm i.val := by
  rw [addCases_nil]
  by_cases h : i.val < m
  · rw [dif_pos h, hf]
  · rw [dif_neg h, chainAt_high q Q bm _ (by omega)]

theorem lvl1 (q Q : Nat) (bm : List Bool) (i : Fin 141) :
    Gen.SymmetricQuery.input q Q bm i = chainAt q Q bm i.val :=
  step (n := 4) _ q Q bm (by omega) (lvl0 q Q bm) i
theorem lvl2 (q Q : Nat) (bm : List Bool) (i : Fin 166) :
    Gen.SymmetricHeaderQuery.input q Q bm i = chainAt q Q bm i.val :=
  step (n := 25) _ q Q bm (by omega) (lvl1 q Q bm) i
theorem lvl3 (q Q : Nat) (bm : List Bool) (i : Fin 170) :
    Gen.ThresholdCache.input q Q bm i = chainAt q Q bm i.val :=
  step (n := 4) _ q Q bm (by omega) (lvl2 q Q bm) i
theorem lvl4 (q Q : Nat) (bm : List Bool) (i : Fin 203) :
    Gen.ThresholdQuery.input q Q bm i = chainAt q Q bm i.val :=
  step (n := 33) _ q Q bm (by omega) (lvl3 q Q bm) i
theorem lvl5 (q Q : Nat) (bm : List Bool) (i : Fin 206) :
    Gen.ThresholdTopQuery.input q Q bm i = chainAt q Q bm i.val :=
  step (n := 3) _ q Q bm (by omega) (lvl4 q Q bm) i
theorem lvl6 (q Q : Nat) (bm : List Bool) (i : Fin 210) :
    Gen.ThresholdReady.input q Q bm i = chainAt q Q bm i.val :=
  step (n := 4) _ q Q bm (by omega) (lvl5 q Q bm) i
theorem lvl7 (q Q : Nat) (bm : List Bool) (i : Fin 211) :
    AppendOutputLength.input (Gen.ThresholdReady.input q Q bm) i = chainAt q Q bm i.val :=
  step (n := 1) _ q Q bm (by omega) (lvl6 q Q bm) i
theorem lvl8 (q Q : Nat) (bm : List Bool) (i : Fin 212) :
    AppendOutputLength.input (AppendOutputLength.input (Gen.ThresholdReady.input q Q bm)) i
      = chainAt q Q bm i.val :=
  step (n := 1) _ q Q bm (by omega) (lvl7 q Q bm) i

/-- **The generic chain's entry**, tape by tape. -/
theorem input_at (q Q : Nat) (bm : List Bool) (i : Fin 214) :
    AppendOutputFrame.input (Gen.ThresholdReady.input q Q bm) i = chainAt q Q bm i.val :=
  step (n := 2) _ q Q bm (by omega) (lvl8 q Q bm) i

end NearCubicWires.SourceRequest.Gen.ChainIn

namespace NearCubicWires.SourceRequest.ThrSystematic
open PacketProduction
open SourceAssemblySymmetricMeaning (bitmap)

abbrev T (a : DecompositionAlgorithm) : Nat := SourceAssemblyTopNative.tapes a
theorem T_eq (a : DecompositionAlgorithm) : T a = 4 + ((DecompositionSource.Counted.tapes a + 2) + 2) := rfl

/-- TopNative's output tape. -/
def oT (a : DecompositionAlgorithm) : Fin (T a) :=
  SourceAssemblyTopNative.slots a ((0 : Fin 2).natAdd (DecompositionSource.Counted.tapes a + 2))
theorem oT_val (a : DecompositionAlgorithm) : (oT a).val = DecompositionSource.Counted.tapes a + 6 := by
  unfold oT SourceAssemblyTopNative.slots
  rw [if_neg (by simp)]
  simp only [Fin.val_natAdd, Fin.val_zero]
  omega

def bVal (i : Nat) : Nat := if i = 0 then 212 else 213 + i
def cVal (i : Nat) : Nat := if i = 0 then 207 else 218 + i
def eVal (a : DecompositionAlgorithm) (i : Nat) : Nat := if i = 0 then 224 + DecompositionSource.Counted.tapes a else 217 + T a + i
def dVal (a : DecompositionAlgorithm) (i : Nat) : Nat := 223 + T a + i
def descVal (a : DecompositionAlgorithm) (k : Nat) : Nat :=
  if k = 0 then 3 else if k = 1 then 13 else if k = 2 then 226 + T a else 236 + T a

def slotA (a : DecompositionAlgorithm) (i : Fin 214) : Fin (437 + T a) := ⟨i.val, by omega⟩
def slotB (a : DecompositionAlgorithm) (i : Fin 6) : Fin (437 + T a) :=
  ⟨bVal i.val, by have := i.isLt; unfold bVal; split_ifs <;> omega⟩
def slotC (a : DecompositionAlgorithm) (i : Fin (T a)) : Fin (437 + T a) :=
  ⟨cVal i.val, by have := i.isLt; unfold cVal; split_ifs <;> omega⟩
def slotE (a : DecompositionAlgorithm) (i : Fin 6) : Fin (437 + T a) :=
  ⟨eVal a i.val, by have := i.isLt; have := T_eq a; unfold eVal; split_ifs <;> omega⟩
def slotD (a : DecompositionAlgorithm) (i : Fin 214) : Fin (437 + T a) :=
  ⟨dVal a i.val, by have := i.isLt; unfold dVal; omega⟩
def descSlots (a : DecompositionAlgorithm) (k : Fin 4) : Fin (437 + T a) :=
  ⟨descVal a k.val, by have := k.isLt; unfold descVal; split_ifs <;> omega⟩

theorem slotA_inj (a : DecompositionAlgorithm) : Function.Injective (slotA a) := by
  intro i j h
  have hv : (slotA a i).val = (slotA a j).val := congrArg Fin.val h
  exact Fin.ext hv
theorem slotB_inj (a : DecompositionAlgorithm) : Function.Injective (slotB a) := by
  intro i j h
  have hv : bVal i.val = bVal j.val := congrArg Fin.val h
  apply Fin.ext
  unfold bVal at hv
  split_ifs at hv <;> omega
theorem slotC_inj (a : DecompositionAlgorithm) : Function.Injective (slotC a) := by
  intro i j h
  have hv : cVal i.val = cVal j.val := congrArg Fin.val h
  apply Fin.ext
  unfold cVal at hv
  split_ifs at hv <;> omega
theorem slotE_inj (a : DecompositionAlgorithm) : Function.Injective (slotE a) := by
  intro i j h
  have hv : eVal a i.val = eVal a j.val := congrArg Fin.val h
  have := T_eq a
  apply Fin.ext
  unfold eVal at hv
  split_ifs at hv <;> omega
theorem slotD_inj (a : DecompositionAlgorithm) : Function.Injective (slotD a) := by
  intro i j h
  have hv : dVal a i.val = dVal a j.val := congrArg Fin.val h
  apply Fin.ext
  unfold dVal at hv
  omega
theorem descSlots_inj (a : DecompositionAlgorithm) : Function.Injective (descSlots a) := by
  intro i j h
  have hv : descVal a i.val = descVal a j.val := congrArg Fin.val h
  have := i.isLt
  have := j.isLt
  apply Fin.ext
  unfold descVal at hv
  split_ifs at hv <;> omega

theorem away {t u : Nat} (s : Fin t → Fin u) (x : Fin u) (h : ∀ j, (s j).val ≠ x.val) :
    ∀ j, s j ≠ x :=
  fun j e => h j (congrArg Fin.val e)

/-- The four descriptor words: the literal's support bitmap and the arity template, once per chain. -/
def desc (q : Nat) (bm : List Bool) (k : Fin 4) : List Bool :=
  if k.val = 0 ∨ k.val = 2 then bm else UnaryTemplate.tape q

def entryVal (a : DecompositionAlgorithm) (q : Nat) (bm : List Bool) (x : Nat) : List Bool :=
  if x < 214 then Gen.ChainIn.chainAt q 0 bm x
  else if 223 + T a ≤ x then Gen.ChainIn.chainAt q 0 bm (x - (223 + T a)) else []

def st0 (a : DecompositionAlgorithm) (q : Nat) (bm : List Bool) : Fin (437 + T a) → List Bool :=
  fun x => entryVal a q bm x.val

theorem entry_eq (a : DecompositionAlgorithm) (q : Nat) (bm : List Bool) :
    install (descSlots a) (fun _ => []) (desc q bm) = st0 a q bm := by
  funext x
  by_cases hx : ∃ k, descSlots a k = x
  · obtain ⟨k, rfl⟩ := hx
    rw [install_slot _ (descSlots_inj a)]
    have hk := k.isLt
    show desc q bm k = entryVal a q bm (descVal a k.val)
    unfold desc descVal entryVal Gen.ChainIn.chainAt
    by_cases h0 : k.val = 0
    · rw [if_pos (Or.inl h0), if_pos h0, if_pos (by omega), if_pos rfl, ZeroPadding.pad_zero]
    · by_cases h1 : k.val = 1
      · rw [if_neg (by omega), if_neg h0, if_pos h1, if_pos (by omega), if_neg (by omega), if_pos rfl]
      · by_cases h2 : k.val = 2
        · rw [if_pos (Or.inr h2), if_neg h0, if_neg h1, if_pos h2, if_neg (by omega), if_pos (by omega),
            show 226 + T a - (223 + T a) = 3 by omega, if_pos rfl, ZeroPadding.pad_zero]
        · rw [if_neg (by omega), if_neg h0, if_neg h1, if_neg h2, if_neg (by omega), if_pos (by omega),
            show 236 + T a - (223 + T a) = 13 by omega, if_neg (by omega), if_pos rfl]
  · rw [install_other _ _ _ _ (fun k e => hx ⟨k, e⟩)]
    have n0 : x.val ≠ 3 := fun e => hx ⟨0, Fin.ext e.symm⟩
    have n1 : x.val ≠ 13 := fun e => hx ⟨1, Fin.ext e.symm⟩
    have n2 : x.val ≠ 226 + T a := fun e => hx ⟨2, Fin.ext e.symm⟩
    have n3 : x.val ≠ 236 + T a := fun e => hx ⟨3, Fin.ext e.symm⟩
    show [] = entryVal a q bm x.val
    unfold entryVal Gen.ChainIn.chainAt
    split_ifs <;> first | rfl | omega

theorem fo_input (bits : List Bool) (j : Fin 6) :
    AppendOutputFrame.input (![bits, []] : Fin 2 → List Bool) j = if j.val = 0 then bits else [] := by
  match j with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨n + 6, h⟩ => exact absurd h (by omega)

/-! ### Stage entries -/

theorem A_entry (a : DecompositionAlgorithm) (q : Nat) (bm : List Bool) (j : Fin 214) :
    st0 a q bm (slotA a j) = AppendOutputFrame.input (Gen.ThresholdReady.input q 0 bm) j := by
  rw [Gen.ChainIn.input_at]
  show entryVal a q bm j.val = _
  unfold entryVal
  rw [if_pos j.isLt]

theorem B_entry (a : DecompositionAlgorithm) (q : Nat) (bm : List Bool) (A1 : Fin 214 → List Bool)
    (w : List Bool) (h212 : A1 212 = w) (j : Fin 6) :
    install (slotA a) (st0 a q bm) A1 (slotB a j) = AppendOutputFrame.input (![w, []] : Fin 2 → List Bool) j := by
  rw [fo_input]
  by_cases h0 : j.val = 0
  · rw [if_pos h0, show slotB a j = slotA a 212 from Fin.ext (by show bVal j.val = 212; unfold bVal; rw [if_pos h0]),
      install_slot _ (slotA_inj a), h212]
  · have hj := j.isLt
    rw [if_neg h0, install_other _ _ _ _ (away _ _ (fun k => by
      have := k.isLt; show k.val ≠ bVal j.val; unfold bVal; rw [if_neg h0]; omega))]
    show entryVal a q bm (bVal j.val) = []
    unfold bVal entryVal
    rw [if_neg h0, if_neg (by omega), if_neg (by omega)]

theorem C_entry (a : DecompositionAlgorithm) (q : Nat) (bm : List Bool) (A1 : Fin 214 → List Bool)
    (B1 : Fin 6 → List Bool) (w : List Bool) (h207 : A1 207 = w) (j : Fin (T a)) :
    install (slotB a) (install (slotA a) (st0 a q bm) A1) B1 (slotC a j) = if j.val = 0 then w else [] := by
  have hj := j.isLt
  have hT := T_eq a
  rw [install_other _ _ _ _ (away _ _ (fun k => by
    have := k.isLt; show bVal k.val ≠ cVal j.val; unfold bVal cVal; split_ifs <;> omega))]
  by_cases h0 : j.val = 0
  · rw [if_pos h0, show slotC a j = slotA a 207 from Fin.ext (by show cVal j.val = 207; unfold cVal; rw [if_pos h0]),
      install_slot _ (slotA_inj a), h207]
  · rw [if_neg h0, install_other _ _ _ _ (away _ _ (fun k => by
      have := k.isLt; show k.val ≠ cVal j.val; unfold cVal; rw [if_neg h0]; omega))]
    show entryVal a q bm (cVal j.val) = []
    unfold cVal entryVal
    rw [if_neg h0, if_neg (by omega), if_neg (by omega)]

theorem E_entry (a : DecompositionAlgorithm) (q : Nat) (bm : List Bool) (A1 : Fin 214 → List Bool)
    (B1 : Fin 6 → List Bool) (C1 : Fin (T a) → List Bool) (w : List Bool) (hC : C1 (oT a) = w) (j : Fin 6) :
    install (slotC a) (install (slotB a) (install (slotA a) (st0 a q bm) A1) B1) C1 (slotE a j)
      = AppendOutputFrame.input (![w, []] : Fin 2 → List Bool) j := by
  have hj := j.isLt
  have hT := T_eq a
  have ho := oT_val a
  rw [fo_input]
  by_cases h0 : j.val = 0
  · rw [if_pos h0, show slotE a j = slotC a (oT a) from Fin.ext (by
      show eVal a j.val = cVal (oT a).val; unfold eVal cVal; rw [if_pos h0, if_neg (by omega)]; omega),
      install_slot _ (slotC_inj a), hC]
  · rw [if_neg h0,
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show cVal k.val ≠ eVal a j.val; unfold cVal eVal; split_ifs <;> omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show bVal k.val ≠ eVal a j.val; unfold bVal eVal; split_ifs <;> omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show k.val ≠ eVal a j.val; unfold eVal; rw [if_neg h0]; omega))]
    show entryVal a q bm (eVal a j.val) = []
    unfold eVal entryVal
    rw [if_neg h0, if_neg (by omega), if_neg (by omega)]

theorem D_entry (a : DecompositionAlgorithm) (q : Nat) (bm : List Bool) (A1 : Fin 214 → List Bool)
    (B1 : Fin 6 → List Bool) (C1 : Fin (T a) → List Bool) (E1 : Fin 6 → List Bool) (j : Fin 214) :
    install (slotE a) (install (slotC a) (install (slotB a) (install (slotA a) (st0 a q bm) A1) B1) C1) E1
      (slotD a j) = AppendOutputFrame.input (Gen.ThresholdReady.input q 0 bm) j := by
  have hj := j.isLt
  have hT := T_eq a
  rw [install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show eVal a k.val ≠ dVal a j.val; unfold eVal dVal; split_ifs <;> omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show cVal k.val ≠ dVal a j.val; unfold cVal dVal; split_ifs <;> omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show bVal k.val ≠ dVal a j.val; unfold bVal dVal; split_ifs <;> omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show k.val ≠ dVal a j.val; unfold dVal; omega)),
      Gen.ChainIn.input_at]
  show entryVal a q bm (dVal a j.val) = _
  unfold dVal entryVal
  rw [if_neg (by omega), if_pos (by omega), show 223 + T a + j.val - (223 + T a) = j.val by omega]

/-! ### The machine and its run -/

def outN (a : DecompositionAlgorithm) : Fin (437 + T a) := slotB a 4
def outT (a : DecompositionAlgorithm) : Fin (437 + T a) := slotE a 4
def outS (a : DecompositionAlgorithm) : Fin (437 + T a) := slotD a 212

def machine (a : DecompositionAlgorithm) :=
  Composition.machine (RecoveryFocus.machine (slotA a) Gen.CircuitFrame.machine)
    (Composition.machine (RecoveryFocus.machine (slotB a) SourceAssemblyFrameOuter.machine)
      (Composition.machine (RecoveryFocus.machine (slotC a) (SourceAssemblyTopNative.machine a))
        (Composition.machine (RecoveryFocus.machine (slotE a) SourceAssemblyFrameOuter.machine)
          (RecoveryFocus.machine (slotD a) Gen.SupportFrame.machine))))

/-- The five stages' cost at the support `S`. -/
def cost (a : DecompositionAlgorithm) {q : Nat} (S : Finset (Fin q)) : Nat :=
  let c := normalizedThresholdParityCircuit S
  let bm := bitmap S
  let chain := 2*Gen.ThresholdPhysical.budget q 0 bm (Gen.ThresholdCanonical.bitmap_length S)
  (chain + 4*(thrWord c).length + 7) + 1 +
    ((12*(thrWord c).length + 13) + 1 +
      (SourceAssemblyTopNative.budget a c.top.wireCount
          ⟨c.top.support.card, nonStrictAsStrict (SupplierPipeline.retainedTopGate c)⟩ + 1 +
        ((12*(natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c)).length + 13) + 1 +
          (chain + 4*(CloseoutRowsTupleSeek.supportWord
            (SourceAssemblyThresholdPhysical.gates q S.card bm)).length + 7))))

theorem zeroH {t u : Nat} (s : Fin t → Fin u) : dockH s (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing s _ _ (fun _ => rfl)

theorem exact_run (a : DecompositionAlgorithm) {q : Nat} (S : Finset (Fin q)) :
    ∃ F, Step (machine a) (cost a S) (fun _ => 0) (st0 a q (bitmap S)) (fun _ => 0) F ∧
      F (outN a) = frame (frame (thrWord (normalizedThresholdParityCircuit S))) ∧
      F (outS a) = frame (CloseoutRowsTupleSeek.supportWord
        (SourceAssemblyThresholdPhysical.gates q S.card (bitmap S))) ∧
      F (outT a) = frame (frame (natWord (normalizedThresholdParityCircuit S).top.support.card ++
        exactListWord (ThresholdRows.children a (normalizedThresholdParityCircuit S)))) := by
  obtain ⟨A1, sA, a212, a207, -, -⟩ := Gen.CircuitFrame.run S 0
  obtain ⟨B1, sB, b4⟩ := SourceAssemblyFrameOuter.run
    (thrWord (normalizedThresholdParityCircuit S))
  obtain ⟨C1, sC, cOut, -⟩ := SourceAssemblyTopNative.threshold_run a
    (normalizedThresholdParityCircuit S)
  obtain ⟨E1, sE, e4⟩ := SourceAssemblyFrameOuter.run
    (natWord (normalizedThresholdParityCircuit S).top.support.card ++
      exactListWord (ThresholdRows.children a (normalizedThresholdParityCircuit S)))
  obtain ⟨D1, sD, d212⟩ := Gen.SupportFrame.run S 0
  have dA := sA.dock (slotA a) (slotA_inj a) (fun _ => 0) (st0 a q (bitmap S)) (fun _ => rfl)
    (A_entry a q _)
  rw [zeroH] at dA
  have dB := sB.dock (slotB a) (slotB_inj a) (fun _ => 0) (install (slotA a) (st0 a q (bitmap S)) A1) (fun _ => rfl)
    (B_entry a q (bitmap S) A1 _ a212)
  rw [zeroH] at dB
  have dC := sC.dock (slotC a) (slotC_inj a) (fun _ => 0)
    (install (slotB a) (install (slotA a) (st0 a q (bitmap S)) A1) B1) (fun _ => rfl)
    (C_entry a q (bitmap S) A1 B1 _ a207)
  rw [zeroH] at dC
  have dE := sE.dock (slotE a) (slotE_inj a) (fun _ => 0)
    (install (slotC a) (install (slotB a) (install (slotA a) (st0 a q (bitmap S)) A1) B1) C1) (fun _ => rfl)
    (E_entry a q (bitmap S) A1 B1 C1 _ cOut)
  rw [zeroH] at dE
  have dD := sD.dock (slotD a) (slotD_inj a) (fun _ => 0)
    (install (slotE a) (install (slotC a) (install (slotB a) (install (slotA a) (st0 a q (bitmap S)) A1) B1) C1) E1)
    (fun _ => rfl) (D_entry a q (bitmap S) A1 B1 C1 E1)
  rw [zeroH] at dD
  have hT := T_eq a
  have ho := oT_val a
  refine ⟨_, dA.seq (dB.seq (dC.seq (dE.seq dD))), ?_, ?_, ?_⟩
  · -- outN = slotB 4
    rw [outN,
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show dVal a k.val ≠ 217; unfold dVal; omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show eVal a k.val ≠ bVal 4; unfold eVal bVal; split_ifs <;> omega)),
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show cVal k.val ≠ bVal 4; unfold cVal bVal; split_ifs <;> omega)),
      install_slot _ (slotB_inj a), b4]
  · rw [outS, install_slot _ (slotD_inj a), d212]
  · rw [outT,
      install_other _ _ _ _ (away _ _ (fun k => by
        have := k.isLt; show dVal a k.val ≠ 217 + T a + 4; unfold dVal; omega)),
      install_slot _ (slotE_inj a), e4]

section normal
open SupplierEstimator NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

/-- The support segment of a systematic THR factor is the parity circuit's declared-support stream. -/
theorem supSeg_systematic (a : DecompositionAlgorithm) (idx : Fin pcpp.systematicBits) :
    supSeg false (C10TotalDecode.Atom.systematic idx : C10TotalDecode.Atom pcpp) =
      CloseoutRowsTupleSeek.supportWord (SourceAssemblyThresholdPhysical.gates q
        (pcpp.systematicSupport idx).card (bitmap (pcpp.systematicSupport idx))) := by
  have h1 := NearCubicWires.SourceRequest.support_eq a 0 0 false
    [(C10TotalDecode.Atom.systematic idx : C10TotalDecode.Atom pcpp)] (by simp)
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h1
  rw [SourceAssemblySingletonRequest.support_eq (pcpp.systematicSupport idx) 0 0 a, ← h1]
  rfl

theorem produce (a : DecompositionAlgorithm) (idx : Fin pcpp.systematicBits) (R : Nat) :
    ∃ F, Step (machine a) (cost a (pcpp.systematicSupport idx)) (fun _ => 0)
      (install (descSlots a) (fun _ => List.replicate R false)
        (fun k => ZeroPadding.pad R (desc q (bitmap (pcpp.systematicSupport idx)) k)))
      (fun _ => 0) F ∧
      F (outN a) = ZeroPadding.pad R (RepairOrdinary.frame
        (FactorLoop.segN false (some (C10TotalDecode.Atom.systematic idx : C10TotalDecode.Atom pcpp)))) ∧
      F (outS a) = ZeroPadding.pad R (RepairOrdinary.frame
        (FactorLoop.segS false (some (C10TotalDecode.Atom.systematic idx : C10TotalDecode.Atom pcpp)))) ∧
      F (outT a) = ZeroPadding.pad R (RepairOrdinary.frame
        (FactorLoop.segT a false (some (C10TotalDecode.Atom.systematic idx : C10TotalDecode.Atom pcpp)))) := by
  obtain ⟨F, hF, hN, hS, hT⟩ := exact_run a (pcpp.systematicSupport idx)
  have hnil : (fun _ : Fin (437 + T a) => ZeroPadding.pad R ([] : List Bool))
      = fun _ => List.replicate R false := by
    funext i
    simp [ZeroPadding.pad]
  refine ⟨_, (hF.pad (fun _ => R)).congr_in rfl ?_, ?_, ?_, ?_⟩
  · rw [← entry_eq]
    refine (SourceAssemblyReuse.pad_install (descSlots a) (fun _ => R) (fun _ => [])
      (desc q (bitmap (pcpp.systematicSupport idx)))).trans ?_
    show install (descSlots a) (fun _ => ZeroPadding.pad R []) _ = _
    rw [hnil]
  · show ZeroPadding.pad R (F (outN a)) = _
    rw [hN]
    rfl
  · show ZeroPadding.pad R (F (outS a)) = _
    rw [hS, ← supSeg_systematic a idx]
    rfl
  · show ZeroPadding.pad R (F (outT a)) = _
    rw [hT]
    rfl

end normal
end NearCubicWires.SourceRequest.ThrSystematic

