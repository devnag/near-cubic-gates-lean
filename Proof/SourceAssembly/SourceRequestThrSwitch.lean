import Proof.SourceAssembly.SourceRequestThrOriginal
import Proof.Amplification.RecoveryWitnessPolicy
import Proof.MachineModel.OrdinarySignedSortKey

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open SupplierPipeline CanonicalWitnessCodec RadixSemantics SourceInterfaces CompilerSemantics
noncomputable section

namespace NearCubicWires.SourceRequest.ThrSwitch
open PacketProduction
open SourceAssemblySymmetricMeaning (bitmap)

/-! ## The original factor's code -/

theorem witness_code {q : Nat} (c : NormalizedThresholdThresholdCircuit q) :
    thresholdCircuitCodec.encode c = encodeNormalizedThresholdThresholdCircuit c := by
  simp only [thresholdCircuitCodec]

/-- The admission width of an original THR code at description cap `L`. -/
def codeWidth (L : Nat) : Nat := RecoveryWitnessPolicy.canonicalThresholdCircuitCodeBitBound L

/-- The original factor's code bits: the witness code in fixed-width binary at the admission width. -/
def codeBits (L : Nat) {q : Nat} (c : NormalizedThresholdThresholdCircuit q) : List Bool :=
  SignedSortKey.binary (codeWidth L) (encodeNormalizedThresholdThresholdCircuit c)

theorem codeBits_length (L : Nat) {q : Nat} (c : NormalizedThresholdThresholdCircuit q) :
    (codeBits L c).length = codeWidth L :=
  SignedSortKey.binary_length _ _

theorem code_lt (value : Nat) : value < 2 ^ natBitLength value := by
  simpa [natBitLength] using Nat.lt_pow_succ_log_self (b := 2) (by omega) value

theorem codeBits_decode (L : Nat) {q : Nat} (c : NormalizedThresholdThresholdCircuit q)
    (h4 : 4 ≤ L) (hL : c.descriptionBits ≤ L) :
    decodeNormalizedThresholdThresholdCircuit q (value (codeBits L c)) = some c := by
  have hb := RecoveryWitnessPolicy.encodeNormalizedThresholdCircuit_bits_le_parameter c h4 hL
  have hlt : encodeNormalizedThresholdThresholdCircuit c < 2 ^ codeWidth L :=
    lt_of_lt_of_le (code_lt _) (Nat.pow_le_pow_right (by omega) hb)
  unfold codeBits
  rw [SignedSortKey.binary_value _ _ hlt]
  exact decodeNormalizedThresholdThresholdCircuit_encode c

/-! ## Layout (`Fin (3864 + 2T)`; one arithmetic atom `T = ThrOriginal.Tn a`) -/

open ThrOriginal (Tn Tn_eq)

theorem T_ge (a : DecompositionAlgorithm) : 8 ≤ Tn a := by
  have := Tn_eq a
  omega

/-- The original producer's tape `j` in the universe (its outputs onto the systematic outputs). -/
def origVal (a : DecompositionAlgorithm) (j : Nat) : Nat :=
  if j = 1711 then 217 else if j = 3423 + Tn a then 435 + Tn a else if j = 1715 + Tn a then 221 + Tn a
  else 437 + Tn a + j

def sysSlot (a : DecompositionAlgorithm) (j : Fin (437 + Tn a)) : Fin (3864 + 2 * Tn a) :=
  ⟨j.val, by omega⟩
def origSlot (a : DecompositionAlgorithm) (j : Fin (3425 + Tn a)) : Fin (3864 + 2 * Tn a) :=
  ⟨origVal a j.val, by have := j.isLt; unfold origVal; split_ifs <;> omega⟩

theorem sysSlot_inj (a : DecompositionAlgorithm) : Function.Injective (sysSlot a) := by
  intro i j h
  have hv : (sysSlot a i).val = (sysSlot a j).val := congrArg Fin.val h
  exact Fin.ext hv

theorem origSlot_inj (a : DecompositionAlgorithm) : Function.Injective (origSlot a) := by
  intro i j h
  have hv : origVal a i.val = origVal a j.val := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  have hT := T_ge a
  apply Fin.ext
  unfold origVal at hv
  split_ifs at hv <;> omega

def flagS (a : DecompositionAlgorithm) : Fin (3864 + 2 * Tn a) := ⟨3862 + 2 * Tn a, by omega⟩
def flagO (a : DecompositionAlgorithm) : Fin (3864 + 2 * Tn a) := ⟨3863 + 2 * Tn a, by omega⟩

/-- `ThrSystematic.descVal` in the switch's arithmetic atom. -/
def sysDescVal (a : DecompositionAlgorithm) (k : Nat) : Nat :=
  if k = 0 then 3 else if k = 1 then 13 else if k = 2 then 226 + Tn a else 236 + Tn a
theorem sysDescVal_eq (a : DecompositionAlgorithm) (k : Nat) :
    ThrSystematic.descVal a k = sysDescVal a k := rfl

/-- The sixteen descriptor tapes: the systematic producer's 4, the original producer's 10, two flags. -/
def descVal (a : DecompositionAlgorithm) (k : Nat) : Nat :=
  if k < 4 then sysDescVal a k
  else if k < 14 then 437 + Tn a + ThrOriginal.descVal a (k - 4) else 3862 + 2 * Tn a + (k - 14)

theorem sysDesc_range (a : DecompositionAlgorithm) (k : Nat) :
    sysDescVal a k = 3 ∨ sysDescVal a k = 13 ∨ sysDescVal a k = 226 + Tn a ∨ sysDescVal a k = 236 + Tn a := by
  unfold sysDescVal
  split_ifs <;> simp

theorem origDesc_range (a : DecompositionAlgorithm) (k : Nat) :
    (1 ≤ ThrOriginal.descVal a k ∧ ThrOriginal.descVal a k ≤ 1699) ∨
      (1718 + Tn a ≤ ThrOriginal.descVal a k ∧ ThrOriginal.descVal a k ≤ 3416 + Tn a) := by
  have r1 := ThrOriginal.posVal_range k
  have r2 := ThrOriginal.posVal_range (k - 5)
  unfold ThrOriginal.descVal
  split_ifs
  · exact Or.inl r1
  · exact Or.inr ⟨by omega, by omega⟩

theorem origDesc_val (a : DecompositionAlgorithm) (k : Nat) :
    origVal a (ThrOriginal.descVal a k) = 437 + Tn a + ThrOriginal.descVal a k := by
  have hr := origDesc_range a k
  have hT := T_ge a
  unfold origVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

def descSlots (a : DecompositionAlgorithm) (k : Fin 16) : Fin (3864 + 2 * Tn a) :=
  ⟨descVal a k.val, by
    have hk := k.isLt
    have r1 := sysDesc_range a k.val
    have r2 := origDesc_range a (k.val - 4)
    unfold descVal; split_ifs <;> omega⟩

theorem descSlots_inj (a : DecompositionAlgorithm) : Function.Injective (descSlots a) := by
  intro i j h
  have hv : descVal a i.val = descVal a j.val := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  have s1 := sysDesc_range a i.val
  have s2 := sysDesc_range a j.val
  have o1 := origDesc_range a (i.val - 4)
  have o2 := origDesc_range a (j.val - 4)
  apply Fin.ext
  unfold descVal at hv
  split_ifs at hv with h1 h2 h3 h4 h5 h6 h7
  · have e := congrArg Fin.val (ThrSystematic.descSlots_inj a (a₁ := ⟨i.val, h1⟩) (a₂ := ⟨j.val, h2⟩)
      (Fin.ext (by show ThrSystematic.descVal a i.val = ThrSystematic.descVal a j.val
                   rw [sysDescVal_eq, sysDescVal_eq]; exact hv)))
    exact e
  all_goals first
    | omega
    | (have e := congrArg Fin.val (ThrOriginal.descSlots_inj a (a₁ := ⟨i.val - 4, by omega⟩)
          (a₂ := ⟨j.val - 4, by omega⟩) (Fin.ext (by
            show ThrOriginal.descVal a (i.val - 4) = ThrOriginal.descVal a (j.val - 4)
            omega)))
       simp only at e
       omega)

/-! ## Entries: pulling the switch's descriptor bank back to each producer -/

theorem install_pull {d d' t u : Nat} (s : Fin d → Fin u) (hs : Function.Injective s)
    (g : Fin t → Fin u) (ls : Fin d' → Fin t) (hls : Function.Injective ls)
    (e : Fin d' → Fin d) (he : ∀ k', s (e k') = g (ls k'))
    (hcov : ∀ k j, s k = g j → ∃ k', ls k' = j)
    (B : Fin u → List Bool) (D : Fin d → List Bool) (j : Fin t) :
    install s B D (g j) = install ls (fun i => B (g i)) (fun k' => D (e k')) j := by
  by_cases h : ∃ k', ls k' = j
  · obtain ⟨k', rfl⟩ := h
    rw [← he, install_slot _ hs, install_slot _ hls]
  · rw [install_other _ _ _ _ (fun k' e' => h ⟨k', e'⟩),
      install_other _ _ _ _ (fun k e' => h (hcov k j e'))]

def sysIdx (k : Fin 4) : Fin 16 := ⟨k.val, by omega⟩
def origIdx (k : Fin 10) : Fin 16 := ⟨k.val + 4, by omega⟩

theorem sys_he (a : DecompositionAlgorithm) (k : Fin 4) :
    descSlots a (sysIdx k) = sysSlot a (ThrSystematic.descSlots a k) := by
  apply Fin.ext
  show descVal a k.val = ThrSystematic.descVal a k.val
  rw [sysDescVal_eq]
  unfold descVal
  rw [if_pos k.isLt]

theorem sys_cov (a : DecompositionAlgorithm) (k : Fin 16) (j : Fin (437 + Tn a))
    (h : descSlots a k = sysSlot a j) : ∃ k', ThrSystematic.descSlots a k' = j := by
  have hv : descVal a k.val = j.val := congrArg Fin.val h
  have hj := j.isLt
  have hk := k.isLt
  have o := origDesc_range a (k.val - 4)
  by_cases h4 : k.val < 4
  · refine ⟨⟨k.val, h4⟩, Fin.ext ?_⟩
    show ThrSystematic.descVal a k.val = j.val
    rw [sysDescVal_eq, ← hv]
    unfold descVal
    rw [if_pos h4]
  · exfalso
    unfold descVal at hv
    rw [if_neg h4] at hv
    split_ifs at hv <;> omega

theorem orig_he (a : DecompositionAlgorithm) (k : Fin 10) :
    descSlots a (origIdx k) = origSlot a (ThrOriginal.descSlots a k) := by
  apply Fin.ext
  show descVal a (k.val + 4) = origVal a (ThrOriginal.descVal a k.val)
  rw [origDesc_val]
  unfold descVal
  rw [if_neg (by omega), if_pos (by omega), show k.val + 4 - 4 = k.val by omega]

theorem orig_cov (a : DecompositionAlgorithm) (k : Fin 16) (j : Fin (3425 + Tn a))
    (h : descSlots a k = origSlot a j) : ∃ k', ThrOriginal.descSlots a k' = j := by
  have hv : descVal a k.val = origVal a j.val := congrArg Fin.val h
  have hj := j.isLt
  have hk := k.isLt
  have hT := T_ge a
  have sr := sysDesc_range a k.val
  have o := origDesc_range a (k.val - 4)
  by_cases h4 : k.val < 4
  · exfalso
    unfold descVal origVal at hv
    rw [if_pos h4] at hv
    split_ifs at hv <;> omega
  · by_cases h14 : k.val < 14
    · refine ⟨⟨k.val - 4, by omega⟩, Fin.ext ?_⟩
      show ThrOriginal.descVal a (k.val - 4) = j.val
      unfold descVal at hv
      rw [if_neg h4, if_pos h14] at hv
      unfold origVal at hv
      split_ifs at hv <;> omega
    · exfalso
      unfold descVal origVal at hv
      rw [if_neg h4, if_neg h14] at hv
      split_ifs at hv <;> omega

/-! ## The descriptors -/

section producer
open SupplierEstimator NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

/-- The systematic producer's descriptor `n` (`ThrSystematic.desc`, by value). -/
def sysDescAt (bm : List Bool) (n : Nat) : List Bool := if n = 0 ∨ n = 2 then bm else UnaryTemplate.tape q
/-- The original producer's descriptor `n` (`ThrOriginal.desc`, by value). -/
def origDescAt (P W L : Nat) (bits : List Bool) (n : Nat) : List Bool :=
  ThrOriginal.thrAt P q W L bits (ThrOriginal.posVal (if n < 5 then n else n - 5))

/-- **What factor selection writes** for a slot holding `o`: the chosen producer's descriptors and its
kind flag; everything else blank. -/
def descAt (P W L : Nat) : Option (C10TotalDecode.Atom pcpp) → Nat → List Bool
  | none, _ => []
  | some (.systematic idx), n =>
      if n < 4 then sysDescAt (q := q) (bitmap (pcpp.systematicSupport idx)) n
      else if n = 14 then [true] else []
  | some (.threshold c), n =>
      if n < 4 then [] else if n < 14 then origDescAt (q := q) P W L (codeBits L c) (n - 4)
      else if n = 15 then [true] else []
  | some (.symmetric _), _ => []

/-- The admission preconditions of a THR-mode slot (`paper.tex:721-733` caps). -/
def ok (P W L : Nat) : Option (C10TotalDecode.Atom pcpp) → Prop
  | none => True
  | some (.systematic _) => True
  | some (.threshold c) =>
      4 ≤ L ∧ c.descriptionBits ≤ L ∧ c.wireCount ≤ W ∧
        CloseoutRowsCircuitCapacity.capacity (codeWidth L) ≤ P
  | some (.symmetric _) => False

def cost (a : DecompositionAlgorithm) (P L : Nat) : Option (C10TotalDecode.Atom pcpp) → Nat
  | none => 0 + 2 + 2
  | some (.systematic idx) => ThrSystematic.cost a (pcpp.systematicSupport idx) + 2
  | some (.threshold c) => ThrOriginal.cost a c P (codeBits L c) + 2 + 2
  | some (.symmetric _) => 0

def sysM (a : DecompositionAlgorithm) := RecoveryFocus.machine (sysSlot a) (ThrSystematic.machine a)
def origM (a : DecompositionAlgorithm) := RecoveryFocus.machine (origSlot a) (ThrOriginal.machine a)
def inner (a : DecompositionAlgorithm) :=
  CloseoutRowsOriginalSwitch.machine (origM a) (CloseoutRowsOriginalSwitch.stop (3864 + 2 * Tn a)) (flagO a)
/-- The kind switch: flag S → systematic; else flag O → original; else stop. -/
def machine (a : DecompositionAlgorithm) := CloseoutRowsOriginalSwitch.machine (sysM a) (inner a) (flagS a)

def outN (a : DecompositionAlgorithm) : Fin (3864 + 2 * Tn a) := ⟨217, by omega⟩
def outS (a : DecompositionAlgorithm) : Fin (3864 + 2 * Tn a) := ⟨435 + Tn a, by omega⟩
def outT (a : DecompositionAlgorithm) : Fin (3864 + 2 * Tn a) := ⟨221 + Tn a, by omega⟩

theorem outN_sys (a : DecompositionAlgorithm) : outN a = sysSlot a (ThrSystematic.outN a) := rfl
theorem outS_sys (a : DecompositionAlgorithm) : outS a = sysSlot a (ThrSystematic.outS a) := by
  apply Fin.ext
  show 435 + Tn a = 223 + Tn a + 212
  omega
theorem outT_sys (a : DecompositionAlgorithm) : outT a = sysSlot a (ThrSystematic.outT a) := by
  apply Fin.ext
  show 221 + Tn a = (if (4 : Nat) = 0 then 224 + DecompositionSource.Counted.tapes a else 217 + Tn a + 4)
  rw [if_neg (by omega)]
  omega
theorem outN_orig (a : DecompositionAlgorithm) : outN a = origSlot a (ThrOriginal.outN a) := by
  apply Fin.ext
  show 217 = origVal a (ThrOriginal.bVal 4)
  unfold ThrOriginal.bVal origVal
  simp
theorem outS_orig (a : DecompositionAlgorithm) : outS a = origSlot a (ThrOriginal.outS a) := by
  apply Fin.ext
  show 435 + Tn a = origVal a (ThrOriginal.dVal a 1706)
  unfold ThrOriginal.dVal origVal
  rw [if_neg (by omega), if_pos (by omega)]
theorem outT_orig (a : DecompositionAlgorithm) : outT a = origSlot a (ThrOriginal.outT a) := by
  apply Fin.ext
  have hT := T_ge a
  have he : ThrOriginal.eVal a 4 = 1715 + Tn a := by
    show (if (4 : Nat) = 0 then 1712 + (DecompositionSource.Counted.tapes a + 6) else 1711 + Tn a + 4) = _
    rw [if_neg (by omega)]
    omega
  show 221 + Tn a = origVal a (ThrOriginal.eVal a 4)
  rw [he]
  unfold origVal
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem flagS_desc (a : DecompositionAlgorithm) : flagS a = descSlots a 14 := by
  apply Fin.ext
  show 3862 + 2 * Tn a = descVal a 14
  unfold descVal
  rw [if_neg (by omega), if_neg (by omega)]
  omega
theorem flagO_desc (a : DecompositionAlgorithm) : flagO a = descSlots a 15 := by
  apply Fin.ext
  show 3863 + 2 * Tn a = descVal a 15
  unfold descVal
  rw [if_neg (by omega), if_neg (by omega)]
  omega

theorem out_blank (a : DecompositionAlgorithm) (x : Fin (3864 + 2 * Tn a))
    (hx : x.val = 217 ∨ x.val = 435 + Tn a ∨ x.val = 221 + Tn a) : ∀ k, descSlots a k ≠ x := by
  intro k e
  have hv : descVal a k.val = x.val := congrArg Fin.val e
  have hk := k.isLt
  have hT := T_ge a
  have sr := sysDesc_range a k.val
  have o := origDesc_range a (k.val - 4)
  unfold descVal at hv
  split_ifs at hv <;> omega

theorem read_true (R : Nat) : readTapeBit (ZeroPadding.pad R [true]) 0 = true := by
  simp [ZeroPadding.pad, readTapeBit]
theorem read_blank (R : Nat) : readTapeBit (ZeroPadding.pad R []) 0 = false := by
  simp [ZeroPadding.pad, readTapeBit]

theorem stop_step {t : Nat} (H : Fin t → Nat) (A : Fin t → List Bool) :
    Step (CloseoutRowsOriginalSwitch.stop t) 0 H A H A :=
  ⟨_, rfl, rfl, rfl, le_refl _⟩

theorem frame_nil_pad (R : Nat) (hR : 1 ≤ R) :
    List.replicate R false = ZeroPadding.pad R (RepairOrdinary.frame []) := by
  obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  simp [ZeroPadding.pad, RepairOrdinary.frame, List.replicate_succ]

/-- **The THR-mode factor producer**: the kind switch over the systematic and original producers. -/
theorem run (a : DecompositionAlgorithm) (P W L : Nat) (o : Option (C10TotalDecode.Atom pcpp)) (R : Nat)
    (hok : ok P W L o) (hR : 1 ≤ R) :
    ∃ A' : Fin (3864 + 2 * Tn a) → List Bool,
      Step (machine a) (cost a P L o) (fun _ => 0)
        (install (descSlots a) (fun _ => List.replicate R false)
          (fun k => ZeroPadding.pad R (descAt P W L o k.val)))
        (fun _ => 0) A' ∧
      A' (outN a) = ZeroPadding.pad R (RepairOrdinary.frame (FactorLoop.segN false o)) ∧
      A' (outS a) = ZeroPadding.pad R (RepairOrdinary.frame (FactorLoop.segS false o)) ∧
      A' (outT a) = ZeroPadding.pad R (RepairOrdinary.frame (FactorLoop.segT a false o)) := by
  set Ab := install (descSlots a) (fun _ => List.replicate R false)
    (fun k => ZeroPadding.pad R (descAt P W L o k.val)) with hAb
  have fS : Ab (flagS a) = ZeroPadding.pad R (descAt P W L o 14) := by
    rw [flagS_desc, hAb, install_slot _ (descSlots_inj a)]
    rfl
  have fO : Ab (flagO a) = ZeroPadding.pad R (descAt P W L o 15) := by
    rw [flagO_desc, hAb, install_slot _ (descSlots_inj a)]
    rfl
  have blank : ∀ x : Fin (3864 + 2 * Tn a), (x.val = 217 ∨ x.val = 435 + Tn a ∨ x.val = 221 + Tn a) →
      Ab x = List.replicate R false := fun x hx => by
    rw [hAb, install_other _ _ _ _ (out_blank a x hx)]
  match o, hok with
  | none, _ =>
    have hs := CloseoutRowsOriginalSwitch.false_run (sysM a) (inner a) (flagS a)
      (CloseoutRowsOriginalSwitch.false_run (origM a) (CloseoutRowsOriginalSwitch.stop (3864 + 2 * Tn a))
        (flagO a) (stop_step (fun _ => 0) Ab) (by rw [fO]; exact read_blank R)) (by rw [fS]; exact read_blank R)
    refine ⟨Ab, hs, ?_, ?_, ?_⟩
    · rw [blank _ (Or.inl rfl)]; exact frame_nil_pad R hR
    · rw [blank _ (Or.inr (Or.inl rfl))]; exact frame_nil_pad R hR
    · rw [blank _ (Or.inr (Or.inr rfl))]; exact frame_nil_pad R hR
  | some (.systematic idx), _ =>
    obtain ⟨F, hF, hN, hS, hT⟩ := ThrSystematic.produce (pcpp := pcpp) a idx R
    have dk := hF.dock (sysSlot a) (sysSlot_inj a) (fun _ => 0) Ab (fun _ => rfl) (fun j => by
      rw [hAb, install_pull (descSlots a) (descSlots_inj a) (sysSlot a) (ThrSystematic.descSlots a)
        (ThrSystematic.descSlots_inj a) sysIdx (sys_he a) (sys_cov a)]
      congr 1
      funext k
      show ZeroPadding.pad R (if k.val < 4 then sysDescAt (q := q) (bitmap (pcpp.systematicSupport idx)) k.val
        else if k.val = 14 then [true] else []) = _
      rw [if_pos k.isLt]
      rfl)
    rw [ThrSystematic.zeroH] at dk
    have hs := CloseoutRowsOriginalSwitch.true_run (sysM a) (inner a) (flagS a) dk (by rw [fS]; exact read_true R)
    refine ⟨_, hs, ?_, ?_, ?_⟩
    · rw [outN_sys, install_slot _ (sysSlot_inj a), hN]
    · rw [outS_sys, install_slot _ (sysSlot_inj a), hS]
    · rw [outT_sys, install_slot _ (sysSlot_inj a), hT]
  | some (.threshold c), ⟨h4, hL, hW, hcap⟩ =>
    obtain ⟨F, hF, hN, hS, hT⟩ := ThrOriginal.produce (pcpp := pcpp) a c P W L (codeBits L c)
      (by rw [codeBits_length]; exact hcap) (codeBits_decode L c h4 hL) hW hL R
    have dk := hF.dock (origSlot a) (origSlot_inj a) (fun _ => 0) Ab (fun _ => rfl) (fun j => by
      rw [hAb, install_pull (descSlots a) (descSlots_inj a) (origSlot a) (ThrOriginal.descSlots a)
        (ThrOriginal.descSlots_inj a) origIdx (orig_he a) (orig_cov a)]
      congr 1
      funext k
      show ZeroPadding.pad R (if k.val + 4 < 4 then [] else if k.val + 4 < 14 then
        origDescAt (q := q) P W L (codeBits L c) (k.val + 4 - 4) else if k.val + 4 = 15 then [true] else []) = _
      rw [if_neg (by omega), if_pos (by omega), show k.val + 4 - 4 = k.val by omega]
      rfl)
    rw [ThrSystematic.zeroH] at dk
    have hs := CloseoutRowsOriginalSwitch.false_run (sysM a) (inner a) (flagS a)
      (CloseoutRowsOriginalSwitch.true_run (origM a) (CloseoutRowsOriginalSwitch.stop (3864 + 2 * Tn a)) (flagO a) dk
        (by rw [fO]; exact read_true R)) (by rw [fS]; exact read_blank R)
    refine ⟨_, hs, ?_, ?_, ?_⟩
    · rw [outN_orig, install_slot _ (origSlot_inj a), hN]
    · rw [outS_orig, install_slot _ (origSlot_inj a), hS]
    · rw [outT_orig, install_slot _ (origSlot_inj a), hT]
  | some (.symmetric _), h => exact h.elim

/-- **The THR-mode `FactorProducer`** (queue (d)2): caps `P W L` are the call's admission caps. -/
def producer (a : DecompositionAlgorithm) (P W L : Nat) : FactorLoop.FactorProducer false a pcpp where
  t := 3864 + 2 * Tn a
  s := _
  machine := machine a
  d := 16
  descSlots := descSlots a
  descInjective := descSlots_inj a
  outN := outN a
  outS := outS a
  outT := outT a
  hNS := fun e => by have := congrArg Fin.val e; simp [outN, outS] at this; omega
  hNT := fun e => by have := congrArg Fin.val e; simp [outN, outT] at this; omega
  hST := fun e => by have := congrArg Fin.val e; simp [outS, outT] at this
  Desc := fun o k => descAt P W L o k.val
  Ok := ok P W L
  cost := cost a P L
  need := fun _ => 1
  run := fun o R hok hR => run a P W L o R hok hR

end producer

end NearCubicWires.SourceRequest.ThrSwitch
