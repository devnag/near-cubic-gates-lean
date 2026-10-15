import Proof.SourceAssembly.SourceRequestSegments
import Proof.SourceAssembly.SourceRequestFieldPass

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.Fields
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open FixedLivePackets PacketProduction
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
noncomputable section

/-! ## 1. A pass at uniform backing `R` -/

/-- The pass with every tape padded by the same `R`: sources `pad R (RepairOrdinary.frame X_i)`, every private tape
`replicate R false`. -/
theorem pass_padded (n : Nat) (w : Fin n → List Bool) (R : Nat)
    (hc : ∀ i, 2 * (w i).length + 1 ≤ R) (hL : 2 * (List.ofFn w).flatten.length + 1 ≤ R) :
    ∃ A' : Fin (n + 2 + 1 + 1 + 2) → List Bool,
      Step (FieldPass.machine n) (FieldPass.cost n w) (fun _ => 0)
        (fun j => ZeroPadding.pad R (FieldPass.input n w R R R j)) (fun _ => 0) A' ∧
      A' (FieldPass.outP n) = ZeroPadding.pad R (List.ofFn w).flatten ∧
      A' (FieldPass.cntP n) = ZeroPadding.pad R (List.replicate (List.ofFn w).flatten.length true) ∧
      A' (FieldPass.dstP n) = ZeroPadding.pad R (RepairOrdinary.frame (List.ofFn w).flatten) ∧
      (∀ i, A' (FieldPass.srcP n i) = ZeroPadding.pad R (RepairOrdinary.frame (w i))) ∧
      A' (FieldPass.logP n) = List.replicate R false ∧
      A' (FieldPass.flogP n) = List.replicate R false := by
  obtain ⟨A', hs, h1, h2, h3, h4, h5, h6⟩ := FieldPass.pass_step n w R R R hc hL
  refine ⟨fun j => ZeroPadding.pad R (A' j), hs.pad (fun _ => R), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ZeroPadding.pad R _ = _; rw [h1]
  · show ZeroPadding.pad R _ = _; rw [h2]
  · show ZeroPadding.pad R _ = _
    rw [h3, SourceAssemblyReuse.pad_pad, Nat.max_self]
  · intro i
    show ZeroPadding.pad R _ = _
    rw [h4, SourceAssemblyReuse.pad_pad, Nat.max_self]
  · show ZeroPadding.pad R _ = _
    rw [h5, pad_replicate_false, Nat.max_self]
  · show ZeroPadding.pad R _ = _
    rw [h6, pad_replicate_false, Nat.max_self]

theorem aol_left {t : Nat} (a : Fin t → List Bool) (i : Fin t) :
    AppendOutputLength.input a (Fin.castAdd 1 i) = a i := by
  simp only [AppendOutputLength.input, Fin.addCases_left]

theorem aol_right {t : Nat} (a : Fin t → List Bool) :
    AppendOutputLength.input a ((0 : Fin 1).natAdd t) = [] := by
  simp only [AppendOutputLength.input, Fin.addCases_right]

/-- The padded pass input, tape by tape. -/
theorem input_src (n : Nat) (w : Fin n → List Bool) (R : Nat) (i : Fin n) :
    ZeroPadding.pad R (FieldPass.input n w R R R (FieldPass.srcP n i))
      = ZeroPadding.pad R (RepairOrdinary.frame (w i)) := by
  rw [FieldPass.srcP, FieldPass.input, FieldPass.extT_left, aol_left, aol_left]
  simp only [FieldPass.tapes, FieldPass.srcT, dif_pos i.isLt, Fin.eta]
  rw [SourceAssemblyReuse.pad_pad, Nat.max_self]

theorem input_out (n : Nat) (w : Fin n → List Bool) (R : Nat) :
    ZeroPadding.pad R (FieldPass.input n w R R R (FieldPass.outP n)) = List.replicate R false := by
  rw [FieldPass.outP, FieldPass.input, FieldPass.extT_left, aol_left, aol_left]
  simp only [FieldPass.tapes, FieldPass.outT, lt_irrefl, if_true, dite_false]
  exact SLoad.Words.pad_nil R

theorem input_log (n : Nat) (w : Fin n → List Bool) (R : Nat) :
    ZeroPadding.pad R (FieldPass.input n w R R R (FieldPass.logP n)) = List.replicate R false := by
  rw [FieldPass.logP, FieldPass.input, FieldPass.extT_left, aol_left, aol_left]
  have h1 : ¬ n + 1 < n := by omega
  have h2 : n + 1 ≠ n := by omega
  simp only [FieldPass.tapes, FieldPass.logT, dif_neg h1, if_neg h2]
  rw [pad_replicate_false, Nat.max_self]

theorem input_cnt (n : Nat) (w : Fin n → List Bool) (R : Nat) :
    ZeroPadding.pad R (FieldPass.input n w R R R (FieldPass.cntP n)) = List.replicate R false := by
  rw [FieldPass.cntP, FieldPass.input, FieldPass.extT_left, aol_left, aol_right, SLoad.Words.pad_nil]

def rlogP (n : Nat) : Fin (n + 2 + 1 + 1 + 2) := Fin.castAdd 2 ((0 : Fin 1).natAdd (n + 2 + 1))

theorem input_rlog (n : Nat) (w : Fin n → List Bool) (R : Nat) :
    ZeroPadding.pad R (FieldPass.input n w R R R (rlogP n)) = List.replicate R false := by
  rw [rlogP, FieldPass.input, FieldPass.extT_left, aol_right, SLoad.Words.pad_nil]

theorem input_dst (n : Nat) (w : Fin n → List Bool) (R : Nat) :
    ZeroPadding.pad R (FieldPass.input n w R R R (FieldPass.dstP n)) = List.replicate R false := by
  rw [FieldPass.input, FieldPass.extT_dst, pad_replicate_false, Nat.max_self]

theorem input_flog (n : Nat) (w : Fin n → List Bool) (R : Nat) :
    ZeroPadding.pad R (FieldPass.input n w R R R (FieldPass.flogP n)) = List.replicate R false := by
  rw [FieldPass.input, FieldPass.extT_flog, pad_replicate_false, Nat.max_self]

theorem seg_le {n : Nat} (w : Fin n → List Bool) (i : Fin n) :
    (w i).length ≤ (List.ofFn w).flatten.length :=
  (List.sublist_flatten_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩)).length_le

/-- The padded pass input at any index: a source's normal-form word, else the blank backing. -/
theorem input_at (n : Nat) (w : Fin n → List Bool) (R : Nat) (j : Fin (n + 2 + 1 + 1 + 2)) :
    ZeroPadding.pad R (FieldPass.input n w R R R j)
      = if h : j.val < n then ZeroPadding.pad R (RepairOrdinary.frame (w ⟨j.val, h⟩))
        else List.replicate R false := by
  have hj := j.isLt
  by_cases h : j.val < n
  · rw [dif_pos h]
    have e : j = FieldPass.srcP n ⟨j.val, h⟩ := Fin.ext rfl
    have hs := input_src n w R ⟨j.val, h⟩
    rw [← e] at hs
    exact hs
  · rw [dif_neg h]
    by_cases h0 : j.val = n
    · rw [show j = FieldPass.outP n from Fin.ext h0, input_out]
    by_cases h1 : j.val = n + 1
    · rw [show j = FieldPass.logP n from Fin.ext h1, input_log]
    by_cases h2 : j.val = n + 2
    · rw [show j = FieldPass.cntP n from Fin.ext h2, input_cnt]
    by_cases h3 : j.val = n + 3
    · rw [show j = rlogP n from Fin.ext h3, input_rlog]
    by_cases h4 : j.val = n + 4
    · rw [show j = FieldPass.dstP n from Fin.ext h4, input_dst]
    rw [show j = FieldPass.flogP n from Fin.ext (by
      show j.val = n + 2 + 1 + 1 + 1
      omega), input_flog]

/-! ## 2. Three docked passes on `Fin 31` -/

def natSlots : Fin 11 → Fin 31 := ![0, 1, 2, 3, 4, 13, 14, 15, 16, 17, 18]
def supSlots : Fin 10 → Fin 31 := ![5, 6, 7, 8, 19, 20, 21, 22, 23, 24]
def topSlots : Fin 10 → Fin 31 := ![9, 10, 11, 12, 25, 26, 27, 28, 29, 30]

theorem natSlots_injective : Function.Injective natSlots := by decide
theorem supSlots_injective : Function.Injective supSlots := by decide
theorem topSlots_injective : Function.Injective topSlots := by decide

def machine :=
  Composition.machine (RecoveryFocus.machine natSlots (FieldPass.machine 5))
    (Composition.machine (RecoveryFocus.machine supSlots (FieldPass.machine 4))
      (RecoveryFocus.machine topSlots (FieldPass.machine 4)))

/-- The entry bank: header, the twelve slot segments in normal form, blank backing elsewhere. -/
def entry (hdr : List Bool) (ns ss ts : Fin 4 → List Bool) (R : Nat) : Fin 31 → List Bool := fun x =>
  if x.val = 0 then ZeroPadding.pad R (RepairOrdinary.frame hdr)
  else if h : x.val < 5 then ZeroPadding.pad R (RepairOrdinary.frame (ns ⟨x.val - 1, by omega⟩))
  else if h : x.val < 9 then ZeroPadding.pad R (RepairOrdinary.frame (ss ⟨x.val - 5, by omega⟩))
  else if h : x.val < 13 then ZeroPadding.pad R (RepairOrdinary.frame (ts ⟨x.val - 9, by omega⟩))
  else List.replicate R false

def wN (hdr : List Bool) (ns : Fin 4 → List Bool) : Fin 5 → List Bool := ![hdr, ns 0, ns 1, ns 2, ns 3]

def cost (hdr : List Bool) (ns ss ts : Fin 4 → List Bool) : Nat :=
  FieldPass.cost 5 (wN hdr ns) + 1 + (FieldPass.cost 4 ss + 1 + FieldPass.cost 4 ts)

theorem flat5 (hdr : List Bool) (ns : Fin 4 → List Bool) :
    (List.ofFn (wN hdr ns)).flatten = hdr ++ (ns 0 ++ ns 1 ++ ns 2 ++ ns 3) := by
  simp [wN, List.ofFn_succ, List.append_assoc]

theorem flat4 (ns : Fin 4 → List Bool) :
    (List.ofFn ns).flatten = ns 0 ++ ns 1 ++ ns 2 ++ ns 3 := by
  simp [List.ofFn_succ, List.append_assoc]

/-- **The three fields from the slot segments** (generic in the segments). Tape `17` / `23` / `29`
hold the framed native / support / TOP field, `13` / `19` / `25` the bare fields, `15` / `21` / `27`
their unary lengths; every head is `0`. -/
theorem fields_step (hdr : List Bool) (ns ss ts : Fin 4 → List Bool) (R : Nat)
    (hN : 2 * (hdr ++ (ns 0 ++ ns 1 ++ ns 2 ++ ns 3)).length + 1 ≤ R)
    (hS : 2 * (ss 0 ++ ss 1 ++ ss 2 ++ ss 3).length + 1 ≤ R)
    (hT : 2 * (ts 0 ++ ts 1 ++ ts 2 ++ ts 3).length + 1 ≤ R) :
    ∃ X : Fin 31 → List Bool,
      Step machine (cost hdr ns ss ts) (fun _ => 0) (entry hdr ns ss ts R) (fun _ => 0) X ∧
      X 17 = ZeroPadding.pad R (RepairOrdinary.frame (hdr ++ (ns 0 ++ ns 1 ++ ns 2 ++ ns 3))) ∧
      X 13 = ZeroPadding.pad R (hdr ++ (ns 0 ++ ns 1 ++ ns 2 ++ ns 3)) ∧
      X 15 = ZeroPadding.pad R (List.replicate (hdr ++ (ns 0 ++ ns 1 ++ ns 2 ++ ns 3)).length true) ∧
      X 23 = ZeroPadding.pad R (RepairOrdinary.frame (ss 0 ++ ss 1 ++ ss 2 ++ ss 3)) ∧
      X 19 = ZeroPadding.pad R (ss 0 ++ ss 1 ++ ss 2 ++ ss 3) ∧
      X 21 = ZeroPadding.pad R (List.replicate (ss 0 ++ ss 1 ++ ss 2 ++ ss 3).length true) ∧
      X 29 = ZeroPadding.pad R (RepairOrdinary.frame (ts 0 ++ ts 1 ++ ts 2 ++ ts 3)) ∧
      X 25 = ZeroPadding.pad R (ts 0 ++ ts 1 ++ ts 2 ++ ts 3) ∧
      X 27 = ZeroPadding.pad R (List.replicate (ts 0 ++ ts 1 ++ ts 2 ++ ts 3).length true) := by
  classical
  have fN := flat5 hdr ns
  have fS := flat4 ss
  have fT := flat4 ts
  obtain ⟨A1, s1, o1, c1, d1, _, _, _⟩ := pass_padded 5 (wN hdr ns) R
    (fun i => le_trans (by have := seg_le (wN hdr ns) i; omega) (fN ▸ hN)) (fN ▸ hN)
  obtain ⟨A2, s2, o2, c2, d2, _, _, _⟩ := pass_padded 4 ss R
    (fun i => le_trans (by have := seg_le ss i; omega) (fS ▸ hS)) (fS ▸ hS)
  obtain ⟨A3, s3, o3, c3, d3, _, _, _⟩ := pass_padded 4 ts R
    (fun i => le_trans (by have := seg_le ts i; omega) (fT ▸ hT)) (fT ▸ hT)
  have hz : ∀ {t : Nat} (sl : Fin t → Fin 31), dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
    fun sl => SLoad.dockH_existing sl _ _ (fun _ => rfl)
  -- the native pass
  have e1 : ∀ j, entry hdr ns ss ts R (natSlots j)
      = ZeroPadding.pad R (FieldPass.input 5 (wN hdr ns) R R R j) := by
    intro j
    rw [input_at]
    fin_cases j <;> rfl
  have t1 := s1.dock natSlots natSlots_injective (fun _ => 0) _ (fun _ => rfl) e1
  rw [hz] at t1
  set B1 := install natSlots (entry hdr ns ss ts R) A1 with hB1
  -- the support pass
  have e2 : ∀ j, B1 (supSlots j) = ZeroPadding.pad R (FieldPass.input 4 ss R R R j) := by
    intro j
    rw [hB1, install_other natSlots _ _ _ (by fin_cases j <;> decide), input_at]
    fin_cases j <;> rfl
  have t2 := s2.dock supSlots supSlots_injective (fun _ => 0) _ (fun _ => rfl) e2
  rw [hz] at t2
  set B2 := install supSlots B1 A2 with hB2
  -- the TOP pass
  have e3 : ∀ j, B2 (topSlots j) = ZeroPadding.pad R (FieldPass.input 4 ts R R R j) := by
    intro j
    rw [hB2, install_other supSlots _ _ _ (by fin_cases j <;> decide), hB1,
      install_other natSlots _ _ _ (by fin_cases j <;> decide), input_at]
    fin_cases j <;> rfl
  have t3 := s3.dock topSlots topSlots_injective (fun _ => 0) _ (fun _ => rfl) e3
  rw [hz] at t3
  refine ⟨install topSlots B2 A3, t1.seq (t2.seq t3), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [install_other topSlots _ _ 17 (by decide), hB2, install_other supSlots _ _ 17 (by decide),
      hB1, show (17 : Fin 31) = natSlots 9 from rfl, install_slot natSlots natSlots_injective]
    rw [← fN]; exact d1
  · rw [install_other topSlots _ _ 13 (by decide), hB2, install_other supSlots _ _ 13 (by decide),
      hB1, show (13 : Fin 31) = natSlots 5 from rfl, install_slot natSlots natSlots_injective]
    rw [← fN]; exact o1
  · rw [install_other topSlots _ _ 15 (by decide), hB2, install_other supSlots _ _ 15 (by decide),
      hB1, show (15 : Fin 31) = natSlots 7 from rfl, install_slot natSlots natSlots_injective]
    rw [← fN]; exact c1
  · rw [install_other topSlots _ _ 23 (by decide), hB2, show (23 : Fin 31) = supSlots 8 from rfl,
      install_slot supSlots supSlots_injective]
    rw [← fS]; exact d2
  · rw [install_other topSlots _ _ 19 (by decide), hB2, show (19 : Fin 31) = supSlots 4 from rfl,
      install_slot supSlots supSlots_injective]
    rw [← fS]; exact o2
  · rw [install_other topSlots _ _ 21 (by decide), hB2, show (21 : Fin 31) = supSlots 6 from rfl,
      install_slot supSlots supSlots_injective]
    rw [← fS]; exact c2
  · rw [show (29 : Fin 31) = topSlots 8 from rfl, install_slot topSlots topSlots_injective]
    rw [← fT]; exact d3
  · rw [show (25 : Fin 31) = topSlots 4 from rfl, install_slot topSlots topSlots_injective]
    rw [← fT]; exact o3
  · rw [show (27 : Fin 31) = topSlots 6 from rfl, install_slot topSlots topSlots_injective]
    rw [← fT]; exact c3

/-! ## 3. At the request of one monomial -/

section request
open NearCubicWires.SourceRequest
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

/-- The four native / support / TOP slot segments of a `≤ 4`-factor monomial. -/
def nSlots (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp)) : Fin 4 → List Bool :=
  fun i => slotSeg (natSeg mode) atoms i.val
def sSlots (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp)) : Fin 4 → List Bool :=
  fun i => slotSeg (supSeg mode) atoms i.val
def tSlots (a : DecompositionAlgorithm) (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp)) :
    Fin 4 → List Bool :=
  fun i => slotSeg (topSeg a mode) atoms i.val

theorem native_slots (L target : Nat) (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp))
    (four : atoms.length ≤ 4) :
    header mode q L target atoms.length ++ (nSlots mode atoms 0 ++ nSlots mode atoms 1 ++
      nSlots mode atoms 2 ++ nSlots mode atoms 3)
      = (monomialRequest L target mode atoms four).nativeWord := by
  rw [native_eq]
  exact congrArg _ (slots_flatMap (natSeg mode) atoms four)

theorem support_slots (a : DecompositionAlgorithm) (L target : Nat) (mode : Bool)
    (atoms : List (C10TotalDecode.Atom pcpp)) (four : atoms.length ≤ 4) :
    sSlots mode atoms 0 ++ sSlots mode atoms 1 ++ sSlots mode atoms 2 ++ sSlots mode atoms 3
      = (monomialRequest L target mode atoms four).supportWord a := by
  rw [support_eq]
  exact slots_flatMap (supSeg mode) atoms four

theorem top_slots (a : DecompositionAlgorithm) (L target : Nat) (mode : Bool)
    (atoms : List (C10TotalDecode.Atom pcpp)) (four : atoms.length ≤ 4) :
    tSlots a mode atoms 0 ++ tSlots a mode atoms 1 ++ tSlots a mode atoms 2 ++ tSlots a mode atoms 3
      = (monomialRequest L target mode atoms four).topWord a := by
  rw [top_eq]
  exact slots_flatMap (topSeg a mode) atoms four

/-- **The factor-loop parent's back half, at the monomial's request.** From the header and the
twelve slot segments of `atoms` in normal form, the three docked passes leave on tapes 17 / 23 / 29
`pad R (frame F)` for `F` = the request's native / support / TOP word, on 13 / 19 / 25 the bare
`pad R F`, and on 15 / 21 / 27 `pad R 1^|F|`; all heads `0`. `R` must dominate the three fields. -/
theorem request_fields (a : DecompositionAlgorithm) (L target : Nat) (mode : Bool)
    (atoms : List (C10TotalDecode.Atom pcpp)) (four : atoms.length ≤ 4) (R : Nat)
    (hN : 2 * (monomialRequest L target mode atoms four).nativeWord.length + 1 ≤ R)
    (hS : 2 * ((monomialRequest L target mode atoms four).supportWord a).length + 1 ≤ R)
    (hT : 2 * ((monomialRequest L target mode atoms four).topWord a).length + 1 ≤ R) :
    let r := monomialRequest L target mode atoms four
    ∃ X : Fin 31 → List Bool,
      Step machine (cost (header mode q L target atoms.length) (nSlots mode atoms) (sSlots mode atoms)
          (tSlots a mode atoms)) (fun _ => 0)
        (entry (header mode q L target atoms.length) (nSlots mode atoms) (sSlots mode atoms)
          (tSlots a mode atoms) R) (fun _ => 0) X ∧
      X 17 = ZeroPadding.pad R (RepairOrdinary.frame r.nativeWord) ∧
      X 13 = ZeroPadding.pad R r.nativeWord ∧
      X 15 = ZeroPadding.pad R (List.replicate r.nativeWord.length true) ∧
      X 23 = ZeroPadding.pad R (RepairOrdinary.frame (r.supportWord a)) ∧
      X 19 = ZeroPadding.pad R (r.supportWord a) ∧
      X 21 = ZeroPadding.pad R (List.replicate (r.supportWord a).length true) ∧
      X 29 = ZeroPadding.pad R (RepairOrdinary.frame (r.topWord a)) ∧
      X 25 = ZeroPadding.pad R (r.topWord a) ∧
      X 27 = ZeroPadding.pad R (List.replicate (r.topWord a).length true) := by
  intro r
  have eN := native_slots L target mode atoms four
  have eS := support_slots a L target mode atoms four
  have eT := top_slots a L target mode atoms four
  obtain ⟨X, hs, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := fields_step
    (header mode q L target atoms.length) (nSlots mode atoms) (sSlots mode atoms)
    (tSlots a mode atoms) R (eN ▸ hN) (eS ▸ hS) (eT ▸ hT)
  rw [eN] at h1 h2 h3
  rw [eS] at h4 h5 h6
  rw [eT] at h7 h8 h9
  exact ⟨X, hs, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end request

end
end NearCubicWires.SourceRequest.Fields
