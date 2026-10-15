import Proof.Wire_3_5.ListMachineRowLoad

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun atomCode)
open NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.WireExponent3_5

/-! ## Uniform evaluator families -/

/-- A uniform evaluator family: ONE machine on the point, the result cell and `t` data tapes. -/
structure EvalFam where
  t : ℕ
  s : ℕ
  machine : Machine (2 + t) s

structure Member (F : EvalFam) (L : ℕ) (f : List Bool → Bool) where
  data : Fin F.t → List Bool
  cost : ℕ
  step : ∀ (Z : List Bool) (b : Bool), Z.length = L →
    Step F.machine cost (fun _ => 0) (Fin.addCases ![frame Z, [b]] data) (fun _ => 0)
      (Fin.addCases ![frame Z, [f Z]] data)

/-- The member as a printer's point evaluator. -/
def Member.pe {F : EvalFam} {L : ℕ} {f : List Bool → Bool} (m : Member F L f) : PointEval L f :=
  ⟨F.t, F.s, F.machine, m.data, m.cost, m.step⟩

noncomputable def innerBodyU (F : EvalFam) :=
  Composition.machine (RecoveryFocus.machine (evS F.t) F.machine) (RecoveryFocus.machine (Fin.castAdd F.t) innerRest)

noncomputable def outerBodyU (F : EvalFam) :=
  Composition.machine (Composition.machine (RecoveryFocus.machine (Fin.castAdd F.t) setFIM)
    (StreamController.machine (innerBodyU F) (Fin.castAdd F.t 4)))
    (RecoveryFocus.machine (Fin.castAdd F.t) (outerRestG (recSpecL [])))

/-- **The family's printer**: one machine. -/
noncomputable def printMU (F : EvalFam) :=
  Composition.machine (StreamController.machine (outerBodyU F) (Fin.castAdd F.t 5))
    (RecoveryFocus.machine (Fin.castAdd F.t) (RecoveryFocus.machine sOut (Put.machine false)))

/-- **Uniformity**: the printer of every member, with every label word, is the family's printer. -/
theorem printMG_eq (F : EvalFam) {L : ℕ} {f : List Bool → Bool} (m : Member F L f) (labs : List ℕ) :
    printMG (recSpecL labs) m.pe = printMU F := rfl

/-! ## The factor layout: record cursor, bank, data, log -/

/-- The record tape. -/
def srcI (t : ℕ) : Fin (1 + (14 + t)) := Fin.castAdd (14 + t) (0 : Fin 1)
/-- Bank tape `b`. -/
def bankI (t : ℕ) (b : Fin 14) : Fin (1 + (14 + t)) := Fin.natAdd 1 (Fin.castAdd t b)
/-- Data tape `j`. -/
def dataI (t : ℕ) (j : Fin t) : Fin (1 + (14 + t)) := Fin.natAdd 1 (Fin.natAdd 14 j)

@[simp] theorem srcI_val (t : ℕ) : (srcI t).val = 0 := rfl
@[simp] theorem bankI_val (t : ℕ) (b : Fin 14) : (bankI t b).val = 1 + b.val := rfl
@[simp] theorem dataI_val (t : ℕ) (j : Fin t) : (dataI t j).val = 1 + (14 + j.val) := rfl

/-- The loaded bank tapes: all but the output. -/
def loadBank : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13]

/-- The load targets, in record order. -/
def targets (t : ℕ) : List (Fin (1 + (14 + t))) := loadBank.map (bankI t) ++ (List.finRange t).map (dataI t)

theorem mem_targets (t : ℕ) (i : Fin (1 + (14 + t))) :
    i ∈ targets t ↔ (1 ≤ i.val ∧ i.val ≠ 11) := by
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
      simp only [loadBank, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
      simp only [dataI_val]; omega
  · rintro ⟨h1, h2⟩
    by_cases hlt : i.val < 15
    · apply List.mem_append_left
      refine List.mem_map.mpr ⟨⟨i.val - 1, by omega⟩, ?_, Fin.ext (by simp; omega)⟩
      have : i.val - 1 ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
      simp only [loadBank, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff] at this ⊢
      omega
    · apply List.mem_append_right
      refine List.mem_map.mpr ⟨⟨i.val - 15, by omega⟩, List.mem_finRange _, Fin.ext (by simp; omega)⟩

theorem targets_nodup (t : ℕ) : (targets t).Nodup := by
  unfold targets
  refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
  · refine List.Nodup.map (fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)) (by decide)
  · exact List.Nodup.map (fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega))
      (List.nodup_finRange t)
  · intro a ha b hb hab
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
    have := congrArg Fin.val hab
    simp at this; omega

theorem src_not_mem (t : ℕ) : srcI t ∉ targets t := by
  rw [mem_targets]; simp

/-- The selected (rewound) tapes of the load: the targets. -/
def selT (t : ℕ) (i : Fin (1 + (14 + t))) : Bool := decide (i ∈ targets t)

/-- The masked load. -/
noncomputable def loadMM (t : ℕ) := MaskedReset.machine (loadL (srcI t) (targets t)) (selT t)

/-- The printer's slots. -/
def prSlot (t : ℕ) (i : Fin (14 + t)) : Fin (1 + (14 + t) + 1) := Fin.castAdd 1 (Fin.natAdd 1 i)

theorem prSlot_inj (t : ℕ) : Function.Injective (prSlot t) := by
  intro a b h
  have := congrArg Fin.val h
  simp [prSlot] at this
  exact Fin.ext this

/-- **The factor stage**: load, then print. ONE machine per family. -/
noncomputable def factorM (F : EvalFam) := Composition.machine (loadMM F.t) (RecoveryFocus.machine (prSlot F.t) (printMU F))

/-! ## Banks of the factor layout -/

/-- Heads without the log: the record cursor, the bank's (output cursor `o`), data at `0`. -/
def iH (t p o : ℕ) : Fin (1 + (14 + t)) → ℕ := Fin.addCases (fun _ : Fin 1 => p) (Fin.addCases (bh o) (fun _ : Fin t => 0))

/-- Tapes without the log: the record, the bank, the data. -/
def iA {t : ℕ} (src : List Bool) (b : Bank) (data : Fin t → List Bool) : Fin (1 + (14 + t)) → List Bool :=
  Fin.addCases (fun _ : Fin 1 => src) (Fin.addCases b.tapes data)

/-- Heads: the record cursor, the bank's (output cursor `o`), data at `0`, log at `0`. -/
def fH (t p o : ℕ) : Fin (1 + (14 + t) + 1) → ℕ := Fin.addCases (iH t p o) (fun _ : Fin 1 => 0)

/-- Tapes: the record, the bank, the data, the log. -/
def fA {t : ℕ} (src : List Bool) (b : Bank) (data : Fin t → List Bool) (log : List Bool) :
    Fin (1 + (14 + t) + 1) → List Bool := Fin.addCases (iA src b data) (fun _ : Fin 1 => log)

/-- The entry bank: every loaded tape empty, the output at its cursor. -/
def entryBank (out B : List Bool) : Bank :=
  ⟨[], [], [], [], [], [], [], [], [], [], overlay out B, [], [], []⟩

def labelWord (labs : List ℕ) : List Bool := labs.flatMap atomCode ++ [false]

/-- The printer's first bank for a member of point length `L`, bound `d`, labels `labs`. -/
noncomputable def firstBank (f : List Bool → Bool) (L d : ℕ) (labs : List ℕ) (out B : List Bool) (cap1 cap2 : ℕ) : Bank :=
  outerBankG (recSpecL labs) f L d [] out B (labelWord labs) (List.replicate L false) cap1 cap2 0

/-- **The factor's fields**, in record order: the printer's first bank (all but the output; its two logs blank of
lengths `cap1`, `cap2`), then the data. -/
def factorFields {t : ℕ} (L d : ℕ) (labs : List ℕ) (cap1 cap2 : ℕ) (data : Fin t → List Bool) : List (List Bool) :=
  [frame (xsAt L d 0), frame (List.replicate L false), [false], [false], [false],
    [decide (0 < (Interp.goods L d).length)], [false], frame (List.replicate L false), frame (List.replicate L false),
    List.replicate d true ++ [false], labelWord labs, List.replicate cap1 false, List.replicate cap2 false] ++
    List.ofFn data

/-- The record block of a factor. -/
def factorBlock {t : ℕ} (L d : ℕ) (labs : List ℕ) (cap1 cap2 : ℕ) (data : Fin t → List Bool) : List Bool :=
  fieldsWord (factorFields L d labs cap1 cap2 data)

/-- What the targets receive. -/
def loadF {t : ℕ} (b : Bank) (data : Fin t → List Bool) : Fin (1 + (14 + t)) → List Bool :=
  Fin.addCases (fun _ : Fin 1 => []) (Fin.addCases b.tapes data)

theorem targets_map (f : List Bool → Bool) (L d : ℕ) (labs : List ℕ) (out B : List Bool) (cap1 cap2 : ℕ) {t : ℕ}
    (data : Fin t → List Bool) :
    (targets t).map (loadF (firstBank f L d labs out B cap1 cap2) data) = factorFields L d labs cap1 cap2 data := by
  simp [targets, loadBank, loadF, bankI, dataI, firstBank, outerBankG, Bank.tapes, factorFields, List.ofFn_eq_map, mAt,
    Function.comp_def]

/-- The cost of the factor stage. -/
noncomputable def factorCost (F : EvalFam) {L : ℕ} {f : List Bool → Bool} (m : Member F L f) (d : ℕ) (labs : List ℕ)
    (cap1 cap2 : ℕ) : ℕ :=
  2 * loadCost (factorFields L d labs cap1 cap2 m.data) + 2 + 1 + printGCost (recSpecL labs) m.pe d

/-- The printed factor. -/
def factorPoly (f : List Bool → Bool) (L d : ℕ) (labs : List ℕ) : List (List ℕ) :=
  (Interp.interpPrint f L d).map (List.map (labOf labs))

/-- The output tape of the factor layout. -/
def outI (t : ℕ) : Fin (1 + (14 + t) + 1) := Fin.castAdd 1 (bankI t 10)
/-- The record tape of the factor layout. -/
def srcO (t : ℕ) : Fin (1 + (14 + t) + 1) := Fin.castAdd 1 (srcI t)

/-- The log tape of the factor layout. -/
def logI (t : ℕ) : Fin (1 + (14 + t) + 1) := Fin.natAdd (1 + (14 + t)) (0 : Fin 1)

@[simp] theorem srcO_val (t : ℕ) : (srcO t).val = 0 := rfl
@[simp] theorem outI_val (t : ℕ) : (outI t).val = 11 := rfl
@[simp] theorem logI_val (t : ℕ) : (logI t).val = 1 + (14 + t) := rfl

theorem iH_src (t p o : ℕ) : iH t p o (srcI t) = p := by simp [iH, srcI]
theorem iA_src {t : ℕ} (src : List Bool) (b : Bank) (data : Fin t → List Bool) : iA src b data (srcI t) = src := by
  simp [iA, srcI]
theorem iH_bank (t p o : ℕ) (c : Fin 14) : iH t p o (bankI t c) = bh o c := by simp [iH, bankI]
theorem iA_bank {t : ℕ} (src : List Bool) (b : Bank) (data : Fin t → List Bool) (c : Fin 14) :
    iA src b data (bankI t c) = b.tapes c := by simp [iA, bankI]
theorem iH_data (t p o : ℕ) (j : Fin t) : iH t p o (dataI t j) = 0 := by simp [iH, dataI]
theorem iA_data {t : ℕ} (src : List Bool) (b : Bank) (data : Fin t → List Bool) (j : Fin t) :
    iA src b data (dataI t j) = data j := by simp [iA, dataI]

/-- Every tape of the inner layout is the record, a bank tape or a data tape. -/
theorem icover (t : ℕ) (i : Fin (1 + (14 + t))) : i = srcI t ∨ (∃ c, i = bankI t c) ∨ (∃ j, i = dataI t j) := by
  have hi := i.isLt
  by_cases h0 : i.val = 0
  · exact Or.inl (Fin.ext (by simp [h0]))
  · by_cases h1 : i.val < 15
    · exact Or.inr (Or.inl ⟨⟨i.val - 1, by omega⟩, Fin.ext (by simp; omega)⟩)
    · exact Or.inr (Or.inr ⟨⟨i.val - 15, by omega⟩, Fin.ext (by simp; omega)⟩)

theorem bank_mem (t : ℕ) (c : Fin 14) : bankI t c ∈ targets t ↔ c.val ≠ 10 := by
  rw [mem_targets, bankI_val]; omega
theorem data_mem (t : ℕ) (j : Fin t) : dataI t j ∈ targets t := by
  rw [mem_targets, dataI_val]; omega

/-- The targets start empty with their heads at `0`. -/
theorem entry_targets (t p o : ℕ) (src out B : List Bool) :
    ∀ i ∈ targets t, iH t p o i = 0 ∧ iA src (entryBank out B) (fun _ : Fin t => []) i = [] := by
  intro i hi
  rcases icover t i with rfl | ⟨c, rfl⟩ | ⟨j, rfl⟩
  · exact absurd hi (src_not_mem t)
  · rw [bank_mem] at hi
    rw [iH_bank, iA_bank]
    fin_cases c <;> simp_all [bh, entryBank, Bank.tapes]
  · rw [iH_data, iA_data]; exact ⟨rfl, rfl⟩

theorem fH_eq (t p o : ℕ) : fH t p o = Fin.addCases (iH t p o) (fun _ : Fin 1 => 0) := rfl

/-- The heads after the masked load. -/
theorem load_heads (t p n o : ℕ) (g : Fin (1 + (14 + t)) → ℕ) :
    (fun i => if selT t i then 0 else (if i = srcI t then p + n else if i ∈ targets t then g i else iH t p o i)) =
      iH t (p + n) o := by
  funext i
  rcases icover t i with rfl | ⟨c, rfl⟩ | ⟨j, rfl⟩
  · simp [selT, src_not_mem, iH_src]
  · by_cases hc : bankI t c ∈ targets t
    · have h' := (bank_mem t c).mp hc
      simp only [selT, hc, decide_true, if_true, iH_bank]
      fin_cases c <;> simp_all [bh]
    · simp only [selT, hc, decide_false, Bool.false_eq_true, if_false]
      have hne : bankI t c ≠ srcI t := fun e => by have := congrArg Fin.val e; simp at this
      simp only [hne, if_false, iH_bank]
  · simp [selT, data_mem, iH_data]

/-- The tapes after the masked load. -/
theorem load_tapes {t : ℕ} (src : List Bool) (b1 : Bank) (data : Fin t → List Bool) (out B : List Bool)
    (ho : b1.o = overlay out B) :
    (fun i => if i ∈ targets t then loadF b1 data i else iA src (entryBank out B) (fun _ : Fin t => []) i) =
      iA src b1 data := by
  funext i
  rcases icover t i with rfl | ⟨c, rfl⟩ | ⟨j, rfl⟩
  · simp [src_not_mem, iA_src]
  · by_cases hc : bankI t c ∈ targets t
    · simp only [hc, if_true, loadF, iA_bank]
      simp [bankI]
    · simp only [hc, if_false, iA_bank]
      have h' : ¬(c.val ≠ 10) := fun h => hc ((bank_mem t c).mpr h)
      fin_cases c <;> simp_all [entryBank, Bank.tapes]
  · rw [if_pos (data_mem t j), iA_data]; simp [loadF, dataI]

theorem printedAtG_zero (R : RecSpec) (f : List Bool → Bool) (L d : ℕ) : printedAtG R f L d 0 = [] := by
  simp [printedAtG]

theorem firstBank_o (f : List Bool → Bool) (L d : ℕ) (labs : List ℕ) (out B : List Bool) (cap1 cap2 : ℕ) :
    (firstBank f L d labs out B cap1 cap2).o = overlay out B := by
  simp [firstBank, outerBankG, printedAtG_zero]

/-- **The masked load**: every target receives its field and is rewound; the record cursor passes the block. -/
theorem load_step (F : EvalFam) {L : ℕ} {f : List Bool → Bool} (m : Member F L f) (labs : List ℕ) (d : ℕ)
    (pre rest out B : List Bool) (cap1 cap2 k : ℕ) :
    ∃ k', Step (loadMM F.t) (2 * loadCost (factorFields L d labs cap1 cap2 m.data) + 2) (fH F.t pre.length out.length)
      (fA (pre ++ factorBlock L d labs cap1 cap2 m.data ++ rest) (entryBank out B) (fun _ => []) (List.replicate k false))
      (fH F.t (pre.length + (factorBlock L d labs cap1 cap2 m.data).length) out.length)
      (fA (pre ++ factorBlock L d labs cap1 cap2 m.data ++ rest) (firstBank f L d labs out B cap1 cap2) m.data
        (List.replicate k' false)) := by
  have hmap := targets_map f L d labs out B cap1 cap2 m.data
  have hl := loadL_run (srcI F.t) (loadF (firstBank f L d labs out B cap1 cap2) m.data) (targets F.t)
    (targets_nodup F.t) (src_not_mem F.t) pre rest (iH F.t pre.length out.length)
    (iA (pre ++ factorBlock L d labs cap1 cap2 m.data ++ rest) (entryBank out B) (fun _ : Fin F.t => []))
    (iH_src _ _ _) (by rw [iA_src, hmap]; rfl)
    (fun i hi => (entry_targets F.t pre.length out.length (pre ++ factorBlock L d labs cap1 cap2 m.data ++ rest) out B
      i hi).1)
    (fun i hi => (entry_targets F.t pre.length out.length (pre ++ factorBlock L d labs cap1 cap2 m.data ++ rest) out B
      i hi).2)
  rw [hmap] at hl
  obtain ⟨k', hm⟩ := maskBlank hl (selT F.t)
    (fun i hi => (entry_targets F.t pre.length out.length (pre ++ factorBlock L d labs cap1 cap2 m.data ++ rest) out B
      i (of_decide_eq_true hi)).1) k
  refine ⟨k', hm.congr ?_ ?_⟩
  · exact congrArg (fun g => Fin.addCases (motive := fun _ => ℕ) g (fun _ : Fin 1 => 0))
      (load_heads F.t pre.length (fieldsWord (factorFields L d labs cap1 cap2 m.data)).length out.length _)
  · exact congrArg (fun g => Fin.addCases (motive := fun _ => List Bool) g (fun _ : Fin 1 => List.replicate k' false))
      (load_tapes _ _ m.data out B (firstBank_o f L d labs out B cap1 cap2))

/-! ## The factor stage -/

/-- Every tape of the factor layout is the record, a bank tape, a data tape, or the log. -/
theorem cover (t : ℕ) (i : Fin (1 + (14 + t) + 1)) :
    i = srcO t ∨ (∃ c, i = prSlot t (Fin.castAdd t c)) ∨ (∃ j, i = prSlot t (Fin.natAdd 14 j)) ∨ i = logI t := by
  have hi := i.isLt
  by_cases h0 : i.val = 0
  · exact Or.inl (Fin.ext (by simp [srcO, srcI, h0]))
  · by_cases h1 : i.val < 15
    · exact Or.inr (Or.inl ⟨⟨i.val - 1, by omega⟩, Fin.ext (by simp [prSlot]; omega)⟩)
    · by_cases h2 : i.val < 15 + t
      · exact Or.inr (Or.inr (Or.inl ⟨⟨i.val - 15, by omega⟩, Fin.ext (by simp [prSlot]; omega)⟩))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext (by simp [logI]; omega))))

theorem prSlot_ne_src (t : ℕ) (j : Fin (14 + t)) : prSlot t j ≠ srcO t := by
  intro h; have := congrArg Fin.val h; simp [prSlot, srcO, srcI] at this

theorem prSlot_ne_log (t : ℕ) (j : Fin (14 + t)) : prSlot t j ≠ logI t := by
  intro h; have := congrArg Fin.val h; simp [prSlot, logI] at this; omega

theorem fH_prSlot (t p o : ℕ) (j : Fin (14 + t)) :
    fH t p o (prSlot t j) = Fin.addCases (motive := fun _ => ℕ) (bh o) (fun _ : Fin t => 0) j := by
  simp [fH, iH, prSlot]

theorem fA_prSlot {t : ℕ} (src : List Bool) (b : Bank) (data : Fin t → List Bool) (log : List Bool) (j : Fin (14 + t)) :
    fA src b data log (prSlot t j) = Fin.addCases (motive := fun _ => List Bool) b.tapes data j := by
  simp [fA, iA, prSlot]

theorem fH_srcO (t p o : ℕ) : fH t p o (srcO t) = p := by simp [fH, iH, srcO, srcI]
theorem fH_logI (t p o : ℕ) : fH t p o (logI t) = 0 := by simp [fH, logI]
theorem fA_srcO {t : ℕ} (src : List Bool) (b : Bank) (data : Fin t → List Bool) (log : List Bool) :
    fA src b data log (srcO t) = src := by simp [fA, iA, srcO, srcI]

/-- **The factor stage**: from the record cursor at a factor block, empty work tapes, blank logs of lengths `cap1`,
`cap2` and a blank log of any length, the output receives the factor's print `polyWord (factorPoly f L d labs)`; the
record cursor passes the block; every other head is at `0`. -/
theorem factor_step (F : EvalFam) {L : ℕ} {f : List Bool → Bool} (m : Member F L f) (labs : List ℕ) (d : ℕ)
    (hd : 1 ≤ d) (hlabs : L ≤ labs.length) (pre rest out B : List Bool) (cap1 cap2 k : ℕ) (hc1 : 2 * L + 1 ≤ cap1)
    (hc2 : ∀ xs : List Bool, xs.length = L → recInnerLCost xs labs ≤ cap1) :
    ∃ A', Step (factorM F) (factorCost F m d labs cap1 cap2) (fH F.t pre.length out.length)
      (fA (pre ++ factorBlock L d labs cap1 cap2 m.data ++ rest) (entryBank out B) (fun _ => [])
        (List.replicate k false))
      (fH F.t (pre.length + (factorBlock L d labs cap1 cap2 m.data).length) (out ++ Rec.polyWord (factorPoly f L d labs)).length)
      A' ∧ A' (srcO F.t) = pre ++ factorBlock L d labs cap1 cap2 m.data ++ rest ∧
      A' (outI F.t) = overlay (out ++ Rec.polyWord (factorPoly f L d labs)) B := by
  obtain ⟨k', hl⟩ := load_step F m labs d pre rest out B cap1 cap2 k (f := f)
  have hp := print_runG (recSpecL labs) m.pe d hd [] out B (labelWord labs) (List.replicate L false) cap1 cap2
    (by simp) (fun xs hxs => ⟨by omega, ⟨[false], by simp [labelWord]⟩, hc2 xs hxs⟩) hc1
  rw [printedAtG_zero, List.append_nil, printMG_eq] at hp
  set P := pre.length + (factorBlock L d labs cap1 cap2 m.data).length with hP
  set src := pre ++ factorBlock L d labs cap1 cap2 m.data ++ rest with hsrc
  set b1 := firstBank f L d labs out B cap1 cap2 with hb1
  have hp' : Step (printMU F) (printGCost (recSpecL labs) m.pe d)
      (Fin.addCases (motive := fun _ => ℕ) (m := 14) (n := F.t) (bh out.length) (fun _ => 0))
      (Fin.addCases (motive := fun _ => List Bool) (m := 14) (n := F.t) b1.tapes m.data)
      (Fin.addCases (motive := fun _ => ℕ) (m := 14) (n := F.t) (bh (out ++ Rec.polyWord (factorPoly f L d labs)).length)
        (fun _ => 0))
      (Fin.addCases (motive := fun _ => List Bool) (m := 14) (n := F.t)
        ({ outerBankG (recSpecL labs) f L d [] out B (labelWord labs) (List.replicate L false) cap1 cap2
            (Interp.goods L d).length with o := overlay (out ++ Rec.polyWord (factorPoly f L d labs)) B } : Bank).tapes
        m.data) := hp
  have hd' := dockRun hp' (prSlot F.t) (prSlot_inj F.t) (fH F.t P out.length) (fA src b1 m.data (List.replicate k' false))
    (fun j => by rw [fH_prSlot]) (fun j => by rw [fA_prSlot])
  refine ⟨_, (hl.seq hd').congr ?_ rfl, ?_, ?_⟩
  · funext i
    rcases cover F.t i with rfl | ⟨c, rfl⟩ | ⟨j, rfl⟩ | rfl
    · rw [dockH_other _ _ _ _ (fun j => prSlot_ne_src F.t j), fH_srcO, fH_srcO]
    · rw [dockH_slot _ (prSlot_inj F.t), fH_prSlot]
    · rw [dockH_slot _ (prSlot_inj F.t), fH_prSlot]
    · rw [dockH_other _ _ _ _ (fun j => prSlot_ne_log F.t j), fH_logI, fH_logI]
  · rw [install_other _ _ _ _ (fun j => prSlot_ne_src F.t j), fA_srcO]
  · show install (prSlot F.t) _ _ (prSlot F.t (Fin.castAdd F.t 10)) = _
    rw [install_slot _ (prSlot_inj F.t)]
    simp [Bank.tapes]

end NearCubicWires.WireExponent3_5.ListMachine.Row
