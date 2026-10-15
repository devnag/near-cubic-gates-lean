import Proof.MachineModel.OrdinaryMemorySortedReplay

/-! The sequential check required at the actual sorter's output. It remembers
only the preceding cell and written bit. Literal field decoding replaces the
earlier semantic timestamp-index lookup. The finite-machine realization of
this scan is a separate execution obligation; no scan runtime is asserted here.
-/
namespace NearCubicWires.RepairOrdinary.MemoryScan
open MemoryLog MemorySort StablePartition RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def memory (previous : Event) : Memory :=
  fun cell => if cell = previous.cell then previous.after else false

def scan : Event → List Event → Bool
  | _, [] => true
  | previous, e :: es =>
      if e.read = memory previous e.cell then scan e es else false

def blank : Event := ⟨(0, 0), false, false⟩

theorem valid_congr (left right : Memory) (es : List Event)
    (h : ∀ e ∈ es, left e.cell = right e.cell) :
    valid left es ↔ valid right es := by
  have he : ∀ cell, (localRun (left cell) (atCell cell es)).isSome =
      (localRun (right cell) (atCell cell es)).isSome := by
    intro cell
    by_cases hm : ∃ e ∈ es, e.cell = cell
    · obtain ⟨e, hin, rfl⟩ := hm
      rw [h e hin]
    · have hn : atCell cell es = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro e hin
        have hne : e.cell ≠ cell := fun hc => hm ⟨e, hin, hc⟩
        simpa using hne
      rw [hn]
      rfl
  simp only [valid, he]

theorem scan_correct (key : Cell → ℕ) (previous : Event) (es : List Event)
    (before : ∀ e ∈ es, key previous.cell ≤ key e.cell)
    (ordered : es.Pairwise (fun e f => key e.cell ≤ key f.cell))
    (injective : ∀ e ∈ es, ∀ f ∈ es, key e.cell = key f.cell → e.cell = f.cell) :
    scan previous es = true ↔ valid (memory previous) es := by
  induction es generalizing previous with
  | nil => simp [scan, valid, atCell, localRun]
  | cons e es ih =>
      obtain ⟨headOrder, tailOrder⟩ := List.pairwise_cons.mp ordered
      have tailInjective : ∀ a ∈ es, ∀ b ∈ es,
          key a.cell = key b.cell → a.cell = b.cell := by
        intro a ha b hb
        exact injective a (by simp [ha]) b (by simp [hb])
      rw [valid_cons]
      by_cases hread : e.read = memory previous e.cell
      · simp only [scan, hread, if_true, true_and]
        rw [ih e headOrder tailOrder tailInjective]
        apply valid_congr
        intro f hf
        by_cases he : f.cell = e.cell
        · simp [memory, he]
        · have hp : f.cell ≠ previous.cell := by
            intro hp
            have hpe := before e (by simp)
            have hef := headOrder f hf
            have hk : key e.cell = key f.cell := by rw [← hp] at hpe; omega
            exact he (injective e (by simp) f (by simp [hf]) hk).symm
          simp [memory, he, hp]
      · simp [scan, hread]

theorem cellCode_div (W : ℕ) (cell : Cell) (h : cell.2 < 2^W) :
    cellCode W cell / 2^W = cell.1 := by
  rw [cellCode, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt h, zero_add]

theorem cellCode_injective (W : ℕ) (a b : Cell)
    (ha : a.2 < 2^W) (hb : b.2 < 2^W)
    (he : cellCode W a = cellCode W b) : a = b := by
  have hd := congrArg (fun n => n / 2^W) he
  have hm := congrArg (fun n => n % 2^W) he
  simp only [cellCode_div W a ha, cellCode_div W b hb] at hd
  simp [cellCode, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hm
  exact Prod.ext hd hm

theorem scan_blank (W : ℕ) (es : List Event)
    (fits : ∀ e ∈ es, e.cell.2 < 2^W)
    (ordered : es.Pairwise (fun e f => cellCode W e.cell ≤ cellCode W f.cell)) :
    scan blank es = true ↔ valid (fun _ => false) es := by
  have hb : ∀ e ∈ es, cellCode W blank.cell ≤ cellCode W e.cell := by
    intro e _
    simp [blank, cellCode]
  have hi : ∀ e ∈ es, ∀ f ∈ es,
      cellCode W e.cell = cellCode W f.cell → e.cell = f.cell := by
    intro e he f hf
    exact cellCode_injective W e.cell f.cell (fits e he) (fits f hf)
  have hm : memory blank = (fun _ => false) := by
    funext cell
    change (if cell = (0, 0) then false else false) = false
    exact ite_self false
  have hs := scan_correct (cellCode W) blank es hb ordered hi
  rw [hm] at hs
  exact hs

/-- Decode actual payload/key bits. The timestamp is skipped, never used to
index a semantic tuple or obtain the event from an uncharged lookup. -/
def decode (I W : ℕ) (record : Record) : Event :=
  let code := value (record.2.drop (I+1))
  ⟨(code / 2^W, code % 2^W), record.1, record.2.headD false⟩

theorem decode_encoded (I K W timestamp : ℕ) (e : Event)
    (hc : cellCode W e.cell < 2^K) (ha : e.cell.2 < 2^W) :
    decode I W (encoded I K W timestamp e) = e := by
  have hv : value ((encoded I K W timestamp e).2.drop (I+1)) = cellCode W e.cell := by
    simp only [encoded, List.drop_succ_cons]
    have hd : (binary I timestamp ++ binary K (cellCode W e.cell)).drop
        (binary I timestamp).length = binary K (cellCode W e.cell) := List.drop_left
    simp only [binary_length] at hd
    rw [hd]
    exact binary_value K _ hc
  dsimp only [decode]
  rw [hv]
  have hq := cellCode_div W e.cell ha
  have hr : cellCode W e.cell % 2^W = e.cell.2 := by
    simp [cellCode, Nat.mod_eq_of_lt ha]
  cases e
  simp [hq, hr, encoded]

theorem decoded_output {N : ℕ} (I K W : ℕ) (events : Fin N → Event)
    (hN : N ≤ 2^I) (hc : ∀ i, cellCode W (events i).cell < 2^K)
    (ha : ∀ i, (events i).cell.2 < 2^W) :
    (SortCarrier.sorted (request I K W events)).map (decode I W) =
      (sortedIndices I K W events).map events := by
  rw [← sorted_output I K W events hN, List.map_map]
  apply List.map_congr_left
  intro i _
  exact decode_encoded I K W i.val (events i) (hc i) (ha i)

theorem sorted_cell_order {N : ℕ} (I K W : ℕ) (events : Fin N → Event)
    (hN : N ≤ 2^I) (hc : ∀ i, cellCode W (events i).cell < 2^K) :
    ((sortedIndices I K W events).map events).Pairwise
      (fun e f => cellCode W e.cell ≤ cellCode W f.cell) := by
  have hs := SortCarrier.sorted_order (request I K W events)
  rw [← sorted_output I K W events hN, List.pairwise_map] at hs
  rw [List.pairwise_map]
  apply hs.imp
  intro i j hij
  rw [encoded_key, encoded_key] at hij
  have inner : ∀ i : Fin N, 2*i.val+(events i).after.toNat < 2^(I+1) := by
    intro i
    have hi := i.isLt.trans_le hN
    cases (events i).after <;> simp only [Bool.toNat_false, Bool.toNat_true, pow_succ] <;> omega
  have ho := (CoordinateKey.key_order (I+1) K _ _ _ _ _ _ (inner i) (inner j) (hc i) (hc j)).mp hij
  omega

/-- The complete semantic checker interface at the literal sorted records.
This is an executable list scan, not a search through the original tuple.
Its ordinary-machine realization and cost are not assumed by this theorem. -/
theorem literal_scan_iff {N : ℕ} (I K W : ℕ) (events : Fin N → Event)
    (hN : N ≤ 2^I) (hc : ∀ i, cellCode W (events i).cell < 2^K)
    (ha : ∀ i, (events i).cell.2 < 2^W) :
    scan blank ((SortCarrier.sorted (request I K W events)).map (decode I W)) = true ↔
      (MemoryLog.run (fun _ => false) ((List.finRange N).map events)).isSome = true := by
  rw [decoded_output I K W events hN hc ha]
  have hfit : ∀ e ∈ (sortedIndices I K W events).map events, e.cell.2 < 2^W := by
    intro e he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    exact ha i
  rw [scan_blank W _ hfit (sorted_cell_order I K W events hN hc), run_success_iff]
  simp only [valid, cell_subsequence I K W events hN hc]

end NearCubicWires.RepairOrdinary.MemoryScan
