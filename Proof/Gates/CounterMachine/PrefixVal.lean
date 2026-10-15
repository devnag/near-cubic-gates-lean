import Proof.Gates.CounterMachine.PrefixMac
import Proof.Gates.CounterMachine.CellNats
import Proof.Gates.CounterMachine.ReqWord

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.PrefixProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary (frame)
open NearCubicWires.WireExponent3_5.FinalPass.Tm (frameP frame_eq_frameP)

/-- A framed `natWord`. -/
abbrev Fn (x : ℕ) : List Bool := frameP (natWord x)

theorem frameP_flat (L : List ℕ) : frameP (L.flatMap natWord) = L.flatMap Fn := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.flatMap_cons, frameP_append, ih]

theorem frameP_flatMap {α : Type} (L : List α) (f : α → List Bool) :
    frameP (L.flatMap f) = L.flatMap (fun a => frameP (f a)) := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.flatMap_cons, frameP_append, ih]

/-! ## The fields of a prefix -/

theorem frame_prefixWord {n : ℕ} (k s B : ℕ) (gates : List (NormalizedThresholdGate n)) (inner outer : List ℕ)
    (hbits : List Bool) (roles : List (ℕ × Bool)) (V : ℕ) :
    frame (prefixWord k s B gates inner outer hbits roles V) =
      Fn n ++ Fn k ++ Fn s ++ Fn B ++ (Fn gates.length ++ (gates.flatMap gateN).flatMap Fn) ++
        (Fn inner.length ++ inner.flatMap Fn) ++ (Fn outer.length ++ outer.flatMap Fn) ++
        (Fn hbits.length ++ hbits.flatMap (fun b => Fn (bitN b))) ++
        (Fn roles.length ++ roles.flatMap (fun ρ => Fn ρ.1 ++ Fn (bitN ρ.2))) ++ Fn V ++ [false] := by
  have hg : listWord gateWord gates = (([gates.length] ++ gates.flatMap gateN)).flatMap natWord := by
    rw [list_word]; congr 1; funext g; exact (gateN_word g).symm
  have hi : ∀ L : List ℕ, listWord natWord L = ([L.length] ++ L).flatMap natWord := by
    intro L; simp [listWord]
  have hb : listWord bitWord hbits = ([hbits.length] ++ hbits.map bitN).flatMap natWord := by
    simp [listWord, bitN, List.flatMap_map]; rfl
  have hr : listWord (fun ρ : ℕ × Bool => natWord ρ.1 ++ bitWord ρ.2) roles =
      ([roles.length] ++ roles.flatMap (fun ρ => [ρ.1, bitN ρ.2])).flatMap natWord := by
    simp [listWord, bitWord, bitN, List.flatMap_assoc]
  unfold prefixWord
  rw [frame_eq_frameP, hg, hi inner, hi outer, hb, hr]
  simp only [frameP_append, frameP_flatMap, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.flatMap_map, List.flatMap_assoc, List.append_assoc, List.singleton_append]

/-! ## Gate blocks -/

theorem gateN_length {n : ℕ} (g : NormalizedThresholdGate n) : (gateN g).length = 2 * n + 3 := by
  unfold gateN intN
  simp only [List.length_append, List.length_flatMap, List.length_cons]
  simp [List.sum_ofFn]; ring

theorem gates_flat_length {n : ℕ} (gates : List (NormalizedThresholdGate n)) :
    (gates.flatMap gateN).length = gates.length * (2 * n + 3) := by
  rw [List.length_flatMap]
  simp only [gateN_length, List.map_const', List.sum_replicate, smul_eq_mul]

theorem resGates_flat (c : Call) (B1 B2 : ℕ) (hadm : c.Admitted B1 B2) :
    resGates c = c.first.gates ++ c.second.gates := by
  unfold resGates
  split_ifs with h
  · rfl
  · rw [hadm.2.2.2.1 h]; simp [NCircuit.empty]

/-! ## Outer coordinates -/

theorem mem_coordsOf {n : ℕ} (I : Finset (Fin n)) (x : ℕ) : x ∈ coordsOf I ↔ ∃ h : x < n, (⟨x, h⟩ : Fin n) ∈ I := by
  simp only [coordsOf, List.mem_map, Finset.mem_sort]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j.isLt, hj⟩
  · rintro ⟨h, hI⟩; exact ⟨_, hI, rfl⟩

theorem outer_eq {n : ℕ} (I : Finset (Fin n)) :
    (outerCoords I).map Fin.val = (List.range n).filter (fun x => decide (x ∉ coordsOf I)) := by
  apply List.Perm.eq_of_pairwise' (r := (· < ·))
  · unfold outerCoords
    exact List.Pairwise.map Fin.val (fun a b h => h) (Finset.sortedLT_sort _).pairwise
  · exact List.Pairwise.filter _ (List.pairwise_lt_range)
  · rw [List.perm_ext_iff_of_nodup]
    · intro x
      simp only [outerCoords, List.mem_map, Finset.mem_sort, Finset.mem_filter, Finset.mem_univ, true_and,
        List.mem_filter, List.mem_range, decide_eq_true_eq, mem_coordsOf]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact ⟨j.isLt, fun ⟨_, h⟩ => hj h⟩
      · rintro ⟨hx, hn⟩; exact ⟨⟨x, hx⟩, fun h => hn ⟨hx, h⟩, rfl⟩
    · unfold outerCoords; exact (Finset.sort_nodup _ _).map Fin.val_injective
    · exact List.Nodup.filter _ (List.nodup_range)

/-! ## The part indicator -/

/-- The bit of the inner index `x` at the position of coordinate `i` (`false` outside the list). -/
def pbit (L : List ℕ) (x i : ℕ) : Bool := if i ∈ L then x.testBit (L.idxOf i) else false

theorem innerParity_innerPt (c : Call) (wt : Wit c.n) (x : ℕ) :
    innerParity c wt (innerPt wt.I x) = (c.parity.map (pbit (coordsOf wt.I) x)).foldl xor false := by
  unfold innerParity
  congr 1
  apply List.map_congr_left
  intro i _
  unfold pbit
  by_cases h : i < c.n
  · rw [dif_pos h]
    by_cases hI : (⟨i, h⟩ : Fin c.n) ∈ wt.I
    · rw [dif_pos hI, if_pos ((mem_coordsOf wt.I i).2 ⟨h, hI⟩)]; rfl
    · rw [dif_neg hI, if_neg (fun hm => hI (by obtain ⟨h', hI'⟩ := (mem_coordsOf wt.I i).1 hm; exact hI'))]
  · rw [dif_neg h, if_neg (fun hm => h (coordsOf_lt wt.I i hm))]

end NearCubicGates.Close.CounterMachine.PrefixProg
