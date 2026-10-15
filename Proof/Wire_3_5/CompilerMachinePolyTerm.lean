import Proof.Wire_3_5.CompilerMachinePolyFactor
import Proof.Wire_3_5.CompilerMachineOrder

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Poly
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Unions NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-- The factor loop's state: the pipeline state, the parity cell, the factor index. -/
def f2i (Q : ℕ) (pool : List (List SynEq)) (j : ℕ) (st : PS × Bool × ℕ) (f : F2Poly ℕ) : PS × Bool × ℕ :=
  ((f2 Q pool (j.testBit st.2.2) (st.1, st.2.1) f).1, (f2 Q pool (j.testBit st.2.2) (st.1, st.2.1) f).2, st.2.2 + 1)

theorem foldl_f2i (Q : ℕ) (pool : List (List SynEq)) (j : ℕ) : ∀ (fs : List (F2Poly ℕ)) (ps : PS) (PJ : Bool) (i : ℕ),
    fs.foldl (f2i Q pool j) (ps, PJ, i) =
      ((selectBits fs (j / 2 ^ i)).flatten.foldl (f1 Q pool) ps,
        xor PJ (decide ((selectBits fs (j / 2 ^ i)).length % 2 = 1)), i + fs.length)
  | [], ps, PJ, i => by simp [selectBits]
  | f :: fs, ps, PJ, i => by
    rw [List.foldl_cons]
    have hb : j.testBit i = decide ((j / 2 ^ i) % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
    have hd : j / 2 ^ i / 2 = j / 2 ^ (i + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
    by_cases h : (j / 2 ^ i) % 2 = 1
    · have hb' : j.testBit i = true := by rw [hb]; simp [h]
      have e : f2i Q pool j (ps, PJ, i) f = (f.foldl (f1 Q pool) ps, !PJ, i + 1) := by
        simp [f2i, f2, hb']
      rw [e, foldl_f2i Q pool j fs _ _ (i + 1)]
      simp only [selectBits, h, if_true, List.flatten_cons, List.foldl_append, List.length_cons, hd]
      refine Prod.ext rfl (Prod.ext ?_ (by simp; omega))
      simp only
      generalize (selectBits fs (j / 2 ^ (i + 1))).length = n
      cases PJ <;> rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;> simp [h2, Nat.add_mod]
    · have hb' : j.testBit i = false := by rw [hb]; simp [h]
      have e : f2i Q pool j (ps, PJ, i) f = (ps, PJ, i + 1) := by
        simp [f2i, f2, hb']
      have h0 : (j / 2 ^ i) % 2 = 0 := by omega
      rw [e, foldl_f2i Q pool j fs _ _ (i + 1)]
      simp only [selectBits, h0, List.length_cons, hd]
      refine Prod.ext rfl (Prod.ext rfl (by simp; omega))

theorem selectBits_sublist {α : Type} : ∀ (ps : List α) (j : ℕ), List.Sublist (selectBits ps j) ps
  | [], _ => List.Sublist.slnil
  | p :: ps, j => by
    unfold selectBits
    split_ifs
    · exact (selectBits_sublist ps (j / 2)).cons_cons p
    · exact (selectBits_sublist ps (j / 2)).cons p

theorem masks_sublist_le (pool : List (List SynEq)) {a b : List (F2Poly ℕ)} (h : List.Sublist a b) :
    (a.flatten.flatMap (monoMasks pool)).length ≤ (b.flatten.flatMap (monoMasks pool)).length :=
  ((h.flatten).flatMap _).length_le

theorem factorRec_head (f : F2Poly ℕ) : ∃ l, factorRec f = true :: l := ⟨_, rfl⟩

theorem factors_run (Q : ℕ) (pool : List (List SynEq)) (fs : List (F2Poly ℕ)) (j m : ℕ) (P post staleT : List Bool)
    (ps : PS) (PJ : Bool) (cap cap2 cap3 d B NF CB : ℕ) (hm : fs.length = m)
    (hp : ∀ f ∈ fs, ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length) (hd : ∀ f ∈ fs, ∀ mono ∈ f, mono.length ≤ d)
    (hNF : ∀ f ∈ fs, f.length ≤ NF) (hCB : ∀ f ∈ fs, ∀ mono ∈ f, (codeBits mono).length ≤ CB)
    (hinv : PInv (Q + pool.flatten.length + 1) ps)
    (hB : ps.G.length + (fs.flatten.flatMap (monoMasks pool)).length ≤ B)
    (hc : Caps d pool.length Q pool.flatten.length B cap cap2 cap3) :
    Step (StreamController.machine factorM 0) (fs.length * (factorCost NF CB d pool.length Q pool.flatten.length B + 2) + 1)
      (head2 P.length 1)
      (bank2 (P ++ fs.flatMap factorRec ++ false :: post) (tableTape (childTable Q pool) staleT) cap cap2 cap3
        (z0 Q pool.flatten.length) (frame (binary m j)) ps PJ)
      (head2 (P.length + (fs.flatMap factorRec).length) (2 * fs.length + 1))
      (bank2 (P ++ fs.flatMap factorRec ++ false :: post) (tableTape (childTable Q pool) staleT) cap cap2 cap3
        (z0 Q pool.flatten.length) (frame (binary m j)) (fs.foldl (f2i Q pool j) (ps, PJ, 0)).1
        (fs.foldl (f2i Q pool j) (ps, PJ, 0)).2.1) := by
  have h := encRun factorRec factorRec_head factorM 0 P fs post (f2i Q pool j) (ps, PJ, 0)
    (fun st q => head2 q (2 * st.2.2 + 1))
    (fun st => bank2 (P ++ fs.flatMap factorRec ++ false :: post) (tableTape (childTable Q pool) staleT) cap cap2 cap3
      (z0 Q pool.flatten.length) (frame (binary m j)) st.1 st.2.1) (fun _ => rfl) (fun _ _ => rfl)
    (factorCost NF CB d pool.length Q pool.flatten.length B) (by
      intro k hk
      have hfk := List.getElem_mem hk
      have hst : (fs.take (k + 1)).foldl (f2i Q pool j) (ps, PJ, 0) =
          f2i Q pool j ((fs.take k).foldl (f2i Q pool j) (ps, PJ, 0)) fs[k] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
        rfl
      have hfold := foldl_f2i Q pool j (fs.take k) ps PJ 0
      simp only [pow_zero, Nat.div_one, Nat.zero_add] at hfold
      have hidx : ((fs.take k).foldl (f2i Q pool j) (ps, PJ, 0)).2.2 = k := by
        rw [hfold]; simp; omega
      have hsel := selectBits_sublist (fs.take k) j
      obtain ⟨hinvk, hlenk⟩ := foldl_f1_inv Q pool (selectBits (fs.take k) j).flatten ps
        (fun mono hmono a ha => by
          obtain ⟨f, hf, hmf⟩ := List.mem_flatten.mp hmono
          exact hp f (List.mem_of_mem_take (hsel.subset hf)) mono hmf a ha) hinv
      have hstate1 : ((fs.take k).foldl (f2i Q pool j) (ps, PJ, 0)).1 =
          (selectBits (fs.take k) j).flatten.foldl (f1 Q pool) ps := by rw [hfold]
      have hmk : ((selectBits (fs.take k) j).flatten.flatMap (monoMasks pool)).length ≤
          ((fs.take k).flatten.flatMap (monoMasks pool)).length := masks_sublist_le pool hsel
      have htot : ((fs.take k).flatten.flatMap (monoMasks pool)).length + (fs[k].flatMap (monoMasks pool)).length ≤
          (fs.flatten.flatMap (monoMasks pool)).length := by
        have e : fs = fs.take k ++ fs[k] :: fs.drop (k + 1) := by
          rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
        conv_rhs => rw [e]
        simp only [List.flatten_append, List.flatten_cons, List.flatMap_append, List.length_append]
        omega
      have hread : readTapeBit (frame (binary m j)) (2 * k + 1) = j.testBit k := by
        rw [read_frame_bit (binary m j) k (by rw [binary_length]; omega), binary_getElem]
      have hb := factor_step Q pool fs[k] (P ++ (fs.take k).flatMap factorRec)
        ((fs.drop (k + 1)).flatMap factorRec ++ false :: post) staleT (frame (binary m j))
        ((fs.take k).foldl (f2i Q pool j) (ps, PJ, 0)).1 ((fs.take k).foldl (f2i Q pool j) (ps, PJ, 0)).2.1
        (j.testBit k) cap cap2 cap3 d B NF CB (2 * k + 1) hread (hp _ hfk) (hd _ hfk) (hNF _ hfk) (hCB _ hfk)
        (by rw [hstate1]; exact hinvk) (by rw [hstate1]; omega) hc
      have hsplit : P ++ (fs.take k).flatMap factorRec ++ factorRec fs[k] ++
          ((fs.drop (k + 1)).flatMap factorRec ++ false :: post) = P ++ fs.flatMap factorRec ++ false :: post := by
        rw [enc_split factorRec fs k hk]; simp [List.append_assoc]
      rw [hsplit] at hb
      have hf2 : f2i Q pool j ((fs.take k).foldl (f2i Q pool j) (ps, PJ, 0)) fs[k] =
          ((f2 Q pool (j.testBit k) (((fs.take k).foldl (f2i Q pool j) (ps, PJ, 0)).1,
              ((fs.take k).foldl (f2i Q pool j) (ps, PJ, 0)).2.1) fs[k]).1,
            (f2 Q pool (j.testBit k) (((fs.take k).foldl (f2i Q pool j) (ps, PJ, 0)).1,
              ((fs.take k).foldl (f2i Q pool j) (ps, PJ, 0)).2.1) fs[k]).2, k + 1) := by
        simp only [f2i, hidx]
      rw [hst, enc_succ_length factorRec fs k hk, hf2, hidx]
      refine (hb.congr_in ?_ rfl).congr ?_ ?_
      · funext i; fin_cases i <;> simp [head2]
      · funext i; fin_cases i <;> simp [head2]
        all_goals omega
      · funext i; fin_cases i <;> rfl)
  have hfin := foldl_f2i Q pool j fs ps PJ 0
  simp only [pow_zero, Nat.div_one, Nat.zero_add] at hfin
  have hidx : (fs.foldl (f2i Q pool j) (ps, PJ, 0)).2.2 = fs.length := by rw [hfin]
  rw [hidx] at h
  exact h

/-- **The running list after the factors is the cancelled polarized polynomial** (from the empty list). -/
theorem factors_G (Q : ℕ) (pool : List (List SynEq)) (fs : List (F2Poly ℕ)) (j : ℕ) (ps : PS) (PJ : Bool)
    (hG : ps.G = []) (hp : ∀ f ∈ fs, ∀ mono ∈ f, ∀ a ∈ mono, a < pool.length) :
    (fs.foldl (f2i Q pool j) (ps, PJ, 0)).1.G =
      (oddMasksM pool (selectBits fs j).flatten).map (fun U => ew Q pool.flatten.length (0, U)) := by
  have hfin := foldl_f2i Q pool j fs ps PJ 0
  simp only [pow_zero, Nat.div_one] at hfin
  rw [hfin]
  exact poly_G Q pool (selectBits fs j).flatten ps hG (fun mono hmono a ha => by
    obtain ⟨f, hf, hmf⟩ := List.mem_flatten.mp hmono
    exact hp f ((selectBits_sublist fs j).subset hf) mono hmf a ha)

/-- **The parity cell after the factors**: the sign of the sub-list, `|selectBits fs j| mod 2`. -/
theorem factors_PJ (Q : ℕ) (pool : List (List SynEq)) (fs : List (F2Poly ℕ)) (j : ℕ) (ps : PS) :
    (fs.foldl (f2i Q pool j) (ps, false, 0)).2.1 = decide ((selectBits fs j).length % 2 = 1) := by
  have hfin := foldl_f2i Q pool j fs ps false 0
  simp only [pow_zero, Nat.div_one] at hfin
  rw [hfin]
  simp

end NearCubicWires.WireExponent3_5.CompilerMachine.Poly
