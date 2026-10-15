import Proof.Wire_3_5.CompilerMachinePolyMono
import Proof.Wire_3_5.CompilerMachineKit4

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Poly
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Unions NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform

theorem f1_inv (Q : ℕ) (pool : List (List SynEq)) (ps : PS) (mono : List ℕ) (hmono : ∀ a ∈ mono, a < pool.length)
    (h : PInv (Q + pool.flatten.length + 1) ps) :
    PInv (Q + pool.flatten.length + 1) (f1 Q pool ps mono) ∧
      (f1 Q pool ps mono).G.length ≤ ps.G.length + (monoMasks pool mono).length := by
  obtain ⟨hR, hR2, hR3, hX, hY, hG⟩ := h
  obtain ⟨m1, m2, m3, m4⟩ := msOf_inv Q pool mono ps hmono hR hR2 hR3
  have hLs := msOf_L Q pool mono ps hmono
  have hLw : ∀ x ∈ (msOf Q pool mono ps).L, x.length = Q + pool.flatten.length + 1 := by
    rw [hLs]; intro x hx
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
    exact entryWord_length Q _ 0 u (by omega)
  obtain ⟨a1, a2, a3, a4⟩ := foldl_allStep_inv (Q + pool.flatten.length + 1) (msOf Q pool mono ps).L ps.G.length
    (as0 ps) hLw ⟨hG, hX, hY, le_refl _⟩
  refine ⟨⟨m2, m3, m4, a2, a3, a1⟩, ?_⟩
  show ((msOf Q pool mono ps).L.foldl allStep (as0 ps)).G.length ≤ _
  have hlen : (msOf Q pool mono ps).L.length = (monoMasks pool mono).length := by rw [hLs, List.length_map]
  rw [hlen] at a4
  exact a4

theorem foldl_f1_G (Q : ℕ) (pool : List (List SynEq)) : ∀ (p : F2Poly ℕ) (ps : PS), (∀ mono ∈ p, ∀ a ∈ mono, a < pool.length) →
    (p.foldl (f1 Q pool) ps).G =
      ((p.flatMap (monoMasks pool)).map (fun U => ew Q pool.flatten.length (0, U))).foldl symInsertW ps.G
  | [], _, _ => rfl
  | mono :: p, ps, hp => by
    rw [List.foldl_cons, foldl_f1_G Q pool p _ (fun m hm => hp m (List.mem_cons_of_mem mono hm)),
      f1_G Q pool ps mono (hp mono List.mem_cons_self), List.flatMap_cons, List.map_append, List.foldl_append]

theorem foldl_f1_inv (Q : ℕ) (pool : List (List SynEq)) : ∀ (p : F2Poly ℕ) (ps : PS),
    (∀ mono ∈ p, ∀ a ∈ mono, a < pool.length) → PInv (Q + pool.flatten.length + 1) ps →
      PInv (Q + pool.flatten.length + 1) (p.foldl (f1 Q pool) ps) ∧
        (p.foldl (f1 Q pool) ps).G.length ≤ ps.G.length + (p.flatMap (monoMasks pool)).length
  | [], _, _, h => ⟨h, by simp⟩
  | mono :: p, ps, hp, h => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := f1_inv Q pool ps mono (hp mono List.mem_cons_self) h
    obtain ⟨h3, h4⟩ := foldl_f1_inv Q pool p _ (fun m hm => hp m (List.mem_cons_of_mem mono hm)) h1
    refine ⟨h3, h4.trans ?_⟩
    rw [List.flatMap_cons, List.length_append]
    omega

/-! ## The loop over a polynomial's monomials -/

/-- The loop over a polynomial's monomial records (source: the expression tape). -/
noncomputable def polyLoopM := StreamController.machine monoInsM 0

theorem recW_head (mono : List ℕ) : ∃ l, recW mono = true :: l := ⟨_, rfl⟩

theorem poly_run (Q : ℕ) (pool : List (List SynEq)) (p : F2Poly ℕ) (P post staleT : List Bool) (ps : PS)
    (cap cap2 cap3 d B : ℕ) (hp : ∀ mono ∈ p, ∀ a ∈ mono, a < pool.length) (hd : ∀ mono ∈ p, mono.length ≤ d)
    (hinv : PInv (Q + pool.flatten.length + 1) ps) (hB : ps.G.length + (p.flatMap (monoMasks pool)).length ≤ B)
    (hc : Caps d pool.length Q pool.flatten.length B cap cap2 cap3) :
    Step polyLoopM (p.length * (monoInsCost d pool.length Q pool.flatten.length B + 2) + 1) (head1 P.length)
      (bank1 (P ++ p.flatMap recW ++ false :: post) (tableTape (childTable Q pool) staleT) cap cap2 cap3
        (z0 Q pool.flatten.length) ps)
      (head1 (P.length + (p.flatMap recW).length))
      (bank1 (P ++ p.flatMap recW ++ false :: post) (tableTape (childTable Q pool) staleT) cap cap2 cap3
        (z0 Q pool.flatten.length) (p.foldl (f1 Q pool) ps)) := by
  refine encRun recW recW_head monoInsM 0 P p post (f1 Q pool) ps (fun _ q => head1 q)
    (fun st => bank1 (P ++ p.flatMap recW ++ false :: post) (tableTape (childTable Q pool) staleT) cap cap2 cap3
      (z0 Q pool.flatten.length) st) (fun _ => rfl) (fun _ _ => rfl) (monoInsCost d pool.length Q pool.flatten.length B) ?_
  intro j hj
  have hmj := List.getElem_mem hj
  have hst : (p.take (j + 1)).foldl (f1 Q pool) ps = f1 Q pool ((p.take j).foldl (f1 Q pool) ps) p[j] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]
    rfl
  obtain ⟨hinvj, hlenj⟩ := foldl_f1_inv Q pool (p.take j) ps (fun m hm => hp m (List.mem_of_mem_take hm)) hinv
  have hmasks : ((p.take j).flatMap (monoMasks pool)).length + (monoMasks pool p[j]).length ≤
      (p.flatMap (monoMasks pool)).length := by
    have e : p = p.take j ++ p[j] :: p.drop (j + 1) := by
      rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
    conv_rhs => rw [e]
    rw [List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append]
    omega
  have hb := mono_ins_step Q pool p[j] (P ++ (p.take j).flatMap recW) ((p.drop (j + 1)).flatMap recW ++ false :: post)
    staleT ((p.take j).foldl (f1 Q pool) ps) cap cap2 cap3 d (ps.G.length + ((p.take j).flatMap (monoMasks pool)).length) B
    (hp _ hmj) (hd _ hmj) hinvj hlenj (by omega) hc
  have hsplit : P ++ (p.take j).flatMap recW ++ recW p[j] ++ ((p.drop (j + 1)).flatMap recW ++ false :: post) =
      P ++ p.flatMap recW ++ false :: post := by
    rw [enc_split recW p j hj]; simp [List.append_assoc]
  rw [hsplit] at hb
  rw [hst, enc_succ_length recW p j hj]
  simpa [List.length_append, Nat.add_assoc] using hb

/-- **The running list after the polynomial is its cancelled substitution** (from the empty list). -/
theorem poly_G (Q : ℕ) (pool : List (List SynEq)) (p : F2Poly ℕ) (ps : PS) (hG : ps.G = [])
    (hp : ∀ mono ∈ p, ∀ a ∈ mono, a < pool.length) :
    (p.foldl (f1 Q pool) ps).G = (oddMasksM pool p).map (fun U => ew Q pool.flatten.length (0, U)) := by
  rw [foldl_f1_G Q pool p ps hp, hG, oddMasksM_entries]

end NearCubicWires.WireExponent3_5.CompilerMachine.Poly
