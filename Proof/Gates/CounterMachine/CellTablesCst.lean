import Proof.Gates.CounterMachine.CellTablesWalk2

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader
open NearCubicGates.Close.CounterMachine.PrefixProg (Oth Oth.refl Oth.trans j1 yv yJ)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW)

/-! ## The walk -/

def walkP : St VV MM := .seq (.op (.rwM sN)) (.seq (.op (.zero wN)) (.seq callW (.seq parW witW)))

theorem walk_spec (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (b : DS VV MM)
    (hN : b.ram sN = cellN c p wt) (hQ : b.ram sQ = []) (hQc : b.rc sQ = 0) (hgS : b.env gS = 2 * c.n + 3)
    (hJR : b.env gJR = p.J * roleCount c.kind) (hc : Cst b) (hL : (cellN c p wt).length < 2 ^ C.Wd)
    (hS : p.factors.sum < 2 ^ C.Wd) :
    Hs C walkP b (b.rc sN + 20 * (cellN c p wt).length + 300) (fun e =>
      e.ram = Function.update b.ram sQ (p.primes.sort (· ≤ ·)) ∧
      e.rc = Function.update (Function.update b.rc sN (cellN c p wt).length) sQ (p.primes.sort (· ≤ ·)).length ∧
      e.env wN = (cellN c p wt).length ∧ ParV e p ∧ e.out = b.out ∧ Oth b e ∧ Cst e ∧ Fr b e parT) := by
  set L := cellN c p wt with hLdef
  have hsplit : L = callN c ++ (paramsN p ++ (witN c p wt ++ [])) := by simp [hLdef, cellN, List.append_assoc]
  have hlen : L.length = (callN c).length + (paramsN p).length + (witN c p wt).length := by
    rw [hsplit]; simp; omega
  apply Hx.hs
  refine Hs.then (hs_rwM C sN b) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.then (hs_zero C wN _) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  have w0 : WS b ((b.rew sN).set wN 0) L L [] :=
    ⟨by simp [DS.rew], by simp [DS.rew], by simp [DS.rew, hN], by simp [DS.rew, hQ],
      fun m h1 _ => by simp [DS.rew], by simp [DS.rew, Function.update_of_ne (show sQ ≠ sN by decide), hQc],
      fun m h1 _ => by simp [DS.rew, Function.update_of_ne h1], by simp [DS.rew], by simp [DS.rew],
      ⟨rfl, rfl, rfl, rfl⟩, ⟨by vsimp [DS.rew, hc.z], by vsimp [DS.rew, hc.one], by vsimp [DS.rew, hc.two]⟩⟩
  rw [hsplit] at w0
  have hL' : (callN c ++ (paramsN p ++ (witN c p wt ++ []))).length < 2 ^ C.Wd := by rw [← hsplit]; exact hL
  refine Hs.then (w0.callW c hL' (by vsimp [DS.rew, hgS])) (fun e3 ⟨w3, f3⟩ n3 hn3 => ?_)
  refine Hs.then (w3.parW p hL' hS) (fun e4 ⟨w4, v4, f4⟩ n4 hn4 => ?_)
  refine Hs.last (w4.witW c p wt hL' (by rw [f4 gJR (by decide), f3 gJR (by decide)]; vsimp [DS.rew, hJR]))
    (fun e5 ⟨w5, f5⟩ n5 hn5 => ?_)
  have hfr : Fr b e5 parT := Fr.trans (Fr.trans (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken f3 (by decide)))
    (Fr.weaken f4 (by decide))) (Fr.weaken f5 (by decide))
  have hl5 := w5.len
  simp only [List.length_nil, add_zero] at hl5
  rw [← hsplit] at hl5
  refine ⟨⟨?_, ?_, by rw [w5.cnt, hl5], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, w5.out,
    w5.oth.trans ⟨rfl, rfl, rfl, rfl⟩, w5.cst, hfr⟩, ?_⟩
  · funext m
    by_cases h1 : m = sQ
    · subst h1; simp [w5.ramQ]
    · by_cases h2 : m = sN
      · subst h2; rw [Function.update_of_ne h1, w5.ramN, hN, hsplit]
      · rw [Function.update_of_ne h1, w5.ram m h2 h1]
  · funext m
    by_cases h1 : m = sQ
    · subst h1; simp [w5.rcQ]
    · by_cases h2 : m = sN
      · subst h2; rw [Function.update_of_ne h1, hl5]; simp
      · rw [Function.update_of_ne h1, Function.update_of_ne h2, w5.rc m h2 h1]
  · rw [f5 wW (by decide)]; exact v4.W
  · rw [f5 wK (by decide)]; exact v4.k
  · rw [f5 wP (by decide)]; exact v4.P
  · rw [f5 wE (by decide)]; exact v4.ex
  · rw [f5 wNP (by decide)]; exact v4.np
  · rw [f5 wM1 (by decide)]; exact v4.M1
  · rw [f5 wF (by decide)]; exact v4.F
  · rw [f5 wA (by decide)]; exact v4.A
  · omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
