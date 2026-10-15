import Proof.Gates.CounterMachine.PrefixHb

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.PrefixProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader

/-- Every scratch variable of the printing phase. -/
def TA : List (Fin VV) := [y0, y1, y2, y3, y4, j1, yv, yJ, jo, fl, jx, par, pi, jp, js, ci, pw, q1, r1, q2, r2, tt,
  hv, jr]

def hdrP : St VV MM := .seq (femNat gN) (.seq (femNat xk) (.seq (femNat xs) (femNat xB)))
def innerP : St VV MM := .seq (femNat xkk) (emAll sIn xkk)

/-- **One prefix.** -/
def preP (gates hb roles : St VV MM) (xV : Fin VV) : St VV MM :=
  .seq hdrP (.seq gates (.seq innerP (.seq outerP (.seq hb (.seq roles (.seq (femNat xV) (.op (.emit false))))))))

theorem femTA (C : Ctx) (x : Fin VV) (hx : x ∉ TA) (a d : DS VV MM) (hfr : Fr a d TA) (hv : Valid C d) (hc : Cst a)
    (hW : 2 ≤ C.Wd) (Λ : ℕ) (hΛ : natBitLength (a.env x) ≤ Λ) :
    OutT C (femNat x) d (25 * Λ + 25) (Fn (a.env x)) TA := by
  have hx' : d.env x = a.env x := hfr x hx
  have hxf : x ∉ femT := fun h => hx (by simp [femT] at h; simp [TA]; tauto)
  have h1 := femO C x hxf d hv (Cst.of_fr hc hfr (by decide)) hW
  have h2 : OutT C (femNat x) d (25 * natBitLength (d.env x) + 25) (Fn (d.env x)) TA := h1.weaken (by decide)
  rw [hx'] at h2
  exact h2.mono (by omega)

theorem preO (C : Ctx) (a : DS VV MM) (hva : Valid C a) (hc : Cst a) (hW : 2 ≤ C.Wd) (Λ n : ℕ) (L : List ℕ)
    (hn : a.env gN = n) (hL : a.ram sIn = L) (hk : a.env xkk = L.length) (hΛn : natBitLength n ≤ Λ)
    (hΛk : natBitLength (a.env xk) ≤ Λ) (hΛs : natBitLength (a.env xs) ≤ Λ) (hΛB : natBitLength (a.env xB) ≤ Λ)
    (hLΛ : ∀ x ∈ L, natBitLength x ≤ Λ) (hLk : natBitLength L.length ≤ Λ) (xV : Fin VV) (hxV : xV ∉ TA)
    (hΛV : natBitLength (a.env xV) ≤ Λ) (gates hb roles : St VV MM) (tg th tr : ℕ) (Δg Δh Δr : List Bool)
    (hg : ∀ d, d.ram = a.ram → Oth a d → Fr a d TA → Valid C d → OutT C gates d tg Δg TA)
    (hh : ∀ d, d.ram = a.ram → Oth a d → Fr a d TA → Valid C d → OutT C hb d th Δh TA)
    (hr : ∀ d, d.ram = a.ram → Oth a d → Fr a d TA → Valid C d → OutT C roles d tr Δr TA) :
    OutT C (preP gates hb roles xV) a (tg + th + tr + (n + L.length + 8) * (25 * Λ + 9 * L.length + 50))
      (Fn n ++ Fn (a.env xk) ++ Fn (a.env xs) ++ Fn (a.env xB) ++ Δg ++ (Fn L.length ++ L.flatMap Fn) ++
        (Fn (a.env xs) ++ ((List.range n).filter (fun x => decide (x ∉ L))).flatMap Fn) ++ Δh ++ Δr ++
        Fn (a.env xV) ++ [false]) TA := by
  have fem : ∀ x : Fin VV, x ∉ TA → natBitLength (a.env x) ≤ Λ → ∀ d, d.ram = a.ram → Oth a d → Fr a d TA →
      Valid C d → OutT C (femNat x) d (25 * Λ + 25) (Fn (a.env x)) TA :=
    fun x hx hΛx d _ _ hfr hv => femTA C x hx a d hfr hv hc hW Λ hΛx
  have hdr : OutT C hdrP a (4 * (25 * Λ + 25) + 3) (Fn n ++ Fn (a.env xk) ++ Fn (a.env xs) ++ Fn (a.env xB)) TA := by
    have h := seqT (fem gN (by decide) (by rw [hn]; exact hΛn) a rfl (Oth.refl a) (Fr.refl _ _) hva)
      (fun d1 e1 o1 f1 v1' => seqT (fem xk (by decide) hΛk d1 e1 o1 f1 v1') (fun d2 e2 o2 f2 v2' =>
        seqT (fem xs (by decide) hΛs d2 (e2.trans e1) (o1.trans o2) (Fr.trans f1 f2) v2')
          (fun d3 e3 o3 f3 v3' => fem xB (by decide) hΛB d3 (e3.trans (e2.trans e1)) (o1.trans (o2.trans o3))
            (Fr.trans f1 (Fr.trans f2 f3)) v3')))
    exact (h.mono (by omega)).eq (by rw [hn]; simp [List.append_assoc])
  have inner : ∀ d, d.ram = a.ram → Oth a d → Fr a d TA → Valid C d →
      OutT C innerP d (25 * Λ + 25 + (L.length * (25 * Λ + 31) + L.length + 7) + 1)
        (Fn L.length ++ L.flatMap Fn) TA := by
    intro d e o f v
    have dk : d.env xkk = L.length := by rw [f xkk (by decide), hk]
    have dc : Cst d := Cst.of_fr hc f (by decide)
    have h0 := fem xkk (by decide) (by rw [hk]; exact hLk) d e o f v
    rw [hk] at h0
    refine seqT h0 (fun d' e' o' f' v' => ?_)
    have dc' : Cst d' := Cst.of_fr dc f' (by decide)
    have := OutT.weaken (T' := TA) (emAllO C sIn xkk (by decide) d' v' dc' hW Λ (by rw [f' xkk (by decide), dk, e', e, hL])
      (by rw [e', e, hL]; exact hLΛ)) (by decide)
    rw [e', e, hL] at this
    exact this
  have outer : ∀ d, d.ram = a.ram → Oth a d → Fr a d TA → Valid C d →
      OutT C outerP d (25 * Λ + 25 + (n * (9 * L.length + 25 * Λ + 44) + 4) + 1)
        (Fn (a.env xs) ++ ((List.range n).filter (fun x => decide (x ∉ L))).flatMap Fn) TA := by
    intro d e o f v
    have dc : Cst d := Cst.of_fr hc f (by decide)
    have := OutT.weaken (T' := TA) (outerO C d v dc hW n (by rw [f gN (by decide), hn]) L (by rw [e, hL])
      (by rw [f xkk (by decide), hk]) Λ hΛn) (by decide)
    rw [f xs (by decide)] at this
    exact this.mono (by omega)
  -- compose
  unfold preP
  have h := seqT hdr (fun d1 e1 o1 f1 v1' => seqT (hg d1 e1 o1 f1 v1') (fun d2 e2 o2 f2 v2' =>
    seqT (inner d2 (e2.trans e1) (o1.trans o2) (Fr.trans f1 f2) v2') (fun d3 e3 o3 f3 v3' =>
    seqT (outer d3 (e3.trans (e2.trans e1)) (o1.trans (o2.trans o3)) (Fr.trans f1 (Fr.trans f2 f3)) v3')
    (fun d4 e4 o4 f4 v4' => seqT (hh d4 (e4.trans (e3.trans (e2.trans e1))) (o1.trans (o2.trans (o3.trans o4)))
      (Fr.trans f1 (Fr.trans f2 (Fr.trans f3 f4))) v4') (fun d5 e5 o5 f5 v5' =>
    seqT (hr d5 (e5.trans (e4.trans (e3.trans (e2.trans e1)))) (o1.trans (o2.trans (o3.trans (o4.trans o5))))
      (Fr.trans f1 (Fr.trans f2 (Fr.trans f3 (Fr.trans f4 f5)))) v5') (fun d6 e6 o6 f6 v6' =>
    seqT (fem xV hxV hΛV d6 (e6.trans (e5.trans (e4.trans (e3.trans (e2.trans e1)))))
      (o1.trans (o2.trans (o3.trans (o4.trans (o5.trans o6)))))
      (Fr.trans f1 (Fr.trans f2 (Fr.trans f3 (Fr.trans f4 (Fr.trans f5 f6))))) v6')
      (fun d7 _ _ _ v7' => endO C d7 v7' hW TA)))))))
  exact (h.mono (by nlinarith)).eq (by simp [List.append_assoc])

end NearCubicGates.Close.CounterMachine.PrefixProg
