import Proof.Gates.Cells.CellLoop3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

variable {C : Ctx}

def wPos : Fin VV := ⟨70, by decide⟩
def wY : Fin VV := ⟨71, by decide⟩

structure WSt (L : List ℕ) (e : DS VV MM) (pos : ℕ) (rest : List ℕ) : Prop where
  ram : e.ram sN = L
  rc : e.rc sN = pos
  pv : e.env wPos = pos
  dr : L.drop pos = rest
  le : pos ≤ L.length

def rdW (x : Fin VV) : St VV MM := .seq (.op (.rdM sN x)) (.op (.inc wPos))

theorem rdW_spec (x : Fin VV) (hx : x ≠ wPos) (L : List ℕ) (e : DS VV MM) (pos v : ℕ) (rest : List ℕ)
    (h : WSt L e pos (v :: rest)) (hW : pos + 1 < 2 ^ C.Wd) :
    Hs C (rdW x) e 3 (fun d => d.env x = v ∧ WSt L d (pos + 1) rest ∧ Agr e d [sN] [x, wPos]) := by
  have hlt : pos < L.length := by
    have := congrArg List.length h.dr; simp at this; omega
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_rdM C sN x e (by rw [h.rc, h.ram]; exact hlt)) (fun d hd => ?_)
  subst hd
  have hv : (e.ram sN).getD (e.rc sN) 0 = v := by
    rw [h.rc, h.ram, List.getD_eq_getElem?_getD]
    have : L[pos]? = (L.drop pos)[0]? := by rw [List.getElem?_drop]; rfl
    rw [this, h.dr]; rfl
  refine Hs.mono (hs_inc C wPos _ (by simp only [DS.adv]; rw [DS.set_env_ne _ _ (Ne.symm hx), h.pv]; exact hW))
    le_rfl ?_
  rintro b rfl
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, by omega⟩, ⟨fun m _ => ?_, fun m hm => ?_, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩⟩
  · rw [DS.set_env_ne _ _ hx]; simp only [DS.adv]; rw [DS.set_env_self, hv]
  · simp [DS.adv, DS.set, h.ram]
  · simp [DS.adv, DS.set, h.rc]
  · rw [DS.set_env_self]; simp only [DS.adv]; rw [DS.set_env_ne _ _ (Ne.symm hx), h.pv]
  · rw [← List.drop_drop, h.dr]; rfl
  · simp [DS.adv, DS.set]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    simp [DS.adv, DS.set, Function.update_of_ne hm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [DS.set_env_ne _ _ hy.2]; simp only [DS.adv]; rw [DS.set_env_ne _ _ hy.1]

def skW : St VV MM := .seq (advP sN wY) (.op (.add wPos wY))

theorem skW_spec (L : List ℕ) (e : DS VV MM) (pos : ℕ) (S rest : List ℕ) (h : WSt L e pos (S ++ rest))
    (hy : e.env wY = S.length) (hW : pos + S.length < 2 ^ C.Wd) :
    Hs C skW e (S.length * (1 + 4) + 4 + 2) (fun d => WSt L d (pos + S.length) rest ∧ d.env wY = e.env wY ∧
      Agr e d [sN] [c0, vJ, wPos]) := by
  have hlen : pos + S.length ≤ L.length := by
    have h1 := congrArg List.length h.dr; have := h.le; simp at h1; omega
  have ha := advP_spec (C := C) sN wY (by decide) (by decide) e (by rw [h.rc, h.ram, hy]; exact hlen)
    (by rw [hy]; omega)
  rw [hy] at ha
  refine Hs.seq (t1 := S.length * (1 + 4) + 4) (t2 := 1) ha (fun d ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ => ?_)
  have dy : d.env wY = S.length := by rw [d8 wY (by decide), hy]
  have dp : d.env wPos = pos := by rw [d8 wPos (by decide), h.pv]
  refine Hs.mono (hs_add C wPos wY d (by decide) (by rw [dp, dy]; exact hW)) le_rfl ?_
  rintro b rfl
  refine ⟨⟨by simp [d1, h.ram], by simp [d2, h.rc, hy], by rw [DS.set_env_self, dp, dy], ?_, hlen⟩,
    by rw [DS.set_env_ne _ _ (by decide), dy, hy],
    ⟨fun m _ => by simp [d1], fun m hm => ?_, d3, d4, d5, d6, d7, fun y hy' => ?_⟩⟩
  · rw [← List.drop_drop, h.dr, List.drop_left]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    simp [d2, Function.update_of_ne hm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
    rw [DS.set_env_ne _ _ hy'.2.2, d8 y (by simp [hy'.1, hy'.2.1])]

def skK (k : ℕ) : St VV MM := .seq (setK wY k) skW

theorem skK_spec (k : ℕ) (L : List ℕ) (e : DS VV MM) (pos : ℕ) (S rest : List ℕ) (h : WSt L e pos (S ++ rest))
    (hk : S.length = k) (hW : pos + k < 2 ^ C.Wd) :
    Hs C (skK k) e (2 * k + 3 + (k * (1 + 4) + 4 + 2) + 1) (fun d => WSt L d (pos + k) rest ∧
      Agr e d [sN] [wY, c0, vJ, wPos]) := by
  refine Hs.seq (setK_spec wY (by decide) k e (by omega)) (fun d ⟨d1, d2, d3⟩ => ?_)
  have hs := Same.of_sh d2
  have hd : WSt L d pos (S ++ rest) := ⟨by rw [hs.ram, h.ram], by rw [hs.rc, h.rc],
    by rw [d3 wPos (by decide), h.pv], h.dr, h.le⟩
  have := skW_spec (C := C) L d pos S rest hd (by rw [d1, hk]) (by omega)
  rw [hk] at this
  refine Hs.mono this le_rfl ?_
  rintro b ⟨b1, -, b3⟩
  refine ⟨b1, ?_⟩
  exact (Agr.of_fr_same (by decide) ⟨hs.ram, hs.rc, hs.ip, hs.out, hs.kin, hs.kout, hs.kc, d3⟩).trans
    (b3.weaken (by decide) (by decide))

end NearCubicGates.Close.Cells
