import Proof.Gates.Cells.Enc

set_option autoImplicit false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimT.ReadEq

variable {V M : ℕ}

/-- The callee's tape count. -/
abbrev TSK (K : Callee) : ℕ := K.wf.program.tapeCount
/-- The tape count of a run's callee. -/
abbrev TS (C : Ctx) : ℕ := TSK C.K

def Rk (C : Ctx) : ℕ := 2 * C.Lk + C.Bk + 3

/-- **The encoding of a language state.** -/
structure Enc (C : Ctx) (a : DS V M) (σ : WState (NS M (TS C) V) (NR M)) : Prop where
  inS : σ.st sIN = frame C.inp
  inH : σ.sh sIN = 2 * a.ip
  inR : σ.val rIP = 2 * a.ip
  outS : σ.st sOUT = a.out
  outH : σ.sh sOUT = a.out.length
  outR : σ.val rOP = a.out.length
  zero : NumOn σ sZ C.Wd 0
  var : ∀ x, NumOn σ (vs x) C.Wd (a.env x)
  ramS : ∀ m, σ.st (sM m) = encR C.Wd (a.ram m)
  ramH : ∀ m, σ.sh (sM m) = (2 * C.Wd + 1) * a.rc m
  ramR : ∀ m, σ.val (rM m) = (2 * C.Wd + 1) * a.rc m
  shL : ∀ m, (σ.st (sS m)).length ≤ (σ.st (sM m)).length
  shH : ∀ m, σ.sh (sS m) = 0
  tpS : ∃ v, σ.st sTP = frame (binary C.Wd v)
  tpH : σ.sh sTP = 0
  kiS : RdEq (σ.st sKI) (frame a.kin)
  kiH : σ.sh sKI = 2 * a.kin.length
  kiR : σ.val rKI = 2 * a.kin.length
  koS : RdEq (σ.st sKO) a.kout
  koH : σ.sh sKO = a.kc
  koR : σ.val rKO = a.kc
  scS : ∀ j, RdEq (σ.st (sT j)) []
  scH : ∀ j, σ.sh (sT j) = 0
  lgS : σ.st sLG = List.replicate C.Bk false
  lgH : σ.sh sLG = 0
  ruS : σ.st sRU = List.replicate (Rk C) true
  ruH : σ.sh sRU = 0
  zF : σ.val rF = 0
  zR : σ.val rR = 0
  zG : σ.val rG = 0
  zK : σ.val rK = 0
  zT : σ.val rT = 0
  zC1 : σ.val rC1 = 0
  zC2 : σ.val rC2 = 0
  cell : σ.cell = false

section Frame
variable {C : Ctx} {a : DS V M} {σ : WState (NS M (TS C) V) (NR M)}

/-- A stream that is no variable stream. -/
def NotVar (i : Fin (NS M (TS C) V + 1)) : Prop := ∀ x : Fin V, i ≠ vs x

theorem notVar_IN : NotVar (C := C) (V := V) (M := M) sIN := by intro x; lay_ne
theorem notVar_OUT : NotVar (C := C) (V := V) (M := M) sOUT := by intro x; lay_ne
theorem notVar_Z : NotVar (C := C) (V := V) (M := M) sZ := by intro x; lay_ne
theorem notVar_KI : NotVar (C := C) (V := V) (M := M) sKI := by intro x; lay_ne
theorem notVar_KO : NotVar (C := C) (V := V) (M := M) sKO := by intro x; lay_ne
theorem notVar_LG : NotVar (C := C) (V := V) (M := M) sLG := by intro x; lay_ne
theorem notVar_RU : NotVar (C := C) (V := V) (M := M) sRU := by intro x; lay_ne
theorem notVar_TP : NotVar (C := C) (V := V) (M := M) sTP := by intro x; lay_ne
theorem notVar_S (m : Fin M) : NotVar (C := C) (V := V) (M := M) (sS m) := by
  intro x e; have := congrArg Fin.val e; simp at this; omega
theorem notVar_M (m : Fin M) : NotVar (C := C) (V := V) (M := M) (sM m) := by
  intro x e; have := congrArg Fin.val e; simp at this; omega
theorem notVar_T (j : Fin (TS C)) : NotVar (C := C) (V := V) (M := M) (sT j) := by
  intro x e; have := congrArg Fin.val e; simp at this; omega

/-- **Variables only.** A state that agrees with `σ` off the variable streams, whose variable streams hold the
values of `a'`, encodes `a'` when `a'` differs from `a` only in its variables. -/
theorem Enc.vars (h : Enc C a σ) (a' : DS V M) (σ' : WState (NS M (TS C) V) (NR M))
    (hst : ∀ i, NotVar i → σ'.st i = σ.st i) (hsh : σ'.sh = σ.sh) (hval : σ'.val = σ.val)
    (hcell : σ'.cell = σ.cell) (hvar : ∀ x, NumOn σ' (vs x) C.Wd (a'.env x)) (hip : a'.ip = a.ip)
    (hout : a'.out = a.out) (hram : a'.ram = a.ram) (hrc : a'.rc = a.rc) (hkin : a'.kin = a.kin)
    (hkout : a'.kout = a.kout) (hkc : a'.kc = a.kc) : Enc C a' σ' where
  inS := by rw [hst _ notVar_IN]; exact h.inS
  inH := by rw [hsh, hip]; exact h.inH
  inR := by rw [hval, hip]; exact h.inR
  outS := by rw [hst _ notVar_OUT, hout]; exact h.outS
  outH := by rw [hsh, hout]; exact h.outH
  outR := by rw [hval, hout]; exact h.outR
  zero := ⟨by rw [hst _ notVar_Z]; exact h.zero.1, by rw [hsh]; exact h.zero.2⟩
  var := hvar
  ramS := fun m => by rw [hst _ (notVar_M m), hram]; exact h.ramS m
  ramH := fun m => by rw [hsh, hrc]; exact h.ramH m
  ramR := fun m => by rw [hval, hrc]; exact h.ramR m
  shL := fun m => by rw [hst _ (notVar_S m), hst _ (notVar_M m)]; exact h.shL m
  shH := fun m => by rw [hsh]; exact h.shH m
  tpS := by rw [hst _ notVar_TP]; exact h.tpS
  tpH := by rw [hsh]; exact h.tpH
  kiS := by rw [hst _ notVar_KI, hkin]; exact h.kiS
  kiH := by rw [hsh, hkin]; exact h.kiH
  kiR := by rw [hval, hkin]; exact h.kiR
  koS := by rw [hst _ notVar_KO, hkout]; exact h.koS
  koH := by rw [hsh, hkc]; exact h.koH
  koR := by rw [hval, hkc]; exact h.koR
  scS := fun j => by rw [hst _ (notVar_T j)]; exact h.scS j
  scH := fun j => by rw [hsh]; exact h.scH j
  lgS := by rw [hst _ notVar_LG]; exact h.lgS
  lgH := by rw [hsh]; exact h.lgH
  ruS := by rw [hst _ notVar_RU]; exact h.ruS
  ruH := by rw [hsh]; exact h.ruH
  zF := by rw [hval]; exact h.zF
  zR := by rw [hval]; exact h.zR
  zG := by rw [hval]; exact h.zG
  zK := by rw [hval]; exact h.zK
  zT := by rw [hval]; exact h.zT
  zC1 := by rw [hval]; exact h.zC1
  zC2 := by rw [hval]; exact h.zC2
  cell := by rw [hcell]; exact h.cell

/-- Writing one variable. -/
theorem Enc.setVar (h : Enc C a σ) (x : Fin V) (v : ℕ) :
    Enc C (a.set x v) (σ.sets (vs x) (frame (binary C.Wd v))) := by
  refine h.vars _ _ (fun i hi => ?_) rfl rfl rfl (fun y => ?_) rfl rfl rfl rfl rfl rfl rfl
  · simp [Function.update_of_ne (hi x)]
  · by_cases hy : y = x
    · subst hy; exact ⟨by simp, by simpa using (h.var y).2⟩
    · refine ⟨?_, by simpa using (h.var y).2⟩
      simp only [WState.sets_st, Function.update_of_ne (vs_inj hy), DS.set_env_ne _ _ hy]
      exact (h.var y).1

/-- Writing the zero word again changes nothing. -/
theorem Enc.setZ (h : Enc C a σ) : σ.sets sZ (frame (binary C.Wd 0)) = σ := BinW.sets_same h.zero.1

/-- Setting the flag register `F` back to `0` changes nothing. -/
theorem Enc.setvF (h : Enc C a σ) : σ.setv rF 0 = σ := BinW.setv_same h.zF

end Frame

end NearCubicGates.Close.Cells
