import Proof.Gates.CounterMachine.TabCallLog
import Proof.Gates.CounterMachine.TabCallDock

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.TabCallProg

variable (tP tK : ℕ)

abbrev NS : ℕ := 16 + tP + tK
abbrev NR : ℕ := 88

/-- An offset embedding. -/
def off {m N : ℕ} (a : ℕ) (h : a + m ≤ N) : Fin m ↪ Fin N :=
  ⟨fun i => ⟨a + i.val, by omega⟩, fun i j e => Fin.ext (by have := congrArg Fin.val e; simp at this; omega)⟩

@[simp] theorem off_val {m N : ℕ} (a : ℕ) (h : a + m ≤ N) (i : Fin m) : (off a h i).val = a + i.val := rfl

def sIN : Fin (NS tP tK + 1) := ⟨0, by simp only [NS]; omega⟩
def Y : Fin 8 ↪ Fin (NS tP tK + 1) := off 1 (by simp only [NS]; omega)
def sGJ : Fin (NS tP tK + 1) := ⟨9, by simp only [NS]; omega⟩
def sPR : Fin (NS tP tK + 1) := ⟨10, by simp only [NS]; omega⟩
def sTMP : Fin (NS tP tK + 1) := ⟨11, by simp only [NS]; omega⟩
def sPFX : Fin (NS tP tK + 1) := ⟨12, by simp only [NS]; omega⟩
def sLOG : Fin (NS tP tK + 1) := ⟨13, by simp only [NS]; omega⟩
def pmap : Fin tP ↪ Fin (NS tP tK + 1) := off 16 (by simp only [NS]; omega)
def kmap : Fin tK ↪ Fin (NS tP tK + 1) := off (16 + tP) (by simp only [NS]; omega)

def X : Fin 24 ↪ Fin NR := ⟨fun i => ⟨i.val, by simp only [NR]; omega⟩, fun i j e => Fin.ext (by simpa using congrArg Fin.val e)⟩
def F : Fin 24 ↪ Fin NR := off 24 (by simp only [NR]; omega)
def Q : Fin 16 ↪ Fin NR := off 48 (by simp only [NR]; omega)
def E : Fin 24 ↪ Fin NR := off 64 (by simp only [NR]; omega)

@[simp] theorem sIN_val : (sIN tP tK).val = 0 := rfl
@[simp] theorem Y_val (i : Fin 8) : (Y tP tK i).val = 1 + i.val := rfl
@[simp] theorem sGJ_val : (sGJ tP tK).val = 9 := rfl
@[simp] theorem sPR_val : (sPR tP tK).val = 10 := rfl
@[simp] theorem sTMP_val : (sTMP tP tK).val = 11 := rfl
@[simp] theorem sPFX_val : (sPFX tP tK).val = 12 := rfl
@[simp] theorem sLOG_val : (sLOG tP tK).val = 13 := rfl
@[simp] theorem pmap_val (j : Fin tP) : (pmap tP tK j).val = 16 + j.val := rfl
@[simp] theorem kmap_val (j : Fin tK) : (kmap tP tK j).val = 16 + tP + j.val := rfl
@[simp] theorem X_val (i : Fin 24) : (X i).val = i.val := rfl
@[simp] theorem F_val (i : Fin 24) : (F i).val = 24 + i.val := rfl
@[simp] theorem Q_val (i : Fin 16) : (Q i).val = 48 + i.val := rfl
@[simp] theorem E_val (i : Fin 24) : (E i).val = 64 + i.val := rfl

def sPIN : Fin (NS tP tK + 1) := ⟨16, by simp only [NS]; omega⟩
def sO : Fin (NS tP tK + 1) := ⟨16 + tP, by simp only [NS]; omega⟩
@[simp] theorem sPIN_val : (sPIN tP tK).val = 16 := rfl
@[simp] theorem sO_val : (sO tP tK).val = 16 + tP := rfl

/-- The unpack's streams: entry, gates, `Y 2`, `Y 4`, primes, scratch, `Y 5`, `Y 1`, `Y 3`. -/
def uSv : Fin 9 → ℕ := ![0, 9, 3, 5, 10, 11, 6, 2, 4]
theorem uSv_inj : Function.Injective uSv := by decide
theorem uSv_lt (i : Fin 9) : uSv i < 12 := by revert i; decide
def uS : Fin 9 ↪ Fin (NS tP tK + 1) :=
  ⟨fun i => ⟨uSv i, by have := uSv_lt i; simp only [NS]; omega⟩, fun i j e => uSv_inj (by simpa using congrArg Fin.val e)⟩
@[simp] theorem uS_val (i : Fin 9) : (uS tP tK i).val = uSv i := rfl

/-- The unpack's registers: `E 0` n, `E 1` kind tag, `E 2`, `X 14` G₀, `X 18` G₁, `E 3` k, `E 4` P, `X 8` e,
`X 1` J, `X 0` pair flag, `E 5` stage counter. -/
def uRv : Fin 11 → ℕ := ![64, 65, 66, 14, 18, 67, 68, 8, 1, 0, 69]
theorem uRv_inj : Function.Injective uRv := by decide
theorem uRv_lt (i : Fin 11) : uRv i < 88 := by revert i; decide
def uR : Fin 11 ↪ Fin NR :=
  ⟨fun i => ⟨uRv i, uRv_lt i⟩, fun i j e => uRv_inj (by simpa using congrArg Fin.val e)⟩
@[simp] theorem uR_val (i : Fin 11) : (uR i).val = uRv i := rfl

theorem uS_0 : uS tP tK 0 = sIN tP tK := Fin.ext rfl
theorem uS_1 : uS tP tK 1 = sGJ tP tK := Fin.ext rfl
theorem uS_2 : uS tP tK 2 = Y tP tK 2 := Fin.ext rfl
theorem uS_3 : uS tP tK 3 = Y tP tK 4 := Fin.ext rfl
theorem uS_4 : uS tP tK 4 = sPR tP tK := Fin.ext rfl
theorem uS_5 : uS tP tK 5 = sTMP tP tK := Fin.ext rfl
theorem uS_6 : uS tP tK 6 = Y tP tK 5 := Fin.ext rfl
theorem uS_7 : uS tP tK 7 = Y tP tK 1 := Fin.ext rfl
theorem uS_8 : uS tP tK 8 = Y tP tK 3 := Fin.ext rfl
theorem uR_0 : uR 0 = E 0 := Fin.ext rfl
theorem uR_1 : uR 1 = E 1 := Fin.ext rfl
theorem uR_2 : uR 2 = E 2 := Fin.ext rfl
theorem uR_3 : uR 3 = X 14 := Fin.ext rfl
theorem uR_4 : uR 4 = X 18 := Fin.ext rfl
theorem uR_5 : uR 5 = E 3 := Fin.ext rfl
theorem uR_6 : uR 6 = E 4 := Fin.ext rfl
theorem uR_7 : uR 7 = X 8 := Fin.ext rfl
theorem uR_8 : uR 8 = X 1 := Fin.ext rfl
theorem uR_9 : uR 9 = X 0 := Fin.ext rfl
theorem uR_10 : uR 10 = E 5 := Fin.ext rfl

/-- The descriptor registers `E 6 … E 9` and the log registers `E 13 … E 18`. -/
def Td : Fin 4 ↪ Fin NR := off 70 (by simp only [NR]; omega)
def Gl : Fin 6 ↪ Fin NR := off 77 (by simp only [NR]; omega)
@[simp] theorem Td_val (i : Fin 4) : (Td i).val = 70 + i.val := rfl
@[simp] theorem Gl_val (i : Fin 6) : (Gl i).val = 77 + i.val := rfl

theorem fin_ne {n : ℕ} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

theorem fin_nmem {n : ℕ} {a : Fin n} {l : List (Fin n)} (h : a.val ∉ l.map Fin.val) : a ∉ l :=
  fun hm => h (List.mem_map_of_mem hm)

/-- Distinctness of layout indices, by their values. -/
macro "lne" : tactic => `(tactic| first
  | (apply fin_ne; simp [uSv, uRv]; done)
  | (intro e; have := congrArg Fin.val e; simp [uSv, uRv] at this; try omega))

/-- Non-membership of a layout index in a list of layout indices, by their values. -/
macro "lnm" : tactic => `(tactic| first
  | (apply fin_nmem; simp [uSv, uRv]; done)
  | (apply fin_nmem; simp [uSv, uRv]; split_ifs <;> simp))

end NearCubicGates.Close.CounterMachine.TabCallProg
