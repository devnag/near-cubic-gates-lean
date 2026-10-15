import Proof.Gates.Expand.Print7

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicGates.Close.Expand

abbrev NS : ℕ := 63
abbrev NR : ℕ := 63

def sE (o k : ℕ) (h : o + k ≤ NS + 1) : Fin k ↪ Fin (NS + 1) :=
  ⟨fun i => ⟨o + i.val, by omega⟩, fun a b e => Fin.ext (by have := congrArg Fin.val e; simp at this; omega)⟩

def rE (o k : ℕ) (h : o + k ≤ NR) : Fin k ↪ Fin NR :=
  ⟨fun i => ⟨o + i.val, by omega⟩, fun a b e => Fin.ext (by have := congrArg Fin.val e; simp at this; omega)⟩

@[simp] theorem sE_val (o k : ℕ) (h : o + k ≤ NS + 1) (i : Fin k) : (sE o k h i).val = o + i.val := rfl
@[simp] theorem rE_val (o k : ℕ) (h : o + k ≤ NR) (i : Fin k) : (rE o k h i).val = o + i.val := rfl

def U : Fin 10 ↪ Fin (NS + 1) := sE 0 10 (by norm_num)
def UF : Fin 12 ↪ Fin (NS + 1) := sE 10 12 (by norm_num)
def X : Fin 4 ↪ Fin (NS + 1) := sE 22 4 (by norm_num)
def MB : Fin 18 ↪ Fin (NS + 1) := sE 26 18 (by norm_num)
def ORC : Fin (NS + 1) := ⟨44, by norm_num⟩
def PB : Fin 14 ↪ Fin (NS + 1) := sE 45 14 (by norm_num)
def O : Fin (NS + 1) := ⟨59, by norm_num⟩
def G : Fin 4 ↪ Fin (NS + 1) := sE 60 4 (by norm_num)

def R : Fin 12 ↪ Fin NR := rE 0 12 (by norm_num)
def RF : Fin 14 ↪ Fin NR := rE 12 14 (by norm_num)
def Y : Fin 8 ↪ Fin NR := rE 26 8 (by norm_num)
def MR : Fin 9 ↪ Fin NR := rE 34 9 (by norm_num)
def PG : Fin 5 ↪ Fin NR := rE 43 5 (by norm_num)
def PR : Fin 4 ↪ Fin NR := rE 48 4 (by norm_num)
def OP : Fin NR := ⟨52, by norm_num⟩
def CI : Fin NR := ⟨53, by norm_num⟩
def CW : Fin NR := ⟨54, by norm_num⟩
def GR : Fin 8 ↪ Fin NR := rE 55 8 (by norm_num)

def MSf : Fin 3 → Fin (NS + 1) := ![⟨12, by norm_num⟩, ⟨22, by norm_num⟩, ⟨44, by norm_num⟩]
def MS : Fin 3 ↪ Fin (NS + 1) := ⟨MSf, by intro a b h; fin_cases a <;> fin_cases b <;> simp_all [MSf]⟩

@[simp] theorem U_val (i : Fin 10) : (U i).val = i.val := by simp [U]
@[simp] theorem UF_val (i : Fin 12) : (UF i).val = 10 + i.val := rfl
@[simp] theorem X_val (i : Fin 4) : (X i).val = 22 + i.val := rfl
@[simp] theorem MB_val (i : Fin 18) : (MB i).val = 26 + i.val := rfl
@[simp] theorem PB_val (i : Fin 14) : (PB i).val = 45 + i.val := rfl
@[simp] theorem G_val (i : Fin 4) : (G i).val = 60 + i.val := rfl
@[simp] theorem ORC_val : ORC.val = 44 := rfl
@[simp] theorem O_val : O.val = 59 := rfl
@[simp] theorem R_val (i : Fin 12) : (R i).val = i.val := by simp [R]
@[simp] theorem RF_val (i : Fin 14) : (RF i).val = 12 + i.val := rfl
@[simp] theorem Y_val (i : Fin 8) : (Y i).val = 26 + i.val := rfl
@[simp] theorem MR_val (i : Fin 9) : (MR i).val = 34 + i.val := rfl
@[simp] theorem PG_val (i : Fin 5) : (PG i).val = 43 + i.val := rfl
@[simp] theorem PR_val (i : Fin 4) : (PR i).val = 48 + i.val := rfl
@[simp] theorem GR_val (i : Fin 8) : (GR i).val = 55 + i.val := rfl
@[simp] theorem OP_val : OP.val = 52 := rfl
@[simp] theorem CI_val : CI.val = 53 := rfl
@[simp] theorem CW_val : CW.val = 54 := rfl

theorem MS_0 : MS 0 = UF 2 := rfl
theorem MS_1 : MS 1 = X 0 := rfl
theorem MS_2 : MS 2 = ORC := rfl

theorem MS_val (i : Fin 3) : (MS i).val = 12 + 10 * i.val ∨ (MS i).val = 44 := by
  fin_cases i <;> simp [MS, MSf]

/-- Two streams/registers differ as soon as their indices do. -/
theorem sne {a b : Fin (NS + 1)} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)
theorem rne {a b : Fin NR} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

def Lc : Lay NS NR where
  U := U
  R := R
  UF := UF
  RF := RF
  X := X
  Y := Y
  dUUF i j := sne (by simp; omega)
  dUX i j := sne (by simp; omega)
  dUFX i j := sne (by simp; omega)
  dRRF i j := rne (by simp; omega)
  dRY i j := rne (by simp; omega)
  dRFY i j := rne (by simp; omega)

theorem hMS : ∀ i j, MB i ≠ MS j := by
  intro i j; apply sne; have := i.isLt; fin_cases j <;> simp [MS, MSf] <;> omega

theorem pplay : PPLay PB PG PR O OP ORC (MB 17) CI CW where
  pl := ⟨fun i => sne (by simp; omega), fun i j => rne (by simp; omega), fun i => rne (by simp; omega),
    fun i => rne (by simp; omega)⟩
  bi i := sne (by simp; omega)
  bc i := sne (by simp; omega)
  io := sne (by simp)
  co := sne (by simp)
  ic := sne (by simp)
  cicw := rne (by simp)
  gci i := rne (by simp; omega)
  gcw i := rne (by simp; omega)
  pci i := rne (by simp; omega)
  pcw i := rne (by simp; omega)
  oci := rne (by simp)
  ocw := rne (by simp)

end NearCubicGates.Close.Expand.Layout
