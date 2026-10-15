import Proof.MachineModel.ClockPaddingReady

/-! Complete, physically bounded inner frames in the external U input.  The
suffix after the third frame is deliberately unrestricted. -/
namespace NearCubicWires.RepairOrdinary.UInputSyntax
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def peel : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: tail => some ([], tail)
  | true :: [] => none
  | true :: b :: tail => (peel tail).map fun p => (b :: p.1, p.2)

theorem peel_frame (bits tail : List Bool) : peel (frame bits ++ tail) = some (bits,tail) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame,peel,ih]

theorem peel_sound (raw bits tail : List Bool) (h : peel raw = some (bits,tail)) :
    raw = frame bits ++ tail := by
  induction raw using peel.induct generalizing bits tail with
  | case1 => simp [peel] at h
  | case2 rest =>
    simp only [peel,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    rfl
  | case3 => simp [peel] at h
  | case4 b rest ih =>
    cases hp : peel rest with
    | none => simp [peel,hp] at h
    | some p =>
      rcases p with ⟨xs,ys⟩
      simp only [peel,hp,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      rw [ih _ _ hp]
      rfl

def advance (q : Fin 7) (b : Bool) : Fin 7 :=
  if h6 : q.val=6 then 6 else if ho : q.val%2=1 then ⟨q.val-1,by have := q.isLt; omega⟩
  else if b then ⟨q.val+1,by have := q.isLt; omega⟩ else ⟨q.val+2,by have := q.isLt; omega⟩
def accepts (q : Fin 7) (bits : List Bool) : Bool :=
  (bits.foldl advance q).val == 6

@[simp] theorem accepts_nil (q : Fin 7) : accepts q [] = (q.val == 6) := rfl
@[simp] theorem accepts_cons (q : Fin 7) (b : Bool) (bits : List Bool) :
    accepts q (b::bits) = accepts (advance q b) bits := rfl
@[simp] theorem accepts_done (bits : List Bool) : accepts 6 bits = true := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simpa [accepts_cons,advance] using ih

def marker (j : Fin 3) : Fin 7 := ⟨2*j.val,by omega⟩
def after (j : Fin 3) : Fin 7 := ⟨2*j.val+2,by omega⟩

theorem accepts_peel (j : Fin 3) (bits : List Bool) :
    accepts (marker j) bits = match peel bits with
      | none => false
      | some p => accepts (after j) p.2 := by
  induction bits using peel.induct with
  | case1 => fin_cases j <;> rfl
  | case2 tail => fin_cases j <;> rfl
  | case3 => fin_cases j <;> rfl
  | case4 b tail ih =>
    have ha : advance (advance (marker j) true) b = marker j := by
      fin_cases j <;> cases b <;> rfl
    simp only [accepts_cons,ha,peel]
    rw [ih]
    cases peel tail <;> rfl

def Fields (raw : List Bool) : Prop :=
  ∃ code input bound padding, raw = frame code ++ (frame input ++ (frame bound ++ padding))

theorem accepts_iff (raw : List Bool) : accepts 0 raw = true ↔ Fields raw := by
  have h0 := accepts_peel 0 raw
  change accepts 0 raw = _ at h0
  rw [h0]
  constructor
  · intro h
    cases hp : peel raw with
    | none => simp [hp] at h
    | some p =>
      rcases p with ⟨code,tail⟩
      simp only [hp] at h
      have h1 := accepts_peel 1 tail
      change accepts 2 tail = _ at h1
      change accepts 2 tail = true at h
      rw [h1] at h
      cases hx : peel tail with
      | none => simp [hx] at h
      | some p =>
        rcases p with ⟨input,rest⟩
        simp only [hx] at h
        have h2 := accepts_peel 2 rest
        change accepts 4 rest = _ at h2
        change accepts 4 rest = true at h
        rw [h2] at h
        cases hb : peel rest with
        | none => simp [hb] at h
        | some p =>
          rcases p with ⟨bound,padding⟩
          exact ⟨code,input,bound,padding,by rw [peel_sound _ _ _ hp,peel_sound _ _ _ hx,peel_sound _ _ _ hb]⟩
  · rintro ⟨code,input,bound,padding,rfl⟩
    rw [peel_frame]
    change accepts 2 (frame input ++ (frame bound ++ padding)) = true
    have h1 := accepts_peel 1 (frame input ++ (frame bound ++ padding))
    change accepts 2 _ = _ at h1
    rw [h1,peel_frame]
    change accepts 4 (frame bound ++ padding) = true
    have h2 := accepts_peel 2 (frame bound ++ padding)
    change accepts 4 _ = _ at h2
    rw [h2,peel_frame]
    exact accepts_done padding

theorem fields_length (raw : List Bool) (h : Fields raw) : 3 ≤ raw.length := by
  rcases h with ⟨code,input,bound,padding,rfl⟩
  simp only [List.length_append,frame_length]
  omega

theorem short_reject (raw : List Bool) (h : raw.length < 3) : accepts 0 raw = false := by
  cases ha : accepts 0 raw
  · rfl
  · have := fields_length raw ((accepts_iff raw).mp ha)
    omega

end NearCubicWires.RepairOrdinary.UInputSyntax
