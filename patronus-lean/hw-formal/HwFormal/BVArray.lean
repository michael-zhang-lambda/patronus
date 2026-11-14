/- - Array is function from bitvector index to bitvector value -/
abbrev BVArray (iw dw : Nat) := BitVec iw → BitVec dw

namespace BVArray

/-- Return array with all indices initialized to one value -/
def const (v : BitVec dw) : BVArray iw dw := fun _ => v

/-- Read value at index -/
def read (a : BVArray iw dw) (i : BitVec iw) : BitVec dw := a i

/-- Write value at index -/
def write (a : BVArray iw dw) (i : BitVec iw) (v : BitVec dw) : BVArray iw dw :=
  fun j => if j == i then v else a j

/-- Return whether arrays have the same elements -/
def equals (a b : BVArray iw dw) : Bool :=
  (List.range (2^iw)).all (fun i => read a (BitVec.ofNat iw i) == read b (BitVec.ofNat iw i))

@[simp]
theorem equals_iff (iw dw : Nat) (a b : BVArray iw dw) :
  equals a b ↔ a = b := by
  simp only [equals, read, List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · intro h
    funext j
    simpa using h j.toNat j.isLt
  · rintro rfl _ _
    rfl

@[simp]
theorem read_const (iw dw : Nat) (i : BitVec iw) (v : BitVec dw) :
  read (const v) i = v := rfl

@[simp]
theorem read_write_same (iw dw : Nat) (i : BitVec iw) (v : BitVec dw) (a : BVArray iw dw) :
  read (write a i v) i = v := by
  simp [read, write]

@[simp]
theorem read_write_diff (iw dw : Nat) (i j : BitVec iw) (v : BitVec dw) (a : BVArray iw dw)
    (h : i ≠ j) :
  read (write a j v) i = read a i := by
  simp [read, write, h]

end BVArray
