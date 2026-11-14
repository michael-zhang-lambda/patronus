/-- Transition system -/
structure TransSys (S I O : Type) where
  init : O → I → S
  next : S → I → S
  constraint : S → I → Bool
  bad : S → I → Bool

/-- Return trace for transistion system execution on finite number of inputs -/
def TransSys.simulate (sys : TransSys S I O) (o : O) (is : List I) : List S :=
  match is with
  | [] => []
  | i :: is =>
    let rec aux sys s is :=
      match is with
      | [] => [s]
      | i :: is => s :: aux sys (sys.next s i) is
    aux sys (sys.init o i) (i :: is)

/-- Return printable execution trace -/
def TransSys.formatTrace [ToString S] (sys : TransSys S I O) (o : O) (is : List I) : String :=
  let trace := sys.simulate o is
  let format : Nat → (S × I) → String := fun c (s, i) =>
    s!"{c}, {toString s}, bad={if sys.bad s i then 1 else 0}, constraint={if sys.constraint s i then 1 else 0}"
  let stateInput := trace.zip is
  "\n".intercalate (stateInput.mapIdx format)

/-- Return for state after `n` steps of execution from initial states -/
def TransSys.run  (sys : TransSys S I O) (o : O) (inp : Nat → I) : Nat → S
  | 0 => sys.init o (inp 0)
  | n + 1 => sys.next (sys.run o inp n) (inp n)

theorem TransSys.length_simulate_aux (sys : TransSys S I O) (s : S) (is : List I) :
    (simulate.aux sys s is).length = is.length + 1 := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih => simp [simulate.aux, ih]

@[simp]
theorem TransSys.length_simulate (sys : TransSys S I O) (o : O) (is : List I) :
    (sys.simulate o is).length = if is = [] then 0 else is.length + 1 := by
  cases is with
  | nil => rfl
  | cons i is => simp [simulate, length_simulate_aux]

/-- The `n`-th state of `simulate.aux` is the fold of `next` over the first `n` inputs. -/
theorem TransSys.getElem_simulate_aux (sys : TransSys S I O) (s : S) (is : List I) (n : Nat)
    (h : n < (simulate.aux sys s is).length) :
    (simulate.aux sys s is)[n] = (is.take n).foldl sys.next s := by
  induction is generalizing s n with
  | nil =>
    simp [simulate.aux] at h
    subst h
    rfl
  | cons i is ih =>
    cases n with
    | zero => rfl
    | succ n => simp [simulate.aux, ih]

/-- Within the input list, `run` is the fold of `next` over the first `n` inputs. -/
theorem TransSys.run_eq_foldl (sys : TransSys S I O) (o : O) (is : List I) (d : I) (n : Nat)
    (h : n ≤ is.length) :
    sys.run o (fun k => is.getD k d) n = (is.take n).foldl sys.next (sys.init o (is.getD 0 d)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : n < is.length := by omega
    have hd : is.getD n d = is[n] := by simp [List.getD_eq_getElem?_getD, hn]
    rw [run, ih (by omega), hd, List.take_add_one, List.getElem?_eq_getElem hn,
      Option.toList_some, List.foldl_append]
    rfl

theorem TransSys.simulate_eq_run (sys : TransSys S I O) (o : O) (is : List I) (n : Nat) (d : I)
    (h : n < (sys.simulate o is).length) :
    (sys.simulate o is)[n] = sys.run o (fun k => is.getD k d) n := by
  cases is with
  | nil => simp at h
  | cons i is =>
    simp at h
    rw [sys.run_eq_foldl o (i :: is) d n (by simp; omega)]
    exact sys.getElem_simulate_aux _ (i :: is) n _

/-- Create proposition that constraints holds up to `n` transitions -/
def TransSys.validUpTo (sys : TransSys S I O) (o : O) (inp : Nat → I) (n : Nat) : Prop :=
  ∀k ≤ n, sys.constraint (sys.run o inp k) (inp k) = true

def TransSys.safe (sys : TransSys S I O) : Prop :=
  ∀(o : O) (inp : Nat → I) (n : Nat), sys.validUpTo o inp n → sys.bad (sys.run o inp n) (inp n) = false
