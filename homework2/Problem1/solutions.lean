-- Problem 1: filtering elements of a list (30 points)

-- Part A: Implement a filter (5 points)
-- only keeps elements that satisfy the condition F
@[simp] def filter{T} : (T -> bool) -> list T -> list T
-- Implementation goes here
| F l := l


-- Part B: filter and boolean and (5 points)
theorem filter_and (T: Type) (F1 F2: T -> bool) (l: list T) :
  filter (λ x, F1 x ∧ F2 x) l = filter F1 (filter F2 l) :=
begin
  -- Proof goes here
  -- HINT: [cases] are your friend
end


-- Part C: filter produces an equal or smaller array (5 points)
theorem filter_len (T: Type) (F1: T -> bool) (l: list T) :
  list.length (filter F1 l) ≤ list.length l :=
begin
  -- Proof goes here
  -- HINT: check nat.add_comm, nat.add_one, and nat.le_trans and nat.succ_le_succ
  -- use the first three with [rewrite] and [apply] the last one when applicable
end


-- Part D: filter is safe (10 points)
-- it does not add any elments that do not satisify the condition
@[simp] def is_safe{T} : (T -> bool) -> list T -> bool
| F list.nil := tt
| F (list.cons h l') := (F h) && (is_safe F l')
theorem filter_safe (T: Type) (F1: T -> bool) (l: list T) :
  is_safe F1 (filter F1 l) = tt :=
begin
  -- Proof goes here
  -- HINT: you will need to use cases H: (<expression>)
  --       instead of cases (<expression>), so that the case is added as a hypothesis with name H
  -- HINT: #check eq_ff_of_not_eq_tt at https://github.com/leanprover/lean/blob/master/library/init/data/bool/lemmas.lean
end


-- part E: correctness (5 points)
-- are these properties enough to guarantee correctness? can you
-- think of an example that satisfy these properties but is incorrect?
-- You do not have to prove it or write it down, just give an informal arguments in comments

