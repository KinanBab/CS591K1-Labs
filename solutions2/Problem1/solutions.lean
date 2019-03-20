-- Problem 1: filtering elements of a list (30 points)

-- Part A: Implement a filter (5 points)
-- only keeps elements that satisfy the condition F
@[simp] def filter{T} : (T -> bool) -> list T -> list T
| F list.nil := list.nil
| F (list.cons h l') :=
  if F h
   then list.cons h (filter F l')
   else filter F l'


-- Part B: filter and boolean and (5 points)
theorem filter_and (T: Type) (F1 F2: T -> bool) (l: list T) :
  filter (λ x, F1 x ∧ F2 x) l = filter F1 (filter F2 l) :=
begin
  induction l,

  simp,

  simp,
  cases (F2 l_hd),
    simp, assumption,

    simp, 
    cases (F1 l_hd),
      simp, assumption,
      simp, assumption,
end


-- Part C: filter produces an equal or smaller array (5 points)
theorem filter_len (T: Type) (F1: T -> bool) (l: list T) :
  list.length (filter F1 l) ≤ list.length l :=
begin
  induction l,
    simp,

    simp,
    cases (F1 l_hd),
      simp,
      rewrite nat.add_comm,
      rewrite nat.add_one,
      apply nat.le_trans,
      assumption,
      apply nat.le_succ,

      simp,
      rewrite nat.add_comm,
      rewrite nat.add_one,
      rewrite nat.add_comm,
      rewrite nat.add_one,
      apply nat.succ_le_succ,
      assumption,
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
  -- HINT: you will need to use cases (<expression>)
  --       instead of cases, so that the case is added as a hypothesis
  -- HINT: #check eq_ff_of_not_eq_tt at https://github.com/leanprover/lean/blob/master/library/init/data/bool/lemmas.lean
  induction l,
    simp,

    simp,
    cases H: (F1 l_hd),
      simp,
      assumption,

      simp,
      apply and.intro; assumption,
end


-- part E: correctness (5 points)
-- are these properties enough to guarantee correctness? can you
-- think of an example that satisfy these properties but is incorrect?
-- You do not have to prove it or write it down, just give an informal arguments in comments

-- ANSWER: No, it does not guarantee correctness: here is a simple counter example
@[simp] def filter_incorrect{T} : (T → bool) → list T → list T
| F l := list.nil

theorem filter_and_incorrect (T: Type) (F1 F2: T → bool) (l: list T) :
  filter_incorrect (λ x, F1 x ∧ F2 x) l = filter_incorrect F1 (filter_incorrect F2 l) :=
begin
  simp,
end

theorem filter_len_incorrect (T: Type) (F1: T -> bool) (l: list T) :
  list.length (filter_incorrect F1 l) ≤ list.length l :=
begin
  simp,
  apply nat.zero_le,
end

theorem filter_safe_incorrect (T: Type) (F1: T -> bool) (l: list T) :
  is_safe F1 (filter_incorrect F1 l) = tt :=
begin
  simp,
end
